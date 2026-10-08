-- Prove2me | solution 1 for WeilDefect.MarkerStability.regularized_marker_isometric_compression
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T14:03:54.400653+00:00
-- url     : https://prove2.me/submissions/7e127bce-9aaa-4cf4-9c91-e81d249a94e9

import Definitions.Def_WeilMarker_regularized_cost
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace ComplexOrder Topology
open ContinuousLinearMap Filter
noncomputable section
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inverse_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ operatorInverse A := by
  rw [operatorInverse, Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)

theorem inverse_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (c : ℝ) (hc : 0 < c) :
    operatorInverse (c • A) = c⁻¹ • operatorInverse A := by
  have hunit := (hA.smul hc).isUnit
  have hright : (c • A) * (c⁻¹ • operatorInverse A) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
    exact Ring.mul_inverse_cancel A hA.isUnit
  calc
    operatorInverse (c • A) = operatorInverse (c • A) * 1 := (mul_one _).symm
    _ = operatorInverse (c • A) * ((c • A) * (c⁻¹ • operatorInverse A)) := by rw [hright]
    _ = (operatorInverse (c • A) * (c • A)) * (c⁻¹ • operatorInverse A) := (mul_assoc _ _ _).symm
    _ = c⁻¹ • operatorInverse A := by
      rw [show operatorInverse (c • A) * (c • A) = 1 from Ring.inverse_mul_cancel _ hunit,
        one_mul]

theorem cost_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ selectedCost A N := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (inverse_nonnegative A hA)).conj_adjoint N.adjoint
  simpa [selectedCost] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_mono {A B : H →L[ℂ] H}
    (hAB : A ≤ B) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    selectedCost B N ≤ selectedCost A N := by
  have hi := CStarAlgebra.ringInverse_le_ringInverse hAB hA
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hi)).conj_adjoint N.adjoint
  apply sub_nonneg.mp
  simpa [selectedCost, operatorInverse, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_smul A hA c hc]
  ext x
  simp [selectedCost]

theorem marker_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ marker A N :=
  inverse_nonnegative _ (isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N))

theorem marker_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : marker A N ≤ 1 := by
  have h := CStarAlgebra.ringInverse_le_ringInverse
    (le_add_of_nonneg_right (cost_nonnegative A hA N)) isStrictlyPositive_one
  simpa [marker, operatorInverse] using h


end WeilDefect.MarkerStability
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Compression decreases original selected inverse cost. Both covariances are
strictly positive and their compression identity is explicit. -/
theorem selectedCost_compression_le (U : H →L[ℂ] K)
    (A : K →L[ℂ] K) (A₀ : H →L[ℂ] H)
    (hA : IsStrictlyPositive A) (hA₀ : IsStrictlyPositive A₀)
    (hcomp : U.adjoint ∘L A ∘L U = A₀) (N : J →L[ℂ] K) :
    selectedCost A₀ (U.adjoint ∘L N) ≤ selectedCost A N := by
  let n := U.adjoint ∘L N
  have hAp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg
  have hb := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (cost_nonnegative A hA N)
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (cost_nonnegative A₀ hA₀ n)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hb.isSelfAdjoint.sub hs.isSelfAdjoint, ?_⟩
  intro a
  let y := operatorInverse A₀ (n a)
  let z := operatorInverse A (N a)
  have hAy : A₀ y = n a := by
    change (A₀ ∘L operatorInverse A₀) (n a) = _
    exact congrArg (fun T : H →L[ℂ] H => T (n a)) (Ring.mul_inverse_cancel A₀ hA₀.isUnit)
  have hAz : A z = N a := by
    change (A ∘L operatorInverse A) (N a) = _
    exact congrArg (fun T : K →L[ℂ] K => T (N a)) (Ring.mul_inverse_cancel A hA.isUnit)
  have hz : RCLike.re ⟪N a, z⟫_ℂ = RCLike.re ⟪selectedCost A N a, a⟫_ℂ := by
    rw [← N.adjoint_inner_right]
    change RCLike.re ⟪a, selectedCost A N a⟫_ℂ = _
    exact inner_re_symm _ _
  have hy : RCLike.re ⟪N a, U y⟫_ℂ = RCLike.re ⟪selectedCost A₀ n a, a⟫_ℂ := by
    rw [← U.adjoint_inner_left]
    change RCLike.re ⟪n a, y⟫_ℂ = _
    rw [← n.adjoint_inner_right]
    change RCLike.re ⟪a, selectedCost A₀ n a⟫_ℂ = _
    exact inner_re_symm _ _
  have hyy : RCLike.re ⟪A (U y), U y⟫_ℂ = RCLike.re ⟪selectedCost A₀ n a, a⟫_ℂ := by
    rw [← U.adjoint_inner_left]
    change RCLike.re ⟪(U.adjoint ∘L A ∘L U) y, y⟫_ℂ = _
    rw [hcomp, hAy]
    change RCLike.re ⟪U.adjoint (N a), y⟫_ℂ = _
    rw [U.adjoint_inner_left]
    exact hy
  have hcross : RCLike.re ⟪A (U y), z⟫_ℂ = RCLike.re ⟪selectedCost A₀ n a, a⟫_ℂ := by
    rw [hAp.inner_left_eq_inner_right, hAz]
    exact (inner_re_symm _ _).trans hy
  have hp := hAp.re_inner_nonneg_left (z - U y)
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub] at hp
  rw [hAz, hz, hy, hcross, hyy] at hp
  change 0 ≤ RCLike.re ⟪(selectedCost A N - selectedCost A₀ n) a, a⟫_ℂ
  simp only [sub_apply, inner_sub_left, map_sub]
  linarith

theorem marker_compression_ge (U : H →L[ℂ] K)
    (A : K →L[ℂ] K) (A₀ : H →L[ℂ] H)
    (hA : IsStrictlyPositive A) (hA₀ : IsStrictlyPositive A₀)
    (hcomp : U.adjoint ∘L A ∘L U = A₀) (N : J →L[ℂ] K) :
    marker A N ≤ marker A₀ (U.adjoint ∘L N) := by
  exact CStarAlgebra.ringInverse_le_ringInverse
    (add_le_add_right (selectedCost_compression_le U A A₀ hA hA₀ hcomp N) 1)
    (isStrictlyPositive_one.add_nonneg (cost_nonnegative A₀ hA₀ (U.adjoint ∘L N)))

/-- Regularization commutes with an original isometric compression, so the
marker on the larger physical carrier is no larger than the compressed marker. -/
theorem regularized_marker_isometric_compression_aux
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (U : H →ₗᵢ[ℂ] K) (P : Q →L[ℂ] K) (N : J →L[ℂ] K)
    (ε : ℝ) (hε : 0 < ε) :
    marker (P ∘L P.adjoint + ε • 1) N ≤
      marker ((U.toContinuousLinearMap.adjoint ∘L P) ∘L
        (U.toContinuousLinearMap.adjoint ∘L P).adjoint + ε • 1)
        (U.toContinuousLinearMap.adjoint ∘L N) := by
  let V := U.toContinuousLinearMap
  let p := V.adjoint ∘L P
  have hu : V.adjoint ∘L V = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [comp_apply, V.adjoint_inner_left]
    change ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ
    exact U.inner_map_map x y
  have hc : V.adjoint ∘L (P ∘L P.adjoint + ε • 1) ∘L V =
      p ∘L p.adjoint + ε • 1 := by
    ext x
    simp only [p, adjoint_comp, adjoint_adjoint, comp_apply, add_apply,
      smul_apply, one_apply_eq_self, map_add, map_smul_of_tower]
    rw [show V.adjoint (V x) = x from congrArg (fun R : H →L[ℂ] H => R x) hu]
  have hp : 0 ≤ P ∘L P.adjoint :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (isPositive_self_comp_adjoint P)
  have hp₀ : 0 ≤ p ∘L p.adjoint :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (isPositive_self_comp_adjoint p)
  exact marker_compression_ge V _ _
    (IsStrictlyPositive.nonneg_add hp (isStrictlyPositive_one.smul hε))
    (IsStrictlyPositive.nonneg_add hp₀ (isStrictlyPositive_one.smul hε)) hc N

/-- Compact antitone families have right limits at an arbitrary endpoint in
an arbitrary closed partial order. No operator or support-order premise is hidden. -/
theorem exists_compact_antitone_right_limit {E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (c : ℝ) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ t : ℝ, c < t → f t ∈ C)
    (hanti : AntitoneOn f (Set.Ioi c)) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsLUB (f '' Set.Ioi c) G₀ ∧
      Filter.Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds G₀) := by
  have hev : ∀ᶠ t in nhdsWithin c (Set.Ioi c), f t ∈ C := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmem t ht
  obtain ⟨G₀, hG₀, hc⟩ := hC.exists_mapClusterPt (Filter.tendsto_principal.mpr hev)
  have hlub : ∀ y : E, MapClusterPt y (nhdsWithin c (Set.Ioi c)) f →
      IsLUB (f '' Set.Ioi c) y := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      apply isClosed_Ici.mem_of_mapClusterPt hy
      filter_upwards [Ioo_mem_nhdsGT ht] with u hu
      exact hanti hu.1 ht hu.2.le
    · intro z hz
      apply isClosed_Iic.mem_of_mapClusterPt hy
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hz (Set.mem_image_of_mem f ht)
  refine ⟨G₀, hG₀, hlub G₀ hc, ?_⟩
  apply hC.tendsto_nhds_of_unique_mapClusterPt hev
  intro y _ hy
  exact (hlub y hy).unique (hlub G₀ hc)

end WeilDefect.MarkerStability

open WeilDefect.MarkerStability
theorem solution {H K J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (U : H →ₗᵢ[ℂ] K) (P : Q →L[ℂ] K) (N : J →L[ℂ] K)
    (ε : ℝ) (hε : 0 < ε) :
    marker (P ∘L P.adjoint + ε • 1) N ≤
      marker ((U.toContinuousLinearMap.adjoint ∘L P) ∘L
        (U.toContinuousLinearMap.adjoint ∘L P).adjoint + ε • 1)
        (U.toContinuousLinearMap.adjoint ∘L N) := regularized_marker_isometric_compression_aux U P N ε hε
