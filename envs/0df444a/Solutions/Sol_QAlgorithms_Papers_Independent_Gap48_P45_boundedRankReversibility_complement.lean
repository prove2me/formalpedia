-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.boundedRankReversibility_complement
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:52:53.530268+00:00
-- url     : https://prove2.me/submissions/f40367d7-5354-4c36-9f55-9070b490efaa

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_threeConditions
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_barycenter_dominates_and_inherits_reversibility
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_barycenter_douglas_resolution
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complete_barycenter_faithful_output
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_identity_dual_sandwich
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pure_family_whitened_sandwich
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_dual_rank_rankOne_resolution
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complement_kraus_of_output_frame
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_boundedRankKraus_schmidt_outputs_and_peb
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complement_kraus_rankOne_of_output_resolution
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_rankOne_kraus_orthogonal_rows_series

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45R

open QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (boundedOperator ReversibleOn IsKrausRepresentation IsParsevalFrame)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

/-- A countable nonempty index type carries a strictly positive probability law. -/
theorem exists_positiveLaw (L : Type) [Countable L] [Nonempty L] :
    ∃ pi : L → ℝ, PositiveLaw pi := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat L
  let w : L → ℝ := fun i => (1 / 2 : ℝ) ^ (e i + 1)
  have hw0 : ∀ i, 0 < w i := fun i => by positivity
  have hws : Summable w := by
    have h2 : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) :=
      (summable_geometric_two).comp_injective (add_left_injective 1)
    exact h2.comp_injective he
  have hs : 0 < ∑' i, w i := by
    obtain ⟨i0⟩ := ‹Nonempty L›
    exact hws.tsum_pos (fun i => (hw0 i).le) i0 (hw0 i0)
  refine ⟨fun i => w i / ∑' j, w j, fun i => div_pos (hw0 i) hs, ?_⟩
  have := hws.hasSum.div_const (∑' j, w j)
  rwa [div_self hs.ne'] at this

/-- A complete family over a nonempty space is indexed by a nonempty type. -/
theorem nonempty_of_complete {I L : Type} [Countable I] [Nonempty I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) : Nonempty L := by
  by_contra hL
  rw [not_nonempty_iff] at hL
  have hS : {v : Hilbert I | ∃ x ∈ Set.range rho, ∃ w,
      boundedOperator x.coefficients w = v} = ∅ := by
    ext v
    simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, ⟨i, _⟩, _⟩
    exact hL.elim i
  obtain ⟨i0⟩ := ‹Nonempty I›
  have hx : (lp.single 2 i0 (1 : ℂ) : Hilbert I) ∈ generatedSpace (Set.range rho) :=
    hC ▸ Submodule.mem_top
  unfold generatedSpace at hx
  rw [hS, Submodule.span_empty] at hx
  have hcl : (⊥ : Submodule ℂ (Hilbert I)).topologicalClosure = ⊥ :=
    IsClosed.submodule_topologicalClosure_eq (by simp [isClosed_singleton])
  rw [hcl, Submodule.mem_bot] at hx
  have h1 := congrArg (fun f : Hilbert I => f i0) hx
  simp at h1

/-- Rank through an injective, dense-range sandwich. -/
theorem rank_le_of_sandwich {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T s : E →L[ℂ] E) (hinj : Function.Injective s)
    (hdense : DenseRange s) (r : ℕ)
    (h : Module.rank ℂ (LinearMap.range (s.comp (T.comp s)).toLinearMap) ≤ r) :
    Module.rank ℂ (LinearMap.range T.toLinearMap) ≤ r := by
  set V := LinearMap.range (s.comp (T.comp s)).toLinearMap with hV
  set W := LinearMap.range (T.comp s).toLinearMap with hW
  have hmaps : ∀ w ∈ W, s.toLinearMap w ∈ V := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  let f : W →ₗ[ℂ] V := s.toLinearMap.restrict hmaps
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact hinj this
  have hWV : Module.rank ℂ W ≤ Module.rank ℂ V := LinearMap.rank_le_of_injective f hf
  have hVfin : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt h (Cardinal.nat_lt_aleph0 r))
  have hWfin : FiniteDimensional ℂ W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (hWV.trans h) (Cardinal.nat_lt_aleph0 r))
  have hWcl : IsClosed (W : Set E) := Submodule.closed_of_finiteDimensional W
  have hsub : LinearMap.range T.toLinearMap ≤ W := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ closure (Set.range s) := by rw [hdense.closure_range]; trivial
    have h1 : T x ∈ closure (T '' Set.range s) :=
      image_closure_subset_closure_image T.continuous ⟨x, hx, rfl⟩
    have h2 : T '' Set.range s ⊆ (W : Set E) := by
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    exact hWcl.closure_subset_iff.mpr h2 h1
  exact (Submodule.rank_mono hsub).trans (hWV.trans h)

/-- A rank-one operator has rank at most one. -/
theorem opRank_rk_le {I : Type} (w : Hilbert I) :
    operatorRank ((innerSL ℂ w).smulRight w : Hilbert I →L[ℂ] Hilbert I) ≤ 1 := by
  unfold operatorRank
  have h1 : LinearMap.range ((innerSL ℂ w).smulRight w : Hilbert I →L[ℂ] Hilbert I).toLinearMap ≤
      Submodule.span ℂ {w} := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨inner ℂ w x, rfl⟩
  have h2 : Module.rank ℂ (LinearMap.range
      ((innerSL ℂ w).smulRight w : Hilbert I →L[ℂ] Hilbert I).toLinearMap) ≤ 1 := by
    refine (Submodule.rank_mono h1).trans ?_
    simpa using rank_span_le (R := ℂ) ({w} : Set (Hilbert I))
  have h3 := Cardinal.toENat.monotone' h2
  simpa using h3

/-- `BoundIndex m` has at most `m` elements. -/
theorem dimensionCount_boundIndex_le (m : ℕ∞) : dimensionCount (BoundIndex m) ≤ m := by
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have e : BoundIndex (n : ℕ∞) ≃ Fin n :=
      { toFun := fun k => ⟨k.1, by exact_mod_cast k.2⟩
        invFun := fun k => ⟨k.1, by exact_mod_cast k.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold dimensionCount
    rw [Cardinal.mk_congr e, Cardinal.mk_fin, Cardinal.toENat_nat]

/-- Counting for the sigma-indexed Kraus family. -/
theorem dimensionCount_sigma_le (L : Type) (m : ℕ∞) :
    dimensionCount (Σ _ : L, BoundIndex m) ≤ dimensionCount L * m := by
  unfold dimensionCount
  rw [Cardinal.mk_congr (Equiv.sigmaEquivProd L (BoundIndex m)), Cardinal.mk_prod,
    Cardinal.lift_id, Cardinal.lift_id, map_mul]
  gcongr
  exact dimensionCount_boundIndex_le m

/-- Iterated nonnegative real sums combine to a sum over the sigma type. -/
theorem hasSum_sigma_nonneg {L M : Type} (f : L → M → ℝ) (g : L → ℝ) (a : ℝ)
    (hf : ∀ i j, 0 ≤ f i j) (hi : ∀ i, HasSum (f i) (g i)) (hg : HasSum g a) :
    HasSum (fun p : Σ _ : L, M => f p.1 p.2) a := by
  have hs : Summable (fun p : Σ _ : L, M => f p.1 p.2) := by
    refine (summable_sigma_of_nonneg (f := fun p : (Σ _ : L, M) => f p.1 p.2)
      (fun p => hf p.1 p.2)).2 ⟨fun i => (hi i).summable, ?_⟩
    simpa [(hi _).tsum_eq] using hg.summable
  convert hs.hasSum using 1
  rw [hs.tsum_sigma']
  · simp_rw [(hi _).tsum_eq]; exact hg.tsum_eq.symm
  · exact fun i => (hi i).summable

/-- Petz identities for the barycenter (petz_threeConditions + barycenter child). -/
theorem petz_identities {I J L : Type} [Countable I] [Countable J] [Countable L]
    [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (rho : L → State I) (pi : L → ℝ) (hpi : PositiveLaw pi)
    (hRev : ReversibleOn Phi.val (Set.range rho)) :
    ∃ sigma : State I,
      (sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) ∧
      ∀ i, (rho i).coefficients =
        petzRecovery Phi.val sigma.coefficients (Phi.val (rho i).coefficients) := by
  obtain ⟨sigma, hbar, hD, hR⟩ := barycenter_dominates_and_inherits_reversibility Phi rho pi hpi
  exact ⟨sigma, hbar, fun i => ((petz_threeConditions Phi (rho i) sigma (hD i)).2.2).mp (hR hRev i)⟩

/-- The output resolution with rank-r dual images (Shirokov, proof of Thm 3). -/
theorem ares {I J L : Type} [Countable I] [Countable J] [Countable L]
    [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (rho : L → State I) (r : ℕ)
    (hC : CompleteFamily (Set.range rho))
    (hRk : ∀ i, operatorRank (boundedOperator (rho i).coefficients) ≤ r)
    (hRev : ReversibleOn Phi.val (Set.range rho)) :
    ∃ B : L → (Hilbert J →L[ℂ] Hilbert J),
      (∀ i, (B i).adjoint = B i ∧ ∀ x, 0 ≤ (inner ℂ x (B i x)).re) ∧
      (∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
        (inner ℂ x (outputProjection Phi.val x)).re) ∧
      (∀ i, (outputProjection Phi.val).comp ((B i).comp (outputProjection Phi.val)) = B i) ∧
      ∀ i, operatorRank (channelDual Phi.val (B i)) ≤ r := by
  have : Nonempty L := nonempty_of_complete rho hC
  obtain ⟨pi, hpi⟩ := exists_positiveLaw L
  obtain ⟨sigma, hbar, hP⟩ := petz_identities Phi rho pi hpi hRev
  obtain ⟨B, hBS, hBt, hBa, hBsum⟩ := barycenter_douglas_resolution Phi rho pi sigma hpi hbar
  obtain ⟨hout, hinj, hdense⟩ := complete_barycenter_faithful_output Phi rho hC pi hpi sigma hbar
  have hsum : ∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (outputProjection Phi.val x)).re := by
    rw [hout]; exact hBsum
  have hsupp : ∀ i, (outputProjection Phi.val).comp ((B i).comp (outputProjection Phi.val)) = B i := by
    rw [hout]; exact hBS
  refine ⟨B, hBa, hsum, hsupp, fun i => ?_⟩
  have h := petz_identity_dual_sandwich Phi (rho i) sigma (hP i) (B i) (pi i) (hpi.1 i) (hBt i)
  have hrk : Module.rank ℂ (LinearMap.range
      ((positiveSquareRoot (boundedOperator sigma.coefficients)).comp
        ((channelDual Phi.val (B i)).comp
          (positiveSquareRoot (boundedOperator sigma.coefficients)))).toLinearMap) ≤ r := by
    rw [h, ContinuousLinearMap.coe_smul,
      LinearMap.range_smul _ _ (by exact_mod_cast (hpi.1 i).ne')]
    have := hRk i
    unfold operatorRank at this
    exact Cardinal.toENat_le_natCast.mp this
  unfold operatorRank
  exact Cardinal.toENat_le_natCast.mpr (rank_le_of_sandwich _ _ hinj hdense r hrk)

/-- The Kraus clause (Theorem 3): count |L| m_r, ranks <= r. -/
theorem kraus_clause {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (rho : L → State I) (r : ℕ)
    (hComplete : CompleteFamily (Set.range rho))
    (hRank : ∀ i, operatorRank (boundedOperator (rho i).coefficients) ≤ r)
    (hRev : ReversibleOn Phi.val (Set.range rho)) :
    HasBoundedRankKraus Psi.val r (dimensionCount L * rankMultiplicity Phi.val r) := by
  obtain ⟨B, hBpos, hBsum, hBsupp, hBrank⟩ := ares Phi rho r hComplete hRank hRev
  have hpsi := fun i =>
    dual_rank_rankOne_resolution Phi Psi hComp (B i) (hBpos i) (hBsupp i) r (hBrank i)
  choose psi hpsiSum hpsiRank using hpsi
  let K := Σ _ : L, BoundIndex (rankMultiplicity Phi.val r)
  let q : K → Hilbert J := fun p => psi p.1 p.2
  have hq : ∀ x, HasSum (fun k => ‖inner ℂ (q k) x‖ ^ 2)
      (inner ℂ x (outputProjection Phi.val x)).re := fun x =>
    hasSum_sigma_nonneg (fun i j => ‖inner ℂ (psi i j) x‖ ^ 2) _ _
      (fun _ _ => by positivity) (fun i => hpsiSum i x) (hBsum x)
  obtain ⟨V, hVK, hVrank⟩ := complement_kraus_of_output_frame Phi Psi hComp K q hq
  exact ⟨K, inferInstance, V, dimensionCount_sigma_le L _, hVK,
    fun k => (hVrank k).trans (hpsiRank k.1 k.2)⟩

/-- The pure-state clause (Theorem 3, r = 1). -/
theorem pure_clause {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (rho : L → State I) (hC : CompleteFamily (Set.range rho))
    (hRev : ReversibleOn Phi.val (Set.range rho))
    (v : L → Hilbert I) (hv : ∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i))
    (pi : L → ℝ) (hpi : PositiveLaw pi) :
    HasWhitenedForm Psi.val pi v (rankMultiplicity Phi.val 1) := by
  obtain ⟨sigma, hbar, hP⟩ := petz_identities Phi rho pi hpi hRev
  obtain ⟨B, hBS, hBt, hBa, hBsum⟩ := barycenter_douglas_resolution Phi rho pi sigma hpi hbar
  obtain ⟨hout, hinj, hdense⟩ := complete_barycenter_faithful_output Phi rho hC pi hpi sigma hbar
  have hsum : ∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (outputProjection Phi.val x)).re := by
    rw [hout]; exact hBsum
  have hsupp : ∀ i, (outputProjection Phi.val).comp ((B i).comp (outputProjection Phi.val)) = B i := by
    rw [hout]; exact hBS
  obtain ⟨h1, h2, hX⟩ := pure_family_whitened_sandwich rho hC v hv pi sigma hpi hbar
  have hdual : ∀ i, channelDual Phi.val (B i) =
      (innerSL ℂ (whitenedVector pi v i)).smulRight (whitenedVector pi v i) := fun i =>
    hX i _ (petz_identity_dual_sandwich Phi (rho i) sigma (hP i) (B i) (pi i) (hpi.1 i) (hBt i))
  have hw0 : ∀ i, whitenedVector pi v i ≠ 0 := by
    intro i h0
    have := h1 i
    rw [h0, map_zero] at this
    have hn := congrArg norm this
    rw [norm_zero, norm_smul, (hv i).1, mul_one] at hn
    have : (0 : ℝ) < ‖(Real.sqrt (pi i) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_pos]
      exact (Real.sqrt_pos.mpr (hpi.1 i)).ne'
    linarith
  have hpsi0 : ∀ i, ∃ psi : BoundIndex (rankMultiplicity Phi.val 1) → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B i x)).re := by
    intro i
    have hr1 : operatorRank (channelDual Phi.val (B i)) ≤ (1 : ℕ) := by
      rw [hdual i]; exact_mod_cast opRank_rk_le (whitenedVector pi v i)
    obtain ⟨psi, hps, _⟩ :=
      dual_rank_rankOne_resolution Phi Psi hComp (B i) (hBa i) (hsupp i) 1 hr1
    exact ⟨psi, hps⟩
  obtain ⟨phi, hphi, hKr⟩ := complement_kraus_rankOne_of_output_resolution Phi Psi hComp B hsum
    hpsi0 (whitenedVector pi v) hw0 hdual
  obtain ⟨psi, hrows, sig, h3, h4⟩ :=
    rankOne_kraus_orthogonal_rows_series (rankMultiplicity Phi.val 1) Psi (whitenedVector pi v)
      phi hphi hKr
  exact ⟨h1, h2, psi, hrows, sig, h3, h4⟩

end P45R

open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution
    {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (rho : L → State I) (r : ℕ) (hr : 0 < r)
    (hComplete : CompleteFamily (Set.range rho))
    (hRank : ∀ i, operatorRank (boundedOperator (rho i).coefficients) ≤ r)
    (hRev : ReversibleOn Phi.val (Set.range rho)) :
    HasBoundedRankKraus Psi.val r (dimensionCount L * rankMultiplicity Phi.val r) ∧
    PartiallyEntanglementBreaking Psi.val r ∧ CountableSchmidtOutputs Psi.val r ∧
    (r = 1 → ∀ (v : L → QAlgorithms.RealRegisters.Hilbert I), (∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i)) →
      ∀ pi : L → ℝ, PositiveLaw pi → HasWhitenedForm Psi.val pi v (rankMultiplicity Phi.val 1)) := by
  have hK := P45R.kraus_clause Phi Psi hComp rho r hComplete hRank hRev
  obtain ⟨hS, hPEB⟩ := boundedRankKraus_schmidt_outputs_and_peb Psi r _ hr hK
  refine ⟨hK, hPEB, hS, ?_⟩
  rintro - v hv pi hpi
  exact P45R.pure_clause Phi Psi hComp rho hComplete hRev v hv pi hpi

end
