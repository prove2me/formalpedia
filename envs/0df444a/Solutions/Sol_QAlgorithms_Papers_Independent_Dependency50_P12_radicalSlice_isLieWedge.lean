-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.radicalSlice_isLieWedge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:12:25.117089+00:00
-- url     : https://prove2.me/submissions/80741872-f421-4078-bd5c-7322d4e45f4f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

set_option linter.unusedSectionVars false
section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

theorem g55a_decomp (D : LeviSplitting A) (x : A) :
    ((piS D x : D.s) : A) + ((piR D x : D.r) : A) = x := by
  have := (coords D).apply_symm_apply x
  exact this

theorem g55a_piS (D : LeviSplitting A) (S : D.s) (R : D.r) :
    piS D ((S : A) + (R : A)) = S := by
  have : (coords D).symm (coords D (S, R)) = (S, R) := (coords D).symm_apply_apply _
  exact congrArg Prod.fst this

theorem g55a_piR (D : LeviSplitting A) (S : D.s) (R : D.r) :
    piR D ((S : A) + (R : A)) = R := by
  have : (coords D).symm (coords D (S, R)) = (S, R) := (coords D).symm_apply_apply _
  exact congrArg Prod.snd this

theorem g55a_add {W : Set A} (hW : IsCone W) {x y : A} (hx : x ∈ W) (hy : y ∈ W) :
    x + y ∈ W := by
  have h := hW.2.1 hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have h2 := hW.2.2 2 (by norm_num) _ h
  convert h2 using 1
  rw [smul_add, smul_smul, smul_smul]; norm_num

theorem g55a_edge_iff (D : LeviSplitting A) (W : Set A) (S : D.s) (R : D.r) :
    (S : A) + (R : A) ∈ edge W ↔
      S ∈ edge (quotientCone D W) ∧ R ∈ fiber D W S ∧ -R ∈ fiber D W (-S) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : ((-S : D.s) : A) + ((-R : D.r) : A) ∈ W := by
      simpa [neg_add, add_comm] using h2
    refine ⟨⟨⟨_, h1, g55a_piS D S R⟩, ⟨_, h2', ?_⟩⟩, h1, h2'⟩
    rw [g55a_piS]
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, ?_⟩
    have : ((-S : D.s) : A) + ((-R : D.r) : A) ∈ W := h2
    simpa [neg_add, add_comm] using this

theorem g55a_edge_eq (D : LeviSplitting A) (W : Set A) :
    edge W = candidateEdge D (quotientCone D W) (fiber D W) := by
  ext x
  constructor
  · intro hx
    rw [← g55a_decomp D x] at hx
    obtain ⟨h1, h2, h3⟩ := (g55a_edge_iff D W _ _).1 hx
    exact ⟨_, h1, _, h2, h3, (g55a_decomp D x).symm⟩
  · rintro ⟨S, hS, R, h1, h2, rfl⟩
    exact (g55a_edge_iff D W S R).2 ⟨hS, h1, h2⟩


theorem g55a_cs_add (D : LeviSplitting A) (S T : D.s) : ((S + T : D.s) : A) = (S : A) + (T : A) := rfl
theorem g55a_cs_smul (D : LeviSplitting A) (a : ℝ) (S : D.s) : ((a • S : D.s) : A) = a • (S : A) := rfl

theorem g55a_smul_mem {W : Set A} (hW : IsCone W) {a : ℝ} (ha : 0 ≤ a) {x : A} (hx : x ∈ W) :
    a • x ∈ W := hW.2.2 a ha x hx

theorem g55a_fiberProps (D : LeviSplitting A) (W : Set A) (hW : IsLieWedge W) :
    FiberProperties D W := by
  obtain ⟨hcl, hcone⟩ := hW.1, hW.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S ⟨x, hx, rfl⟩
    refine ⟨⟨piR D x, ?_⟩, ?_, ?_⟩
    · show ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ W
      rw [g55a_decomp]; exact hx
    · exact hcl.preimage (continuous_const.add continuous_subtype_val)
    · intro R1 h1 R2 h2 a b ha hb hab
      show ((piS D x : D.s) : A) + ((a • R1 + b • R2 : D.r) : A) ∈ W
      have := hcone.2.1 h1 h2 ha hb hab
      convert this using 1
      simp only [LieSubmodule.coe_add, LieSubmodule.coe_smul]
      obtain rfl : b = 1 - a := by linarith
      module
  · ext R; simp [fiber, radicalSlice]
  · intro S _ T _ R hR Q hQ
    show ((S + T : D.s) : A) + ((R + Q : D.r) : A) ∈ W
    have := g55a_add hcone hR hQ
    convert this using 1
    simp only [g55a_cs_add, LieSubmodule.coe_add]; abel
  · rintro a ha S _ _ ⟨R, hR, rfl⟩
    show ((a • S : D.s) : A) + ((a • R : D.r) : A) ∈ W
    have := g55a_smul_mem hcone ha hR
    convert this using 1
    simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add]
  · intro a ha S _
    apply Set.Subset.antisymm
    · rintro _ ⟨R, hR, rfl⟩
      show ((a • S : D.s) : A) + ((a • R : D.r) : A) ∈ W
      have := g55a_smul_mem hcone ha.le hR
      convert this using 1
      simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add]
    · intro R hR
      refine ⟨a⁻¹ • R, ?_, ?_⟩
      · show ((S : D.s) : A) + ((a⁻¹ • R : D.r) : A) ∈ W
        have := g55a_smul_mem hcone (inv_nonneg.2 ha.le) hR
        convert this using 1
        simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add, smul_smul,
          inv_mul_cancel₀ ha.ne', one_smul]
      · simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · have : fiberGraph D (quotientCone D W) (fiber D W) =
        (fun p : D.s × D.r => ((p.1 : D.s) : A) + ((p.2 : D.r) : A)) ⁻¹' W := by
      ext p
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        exact ⟨⟨_, h, g55a_piS D p.1 p.2⟩, h⟩
    rw [this]
    exact hcl.preimage ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd))

theorem g55a_collapse (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W)
    (hC : ∀ S ∈ quotientCone D W, (S : A) ∈ edge W) :
    (∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) ∧
    W = {x | ∃ S ∈ quotientCone D W, ∃ R ∈ radicalSlice D W,
      x = (S : A) + (R : A)} ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ →
      Module.finrank ℝ D.s < Module.finrank ℝ A ∧
      Module.finrank ℝ D.r < Module.finrank ℝ A) := by
  have hcone := hW.2.1
  have hfib : ∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W := by
    intro S hS
    obtain ⟨h1, h2⟩ := hC S hS
    ext R
    constructor
    · intro hR
      show (R : A) ∈ W
      have := g55a_add hcone h2 hR
      simpa using this
    · intro hR
      exact g55a_add hcone h1 hR
  refine ⟨hfib, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hS : piS D x ∈ quotientCone D W := ⟨x, hx, rfl⟩
      refine ⟨_, hS, piR D x, ?_, (g55a_decomp D x).symm⟩
      rw [← hfib _ hS]
      show ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ W
      rw [g55a_decomp]; exact hx
    · rintro ⟨S, hS, R, hR, rfl⟩
      exact g55a_add hcone (hC S hS).1 hR
  · intro hs hr
    have hsum := Submodule.finrank_add_eq_of_isCompl D.complementary
    have h1 : 0 < Module.finrank ℝ D.s.toSubmodule := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      by_contra hc
      push Not at hc
      apply hs
      ext x
      constructor
      · intro hx
        have := hc ⟨x, hx⟩
        simpa using congrArg Subtype.val this
      · intro hx
        rw [LieSubalgebra.mem_bot] at hx
        rw [hx]; exact D.s.zero_mem
    have h2 : 0 < Module.finrank ℝ D.r.toSubmodule := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      by_contra hc
      push Not at hc
      apply hr
      ext x
      constructor
      · intro hx
        have := hc ⟨x, hx⟩
        simpa using congrArg Subtype.val this
      · intro hx
        rw [LieSubmodule.mem_bot] at hx
        rw [hx]; exact D.r.zero_mem
    exact ⟨by change Module.finrank ℝ D.s.toSubmodule < _; omega,
      by change Module.finrank ℝ D.r.toSubmodule < _; omega⟩


theorem g55a_mem_sr (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) (S : D.s) (R : D.r) :
    (S : A) + (R : A) ∈ reconstructLeviFibers D C F ↔ S ∈ C ∧ R ∈ F S := by
  constructor
  · rintro ⟨S', hS', R', hR', heq⟩
    have h1 := congrArg (piS D) heq
    have h2 := congrArg (piR D) heq
    rw [g55a_piS, g55a_piS] at h1
    rw [g55a_piR, g55a_piR] at h2
    subst h1; subst h2; exact ⟨hS', hR'⟩
  · rintro ⟨hS, hR⟩; exact ⟨S, hS, R, hR, rfl⟩

theorem g55a_mem_recon (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) (x : A) :
    x ∈ reconstructLeviFibers D C F ↔ piS D x ∈ C ∧ piR D x ∈ F (piS D x) := by
  conv_lhs => rw [← g55a_decomp D x]
  exact g55a_mem_sr D C F _ _

theorem g55a_cont_split (D : LeviSplitting A) :
    Continuous (fun x : A => (piS D x, piR D x)) := by
  have h1 : Continuous (fun x : A => ((piS D x : D.s) : A)) := by
    let f : A →ₗ[ℝ] A := D.s.toSubmodule.subtype ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ (coords D).symm.toLinearMap
    exact f.continuous_of_finiteDimensional
  have h2 : Continuous (fun x : A => ((piR D x : D.r) : A)) := by
    let f : A →ₗ[ℝ] A := D.r.toSubmodule.subtype ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ (coords D).symm.toLinearMap
    exact f.continuous_of_finiteDimensional
  exact (continuous_induced_rng.2 h1).prodMk (continuous_induced_rng.2 h2)

theorem g55a_neg_sr (D : LeviSplitting A) (S : D.s) (R : D.r) :
    -((S : A) + (R : A)) = ((-S : D.s) : A) + ((-R : D.r) : A) := by
  simp [neg_add, add_comm]

theorem g55a_recon (D : LeviSplitting A) (C : Set D.s)
    (F : D.s → Set D.r) (h : AdmissibleLeviFibers D C F) :
    ReconstructionResult D C F := by
  obtain ⟨hC, hF, hadd, hsmul, hgraph, hD5, hD6⟩ := h
  have hmem := g55a_mem_sr D C F
  have hF0 : (0 : D.r) ∈ F 0 := by
    obtain ⟨R, hR⟩ := (hF 0 hC.1).1
    have := hsmul 0 le_rfl 0 hC.1 R hR
    simpa using this
  have hedge : edge (reconstructLeviFibers D C F) = candidateEdge D C F := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      rw [← g55a_decomp D x] at h1 h2
      rw [g55a_neg_sr, hmem] at h2
      rw [hmem] at h1
      exact ⟨_, ⟨h1.1, h2.1⟩, _, h1.2, h2.2, (g55a_decomp D x).symm⟩
    · rintro ⟨S, ⟨hS1, hS2⟩, R, hR1, hR2, rfl⟩
      refine ⟨(hmem S R).2 ⟨hS1, hR1⟩, ?_⟩
      rw [g55a_neg_sr, hmem]; exact ⟨hS2, hR2⟩
  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, hedge, ?_, ?_⟩
  · have : reconstructLeviFibers D C F =
        (fun x : A => (piS D x, piR D x)) ⁻¹' fiberGraph D C F := by
      ext x; exact g55a_mem_recon D C F x
    rw [this]; exact hgraph.preimage (g55a_cont_split D)
  · have := (hmem 0 0).2 ⟨hC.1, hF0⟩
    simpa using this
  · rintro _ ⟨S, hS, R, hR, rfl⟩ _ ⟨T, hT, Q, hQ, rfl⟩ a b ha hb hab
    have e : a • ((S : A) + (R : A)) + b • ((T : A) + (Q : A)) =
        ((a • S + b • T : D.s) : A) + ((a • R + b • Q : D.r) : A) := by
      simp only [g55a_cs_add, g55a_cs_smul, LieSubmodule.coe_add, LieSubmodule.coe_smul]
      module
    rw [e, hmem]
    refine ⟨hC.2.1 hS hT ha hb hab, ?_⟩
    exact hadd _ (hC.2.2 a ha S hS) _ (hC.2.2 b hb T hT) _ (hsmul a ha S hS R hR) _
      (hsmul b hb T hT Q hQ)
  · rintro a ha _ ⟨S, hS, R, hR, rfl⟩
    have e : a • ((S : A) + (R : A)) = ((a • S : D.s) : A) + ((a • R : D.r) : A) := by
      simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add]
    rw [e, hmem]
    exact ⟨hC.2.2 a ha S hS, hsmul a ha S hS R hR⟩
  · intro x hx
    rw [hedge] at hx
    rintro _ ⟨y, ⟨S, hS, R, hR, rfl⟩, rfl⟩
    have h6 := hD6 x hx S hS (Set.mem_image_of_mem (expAd x) (⟨R, hR, rfl⟩ : ((S : A) + (R : A)) ∈ slice D F S))
    obtain ⟨R', hR', he⟩ := h6
    rw [← he, hmem]
    exact ⟨hD5 x hx ⟨S, hS, rfl⟩, hR'⟩
  · ext R
    show ((R : D.r) : A) ∈ reconstructLeviFibers D C F ↔ R ∈ F 0
    have : ((R : D.r) : A) = ((0 : D.s) : A) + (R : A) := by simp
    rw [this, hmem]
    exact ⟨fun h => h.2, fun h => ⟨hC.1, h⟩⟩
  · ext S
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((g55a_mem_recon D C F x).1 hx).1
    · intro hS
      obtain ⟨R, hR⟩ := (hF S hS).1
      exact ⟨_, (hmem S R).2 ⟨hS, hR⟩, g55a_piS D S R⟩
  · intro S hS
    ext R
    show (S : A) + (R : A) ∈ reconstructLeviFibers D C F ↔ R ∈ F S
    rw [hmem]
    exact ⟨fun h => h.2, fun h => ⟨hS, h⟩⟩
  · intro V hV hfib
    ext x
    rw [g55a_mem_recon]
    constructor
    · intro hx
      have hS : piS D x ∈ C := hV ▸ ⟨x, hx, rfl⟩
      refine ⟨hS, ?_⟩
      rw [← hfib _ hS]
      show ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ V
      rw [g55a_decomp]; exact hx
    · rintro ⟨hS, hR⟩
      rw [← hfib _ hS] at hR
      have : ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ V := hR
      rwa [g55a_decomp] at this


end AbstractResults

section G55AExp

open scoped Nat

theorem g55a_exp_summable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (y : E) :
    Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (T ^ n) y) := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  let T' : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    LinearMap.toContinuousLinearMap
      (e.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearEquiv.toLinearMap)
  have hs : Summable (fun n : ℕ => ((n ! : ℝ)⁻¹) • T' ^ n) :=
    NormedSpace.expSeries_summable' T'
  have hpow : ∀ n : ℕ, (T' ^ n) (e y) = e ((T ^ n) y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [T']
  have h2 := (hs.mapL (ContinuousLinearMap.apply ℝ _ (e y))).mapL
    (e.symm : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E)
  convert h2 using 1
  ext n
  simp [hpow]

theorem g55a_map_expAd {A B : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]
    [LieRing B] [LieAlgebra ℝ B] [TopologicalSpace B] [T2Space B]
    (f : A →ₗ[ℝ] B) (hf : ∀ a b, f ⁅a, b⁆ = ⁅f a, f b⁆) (hc : Continuous f) (x y : A) :
    f (expAd x y) = expAd (f x) (f y) := by
  have hpow : ∀ n : ℕ, f ((adMap x ^ n) y) = (adMap (f x) ^ n) (f y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      simp [adMap, hf]
  have h := (g55a_exp_summable (adMap x) y).hasSum.map f hc
  unfold expAd
  rw [← h.tsum_eq]
  congr 1
  ext n
  simp [hpow]

end G55AExp

section G55ASlice

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

theorem g55a_radslice (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    IsLieWedge (radicalSlice D W) ∧
    edge (radicalSlice D W) = {R : D.r | (R : A) ∈ edge W} := by
  have : IsTopologicalAddGroup D.r := inferInstanceAs (IsTopologicalAddGroup D.r.toSubmodule)
  have : ContinuousSMul ℝ D.r := inferInstanceAs (ContinuousSMul ℝ D.r.toSubmodule)
  have : FiniteDimensional ℝ D.r := inferInstanceAs (FiniteDimensional ℝ D.r.toSubmodule)
  obtain ⟨hcl, hcone, hinv⟩ := hW
  have hedge : edge (radicalSlice D W) = {R : D.r | (R : A) ∈ edge W} := by
    ext R; simp [edge, radicalSlice]
  refine ⟨⟨hcl.preimage continuous_subtype_val, ⟨?_, ?_, ?_⟩, ?_⟩, hedge⟩
  · show ((0 : D.r) : A) ∈ W
    simpa using hcone.1
  · intro R hR Q hQ a b ha hb hab
    show ((a • R + b • Q : D.r) : A) ∈ W
    simpa using hcone.2.1 hR hQ ha hb hab
  · intro a ha R hR
    show ((a • R : D.r) : A) ∈ W
    simpa using hcone.2.2 a ha _ hR
  · intro x hx
    rw [hedge] at hx
    rintro _ ⟨R, hR, rfl⟩
    show ((expAd x R : D.r) : A) ∈ W
    have := g55a_map_expAd (LieIdeal.incl D.r : D.r →ₗ⁅ℝ⁆ A).toLinearMap
      (fun a b => (LieIdeal.incl D.r).map_lie a b) continuous_subtype_val x R
    simp only [LieHom.coe_toLinearMap, LieIdeal.incl_apply] at this
    rw [this]
    exact hinv _ hx ⟨_, hR, rfl⟩

theorem g55a_piS_lie (D : LeviSplitting A) (x y : A) :
    piS D ⁅x, y⁆ = ⁅piS D x, piS D y⁆ := by
  have hx := g55a_decomp D x
  have hy := g55a_decomp D y
  set S1 := piS D x; set R1 := piR D x; set S2 := piS D y; set R2 := piR D y
  have hr : (⁅(S1 : A), (R2 : A)⁆ + ⁅(R1 : A), (S2 : A)⁆ + ⁅(R1 : A), (R2 : A)⁆) ∈ D.r := by
    refine add_mem (add_mem ?_ ?_) ?_
    · exact lie_mem_right ℝ A D.r _ _ R2.2
    · exact lie_mem_left ℝ A D.r _ _ R1.2
    · exact lie_mem_right ℝ A D.r _ _ R2.2
  have e : ⁅x, y⁆ = ((⁅S1, S2⁆ : D.s) : A) +
      ((⟨_, hr⟩ : D.r) : A) := by
    rw [← hx, ← hy]
    simp only [LieSubalgebra.coe_bracket, lie_add, add_lie]
    abel
  rw [e, g55a_piS]

theorem g55a_piS_expAd (D : LeviSplitting A) (x y : A) :
    piS D (expAd x y) = expAd (piS D x) (piS D y) := by
  let f : A →ₗ[ℝ] D.s := LinearMap.fst ℝ _ _ ∘ₗ (coords D).symm.toLinearMap
  have hc : Continuous f := (g55a_cont_split D).fst
  exact g55a_map_expAd f (fun a b => g55a_piS_lie D a b) hc x y

theorem g55a_fcc (D : LeviSplitting A) (W : Set A) (hW : IsLieWedge W) : FCC D W := by
  intro X hX S hS
  obtain ⟨y, hy, rfl⟩ := hS
  refine ⟨⟨expAd X y, hW.2.2 X hX ⟨y, hy, rfl⟩, g55a_piS_expAd D X y⟩, ?_⟩
  rintro _ ⟨_, ⟨R, hR, rfl⟩, rfl⟩
  set z := expAd X ((piS D y : A) + (R : A))
  have hz : z ∈ W := hW.2.2 X hX ⟨_, hR, rfl⟩
  have hpz : piS D z = expAd (piS D X) (piS D y) := by
    rw [g55a_piS_expAd, g55a_piS]
  refine ⟨piR D z, ?_, ?_⟩
  · show ((expAd (piS D X) (piS D y) : D.s) : A) + ((piR D z : D.r) : A) ∈ W
    rw [← hpz, g55a_decomp]; exact hz
  · show ((expAd (piS D X) (piS D y) : D.s) : A) + ((piR D z : D.r) : A) = z
    rw [← hpz, g55a_decomp]

end G55ASlice


open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- arXiv:2608.27330v1, PDF p.21, Lemma 4.2. -/
theorem solution (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    IsLieWedge (radicalSlice D W) ∧
    edge (radicalSlice D W) = {R : D.r | (R : A) ∈ edge W} := by
  exact g55a_radslice D W hW

end AbstractResults


end

