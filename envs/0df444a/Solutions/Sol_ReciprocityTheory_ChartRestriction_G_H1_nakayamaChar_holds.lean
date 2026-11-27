-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.nakayamaChar_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:41.830795+00:00
-- url     : https://prove2.me/submissions/21a67d71-8343-4357-b2ad-8851c2602d42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_Lemmata_GeneralBFactExtra_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_linearIndependent_of_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open Module TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution : NakayamaCharStatement := by
  intro R _ _ M _ _ _ _ ι _ Γ T χ s hcard hs hT hχ
  classical
  have hiff : ∀ x : M, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = 0 ↔
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    intro x
    have h1 : TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)
        ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
      have h := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (IsLocalRing.maximalIdeal R) (1 : R) x
      rw [one_smul] at h
      exact h
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, LinearEquiv.map_eq_zero_iff]
    exact Iff.rfl
  let w : ι → IsLocalRing.ResidueField R ⊗[R] M := fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] s i
  have hw0 : ∀ i, w i ≠ 0 := fun i h => hs i ((hiff (s i)).mp h)
  have he : ∀ i γ, ((T γ).baseChange (IsLocalRing.ResidueField R)) (w i) =
      IsLocalRing.residue R (χ i γ) • w i := by
    intro i γ
    have hd := (hiff _).mpr (hT i γ)
    rw [TensorProduct.tmul_sub, sub_eq_zero] at hd
    simp only [w, LinearMap.baseChange_tmul, hd, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    congr 1
    rw [Algebra.smul_def, mul_one]
    rfl
  have hd : ∀ i j, i ≠ j → ∃ γ, IsLocalRing.residue R (χ i γ) ≠ IsLocalRing.residue R (χ j γ) := by
    intro i j hij
    obtain ⟨γ, hγ⟩ := hχ i j hij
    refine ⟨γ, fun h => hγ ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have hli : LinearIndependent (IsLocalRing.ResidueField R) w :=
    linearIndependent_of_eigen (fun γ => (T γ).baseChange (IsLocalRing.ResidueField R))
      (fun i γ => IsLocalRing.residue R (χ i γ)) w hw0 he hd
  have hcard' : Fintype.card ι = finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) := by
    rw [Module.finrank_baseChange, hcard]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) = 0 := by
      rw [← hcard']
      exact Fintype.card_eq_zero
    haveI : Subsingleton (IsLocalRing.ResidueField R ⊗[R] M) := Module.finrank_zero_iff.mp h0
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis s (Basis.empty _) (fun i => isEmptyElim i)
  · exact IsLocalRing.span_eq_top_of_tmul_eq_basis s
      (basisOfLinearIndependentOfCardEqFinrank hli hcard')
      (fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank])
end ReciprocityTheory.ChartRestriction.G.H1
