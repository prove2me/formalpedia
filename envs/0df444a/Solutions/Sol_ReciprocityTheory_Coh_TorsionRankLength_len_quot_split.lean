-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.len_quot_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:19.030163+00:00
-- url     : https://prove2.me/submissions/accf7364-ca43-4faf-84ff-f3e076a7ba3c

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_finrank_torsion_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution (r : R) :
    Module.length R (QuotSMulTop r H) = Module.length R (QuotSMulTop r (torsion R H)) +
      Module.finrank R H * Module.length R (R ⧸ Ideal.span {r}) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := H ⧸ torsion R H)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (torsion R H).mkQ LinearMap.id
    (torsion R H).mkQ_surjective
  have e : (torsion R H × (H ⧸ torsion R H)) ≃ₗ[R] H :=
    lequivProdOfRightSplitExact (torsion R H).injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  have hrank : Module.finrank R H = n := by
    have h := Submodule.finrank_quotient_add_finrank (torsion R H)
    rw [finrank_torsion_eq_zero, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin] at h
    exact h.symm
  have e2 : QuotSMulTop r H ≃ₗ[R]
      ((R ⧸ Ideal.span {r}) ⊗[R] torsion R H) × ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) :=
    (QuotSMulTop.congr r e.symm).trans ((QuotSMulTop.equivQuotTensor r _).trans
      (TensorProduct.prodRight R R _ _ _))
  have e3 : ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) ≃ₗ[R] (Fin n →₀ (R ⧸ Ideal.span {r})) :=
    (LinearEquiv.lTensor _ b.repr).trans (TensorProduct.finsuppScalarRight R R _ _)
  rw [e2.length_eq, Module.length_prod, ← (QuotSMulTop.equivQuotTensor r _).length_eq,
    e3.length_eq, Module.length_finsupp, hrank]
  simp
end ReciprocityTheory.Coh.TorsionRankLength
