-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.finsum_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:10.826333+00:00
-- url     : https://prove2.me/submissions/eea6cd71-4699-456f-a9fd-4a0c1d43911c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {H M : Type} [Group H] [AddCommMonoid M] (A B : Subgroup H) (hAB : A ≤ B)
    [Finite (H ⧸ A)] (F : H → M) (hF : ∀ x, ∀ b ∈ B, F (x * b) = F x) :
    ∑ᶠ q : H ⧸ A, F q.out = (A.relIndex B) • ∑ᶠ q : H ⧸ B, F q.out := by
  classical
  let e := Subgroup.quotientEquivProdOfLE hAB
  haveI : Finite ((H ⧸ B) × (B ⧸ A.subgroupOf B)) := Finite.of_equiv _ e
  haveI : Finite (H ⧸ B) :=
    Finite.of_surjective Prod.fst (fun p =>
      ⟨(p, ((1 : B) : B ⧸ A.subgroupOf B)), rfl⟩)
  haveI : Finite (B ⧸ A.subgroupOf B) :=
    Finite.of_surjective Prod.snd (fun r => ⟨(((1 : H) : H ⧸ B), r), rfl⟩)
  letI := Fintype.ofFinite (H ⧸ A)
  letI := Fintype.ofFinite (H ⧸ B)
  letI := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (p : H ⧸ B) (r : B ⧸ A.subgroupOf B), F (e.symm (p, r)).out = F p.out := by
    intro p r
    induction r using QuotientGroup.induction_on with
    | H b =>
      have h1 : e.symm (p, (b : B ⧸ A.subgroupOf B)) = ((p.out * (b : H) : H) : H ⧸ A) := rfl
      rw [h1]
      obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A (p.out * (b : H))
      rw [ha, hF _ _ (hAB a.2), hF _ _ b.2]
  simp only [key, Finset.sum_const, Finset.card_univ]
  rw [← Finset.smul_sum, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
end PositivityTheory.Rg.BcB.F.EigA
