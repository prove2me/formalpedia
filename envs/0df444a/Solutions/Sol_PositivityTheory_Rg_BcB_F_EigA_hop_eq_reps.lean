-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.hop_eq_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:15.121987+00:00
-- url     : https://prove2.me/submissions/b58aa8ab-7742-4f02-a908-8472b1c5b66a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_apply
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
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] (v : V) :
    hop ρ K g v = ∑ γ ∈ reps K g, ρ γ v := by
  classical
  rw [hop_apply, finsum_eq_sum_of_fintype, reps]
  rw [Finset.sum_image]
  · simp only [map_mul, Module.End.mul_apply]
  · intro a _ b _ hab
    have : (a.out : K) = b.out := Subtype.ext (mul_right_cancel hab)
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, this]
end PositivityTheory.Rg.BcB.F.EigA
