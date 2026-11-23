-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.out_mk_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:37.678034+00:00
-- url     : https://prove2.me/submissions/670fe2e9-b4e5-49b1-9587-d21dc8ed7bfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {H M : Type} [Group H] (A : Subgroup H) (F : H → M) (hF : ∀ x, ∀ a ∈ A, F (x * a) = F x)
    (y : H) : F ((y : H ⧸ A).out) = F y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A y
  rw [ha, hF _ _ a.2]
end PositivityTheory.Rg.BcB.F.EigA
