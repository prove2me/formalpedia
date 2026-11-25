-- Prove2me | solution 1 for P2M_GlobalTheory_HL_MoveWit_f__perp_4f16c2e0247f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:50.061547+00:00
-- url     : https://prove2.me/submissions/add00f31-3dd5-407c-959f-ef3915488e5f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_add_r
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_smul_r
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_zero_r
import Theorems.Thm_P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveWit
theorem _root_.solution (b : Fin (r + 1)) : S.f' b ∈ perp L S.Hm S.X' := by
  rw [← X'_eq]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [S.gram', if_neg]
    exact fun h => (Fin.castSucc_lt_last j).ne h.2
  | zero => exact h_zero_r S _
  | add y z _ _ h1 h2 => exact (h_add_r S _ _ _).trans (by unfold Frames.h; rw [h1, h2, add_zero])
  | smul c y _ h1 => exact (h_smul_r S _ _ _).trans (by unfold Frames.h; rw [h1, mul_zero])
end GlobalTheory.HL.MoveWit
