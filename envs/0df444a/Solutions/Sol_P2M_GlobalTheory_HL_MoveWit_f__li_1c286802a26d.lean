-- Prove2me | solution 1 for P2M_GlobalTheory_HL_MoveWit_f__li_1c286802a26d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:06.859419+00:00
-- url     : https://prove2.me/submissions/f50691f5-e6b4-4479-af29-b95bfafc9511

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_add_l
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_smul_l
import Theorems.Thm_GlobalTheory_HL_MoveWit_h_zero_l
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveWit
theorem _root_.solution : LinearIndependent E fun j : Fin r => S.f' j.castSucc := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : S.h (∑ j, c j • S.f' j.castSucc) (S.es' i) = ∑ j, c j * S.h (S.f' j.castSucc) (S.es' i) := by
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [h_zero_l]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_l, ih, h_smul_l]
  rw [hc, h_zero_l] at h1
  simp only [Frames.h, S.dual', Fin.castSucc_inj] at h1
  simpa using h1.symm
end GlobalTheory.HL.MoveWit
