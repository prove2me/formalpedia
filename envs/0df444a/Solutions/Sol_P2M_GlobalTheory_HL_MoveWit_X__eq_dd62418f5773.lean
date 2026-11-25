-- Prove2me | solution 1 for P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:57.417669+00:00
-- url     : https://prove2.me/submissions/bbc4f623-20cf-48cc-aa66-a9f86d86e88e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses

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
theorem _root_.solution : Submodule.span E (Set.range fun j : Fin r => S.f' j.castSucc) = S.X' := by
  unfold Frames.X' Frames.spanTo
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
end GlobalTheory.HL.MoveWit
