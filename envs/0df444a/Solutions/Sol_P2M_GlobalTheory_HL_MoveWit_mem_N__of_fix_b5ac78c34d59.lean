-- Prove2me | solution 1 for P2M_GlobalTheory_HL_MoveWit_mem_N__of_fix_b5ac78c34d59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:18:46.722881+00:00
-- url     : https://prove2.me/submissions/5ac444af-8023-4a7f-8e0b-8dd7784777cb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_mem_unipOn_of_fix
import Theorems.Thm_GlobalTheory_HL_MoveWit_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp


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
theorem _root_.solution {g : S.GLV} (hg : g ∈ isomG L S.Hm) (h : ∀ v ∈ perp L S.Hm S.X', g v = v) :
    g ∈ S.N' := by
  refine ⟨⟨hg, ?_⟩, mem_unipOn_of_fix S h⟩
  change g ∈ ⨅ j : Fin r, unipOn (S.spanTo S.f' (j + 1)) (S.spanTo S.f' j)
  rw [Subgroup.mem_iInf]
  exact fun j => mem_unipOn_of_fix S fun v hv => h v (spanTo_le_perp S _ hv)
end GlobalTheory.HL.MoveWit
