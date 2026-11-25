-- Prove2me | solution 1 for P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:51.512237+00:00
-- url     : https://prove2.me/submissions/774e0f11-e048-4751-8cf7-4321c76fe335

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_mem_gr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution (d : LocNG.Datum P) (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))) :
    (c.e x', c.e x) ∈ (c.dat d).2.2 ↔ Q d x' x := by
  rw [mem_gr]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x'.2, x.2, h⟩⟩
end GlobalTheory.HL.CoordDatum
