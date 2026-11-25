-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_wt_eq_mul_nu__44594a671204
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:07.803955+00:00
-- url     : https://prove2.me/submissions/50665fdc-8368-4939-ac4e-0447da649473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsWtEqMulNu
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsWtEqMulNuStatement
import Theorems.Thm_GlobalTheory_HL_CoordDatum_exists_wt_eq_mul_nu


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  first | exact @GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu | exact GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu | (intros; apply GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu <;> assumption)
end _root_.GlobalTheory.T
