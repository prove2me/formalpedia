-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_translate_inCell__7d37710349e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:33.191427+00:00
-- url     : https://prove2.me/submissions/35432351-ae7a-4396-8d12-a4abef54619a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCell
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCellStatement
import Theorems.Thm_GlobalTheory_KSp_exists_translate_inCell


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))), ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  first | exact @GlobalTheory.KSp.exists_translate_inCell | exact GlobalTheory.KSp.exists_translate_inCell | (intros; apply GlobalTheory.KSp.exists_translate_inCell <;> assumption)
end _root_.GlobalTheory.T
