-- Prove2me | solution 1 for SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.eq_one_of_pow_two_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:43.064547+00:00
-- url     : https://prove2.me/submissions/df10691e-5a36-44d6-9270-f4c96159cae4

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
import Theorems.Thm_GlobalTheory_PositiveFormRecursion_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchrodingerSchwartzBruhat
open MeasureTheory Matrix
open SchrodingerSchwartzBruhat.GlobalTheory SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB
namespace SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PositiveFormRecursion.main
  | exact _root_.GlobalTheory.PositiveFormRecursion.main
  | (apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)
end SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB
