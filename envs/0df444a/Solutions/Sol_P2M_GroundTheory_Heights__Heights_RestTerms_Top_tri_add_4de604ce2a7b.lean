-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:26.902193+00:00
-- url     : https://prove2.me/submissions/2801ce53-7c13-4cc1-be95-a57116f9c99a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  have h1 : (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show r' + 1 + (a' + 1) - 1 = r' + a' + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  obtain ⟨x, hx⟩ := Nat.even_mul_pred_self r
  obtain ⟨y, hy⟩ := Nat.even_mul_pred_self a
  generalize r * (r - 1) = A at h1 hx ⊢
  generalize a * (a - 1) = B at h1 hy ⊢
  generalize r * a = P at h1 ⊢
  generalize (r + a) * (r + a - 1) = T at h1 ⊢
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
