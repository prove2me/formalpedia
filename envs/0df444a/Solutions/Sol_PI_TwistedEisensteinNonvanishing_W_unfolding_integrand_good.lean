-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unfolding_integrand_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:51.189851+00:00
-- url     : https://prove2.me/submissions/af08ee28-400d-4c8b-ae73-c6ecb1eb81fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_chArg_add
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unfolding_matrix_free_coordinate
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unfolding_matrix_sub
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_character_argument_bounded
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_neg
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_qpow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_up
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : HGoodP := by
  intro E K _ _ _ _ P hp n' c' n c D j hjD psi hpsi G hGs hGp y
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  refine ⟨?_, ?_⟩
  · intro t ht l
    have hGne : G (xx1 y t) ≠ 0 := by
      intro h0; apply ht; simp only [h0, zero_mul]
    rw [← unfolding_matrix_free_coordinate y t l]
    exact hGs _ hGne _ _
  · intro t δ hδ
    set X := xx1 y t with hX
    set Dm := xx1 y (t + δ) - X with hDm
    have hsplit : xx1 y (t + δ) = X + Dm := by rw [hDm]; abel
    have hD : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
      intro s l
      rw [hDm, hX, unfolding_matrix_sub]
      split_ifs with hs hf
      · simp only [Pi.add_apply, add_sub_cancel_left]; exact hδ _
      · rw [zero_div]; exact ia_zero (P := P)
      · rw [zero_div]; exact ia_zero (P := P)
    have hDint : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l) := by
      intro s l
      have e : Dm (eN E (n' + c') s) l
          = (qOf P : E) ^ j * (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
        field_simp
      rw [e]; exact ia_mul (P := P) (ia_qpow (P := P) j) (hD s l)
    have hGeq : G (X + Dm) = G X := hGp X Dm hD
    simp only
    rw [hsplit, hGeq]
    by_cases hG : G X = 0
    · rw [hG, zero_mul, zero_mul]
    · have hB : IntAt P (chArg (n := n) (c := c) Dm) := by
        have := character_argument_bounded E P n' c' n c 0 Dm (fun s l => by rw [pow_zero, one_mul]; exact hDint s l)
        rwa [pow_zero, one_mul] at this
      have hA : IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) X) :=
        character_argument_bounded E P n' c' n c j X (hGs X hG)
      have hA' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) X) :=
        ia_up (P := P) hjD (by rw [mul_neg]; exact ia_neg (P := P) hA)
      have hB' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) Dm) :=
        ia_mul (P := P) (ia_qpow (P := P) D) (ia_neg (P := P) hB)
      rw [gh_chArg_add, neg_add, hpsi.1 _ _ hA' hB', hpsi.2.1 _ (ia_neg (P := P) hB), mul_one]
end PI.TwistedEisensteinNonvanishing.W
