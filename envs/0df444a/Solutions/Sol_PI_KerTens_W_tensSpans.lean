-- Prove2me | solution 1 for PI.KerTens.W.tensSpans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:18.166732+00:00
-- url     : https://prove2.me/submissions/c9963516-34bd-430f-965c-526d9c4762fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
import Theorems.Thm_PI_KerTens_W_key
import Theorems.Thm_PI_KerTens_W_tens_eq
import Theorems.Thm_PI_KerTens_W_slice_th
import Theorems.Thm_PI_KerTens_W_upd_part


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
namespace PI.KerTens.W
theorem _root_.solution : PI.KerTens.TensSpans := by
  intro c L n _ _ ΛM θ hyp N N' F hF
  by_cases hex : ∃ t0, θ t0 ^ Fintype.card (Fin N' × Fin N) ≠ 0
  · obtain ⟨t0, ht0⟩ := hex
    refine ⟨F (fun τ _ _ => t0 τ) / θ t0 ^ Fintype.card (Fin N' × Fin N), ?_⟩
    funext z
    have h := key c L ΛM θ hyp F hF t0 Finset.univ z
    have hr : repl t0 Finset.univ z = fun τ _ _ => t0 τ := by
      funext τ i j
      simp [repl]
    rw [hr, Finset.card_univ, ← tens_eq] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h
  · simp only [not_exists, not_not] at hex
    have hcard : Fintype.card (Fin N' × Fin N) ≠ 0 := by
      intro h0
      have := hex 0
      rw [h0, pow_zero] at this
      exact one_ne_zero this
    have hθ : ∀ t, θ t = 0 := fun t => (pow_eq_zero_iff hcard).mp (hex t)
    obtain ⟨b⟩ : Nonempty (Fin N' × Fin N) := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    refine ⟨0, ?_⟩
    funext z
    obtain ⟨a, ha⟩ := hyp _ (slice_th c L ΛM F hF z b)
    have e := congrFun ha (part z b)
    simp only [Pi.smul_apply, smul_eq_mul, upd_part, hθ, mul_zero] at e
    simp [e]
end PI.KerTens.W
