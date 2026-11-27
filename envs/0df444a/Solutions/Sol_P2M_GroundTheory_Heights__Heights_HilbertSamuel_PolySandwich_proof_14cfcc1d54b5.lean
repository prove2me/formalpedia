-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_proof_14cfcc1d54b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:25.790462+00:00
-- url     : https://prove2.me/submissions/d50989fa-1f90-4a3c-a9ef-ff254c8b9655

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial Filter
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PolySandwich
theorem _root_.solution : PolySandwich.Statement := by
  intro D c p q hq hev
  set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg
  have h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ) :=
    hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]
  have h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ) :=
    hev.mono fun n hn => by
      rw [eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]; linarith [hn.2]
  have hgdeg : g.natDegree = p.natDegree := PolySandwich.natDegree_shift p c

  have key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E := by
    intro E hp hqE
    have a := PolySandwich.coeff_nonneg_of_eventually (q - p) E
      ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1
    have b := PolySandwich.coeff_nonneg_of_eventually (g - q) E
      ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2
    rw [coeff_sub] at a b
    rw [hg, PolySandwich.coeff_shift p c E hp] at b
    linarith
  have hpD : p.natDegree ≤ D := by
    by_contra hlt
    push Not at hlt
    have e := key p.natDegree le_rfl (hq.trans hlt.le)
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)] at e
    have hp0 : p = 0 := leadingCoeff_eq_zero.mp e
    rw [hp0, natDegree_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  exact ⟨hpD, key D hpD hq⟩
end PolySandwich
end GroundTheory.Heights₂.Heights.HilbertSamuel
