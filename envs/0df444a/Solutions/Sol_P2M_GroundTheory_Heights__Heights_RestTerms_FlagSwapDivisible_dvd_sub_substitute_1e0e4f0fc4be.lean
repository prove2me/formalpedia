-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:55.984873+00:00
-- url     : https://prove2.me/submissions/ceb85fa1-9410-4758-a4b2-3bc77f3c062f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagSwapDivisible

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagSwapDivisible
theorem _root_.solution {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)
end FlagSwapDivisible
end GroundTheory.Heights₂.Heights.RestTerms
