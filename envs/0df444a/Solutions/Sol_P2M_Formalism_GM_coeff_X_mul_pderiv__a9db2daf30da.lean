-- Prove2me | solution 1 for P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:55.582586+00:00
-- url     : https://prove2.me/submissions/14ab7eab-38fa-40a3-9d6a-b479c70a668f

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM
theorem _root_.solution (i : σ) (p : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i p) = coeff m p * (m i : k) := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro s a
    have key : X i * pderiv i (monomial s a : MvPolynomial σ k) = monomial s (a * (s i : k)) := by
      rw [pderiv_monomial]
      by_cases hs : s i = 0
      · simp [hs]
      · rw [show (X i : MvPolynomial σ k) = monomial (Finsupp.single i 1) 1 from rfl,
          monomial_mul, one_mul]
        have hsum : Finsupp.single i 1 + (s - Finsupp.single i 1) = s := by
          ext j
          by_cases hij : i = j
          · subst hij
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
            omega
          · simp [hij]
        rw [hsum]
    rw [key, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  · intro p q hp hq
    simp only [map_add, mul_add, coeff_add, hp, hq, add_mul]
end Formalism.GM
