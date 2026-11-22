-- Prove2me | solution 1 for P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:49.00479+00:00
-- url     : https://prove2.me/submissions/8f811397-340b-46ab-91d6-c9ae9ec5f331

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (i j : σ) (f : MvPolynomial σ ℚ_[p]) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f k ih =>
    have h0 : ∀ a b : σ, pderiv a ((Pi.single b (1 : MvPolynomial σ ℚ_[p]) : σ → MvPolynomial σ ℚ_[p]) k) = 0 := by
      intro a b; rw [Pi.single_apply]; split_ifs <;> simp
    simp only [Derivation.leibniz, map_add, pderiv_X, smul_eq_mul, ih, h0]
    ring
end Formalism.GM.M.PhiIntegrality
