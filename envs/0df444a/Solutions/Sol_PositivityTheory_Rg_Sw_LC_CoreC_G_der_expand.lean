-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.der_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:11.9958+00:00
-- url     : https://prove2.me/submissions/2ff92005-b899-4c4f-8527-b7b94965cac9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, D (X v) * pderiv v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p u hp =>
    rw [Derivation.leibniz, hp]
    simp only [smul_eq_mul, Derivation.leibniz, pderiv_X', mul_add, Finset.sum_add_distrib]
    have h1 : ∑ v, D (X v) * (p * (if v = u then (1 : MvPolynomial τ ℂ) else 0)) = p * D (X u) := by
      simp [mul_ite]; ring
    have h2 : ∑ v, D (X v) * (X u * pderiv v p) = X u * ∑ v, D (X v) * pderiv v p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1, h2]
end PositivityTheory.Rg.Sw.LC.CoreC.G
