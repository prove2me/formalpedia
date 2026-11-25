-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.key_ineq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:40.353933+00:00
-- url     : https://prove2.me/submissions/ba4e2574-cf3a-4cd2-a85c-76bc56592cd0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (hc : 0 < c)
    (v y : Fin n → ℂ) (hvy : herm H v y = ((nsq v : ℝ) : ℂ)) (hyv : herm H y v = ((nsq v : ℝ) : ℂ))
    (hyy : (herm H y y).re ≤ c * nsq v) (hpos : 0 ≤ (herm H ((c : ℂ) • v - y) ((c : ℂ) • v - y)).re) :
    nsq v ≤ c * (herm H v v).re := by
  rw [herm_expand H hH c v y, hvy, hyv] at hpos
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hpos
  nlinarith
end PI.PolynomialProperness.CoreW
