-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.mom_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:10.564449+00:00
-- url     : https://prove2.me/submissions/b1ba6101-8c52-4dcb-83cd-e509c1fa2b96

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_phi_rel
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hM : OneMom)
include hM
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add, mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]
end PositivityTheory.Rg.Sw.LC
