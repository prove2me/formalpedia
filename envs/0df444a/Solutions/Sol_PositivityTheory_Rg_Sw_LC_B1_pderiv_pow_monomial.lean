-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.pderiv_pow_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:50.992906+00:00
-- url     : https://prove2.me/submissions/55bfdd7b-2e1e-4d04-9ba4-9f71b231db0e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (i : σ) (e : ℕ) (s : σ →₀ ℕ) (a : ℂ) :
    (((pderiv (R := ℂ) i).toLinearMap ^ e) (monomial s a) : PX m n) =
      monomial (s - Finsupp.single i e) (a * ((s i).descFactorial e : ℂ)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    show (pderiv (R := ℂ) i) (monomial _ _) = _
    rw [pderiv_monomial]
    have e1 : s - Finsupp.single i e - Finsupp.single i 1 = s - Finsupp.single i (e + 1) := by
      ext k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have h : (s - Finsupp.single i e) i = s i - e := by simp
    rw [e1, h, Nat.descFactorial_succ]
    congr 1
    push_cast
    ring
end PositivityTheory.Rg.Sw.LC.B1
