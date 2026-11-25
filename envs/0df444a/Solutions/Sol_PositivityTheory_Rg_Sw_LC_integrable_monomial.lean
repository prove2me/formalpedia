-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.integrable_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:27.067067+00:00
-- url     : https://prove2.me/submissions/71484633-af1d-4e14-a584-66b10ba4eb89

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_evX_monomial_mul_gs

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
theorem _root_.solution (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX (monomial s r) x * gs c x) := by
  simp_rw [evX_monomial_mul_gs]
  refine Integrable.const_mul ?_ r
  exact Integrable.fintype_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))
    (fun a => Integrable.fintype_prod (f := fun i (z : ℂ) => fac c s a i z) (fun i => (hM c hc _ _).1))
end PositivityTheory.Rg.Sw.LC
