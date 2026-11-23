-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.mom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:29.229438+00:00
-- url     : https://prove2.me/submissions/b5b5ab7d-1d8a-4f77-8aae-80017aeee59e

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
    mom c (monomial s r) = r * phi c s := by
  rw [mom]
  simp_rw [evX_monomial_mul_gs]
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_volume_eq_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) => fac c s a i z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hM c hc _ _).2
end PositivityTheory.Rg.Sw.LC
