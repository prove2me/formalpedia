-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.coeff_eq_zero_of_evU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:05.480903+00:00
-- url     : https://prove2.me/submissions/47438687-4940-4a3c-b285-fcf292bdc11c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QF
theorem _root_.solution (r : (Module.End ℂ M)[X]) (h : ∀ u : ℂ, evU u r = 0) (i : ℕ) : r.coeff i = 0 := by
  by_cases hi : i ∈ r.support
  swap
  · exact notMem_support_iff.mp hi
  ext m
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  have hq0 : (∑ e ∈ r.support, monomial e (φ (r.coeff e m))) = 0 := by
    refine Polynomial.funext fun u => ?_
    rw [eval_zero, eval_finset_sum]
    have hu := congrArg (fun T : Module.End ℂ M => φ (T m)) (h u)
    simp only [evU_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.zero_apply, map_zero, RingHom.id_apply,
      LinearMap.sum_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
      map_smul, map_sum, smul_eq_mul] at hu
    rw [← hu]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, mul_comm]
  have hc := congrArg (fun p : ℂ[X] => p.coeff i) hq0
  simp only [finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', if_pos hi] at hc
  exact hc
end PositivityTheory.Rg.Cz.QF
