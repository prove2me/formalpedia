-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.fA_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:30.12308+00:00
-- url     : https://prove2.me/submissions/a6a0a57d-530f-49f2-9ede-b5185401bd5c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_fun_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Qp_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Qp_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_partial_deriv_quadratic_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
private theorem sum_X_mul_pderiv_mem_QA_of_generators (ε : Fin m → Bool) (g h : Fin m → Fin m × Fin n × Bool)
    (hgen : ∀ k l, (∑ a, X (g a) * pderiv (h a) (Qp ε k l) : PX m n) ∈ QA ε) :
    ∀ R ∈ QA ε, (∑ a, X (g a) * pderiv (h a) R : PX m n) ∈ QA ε := by
  apply fun_mem ε (fun R => ∑ a, X (g a) * pderiv (h a) R)
  · intro x y
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  · intro x y
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun a _ => by ring)
  · intro r
    simp [Derivation.map_algebraMap]
  · exact hgen
end PositivityTheory.Rg.Sw.LC.NullS
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fA i j R ∈ QA ε := by
  intro R hR
  unfold fA
  refine sum_X_mul_pderiv_mem_QA_of_generators ε (fun a => (a, i, true)) (fun a => (a, j, true)) (fun k l => ?_) R hR
  simp only [partial_deriv_quadratic_pairing]
  by_cases h : k = j
  · subst h
    have e : (∑ a, X (a, i, true) * (C (sgn ε a) * X (a, l, false)) : PX m n) = Qp ε i l := by
      rw [Qp_eq]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    simp only [if_true]
    rw [e]
    exact Qp_mem ε i l
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    exact zero_mem _
end PositivityTheory.Rg.Sw.LC.NullS
