-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_dvE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:56.115846+00:00
-- url     : https://prove2.me/submissions/d477da43-a653-4cfa-9f9a-0c965e154d3c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_comapDomain_inl_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_dvE_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_sum


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (w : Sym m n) (δ : Ix m n →₀ ℕ) (f : PX m n) :
    op w (dvE (fun k => δ k) f) = op (w * monomial (δ.mapDomain Sum.inr) 1) f := by
  classical
  conv_rhs => rw [w.as_sum, Finset.sum_mul, op_sum]
  conv_lhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, mul_one, op_monomial, opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, mapDomain_inr_inl]
  have h2 : (fun k : Ix m n => (t + δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) =
      (fun k => t (Sum.inr k)) + fun k => δ k := by
    ext j; simp [mapDomain_inr_inr]
  rw [h1, add_zero, h2, ← dvE_mul]
  rfl
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
