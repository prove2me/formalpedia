-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.op_renameL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:29.563797+00:00
-- url     : https://prove2.me/submissions/4354ed7a-b8a0-43e9-a627-0b179631a084

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_mulL

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
theorem _root_.solution (p : PX m n) (s : Sym m n) (f : PX m n) : op (rename Sum.inl p * s) f = p * op s f := by
  conv_lhs => rw [p.as_sum, map_sum, Finset.sum_mul]
  conv_rhs => rw [p.as_sum, Finset.sum_mul]
  rw [op_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : (monomial (Finsupp.mapDomain Sum.inl μ) (coeff μ p) : Sym m n) =
      coeff μ p • monomial (Finsupp.mapDomain Sum.inl μ) 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : (monomial μ (coeff μ p) : PX m n) = coeff μ p • monomial μ 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [rename_monomial, h1, h2, smul_mul_assoc, op_smul, op_mulL, smul_mul_assoc]
end PositivityTheory.Rg.Sw.LC.B1
