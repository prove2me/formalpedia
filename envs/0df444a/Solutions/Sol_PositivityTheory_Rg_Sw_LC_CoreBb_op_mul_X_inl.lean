-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:23.912878+00:00
-- url     : https://prove2.me/submissions/84104888-a94a-461c-b4d0-372a6ea6153c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_monomial

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (s : Sym m n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    op (s * X (Sum.inl k)) f = X k * op s f := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [X, monomial_mul, mul_one, op_monomial, op_monomial, opMono_eq, opMono_eq]
    have h1 : (t + Finsupp.single (Sum.inl k) 1).comapDomain Sum.inl Sum.inl_injective.injOn =
        t.comapDomain Sum.inl Sum.inl_injective.injOn + Finsupp.single k 1 := by
      ext x; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
    have h2 : (fun x => (t + Finsupp.single (Sum.inl k) 1 : _ →₀ ℕ) (Sum.inr x)) = fun x => t (Sum.inr x) := by
      funext x; simp [Finsupp.single_apply]
    rw [h1, h2, ← mul_one (1 : ℂ), ← monomial_mul, ← X]
    simp only [mul_one, smul_eq_mul]
    ring_nf
    simp [mul_comm, mul_left_comm, mul_assoc, Algebra.mul_smul_comm]
  | add p q hp hq => rw [add_mul, op_add, op_add, hp, hq, mul_add]
end PositivityTheory.Rg.Sw.LC.CoreBb
