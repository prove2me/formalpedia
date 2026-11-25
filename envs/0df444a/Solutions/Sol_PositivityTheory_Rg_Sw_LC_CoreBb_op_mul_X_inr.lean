-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_X_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:38.521117+00:00
-- url     : https://prove2.me/submissions/77b1cf62-4749-48b1-ba1e-e40be378ab91

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_Dfun_add_single
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
    op (s * X (Sum.inr k)) f = op s (pderiv k f) := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [X, monomial_mul, mul_one, op_monomial, op_monomial, opMono_eq, opMono_eq]
    have h1 : (t + Finsupp.single (Sum.inr k) 1).comapDomain Sum.inl Sum.inl_injective.injOn =
        t.comapDomain Sum.inl Sum.inl_injective.injOn := by
      ext x; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
    have h2 : (fun x => (t + Finsupp.single (Sum.inr k) 1 : _ →₀ ℕ) (Sum.inr x)) =
        fun x => t (Sum.inr x) + if x = k then 1 else 0 := by
      funext x; simp [Finsupp.single_apply, eq_comm]
    rw [h1, h2, Dfun_add_single]
    rfl
  | add p q hp hq => rw [add_mul, op_add, op_add, hp, hq]
end PositivityTheory.Rg.Sw.LC.CoreBb
