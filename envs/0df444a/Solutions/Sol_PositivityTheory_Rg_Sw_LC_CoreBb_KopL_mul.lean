-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.KopL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:02.301981+00:00
-- url     : https://prove2.me/submissions/4bf7c22e-cb40-4787-913c-571f14420c6f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_apply

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (g h : PX m n) :
    KopL ε i j (g * h) = KopL ε i j g * h + g * KopL ε i j h := by
  rw [KopL_apply, KopL_apply, KopL_apply]
  have e1 : ∀ (p q : Fin m × Fin n × Bool), X p * pderiv q (g * h) = (X p * pderiv q g) * h + g * (X p * pderiv q h) := by
    intro p q; rw [pderiv_mul]; ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring
end PositivityTheory.Rg.Sw.LC.CoreBb
