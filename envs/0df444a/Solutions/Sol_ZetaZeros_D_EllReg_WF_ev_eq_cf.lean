-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.ev_eq_cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:58.22935+00:00
-- url     : https://prove2.me/submissions/77a64c12-46a0-444e-b3ef-a75e58e333ef

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_single_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {m : ℕ} (g : E d → ℂ) (y : E d) : ∀ L : List (List (Fin d) × (E d → ℂ)),
    (∀ p ∈ L, p.1.length < m) →
    ev L g y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, cf L n w y * dw (List.ofFn w) g y
  | [], _ => by simp [ev, cf]
  | p :: L, hL => by
    rw [ev_cons, solution g y L (fun q hq => hL q (by simp [hq])), ← single_term p (hL p (by simp)) g y,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    simp only [cf, List.map_cons, List.sum_cons]
    ring
end ZetaZeros.D.EllReg.WF
