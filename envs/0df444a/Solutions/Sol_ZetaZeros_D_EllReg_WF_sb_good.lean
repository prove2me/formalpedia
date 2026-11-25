-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.sb_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:33:24.487361+00:00
-- url     : https://prove2.me/submissions/c0e73286-e225-41e8-9d7e-90cc83242aff

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_lb_good

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
theorem _root_.solution {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {k : ℕ} {K : Set (E d)} :
    ∀ L : List (List (Fin d) × (E d → ℂ)), Good k K L → Good k K (sb a L)
  | [], _ => by intro p hp; simp [sb] at hp
  | p :: L, hL => by
    have hp := hL p (by simp)
    have ih := solution ha L (fun q hq => hL q (by simp [hq]))
    have hlb := lb_good ha isClosed_univ (by simp) p.1
    intro q hq
    simp only [sb, sc, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩ | hq
    · exact ⟨hp.1, hp.2.1.mul ha, fun y hy => by simp [hp.2.2 y hy]⟩
    · obtain ⟨h1, h2, -⟩ := hlb r hr
      exact ⟨lt_trans h1 hp.1, hp.2.1.mul h2, fun y hy => by simp [hp.2.2 y hy]⟩
    · exact ih q hq
end ZetaZeros.D.EllReg.WF
