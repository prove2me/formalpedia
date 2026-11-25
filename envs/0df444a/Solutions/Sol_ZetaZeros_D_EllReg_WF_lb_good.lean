-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.lb_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:42.023741+00:00
-- url     : https://prove2.me/submissions/7a369c1f-155b-4491-ac33-3147280fe3dd

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_Dk
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_zero_off

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
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set (E d)} (hK : IsClosed K)
    (hfK : ∀ y ∉ K, f y = 0) : ∀ w : List (Fin d), Good w.length K (lb w f)
  | [] => by intro p hp; simp [lb] at hp
  | k :: w => by
    have ih := solution hf hK hfK w
    intro p hp
    simp only [lb, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨by simp, contDiff_Dk hf k, Dk_zero_off hK hfK k⟩
    · obtain ⟨h1, h2, h3⟩ := ih q hq
      exact ⟨by simp; omega, contDiff_Dk h2 k, Dk_zero_off hK h3 k⟩
    · obtain ⟨h1, h2, h3⟩ := ih q hq
      exact ⟨by simp; omega, h2, h3⟩
end ZetaZeros.D.EllReg.WF
