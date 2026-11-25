-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_prm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:31.387402+00:00
-- url     : https://prove2.me/submissions/7461a8bd-8e36-47dd-9a92-1948cb95a14a

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_sum_le_idealZetaR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) := by
  classical
  refine summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ ?_
  unfold Nrm
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 E) ↦ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s))
    (g := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    (fun v _ w _ h ↦ IsDedekindDomain.HeightOneSpectrum.ext h)]
  exact sum_le_idealZetaR E hs _
end ReciprocityTheory.Cheb
