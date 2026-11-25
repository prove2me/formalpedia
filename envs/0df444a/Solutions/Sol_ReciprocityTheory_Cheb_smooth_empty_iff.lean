-- Prove2me | solution 1 for ReciprocityTheory.Cheb.smooth_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:27.599057+00:00
-- url     : https://prove2.me/submissions/fd3c7228-bd6a-453e-b3ba-1cb6b7539a42

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) :
    Smooth ∅ a ↔ a = ⊤ := by
  constructor
  · intro hs
    by_contra htop
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal a htop
    have hMb : M ≠ ⊥ := fun h => ha (le_bot_iff.1 (h ▸ haM))
    let q : Prm E := ⟨M, hM.isPrime, hMb⟩
    exact absurd (hs q (Ideal.dvd_iff_le.2 haM)) (Finset.notMem_empty q)
  · rintro rfl q hq
    rw [← Ideal.one_eq_top] at hq
    exact absurd (isUnit_of_dvd_one hq) q.prime.not_isUnit
end ReciprocityTheory.Cheb
