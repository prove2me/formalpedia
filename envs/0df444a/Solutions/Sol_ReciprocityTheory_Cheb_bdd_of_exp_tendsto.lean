-- Prove2me | solution 1 for ReciprocityTheory.Cheb.bdd_of_exp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:16.60335+00:00
-- url     : https://prove2.me/submissions/b2b87092-9c8a-465e-be34-0f9899ddecc6

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Theorems.Thm_ReciprocityTheory_Cheb_bounded_of_tendsto_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Filter Topology Set Complex
namespace ReciprocityTheory.Cheb
theorem _root_.solution (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 1)) (L1 : ℂ) (hL : L1 ≠ 0)
    (h : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_tendsto_exp (hf.mono Set.Ioc_subset_Ioi_self) hL h
  exact ⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT one_lt_two) hC⟩
end ReciprocityTheory.Cheb
