-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redSys_twistSys_zero_4c3119d833e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:08.965808+00:00
-- url     : https://prove2.me/submissions/7410e893-4126-4e0a-aa8d-b165b9cd1f49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    change redAt k x y (q / 1) ∈ twistMod k y 0 I
    rw [div_one]
    exact res_mem_twistMod_zero_of_mem_chartRing
      (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_redAt_eq hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hz)
    exact Submodule.subset_span ⟨a, res_mem_twistMod_zero_of_mem_chartRing ha, by
      change redAt k x y (a / 1) = redAt k x y a
      rw [div_one]⟩
end GroundTheory.Heights₂.Heights.Kleiman
