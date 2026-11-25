-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:47.187741+00:00
-- url     : https://prove2.me/submissions/8f72b0bb-7a5d-466d-bf39-015f4a99e912

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution (M : SubFamily S x Ω) (I J : Chart x) {y : Ω}
    (hy : y ∈ M.sub (unionChart I J)) : ∃ D : ℕ, chartRatio I J ^ D * y ∈ M.sub I := by
  obtain ⟨a, ha, hay⟩ := (M.mem_iff I (unionChart I J) (subset_unionChart_left I J) y).mp hy
  obtain ⟨v, hv⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I J v.2
  refine ⟨D, ?_⟩
  have hv' : (v : Ω) * (a : Ω) = 1 := congrArg Subtype.val hv
  have e : chartRatio I J ^ D * y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul]
    calc chartRatio I J ^ D * y = chartRatio I J ^ D * ((v : Ω) * a) * y := by rw [hv', mul_one]
      _ = _ := by ring
  rw [e]
  exact Submodule.smul_mem _ _ hay
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
