-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:17.964209+00:00
-- url     : https://prove2.me/submissions/473735fc-5b82-4ad9-b4e3-eff066a3c95d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) : aeval y f = 0 := by
  have h1 : (aeval (fun _ : ι => (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ => φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2]
end GroundTheory.Heights₂.Heights.ChartLatSection
