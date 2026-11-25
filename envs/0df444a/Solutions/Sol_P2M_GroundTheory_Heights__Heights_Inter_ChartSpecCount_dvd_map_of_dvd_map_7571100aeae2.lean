-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_dvd_map_of_dvd_map_7571100aeae2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:03.585716+00:00
-- url     : https://prove2.me/submissions/50b68d46-fc16-465e-ae00-32758a77403f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocAwaySpec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartSpecCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Polynomial
open GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
namespace GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
theorem _root_.solution {A Φ K : Type*} [CommRing A] [Field Φ] [CommRing K] (fA : A →+* Φ) (σ : A →+* K)
    (hker : RingHom.ker fA ≤ RingHom.ker σ) {mA : A[X]} (hm : mA.Monic) {p : A[X]}
    (hp : mA.map fA ∣ p.map fA) : mA.map σ ∣ p.map σ := by
  have h0 : (p %ₘ mA).map fA = 0 := by
    rw [map_modByMonic fA hm]
    exact (modByMonic_eq_zero_iff_dvd (hm.map fA)).2 hp
  have h1 : (p %ₘ mA).map σ = 0 := by
    ext n
    rw [coeff_map, coeff_zero]
    exact RingHom.mem_ker.mp (hker (RingHom.mem_ker.mpr (by rw [← coeff_map, h0, coeff_zero])))
  refine ⟨(p /ₘ mA).map σ, ?_⟩
  conv_lhs => rw [← modByMonic_add_div p mA]
  rw [Polynomial.map_add, Polynomial.map_mul, h1, zero_add]
end GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
