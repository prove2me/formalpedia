-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCenterLe_proof_d615c0dd3482
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:06:49.779098+00:00
-- url     : https://prove2.me/submissions/00c69933-f3e1-49fa-9ff0-7fb5554a8a3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitePlaceSumLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e

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
open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace OrbitCenterLe
theorem _root_.solution : OrbitCenterLe.Statement := by
  intro ι _ _ n x v F d hF
  classical
  have hle : ∀ k i, v (coordVec x k i) ≤ ⨆ j, v (coordVec x k j) := fun k i ↦
    le_ciSup (f := fun j ↦ v (coordVec x k j)) (Set.finite_range _).bddAbove i
  have hM0 : ∀ k, 0 ≤ ⨆ j, v (coordVec x k j) := fun k ↦ (apply_nonneg v _).trans (hle k 0)
  have hna : IsNonarchimedean (v : coordField x → ℝ) := fun a b ↦ v.add_le a b
  have hW : IsWeightedHomogeneous (coordDeg n) F d := (geoMultiHomog_iff F d).mp hF
  unfold evalCone
  rw [eval₂_eq']
  refine finitePlace_sum_le v _ _
    (Finset.prod_nonneg fun k _ ↦ pow_nonneg (hM0 k) _) fun m hm ↦ ?_
  have hw : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hW (mem_support_iff.mp hm)]
  have hc : v ((Int.castRingHom (coordField x)) (F.coeff m)) ≤ 1 := by
    simpa using IsNonarchimedean.apply_intCast_le_one (f := v) hna (n := F.coeff m)
  rw [map_mul, map_prod]
  calc v ((Int.castRingHom (coordField x)) (F.coeff m)) * ∏ p, v (coordVec x p.1 p.2 ^ m p)
      ≤ 1 * ∏ p : Coord n, (⨆ j, v (coordVec x p.1 j)) ^ m p := by
        gcongr with p
        rw [map_pow]; exact pow_le_pow_left₀ (apply_nonneg v _) (hle _ _) _
    _ = ∏ k, (⨆ j, v (coordVec x k j)) ^ d k := by
        rw [one_mul, Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.prod_pow_eq_pow_sum, hw k]
end OrbitCenterLe
end GroundTheory.Heights₂.Heights
