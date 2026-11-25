-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:14.862552+00:00
-- url     : https://prove2.me/submissions/1bddab16-b55e-4c49-9c57-683cb9b55e36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
open GroundTheory.Heights₂.Heights.SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SheetLift
theorem _root_.solution [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ}
    (hz : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) = bsmul (fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hz) k (Finset.mem_univ k)
  funext ⟨k, j⟩
  have e1 : segre z (Function.update i0 k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ :=
    prod_update_eq z i0 k j
  have e2 : segre z i0 = z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
    have := prod_update_eq z i0 k (i0 k)
    rwa [Function.update_eq_self] at this
  have hQ : ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => h0 k'
  have hk := h0 k
  simp only [lift, bsmul]
  rw [e1, e2]
  field_simp
end GroundTheory.Heights₂.Heights.SheetLift
