-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetLift_lift_spec_d6ce7d4e2b06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:38.235897+00:00
-- url     : https://prove2.me/submissions/952559d5-831e-4bf6-b091-b86b271a7443

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_bsmul_mem_58372630c091
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_segre_bsmul_9046691c99e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458
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
theorem _root_.solution [DecidableEq K] {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (i0 : (k : K) → ι k)
    (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ mcPts P ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨bsmul_mem hP (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]
end GroundTheory.Heights₂.Heights.SheetLift
