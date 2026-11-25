-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetLift_bsmul_mem_58372630c091
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:11.518059+00:00
-- url     : https://prove2.me/submissions/7f4c2ff3-4f5b-486e-b11d-dba2b4c7c312

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
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : bsmul c z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · obtain ⟨S, hS, hPS⟩ := hP
    have hle : P ≤ RingHom.ker ((eval (bsmul c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [hPS, Ideal.span_le]
      intro g hg
      obtain ⟨a, ha⟩ := hS g hg
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, eval_bsmul_of_isMultiHomog ha c z,
        hz.2 g (by rw [hPS]; exact Ideal.subset_span hg), mul_zero]
    exact hle hf
end GroundTheory.Heights₂.Heights.SheetLift
