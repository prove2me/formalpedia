-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Normal_proof_52035cac6f86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:31:52.918134+00:00
-- url     : https://prove2.me/submissions/31471784-7f32-460e-b5ec-35367425e7dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832

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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
namespace Normal
theorem _root_.solution (hF : FiniteSections.Statement.{w, w}) : Normal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ _ hbir' hnorm
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0),
      domRing S x x' i = (chartRing S x (singleChart hi) : Set Ω) := by
    intro i hi
    ext b
    constructor
    · intro hb
      exact hnorm i hi b (IsIntegral.of_mem_of_fg _ (fg_domSub hi hF hx') b
        ((mem_domSub_iff hi b).mpr hb))
    · intro hb
      exact (mem_domRing_iff hi b).mpr fun J =>
        Subalgebra.algebraMap_mem _ (⟨b, hb⟩ : chartRing S x (singleChart hi))
  refine ⟨key, fun L n => ?_⟩
  intro z hz
  have h := mul_mem_secs_of_pullSecs (κ := 1) (L := L.pow n) (L' := L.pow n)
    (fun i hi b hb l hl => by
      rw [one_mul]
      have hb' : b ∈ chartRing S x (singleChart hi) := by
        rw [key i hi] at hb
        exact hb
      exact Submodule.smul_mem _ (⟨b, hb'⟩ : chartRing S x (singleChart hi)) hl) z hz
  rwa [one_mul] at h
end Normal
end GroundTheory.Heights₂.Heights.Kleiman.Domination
