-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Generic_proof_f0afc2d97b29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:46.265916+00:00
-- url     : https://prove2.me/submissions/eb1ee28b-f4ef-450e-a4cc-965041caef94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677

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
namespace Generic
theorem _root_.solution (hF : FiniteSections.Statement.{w, w}) : Generic.Statement.{u, w} := by
  intro S _ _ _ Ω _ _ N N' x x' hx' _ hcl
  classical
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ m : S, algebraMap S Ω m ≠ 0 ∧
      ∀ b ∈ domRing S x x' i, algebraMap S Ω m * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨m, hm0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx') {y | ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s = y}
      ⟨1, by simp, by simp⟩
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact ⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, map_mul _ _ _⟩)
      (by
        rintro _ ⟨a, -, rfl⟩
        exact Subalgebra.algebraMap_mem _ a)
      (fun g hg => by
        obtain ⟨s, hs0, hs⟩ := hcl i hi g ((mem_domSub_iff hi g).mp hg)
        exact ⟨_, ⟨s, hs0, rfl⟩, hs⟩)
    exact ⟨m, hm0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose m hm0 hm using key
  have hM : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i,
      algebraMap S Ω (∏ j : {i // x i ≠ 0}, m j.1 j.2) * b ∈ chartRing S x (singleChart hi) := by
    intro i hi b hb
    rw [← Finset.mul_prod_erase Finset.univ (fun j : {i // x i ≠ 0} => m j.1 j.2)
      (Finset.mem_univ ⟨i, hi⟩), map_mul, mul_comm (algebraMap S Ω _) (algebraMap S Ω _), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hm i hi b hb)
  refine ⟨∏ j : {i // x i ≠ 0}, m j.1 j.2, ?_, hM, fun L n z hz => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hm0 j.1 j.2
  · refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    rw [← mul_assoc]
    exact Submodule.smul_mem _ (⟨_, hM i hi b hb⟩ : chartRing S x (singleChart hi)) hl
end Generic
end GroundTheory.Heights₂.Heights.Kleiman.Domination
