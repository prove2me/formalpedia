-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.four_hits_mem_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:33:53.636033+00:00
-- url     : https://prove2.me/submissions/743a8373-4713-47de-91bb-84896d7c7c1c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NetCatch
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventAnchor_mem
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_grid_cover
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_hit_center_near_anchor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mem_global_event
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_eq
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_unitBall_subset_radiusTwo


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : Event P J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (eventSupport P J radius)
      (eventBad P J radius lambda ((alpha+2)*lambda)) e := by
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ lambda := by positivity
  have hz := hit_center_near_anchor P J p t ((alpha : ℝ)*lambda) lambda hJ hl0 hp
    (eventAnchor P J radius e) z (hits _ (eventAnchor_mem P J radius e))
  have hball : z ∈ Metric.closedBall ((lambda : ℝ) • oldAnchor P J (eventAnchor P J radius e))
      (((alpha+2)*lambda : ℕ) : ℝ) := by
    change dist z _ ≤ _
    push_cast
    nlinarith
  obtain ⟨g,hg⟩ := exists_grid_cover ((alpha+2)*lambda)
    ((lambda : ℝ) • oldAnchor P J (eventAnchor P J radius e)) z hball
  apply (mem_global_event P J radius lambda ((alpha+2)*lambda) e p).mpr
  refine ⟨g,?_⟩
  intro a
  obtain ⟨y,hy,hyz⟩ := hits a.val a.property
  have hnet : dist z (eventCenter P J radius lambda ((alpha+2)*lambda) e g) ≤ 1 := hg
  have hynet := unitBall_subset_radiusTwo z _ hnet hyz
  rw [oldTriangleImage_eq] at hy
  refine ⟨y,?_,hynet⟩
  exact hy
end QEC.Coding.BDL26RandomPerturbation
