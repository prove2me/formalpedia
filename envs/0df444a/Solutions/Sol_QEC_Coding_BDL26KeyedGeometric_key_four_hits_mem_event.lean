-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.key_four_hits_mem_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:42:34.795237+00:00
-- url     : https://prove2.me/submissions/86e63d8d-6ca7-419c-9467-549be161d5d3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_mem
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_mem_keyEvent
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_grid_cover
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_hit_center_near_anchor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_eq
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_unitBall_subset_radiusTwo


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : KeyEvent P key hk J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (keySupport P key hk J radius)
      (keyBad P key hk J radius lambda ((alpha+2)*lambda)) e := by
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ lambda := by positivity
  have hz := hit_center_near_anchor P J p t ((alpha : ℝ)*lambda) lambda hJ hl0 hp
    (keyAnchor P key hk J radius e) z (hits _ (keyAnchor_mem P key hk J radius e))
  have hball : z ∈ Metric.closedBall ((lambda : ℝ) • oldAnchor P J (keyAnchor P key hk J radius e))
      (((alpha+2)*lambda : ℕ) : ℝ) := by
    change dist z _ ≤ _
    push_cast
    nlinarith
  obtain ⟨g,hg⟩ := exists_grid_cover ((alpha+2)*lambda)
    ((lambda : ℝ) • oldAnchor P J (keyAnchor P key hk J radius e)) z hball
  apply (mem_keyEvent P key hk J radius lambda ((alpha+2)*lambda) e p).mpr
  refine ⟨g,?_⟩
  intro a
  obtain ⟨y,hy,hyz⟩ := hits a.val a.property
  have hnet : dist z (keyCenter P key hk J radius lambda ((alpha+2)*lambda) e g) ≤ 1 := hg
  have hynet := unitBall_subset_radiusTwo z _ hnet hyz
  rw [oldTriangleImage_eq] at hy
  refine ⟨y,?_,hynet⟩
  exact hy
end QEC.Coding.BDL26KeyedGeometric
