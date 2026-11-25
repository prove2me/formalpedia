-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:29:15.04543+00:00
-- url     : https://prove2.me/submissions/b8f89977-75b8-48b5-9aaf-f08876a6e915

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim_309aed0fc72d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
namespace GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
theorem _root_.solution {d m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Fin n ≃ Fin d ⊕ Fin m) (φ : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (φm : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (ι ⊕ κ), Isometry ψ ∧
      ∀ (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) x,
        ψ (graphPt e F x) = WithLp.toLp 2 (Sum.elim (fun i => φ x i) (fun i => φm (F x) i)) := by
  let πd : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin d) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  let πm : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inr k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  have hz : ∀ z : EuclideanSpace ℂ (Fin n),
      z = WithLp.toLp 2 (fun j => Sum.elim (fun i => πd z i) (fun i => πm z i) (e j)) := by
    intro z
    ext j
    obtain ⟨s, rfl⟩ := e.symm.surjective j
    rcases s with i | i <;> simp [πd, πm]
  refine ⟨fun z => WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)), ?_, ?_⟩
  · refine Isometry.of_dist_eq fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)) :
        EuclideanSpace ℝ (ι ⊕ κ)) - WithLp.toLp 2 (Sum.elim (fun i => φ (πd w) i) (fun i => φm (πm w) i)) =
        WithLp.toLp 2 (Sum.elim (fun i => φ (πd (z - w)) i) (fun i => φm (πm (z - w)) i)) := by
      ext s
      rcases s with i | i <;> simp [map_sub]
    rw [hsub]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hn := norm_sq_sumElim e (πd (z - w)) (πm (z - w))
    rw [← hz (z - w)] at hn
    rw [norm_sq_sumElim', φ.norm_map, φm.norm_map, hn]
  · intro F x
    have h1 : πd (graphPt e F x) = x := by ext k; simp [πd, graphPt]
    have h2 : πm (graphPt e F x) = F x := by ext k; simp [πm, graphPt]
    simp only [h1, h2]
end GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
