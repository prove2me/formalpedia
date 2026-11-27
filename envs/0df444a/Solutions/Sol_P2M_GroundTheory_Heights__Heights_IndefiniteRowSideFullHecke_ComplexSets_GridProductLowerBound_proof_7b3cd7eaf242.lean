-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_proof_7b3cd7eaf242
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:27.098929+00:00
-- url     : https://prove2.me/submissions/f01b4e74-0026-4873-a88c-17c9d2cfbc20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGridProductLowerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GridProductLowerBound
theorem _root_.solution : GridProductLowerBound.Statement := by
  classical
  intro σ _ N Z z₀ hZ hz₀
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by
    rw [Metric.mem_closure_iff] at hz₀
    push Not at hz₀
    exact hz₀
  obtain ⟨R, hR⟩ := hZ.subset_closedBall z₀
  set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK0 : ∀ w ∈ K, w ≠ 0 := by
    rintro w hw rfl
    simp [hK, hε] at hw
  let g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ := fun k v =>
    Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖
  have hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v := by
    intro k
    by_cases hk : k ≤ N
    · rcases (Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩
      have hgc : Continuous (g k) := Continuous.finset_sup'_apply
        (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _
        fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_apply m)))
      obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn
      obtain ⟨u, hu⟩ := GridProductLowerBound.exists_grid_prod_ne_zero hk v₀
        fun m => hK0 _ (hv₀ m (Set.mem_univ _))
      exact ⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) =>
        ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose μf hμf0 hμf using hbd
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf,
    (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro z hz s hs hcard
  set e := s.equivFin
  set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef
  have hv : v ∈ Set.univ.pi fun _ : Fin s.card => K := by
    intro m _
    have hx := hs (e.symm m).2
    have h1 := hεZ _ hx
    have h2 := Metric.mem_closedBall.1 (hR hx)
    have h3 := Metric.mem_ball.1 hz
    have h4 := dist_triangle z₀ z (e.symm m : σ → ℂ)
    have h5 := dist_triangle z z₀ (e.symm m : σ → ℂ)
    rw [dist_comm z₀ z] at h4
    rw [dist_comm] at h2
    simp only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm,
      not_lt]
    constructor <;> linarith
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)
  refine ⟨u, ?_⟩
  have hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i := by
    rw [← Finset.prod_coe_sort, ← e.symm.prod_comp]
    rfl
  rw [hprod]
  have hle := (Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)
  simp only [g] at hle
  rwa [hu] at hle
end GridProductLowerBound
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
