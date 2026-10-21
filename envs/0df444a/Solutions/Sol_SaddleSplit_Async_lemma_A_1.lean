-- Prove2me | solution 1 for SaddleSplit.Async.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:13:45.844716+00:00
-- url     : https://prove2.me/submissions/a9873a91-71c5-469e-b063-32fcd5d2b51f

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → Set E) (hA : IsMaximalMonotone A)
    (J : ℝ → E → E) (hJ : ∀ γ : ℝ, 0 < γ → IsResolvent γ A (J γ))
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x))
    (γ : ℕ → ℝ) (hγpos : ∀ n, 0 < γ n) (hγ : Bornology.IsBounded (Set.range γ)) :
    Bornology.IsBounded (Set.range fun n => J (γ n) (x n)) := by
  -- the graph of a maximally monotone operator is nonempty
  have hne : ∃ z w, w ∈ A z := by
    by_contra hcon
    push Not at hcon
    let A' : E → Set E := fun u => {v | u = 0 ∧ v = 0}
    have hmon : IsMonotoneOp A' := by
      intro u u' v v' hv hv'
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨rfl, rfl⟩ := hv'
      simp
    have hsub : ∀ u, A u ⊆ A' u := fun u v hv => absurd hv (hcon u v)
    have heq := hA.2 A' hmon hsub
    have h0 : (0 : E) ∈ A' 0 := ⟨rfl, rfl⟩
    rw [heq] at h0
    exact hcon 0 0 h0
  obtain ⟨z, w, hw⟩ := hne
  rw [isBounded_iff_forall_norm_le] at hx hγ ⊢
  obtain ⟨Cx, hCx⟩ := hx
  obtain ⟨Cg, hCg⟩ := hγ
  refine ⟨Cx + ‖z‖ + Cg * ‖w‖ + ‖z‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hxn : ‖x n‖ ≤ Cx := hCx _ ⟨n, rfl⟩
  have hgn : ‖γ n‖ ≤ Cg := hCg _ ⟨n, rfl⟩
  have hg0 := hγpos n
  set p := J (γ n) (x n)
  have hres := hJ (γ n) hg0 (x n)
  have hmon := hA.1 p z _ w hres hw
  -- ⟪p - z, (x - p) - γ w⟫ ≥ 0
  have key : 0 ≤ ⟪p - z, (x n - p) - γ n • w⟫_ℝ := by
    have e : (x n - p) - γ n • w = γ n • ((γ n)⁻¹ • (x n - p) - w) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hg0.ne', one_smul]
    rw [e, real_inner_smul_right]
    exact mul_nonneg hg0.le hmon
  have e2 : (x n - p) - γ n • w = (x n - z - γ n • w) - (p - z) := by abel
  rw [e2, inner_sub_right, real_inner_self_eq_norm_sq] at key
  have cs := real_inner_le_norm (p - z) (x n - z - γ n • w)
  have hb : ‖x n - z - γ n • w‖ ≤ Cx + ‖z‖ + Cg * ‖w‖ := by
    calc ‖x n - z - γ n • w‖ ≤ ‖x n - z‖ + ‖γ n • w‖ := norm_sub_le _ _
      _ ≤ (‖x n‖ + ‖z‖) + ‖γ n‖ * ‖w‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact (norm_smul _ _).le
      _ ≤ Cx + ‖z‖ + Cg * ‖w‖ := by gcongr
  have hpz : ‖p - z‖ ≤ ‖x n - z - γ n • w‖ := by
    have h0 := norm_nonneg (p - z)
    by_cases hz : ‖p - z‖ = 0
    · rw [hz]; exact norm_nonneg _
    · have hpos : 0 < ‖p - z‖ := lt_of_le_of_ne h0 (Ne.symm hz)
      nlinarith
  calc ‖p‖ = ‖(p - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ Cx + ‖z‖ + Cg * ‖w‖ + ‖z‖ := by linarith
