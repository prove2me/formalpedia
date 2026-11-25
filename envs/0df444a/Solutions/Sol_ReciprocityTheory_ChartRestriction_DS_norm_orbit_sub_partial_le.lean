-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.norm_orbit_sub_partial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:11.346391+00:00
-- url     : https://prove2.me/submissions/b380019f-ee42-40fc-aeef-18acc3b57fa4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_iteratedDeriv_dual_orbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_contDiff_dual_orbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_orbit_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ) (N : ℕ) :
    ‖σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H)‖ ≤
      a (N + 1) * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  rcases eq_or_ne t₀ t with rfl | htt
  · have h0 : σ (NormedSpace.exp ((t₀ : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t₀ - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) = 0 := by
      rw [Finset.sum_range_succ']
      simp
    rw [h0, norm_zero]
    simp
  set R := σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) with hR
  obtain ⟨φ, hφ1, hφR⟩ := exists_dual_vector'' ℝ R
  set g : ℝ → ℝ := fun s => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) with hg
  have hgd := iteratedDeriv_dual_orbit hσ hD hX φ
  have hu : UniqueDiffOn ℝ (Set.uIcc t₀ t) := uniqueDiffOn_uIcc htt
  have hwithin : ∀ k : ℕ, iteratedDerivWithin k g (Set.uIcc t₀ t) t₀ =
      φ (σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ k) v : D) : H)) := by
    intro k
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_eq_iteratedFDeriv hu
        ((contDiff_dual_orbit hσ hD hX φ v k).contDiffAt) Set.left_mem_uIcc,
      ← iteratedDeriv_eq_iteratedFDeriv, hgd k v]
  have hf : ContDiffOn ℝ (N + 1) g (Set.uIcc t₀ t) := by
    have := contDiff_dual_orbit hσ hD hX φ v (N + 1)
    exact_mod_cast this.contDiffOn
  obtain ⟨x', -, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htt hf
  have hφsum : φ R = g t - taylorWithinEval g N (Set.uIcc t₀ t) t₀ t := by
    rw [taylor_within_apply, hR, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.coe_smul, φ.map_smul, hwithin k, smul_eq_mul, smul_eq_mul, div_eq_inv_mul]
  have hD1 : |iteratedDeriv (N + 1) g x'| ≤ a (N + 1) := by
    rw [hgd (N + 1) v]
    calc |φ (σ (NormedSpace.exp ((x' : ℂ) • X)) ((((actM E X) ^ (N + 1)) v : D) : H))|
        ≤ ‖φ‖ * ‖σ (NormedSpace.exp ((x' : ℂ) • X)) ((((actM E X) ^ (N + 1)) v : D) : H)‖ :=
          φ.le_opNorm _
      _ ≤ 1 * ‖((((actM E X) ^ (N + 1)) v : D) : H)‖ := by
          rw [norm_orbit_apply hσ hX]
          exact mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
      _ ≤ a (N + 1) := by rw [one_mul]; exact ha _
  calc ‖R‖ = φ R := hφR.symm
    _ = iteratedDeriv (N + 1) g x' * (t - t₀) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
        rw [hφsum, heq]
    _ ≤ |iteratedDeriv (N + 1) g x' * (t - t₀) ^ (N + 1) / ((N + 1).factorial : ℝ)| :=
        le_abs_self _
    _ = |iteratedDeriv (N + 1) g x'| * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
        rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    _ ≤ a (N + 1) * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by gcongr
end ReciprocityTheory.ChartRestriction.DS
