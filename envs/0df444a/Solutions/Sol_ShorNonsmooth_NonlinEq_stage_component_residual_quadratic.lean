-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.stage_component_residual_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T17:47:24.435991+00:00
-- url     : https://prove2.me/submissions/a5b66d4d-f6c8-42bd-ac56-3e286cacd365

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_stage_component_base_bound
import Theorems.Thm_stage_component_increment_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_local_residual_linear_equivalence
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_uniform_lower_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_linear_bound_and_growth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq
theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n)))
    (k : Fin n) :
    ∃ ε > 0, ∃ C > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → |ψ k (x n)| ≤ C * ‖x 0‖ ^ 2 := by
  classical
  obtain ⟨ηa, hηapos, _a, _hapos, M, hMpos, hlocal⟩ :=
    local_residual_linear_equivalence ψ hψ h0 hind
  obtain ⟨ηb, hηbpos, b, hbpos, horth⟩ :=
    stage_orthDir_uniform_lower_bound ψ hψ hind
  obtain ⟨εlin, hεlinpos, c1, _hc1pos, _c2, _hc2pos, hlin⟩ :=
    stage_linear_bound_and_growth ψ hψ h0 δ L hδ hLip hind
  let S : ℝ := max c1 1
  let D : ℝ := min (min ηa ηb) δ
  let ε : ℝ := min εlin (D / (2 * S))
  let Base : ℝ := max (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) 1
  let Inc : ℝ := max (max L 0 * (M * S / b) * (M * S / b + 2 * S)) 1
  let C : ℝ := Base + (n : ℝ) * Inc + 1
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right c1 1)
  have hDpos : 0 < D := lt_min (lt_min hηapos hηbpos) hδ
  have hεpos : 0 < ε := lt_min hεlinpos (div_pos hDpos (mul_pos two_pos hSpos))
  have hBasepos : 0 < Base := lt_of_lt_of_le zero_lt_one (le_max_right _ 1)
  have hIncpos : 0 < Inc := lt_of_lt_of_le zero_lt_one (le_max_right _ 1)
  have hCpos : 0 < C := by
    dsimp [C]
    have hnI : 0 ≤ (n : ℝ) * Inc := mul_nonneg (Nat.cast_nonneg n) hIncpos.le
    linarith
  refine ⟨ε, hεpos, C, hCpos, ?_⟩
  intro x hx hx0
  let r : ℝ := ‖x 0‖
  have hnorm : ∀ t, t ≤ n → ‖x t‖ ≤ S * r := by
    intro t htn
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · have hS1 : 1 ≤ S := le_max_right c1 1
      dsimp [r]
      simpa using mul_le_mul_of_nonneg_right hS1 (norm_nonneg (x 0))
    · calc
        ‖x t‖ ≤ c1 * r := (hlin x hx (le_trans hx0 (min_le_left _ _))).1 t htpos htn
        _ ≤ S * r := mul_le_mul_of_nonneg_right (le_max_left c1 1) (norm_nonneg _)
  have hsmall : ∀ t, t ≤ n → ‖x t‖ < D := by
    intro t htn
    have hSR : S * r ≤ D / 2 := by
      calc
        S * r ≤ S * ε := mul_le_mul_of_nonneg_left hx0 hSpos.le
        _ ≤ S * (D / (2 * S)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hSpos.le
        _ = D / 2 := by field_simp [hSpos.ne']
    nlinarith [hnorm t htn, hDpos]
  have hball : ∀ t, t ≤ n → x t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ := by
    intro t htn
    simpa [Metric.mem_ball, dist_eq_norm] using
      lt_of_lt_of_le (hsmall t htn) (min_le_right _ _)
  have hlocalBall : ∀ t, t ≤ n → x t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ηa := by
    intro t htn
    simpa [Metric.mem_ball, dist_eq_norm] using
      lt_of_lt_of_le (hsmall t htn) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hdir : ∀ t : Fin n, b ≤ ‖orthDir ψ x t‖ := by
    intro t
    exact horth x t (by
      intro j
      exact lt_of_lt_of_le (hsmall j.val (by omega))
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  have horthEarlier {j : Fin n} (hkj : k.val < j.val) :
      inner ℝ (gradient (ψ k) (x k.val)) (orthDir ψ x j) = 0 := by
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ
      (Set.range fun l : Fin j.val =>
        gradient (ψ ⟨l.val, l.isLt.trans j.isLt⟩) (x l.val))
    have hmem : orthDir ψ x j ∈ Kᗮ := by
      simpa [K, orthDir] using
        (Submodule.starProjection_apply_mem (Kᗮ) (gradient (ψ j) (x j.val)))
    rw [Submodule.mem_orthogonal] at hmem
    apply hmem
    apply Submodule.subset_span
    refine ⟨⟨k.val, hkj⟩, ?_⟩
    simp
  have hpsiAt : ∀ t, t ≤ n → |ψ k (x t)| ≤ M * (S * r) := by
    intro t htn
    calc
      |ψ k (x t)| ≤ M * ‖x t‖ :=
        (hlocal (x t) (by simpa [Metric.mem_ball, dist_eq_norm] using hlocalBall t htn)).2 k
      _ ≤ M * (S * r) := mul_le_mul_of_nonneg_left (hnorm t htn) hMpos.le
  have hbase := stage_component_base_bound ψ hψ δ L hδ hLip x hx k M S b r
    hMpos.le hSpos.le hbpos (norm_nonneg _) (hpsiAt k.val (Nat.le_of_lt k.isLt))
    (hdir k) (hball k.val (Nat.le_of_lt k.isLt))
    (hball (k.val + 1) (Nat.succ_le_of_lt k.isLt))
  have hlater : ∀ t, k.val < t → t < n →
      |ψ k (x (t + 1)) - ψ k (x t)| ≤ Inc * r ^ 2 := by
    intro t hkt htn
    let j : Fin n := ⟨t, htn⟩
    have hψj : |ψ j (x j.val)| ≤ M * (S * r) := by
      calc
        |ψ j (x j.val)| ≤ M * ‖x j.val‖ :=
          (hlocal (x j.val) (by
            simpa [Metric.mem_ball, dist_eq_norm] using hlocalBall j.val (Nat.le_of_lt j.isLt))).2 j
        _ ≤ M * (S * r) := mul_le_mul_of_nonneg_left (hnorm j.val (Nat.le_of_lt j.isLt)) hMpos.le
    have hv := stage_component_increment_bound ψ hψ δ L hδ hLip x hx k j hkt
      M S b r hMpos.le hSpos.le hbpos (norm_nonneg _) hψj
      (hdir j) (hnorm k.val (Nat.le_of_lt k.isLt)) (hnorm t (Nat.le_of_lt htn))
      (hball k.val (Nat.le_of_lt k.isLt)) (hball t (Nat.le_of_lt htn))
      (hball (t + 1) (Nat.succ_le_of_lt htn)) (horthEarlier hkt)
    simpa [j, Inc] using hv
  have hres : ∀ t, k.val + 1 ≤ t → t ≤ n →
      |ψ k (x t)| ≤ (Base + (t : ℝ) * Inc) * r ^ 2 := by
    intro t ht0
    induction t, ht0 using Nat.le_induction with
    | base =>
        intro _
        calc
          |ψ k (x (k.val + 1))| ≤ Base * r ^ 2 := by simpa [Base] using hbase
          _ ≤ (Base + ((k.val + 1 : ℕ) : ℝ) * Inc) * r ^ 2 := by
            have hnonneg : 0 ≤ ((k.val + 1 : ℕ) : ℝ) * Inc := mul_nonneg (Nat.cast_nonneg _) hIncpos.le
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hnonneg) (sq_nonneg r)
    | succ t htk ih =>
        intro htn
        have hprev := ih (Nat.le_of_lt (Nat.lt_of_succ_le htn))
        have hinc := hlater t (Nat.lt_of_succ_le htk) (Nat.lt_of_succ_le htn)
        calc
          |ψ k (x (t + 1))| ≤ |ψ k (x t)| +
              |ψ k (x (t + 1)) - ψ k (x t)| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (abs_add_le (ψ k (x t)) (ψ k (x (t + 1)) - ψ k (x t)))
          _ ≤ (Base + (t : ℝ) * Inc) * r ^ 2 + Inc * r ^ 2 :=
            add_le_add hprev hinc
          _ ≤ (Base + (((t + 1 : ℕ) : ℝ)) * Inc) * r ^ 2 := by
            apply le_of_eq
            calc
              (Base + (t : ℝ) * Inc) * r ^ 2 + Inc * r ^ 2
                  = (Base + ((t : ℝ) + 1) * Inc) * r ^ 2 := by ring
              _ = (Base + (((t + 1 : ℕ) : ℝ)) * Inc) * r ^ 2 := by norm_num [Nat.cast_add, Nat.cast_one]
  have hresult := hres n (Nat.succ_le_of_lt k.isLt) le_rfl
  have hcoef : Base + (n : ℝ) * Inc ≤ C := by
    dsimp [C]
    linarith
  exact hresult.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg r))
