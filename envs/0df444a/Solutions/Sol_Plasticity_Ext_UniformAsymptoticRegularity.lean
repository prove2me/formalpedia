-- Prove2me | solution 1 for Plasticity.Ext.UniformAsymptoticRegularity
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:05:46.522929+00:00
-- url     : https://prove2.me/submissions/ec6dfc46-989d-49fc-af10-a3ef264e7dc9

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
Uniform asymptotic regularity of averaged nonexpansive maps of a bounded convex set
(Edelstein–O'Brien 1978; quantitative form via the Goebel–Kirk inequality, 1983).
-/

namespace Sol_Plasticity_Ext_UniformAsymptoticRegularity

/-- Bernoulli-type bound: `(1 - α)^n (1 + n α) ≤ 1` for `0 ≤ α ≤ 1`. -/
lemma bernoulli_aux (α : ℝ) (hα1 : α ≤ 1) (n : ℕ) :
    (1 - α) ^ n * (1 + n * α) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ (1 - α) ^ n := pow_nonneg (by linarith) n
    have h2 : 0 ≤ (1 - α) ^ n * (((n : ℝ) + 1) * α ^ 2) := by positivity
    have heq : (1 - α) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℝ) * α) =
        (1 - α) ^ n * (1 + n * α) - (1 - α) ^ n * (((n : ℝ) + 1) * α ^ 2) := by
      push_cast; ring
    rw [heq]
    linarith

lemma norm_K_sub {E : Type*} [NormedAddCommGroup E] {C : Set E} {K : E → E} (hlip : LipschitzOnWith 1 K C) {a b : E}
    (ha : a ∈ C) (hb : b ∈ C) : ‖K a - K b‖ ≤ ‖a - b‖ := by
  have := hlip.dist_le_mul a ha b hb
  simpa [dist_eq_norm] using this

section Orbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {K : E → E} {α : ℝ} {x : ℕ → E}

lemma step_eq (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (k : ℕ) :
    x (k + 1) - x k = α • (K (x k) - x k) := by
  rw [hx k]; module

lemma norm_step (hα0 : 0 ≤ α) (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (k : ℕ) :
    ‖x (k + 1) - x k‖ = α * ‖K (x k) - x k‖ := by
  rw [step_eq hx k, norm_smul, Real.norm_of_nonneg hα0]

lemma d_succ_le (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hlip : LipschitzOnWith 1 K C)
    (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (hxC : ∀ k, x k ∈ C) (k : ℕ) :
    ‖K (x (k + 1)) - x (k + 1)‖ ≤ ‖K (x k) - x k‖ := by
  have hdecomp : K (x (k + 1)) - x (k + 1) =
      (K (x (k + 1)) - K (x k)) + (1 - α) • (K (x k) - x k) := by
    rw [hx k]; module
  rw [hdecomp]
  calc ‖(K (x (k + 1)) - K (x k)) + (1 - α) • (K (x k) - x k)‖
      ≤ ‖K (x (k + 1)) - K (x k)‖ + ‖(1 - α) • (K (x k) - x k)‖ := norm_add_le _ _
    _ ≤ ‖x (k + 1) - x k‖ + (1 - α) * ‖K (x k) - x k‖ := by
        refine add_le_add (norm_K_sub hlip (hxC _) (hxC _)) (le_of_eq ?_)
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    _ = ‖K (x k) - x k‖ := by rw [norm_step hα0 hx k]; ring

lemma d_antitone (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hlip : LipschitzOnWith 1 K C)
    (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (hxC : ∀ k, x k ∈ C) :
    Antitone (fun k => ‖K (x k) - x k‖) :=
  antitone_nat_of_succ_le (d_succ_le hα0 hα1 hlip hx hxC)

lemma norm_sub_le_mul (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hlip : LipschitzOnWith 1 K C)
    (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (hxC : ∀ k, x k ∈ C) (i m : ℕ) :
    ‖x (i + m) - x i‖ ≤ α * m * ‖K (x i) - x i‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hanti := d_antitone hα0 hα1 hlip hx hxC
    have hmono : ‖K (x (i + m)) - x (i + m)‖ ≤ ‖K (x i) - x i‖ :=
      hanti (Nat.le_add_right i m)
    calc ‖x (i + (m + 1)) - x i‖
        = ‖(x (i + m + 1) - x (i + m)) + (x (i + m) - x i)‖ := by
          rw [← add_assoc]; congr 1; abel
      _ ≤ ‖x (i + m + 1) - x (i + m)‖ + ‖x (i + m) - x i‖ := norm_add_le _ _
      _ ≤ α * ‖K (x i) - x i‖ + α * m * ‖K (x i) - x i‖ := by
          rw [norm_step hα0 hx (i + m)]
          exact add_le_add (mul_le_mul_of_nonneg_left hmono hα0) ih
      _ = α * ((m + 1 : ℕ) : ℝ) * ‖K (x i) - x i‖ := by push_cast; ring

/-- The Goebel–Kirk inequality, multiplied by `(1 - α)^n`. -/
lemma goebel_kirk (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hlip : LipschitzOnWith 1 K C)
    (hx : ∀ k, x (k + 1) = (1 - α) • x k + α • K (x k)) (hxC : ∀ k, x k ∈ C) (n : ℕ) :
    ∀ i : ℕ, (1 - α) ^ n * (1 + n * α) * ‖K (x i) - x i‖ ≤
      (1 - α) ^ n * ‖K (x (i + n)) - x i‖ +
        (‖K (x i) - x i‖ - ‖K (x (i + n)) - x (i + n)‖) := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    have hIH := ih (i + 1)
    rw [show i + 1 + n = i + (n + 1) by omega] at hIH
    have hβ : 0 ≤ 1 - α := by linarith
    have hkey : ‖K (x (i + (n + 1))) - x (i + 1)‖ ≤
        (1 - α) * ‖K (x (i + (n + 1))) - x i‖ +
          α * (α * ((n + 1 : ℕ) : ℝ) * ‖K (x i) - x i‖) := by
      have hdec : K (x (i + (n + 1))) - x (i + 1) =
          (1 - α) • (K (x (i + (n + 1))) - x i) + α • (K (x (i + (n + 1))) - K (x i)) := by
        rw [hx i]; module
      rw [hdec]
      calc ‖(1 - α) • (K (x (i + (n + 1))) - x i) + α • (K (x (i + (n + 1))) - K (x i))‖
          ≤ ‖(1 - α) • (K (x (i + (n + 1))) - x i)‖ +
              ‖α • (K (x (i + (n + 1))) - K (x i))‖ := norm_add_le _ _
        _ = (1 - α) * ‖K (x (i + (n + 1))) - x i‖ +
              α * ‖K (x (i + (n + 1))) - K (x i)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hβ, Real.norm_of_nonneg hα0]
        _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hα0)
          exact (norm_K_sub hlip (hxC _) (hxC _)).trans
            (norm_sub_le_mul hα0 hα1 hlip hx hxC i (n + 1))
    have hB := bernoulli_aux α hα1 n
    have hmono : ‖K (x (i + 1)) - x (i + 1)‖ ≤ ‖K (x i) - x i‖ :=
      d_succ_le hα0 hα1 hlip hx hxC i
    have hp : 0 ≤ (1 - α) ^ n := pow_nonneg hβ n
    have h1 := mul_le_mul_of_nonneg_left hkey hp
    have h2 : 0 ≤ (1 - (1 - α) ^ n * (1 + n * α)) *
        (‖K (x i) - x i‖ - ‖K (x (i + 1)) - x (i + 1)‖) :=
      mul_nonneg (by linarith) (by linarith)
    push_cast at hIH h1 ⊢
    linear_combination hIH + h1 + h2

end Orbit

end Sol_Plasticity_Ext_UniformAsymptoticRegularity

open Sol_Plasticity_Ext_UniformAsymptoticRegularity in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (hbdd : Bornology.IsBounded C)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ C,
      ‖(fun z => (1 - α) • z + α • K z)^[n + 1] x - (fun z => (1 - α) • z + α • K z)^[n] x‖ ≤ ε := by
  set P : E → E := fun z => (1 - α) • z + α • K z with hP
  have hPC : Set.MapsTo P C C := fun z hz =>
    hconv hz (hmaps hz) (by linarith) hα0.le (by ring)
  -- a diameter bound for `C`
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.mp hbdd
  set D : ℝ := max D₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ p ∈ C, ∀ q ∈ C, ‖p - q‖ ≤ D := fun p hp q hq => by
    rw [← dist_eq_norm]; exact (hD₀ hp hq).trans (le_max_left _ _)
  -- the block length `n` and the number of blocks `m`
  have hαε : 0 < α * ε := mul_pos hα0 hε
  obtain ⟨n, hn⟩ := exists_nat_ge ((2 * D + 1) / (α * ε))
  have hnαε : 2 * D + 1 ≤ n * α * ε := by
    rw [div_le_iff₀ hαε] at hn; linarith
  have hβ0 : 0 < (1 - α) ^ n := pow_pos (by linarith) n
  obtain ⟨m, hm⟩ := exists_nat_ge (1 / (1 - α) ^ n)
  have hmβ : 1 ≤ m * (1 - α) ^ n := by
    rw [div_le_iff₀ hβ0] at hm; linarith
  refine ⟨m * n, fun k hk x₀ hx₀ => ?_⟩
  -- the orbit of `x₀`
  set x : ℕ → E := fun j => P^[j] x₀ with hxdef
  have hx : ∀ j, x (j + 1) = (1 - α) • x j + α • K (x j) := fun j => by
    simp only [hxdef]; rw [Function.iterate_succ_apply']
  have hxC : ∀ j, x j ∈ C := fun j => hPC.iterate j hx₀
  show ‖x (k + 1) - x k‖ ≤ ε
  have hanti := d_antitone hα0.le hα1.le hlip hx hxC
  have hdnn : ∀ j, 0 ≤ ‖K (x j) - x j‖ := fun j => norm_nonneg _
  have hdD : ∀ j, ‖K (x j) - x j‖ ≤ D := fun j => hD _ (hmaps (hxC j)) _ (hxC j)
  -- it suffices to show that the displacement at time `m n` is at most `ε`
  suffices hfin : ‖K (x (m * n)) - x (m * n)‖ ≤ ε by
    rw [norm_step hα0.le hx k]
    have h1 : ‖K (x k) - x k‖ ≤ ‖K (x (m * n)) - x (m * n)‖ := hanti hk
    have h2 : α * ‖K (x k) - x k‖ ≤ ‖K (x k) - x k‖ := by
      have := hdnn k
      nlinarith
    linarith
  by_contra hcon'
  have hcon : ε < ‖K (x (m * n)) - x (m * n)‖ := lt_of_not_ge hcon'
  -- every block `[j n, (j+1) n]` with `j < m` has a large drop
  have hdrop : ∀ j < m, (1 - α) ^ n * (D + 1) ≤
      ‖K (x (j * n)) - x (j * n)‖ - ‖K (x ((j + 1) * n)) - x ((j + 1) * n)‖ := by
    intro j hj
    have hεj : ε ≤ ‖K (x (j * n)) - x (j * n)‖ :=
      hcon.le.trans (hanti (Nat.mul_le_mul_right n hj.le))
    have hGK := goebel_kirk hα0.le hα1.le hlip hx hxC n (j * n)
    rw [show j * n + n = (j + 1) * n by ring] at hGK
    have hA : ‖K (x ((j + 1) * n)) - x (j * n)‖ ≤ D := hD _ (hmaps (hxC _)) _ (hxC _)
    have h1 : (1 - α) ^ n * ‖K (x ((j + 1) * n)) - x (j * n)‖ ≤ (1 - α) ^ n * D :=
      mul_le_mul_of_nonneg_left hA hβ0.le
    have h2 : (1 - α) ^ n * (2 * D + 1) ≤
        (1 - α) ^ n * ((1 + n * α) * ‖K (x (j * n)) - x (j * n)‖) := by
      refine mul_le_mul_of_nonneg_left ?_ hβ0.le
      have : (n : ℝ) * α * ε ≤ (1 + n * α) * ‖K (x (j * n)) - x (j * n)‖ := by
        have hnα : 0 ≤ (n : ℝ) * α := by positivity
        nlinarith
      linarith
    linear_combination hGK + h1 + h2
  -- summing the drops
  have hsum : ∀ j ≤ m, j * ((1 - α) ^ n * (D + 1)) ≤
      ‖K (x 0) - x 0‖ - ‖K (x (j * n)) - x (j * n)‖ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := ih (by omega)
      have := hdrop j (by omega)
      push_cast
      linarith
  have hm' := hsum m le_rfl
  have hfinal : D + 1 ≤ m * ((1 - α) ^ n * (D + 1)) := by
    have : 0 ≤ (m * (1 - α) ^ n - 1) * (D + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  linarith [hdnn (m * n), hdD 0]
