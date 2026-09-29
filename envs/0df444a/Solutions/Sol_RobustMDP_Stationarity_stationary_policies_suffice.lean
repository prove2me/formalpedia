-- Prove2me | solution 1 for RobustMDP.Stationarity.stationary_policies_suffice
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T13:19:20.297263+00:00
-- url     : https://prove2.me/submissions/8f08c4e4-3475-401c-a724-3daa024d3a12

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

set_option autoImplicit false

/-- Weighted-sum comparison under a probability vector. -/
theorem rst91_wsum {n : ℕ} (μ f g : Fin n → ℝ) (e : ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (hμ1 : ∑ i, μ i = 1) (h : ∀ i, f i ≤ g i + e) :
    ∑ i, μ i * f i ≤ ∑ i, μ i * g i + e := by
  calc ∑ i, μ i * f i ≤ ∑ i, μ i * (g i + e) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hμ0 i)
    _ = ∑ i, μ i * g i + (∑ i, μ i) * e := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, μ i * g i + e := by rw [hμ1, one_mul]

theorem rst91_wsum_ge {n : ℕ} (μ f g : Fin n → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (h : ∀ i, f i ≤ g i) : ∑ i, μ i * f i ≤ ∑ i, μ i * g i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hμ0 i)

theorem rst91_lin {n : ℕ} (μ c D : Fin n → ℝ) (ν : ℝ) :
    ∑ i, μ i * (c i + ν * D i) = ∑ i, μ i * c i + ν * ∑ i, μ i * D i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem rst91_le_norm {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : |v j| ≤ ‖v‖ := by
  have := norm_le_pi_norm v j
  rwa [Real.norm_eq_abs] at this

theorem rst91_Ebd {n : ℕ} (μ v : Fin n → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) :
    |∑ i, μ i * v i| ≤ ‖v‖ := by
  rw [abs_le]
  constructor
  · have h := rst91_wsum μ (fun _ => -‖v‖) v 0 hμ0 hμ1 (fun i => by
      have := rst91_le_norm v i; rw [abs_le] at this; linarith)
    have h2 : ∑ i, μ i * (-‖v‖) = -‖v‖ := by rw [← Finset.sum_mul, hμ1, one_mul]
    beta_reduce at h
    linarith
  · have h := rst91_wsum μ v (fun _ => 0) ‖v‖ hμ0 hμ1 (fun i => by
      have := rst91_le_norm v i; rw [abs_le] at this; linarith)
    simpa using h

theorem rst91_lim {x y B ν : ℝ} (_h0 : 0 ≤ ν) (h1 : ν < 1) (h : ∀ N : ℕ, x ≤ y + ν ^ N * B) :
    x ≤ y := by
  by_contra hxy
  push Not at hxy
  have hB : 0 < B := by have := h 0; simp at this; linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.2 hxy) hB) h1
  have h2 := h N
  have h3 : ν ^ N * B < x - y := by rwa [lt_div_iff₀ hB] at hN
  linarith

open RobustMDP.Stationarity in
theorem rst91_sd_succ {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n) (π : Policy n A)
    (τ : M.NaturePolicy) (t : ℕ) (j : Fin n) :
    M.stateDist i₀ π τ (t + 1) j = ∑ i, M.stateDist i₀ π τ t i * (τ t).1 (π t i) i j := rfl

open RobustMDP.Stationarity in
theorem rst91_simplex {n : ℕ} {A : Type} (M : Model n A) (P : M.Choice) (a : A) (i : Fin n) :
    (∀ j, 0 ≤ P.1 a i j) ∧ ∑ j, P.1 a i j = 1 :=
  M.rows_subset_simplex a i (P.2 a i)

open RobustMDP.Stationarity in
theorem rst91_sd_prob {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n) (π : Policy n A)
    (τ : M.NaturePolicy) (t : ℕ) :
    (∀ j, 0 ≤ M.stateDist i₀ π τ t j) ∧ ∑ j, M.stateDist i₀ π τ t j = 1 := by
  induction t with
  | zero =>
    refine ⟨fun j => ?_, ?_⟩
    · show 0 ≤ (if j = i₀ then (1:ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ j, (if j = i₀ then (1:ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun j => ?_, ?_⟩
    · rw [rst91_sd_succ]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (ih.1 i) ((rst91_simplex M (τ t) (π t i) i).1 j)
    · have hs : ∀ a i, ∑ j, (τ t).1 a i j = 1 := fun a i => (rst91_simplex M (τ t) a i).2
      simp only [rst91_sd_succ]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hs, mul_one]
      exact ih.2

open RobustMDP.Stationarity in
theorem rst91_E_succ {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n) (π : Policy n A)
    (τ : M.NaturePolicy) (t : ℕ) (v : Fin n → ℝ) :
    ∑ j, M.stateDist i₀ π τ (t + 1) j * v j =
      ∑ i, M.stateDist i₀ π τ t i * ∑ j, (τ t).1 (π t i) i j * v j := by
  simp only [rst91_sd_succ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

open RobustMDP.Stationarity in
theorem rst91_E0 {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n) (π : Policy n A)
    (τ : M.NaturePolicy) (v : Fin n → ℝ) :
    ∑ j, M.stateDist i₀ π τ 0 j * v j = v i₀ := by
  show ∑ j, (if j = i₀ then (1:ℝ) else 0) * v j = v i₀
  simp

open RobustMDP.Stationarity in
theorem rst91_cost_le {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (i : Fin n) (a : A) :
    M.cost i a ≤ M.cmax := by
  unfold Model.cmax
  exact le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) a)

open RobustMDP.Stationarity in
theorem rst91_stage_bd {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (t : ℕ) :
    0 ≤ M.stageCost ν i₀ π τ t ∧ M.stageCost ν i₀ π τ t ≤ ν ^ t * M.cmax := by
  obtain ⟨h0, h1⟩ := rst91_sd_prob M i₀ π τ t
  unfold Model.stageCost
  constructor
  · exact mul_nonneg (pow_nonneg hν0 t)
      (Finset.sum_nonneg fun i _ => mul_nonneg (h0 i) (M.cost_nonneg _ _))
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hν0 t)
    have := rst91_wsum _ (fun i => M.cost i (π t i)) (fun _ => 0) M.cmax h0 h1
      (fun i => by simpa using rst91_cost_le M i (π t i))
    simpa using this

open RobustMDP.Stationarity in
theorem rst91_summable {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) :
    Summable (fun t => M.stageCost ν i₀ π τ t) :=
  Summable.of_nonneg_of_le (fun t => (rst91_stage_bd M ν hν0 i₀ π τ t).1)
    (fun t => (rst91_stage_bd M ν hν0 i₀ π τ t).2)
    ((summable_geometric_of_lt_one hν0 hν1).mul_right M.cmax)

open RobustMDP.Stationarity in
theorem rst91_fin_le_inf {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.finiteCost ν i₀ N π τ ≤ M.infCost ν i₀ π τ :=
  Summable.sum_le_tsum (Finset.range N) (fun t _ => (rst91_stage_bd M ν hν0 i₀ π τ t).1)
    (rst91_summable M ν hν0 hν1 i₀ π τ)

open RobustMDP.Stationarity in
theorem rst91_fin_nonneg {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    0 ≤ M.finiteCost ν i₀ N π τ :=
  Finset.sum_nonneg fun t _ => (rst91_stage_bd M ν hν0 i₀ π τ t).1

open RobustMDP.Stationarity in
theorem rst91_inf_nonneg {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) :
    0 ≤ M.infCost ν i₀ π τ :=
  tsum_nonneg fun t => (rst91_stage_bd M ν hν0 i₀ π τ t).1

open RobustMDP.Stationarity in
theorem rst91_inf_le {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.infCost ν i₀ π τ ≤ M.finiteCost ν i₀ N π τ + ν ^ N * M.cmax / (1 - ν) := by
  have hs := rst91_summable M ν hν0 hν1 i₀ π τ
  have htail : ∑' t, M.stageCost ν i₀ π τ (t + N) ≤ ν ^ N * M.cmax / (1 - ν) := by
    have hg : Summable (fun t : ℕ => ν ^ t * (ν ^ N * M.cmax)) :=
      (summable_geometric_of_lt_one hν0 hν1).mul_right _
    calc ∑' t, M.stageCost ν i₀ π τ (t + N) ≤ ∑' t : ℕ, ν ^ t * (ν ^ N * M.cmax) :=
          Summable.tsum_le_tsum (fun t => by
            have := (rst91_stage_bd M ν hν0 i₀ π τ (t + N)).2
            rw [pow_add] at this
            linarith) ((summable_nat_add_iff N).2 hs) hg
      _ = ν ^ N * M.cmax / (1 - ν) := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one hν0 hν1, div_eq_mul_inv]
          ring
  unfold Model.infCost Model.finiteCost
  rw [← hs.sum_add_tsum_nat_add N]
  linarith

open RobustMDP.Stationarity in
theorem rst91_inf_bd {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) :
    M.infCost ν i₀ π τ ≤ M.cmax / (1 - ν) := by
  have := rst91_inf_le M ν hν0 hν1 i₀ π τ 0
  simpa [Model.finiteCost] using this

open RobustMDP.Stationarity in
/-- The support function of the row set `𝒫_i^a` evaluated at `v`. -/
noncomputable def rst91Sig {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (v : Fin n → ℝ) : ℝ :=
  ⨆ p : M.rows a i, ∑ j, (p : Fin n → ℝ) j * v j

open RobustMDP.Stationarity in
theorem rst91_dot_le_norm {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (p : Fin n → ℝ) (hp : p ∈ M.rows a i) (v : Fin n → ℝ) : ∑ j, p j * v j ≤ ‖v‖ := by
  have hs := M.rows_subset_simplex a i hp
  have := rst91_wsum p v (fun _ => 0) ‖v‖ hs.1 hs.2 (fun j => by
    have := rst91_le_norm v j; rw [abs_le] at this; linarith)
  simpa using this

open RobustMDP.Stationarity in
theorem rst91_sig_bdd {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (v : Fin n → ℝ) :
    BddAbove (Set.range fun p : M.rows a i => ∑ j, (p : Fin n → ℝ) j * v j) :=
  ⟨‖v‖, by rintro _ ⟨p, rfl⟩; exact rst91_dot_le_norm M a i p p.2 v⟩

open RobustMDP.Stationarity in
theorem rst91_sig_ge {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (p : Fin n → ℝ) (hp : p ∈ M.rows a i) (v : Fin n → ℝ) :
    ∑ j, p j * v j ≤ rst91Sig M a i v :=
  le_ciSup (rst91_sig_bdd M a i v) ⟨p, hp⟩

open RobustMDP.Stationarity in
theorem rst91_sig_approx {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (v : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p ∈ M.rows a i, rst91Sig M a i v - δ < ∑ j, p j * v j := by
  have : Nonempty (M.rows a i) := (M.rows_nonempty a i).to_subtype
  have h : rst91Sig M a i v - δ < ⨆ p : M.rows a i, ∑ j, (p : Fin n → ℝ) j * v j := by
    unfold rst91Sig
    linarith
  obtain ⟨⟨p, hp⟩, hp'⟩ := exists_lt_of_lt_ciSup h
  exact ⟨p, hp, hp'⟩

open RobustMDP.Stationarity in
theorem rst91_sig_mono {n : ℕ} {A : Type} (M : Model n A) (a : A) (i : Fin n)
    (v w : Fin n → ℝ) (d : ℝ) (h : ∀ j, v j ≤ w j + d) :
    rst91Sig M a i v ≤ rst91Sig M a i w + d := by
  have : Nonempty (M.rows a i) := (M.rows_nonempty a i).to_subtype
  refine ciSup_le fun p => ?_
  have hs := M.rows_subset_simplex a i p.2
  have h1 := rst91_wsum p.1 v w d hs.1 hs.2 h
  have h2 := rst91_sig_ge M a i p.1 p.2 w
  linarith

open RobustMDP.Stationarity in
theorem rst91_T_mono {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (v w : Fin n → ℝ) (d : ℝ) (h : ∀ j, v j ≤ w j + d) (i : Fin n) :
    ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v) ≤
      (⨅ a : A, (M.cost i a + ν * rst91Sig M a i w)) + ν * d := by
  have key : ∀ a : A, (⨅ a : A, (M.cost i a + ν * rst91Sig M a i v)) - ν * d ≤
      M.cost i a + ν * rst91Sig M a i w := by
    intro a
    have h1 : (⨅ a : A, (M.cost i a + ν * rst91Sig M a i v)) ≤
        M.cost i a + ν * rst91Sig M a i v :=
      ciInf_le (Finite.bddBelow_range _) a
    have h2 := rst91_sig_mono M a i v w d h
    have h3 := mul_le_mul_of_nonneg_left h2 hν0
    linarith
  have := le_ciInf key
  linarith

open RobustMDP.Stationarity in
/-- The robust Bellman operator. -/
noncomputable def rst91T {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v)

open RobustMDP.Stationarity in
theorem rst91_fix {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) :
    ∃ v : Fin n → ℝ, ∀ i, ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v) = v i := by
  have hc : ContractingWith (Real.toNNReal ν) (rst91T M ν) := by
    refine ⟨Real.toNNReal_lt_one.2 hν1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [Real.coe_toNNReal _ hν0]
    refine (dist_pi_le_iff (mul_nonneg hν0 dist_nonneg)).2 fun i => ?_
    have hvw : ∀ j, v j ≤ w j + dist v w := fun j => by
      have := dist_le_pi_dist v w j
      rw [Real.dist_eq, abs_le] at this
      linarith
    have hwv : ∀ j, w j ≤ v j + dist v w := fun j => by
      have := dist_le_pi_dist v w j
      rw [Real.dist_eq, abs_le] at this
      linarith
    have h1 := rst91_T_mono M ν hν0 v w _ hvw i
    have h2 := rst91_T_mono M ν hν0 w v _ hwv i
    rw [Real.dist_eq, abs_le]
    simp only [rst91T]
    constructor <;> linarith
  exact ⟨ContractingWith.fixedPoint _ hc, fun i =>
    congrFun (ContractingWith.fixedPoint_isFixedPt hc) i⟩

open RobustMDP.Stationarity in
theorem rst91_tel_lo {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) (v : Fin n → ℝ) (e : ℝ)
    (h : ∀ t i, v i ≤ M.cost i (π t i) + ν * ∑ j, (τ t).1 (π t i) i j * v j + e) (N : ℕ) :
    v i₀ ≤ M.finiteCost ν i₀ N π τ + ν ^ N * ∑ j, M.stateDist i₀ π τ N j * v j +
      e * ∑ t ∈ Finset.range N, ν ^ t := by
  induction N with
  | zero =>
    rw [rst91_E0]
    simp [Model.finiteCost]
  | succ N ih =>
    obtain ⟨hμ0, hμ1⟩ := rst91_sd_prob M i₀ π τ N
    have hstep := rst91_wsum (M.stateDist i₀ π τ N) v
      (fun i => M.cost i (π N i) + ν * ∑ j, (τ N).1 (π N i) i j * v j) e hμ0 hμ1 (h N)
    have hlin := rst91_lin (M.stateDist i₀ π τ N) (fun i => M.cost i (π N i))
      (fun i => ∑ j, (τ N).1 (π N i) i j * v j) ν
    beta_reduce at hstep hlin
    have hE := rst91_E_succ M i₀ π τ N v
    have hC : M.finiteCost ν i₀ (N + 1) π τ = M.finiteCost ν i₀ N π τ +
        ν ^ N * ∑ i, M.stateDist i₀ π τ N i * M.cost i (π N i) := by
      unfold Model.finiteCost
      rw [Finset.sum_range_succ]
      rfl
    have hS : ∑ t ∈ Finset.range (N + 1), ν ^ t = ∑ t ∈ Finset.range N, ν ^ t + ν ^ N :=
      Finset.sum_range_succ _ _
    have hstep2 : ∑ j, M.stateDist i₀ π τ N j * v j ≤
        ∑ i, M.stateDist i₀ π τ N i * M.cost i (π N i) +
          ν * ∑ j, M.stateDist i₀ π τ (N + 1) j * v j + e := by
      rw [hE]; linarith
    have hmul := mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hν0 N)
    rw [hC, hS, pow_succ]
    linarith

open RobustMDP.Stationarity in
theorem rst91_tel_up {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (hν0 : 0 ≤ ν) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) (v : Fin n → ℝ)
    (h : ∀ t i, M.cost i (π t i) + ν * ∑ j, (τ t).1 (π t i) i j * v j ≤ v i) (N : ℕ) :
    M.finiteCost ν i₀ N π τ + ν ^ N * ∑ j, M.stateDist i₀ π τ N j * v j ≤ v i₀ := by
  induction N with
  | zero =>
    rw [rst91_E0]
    simp [Model.finiteCost]
  | succ N ih =>
    obtain ⟨hμ0, _⟩ := rst91_sd_prob M i₀ π τ N
    have hstep := rst91_wsum_ge (M.stateDist i₀ π τ N)
      (fun i => M.cost i (π N i) + ν * ∑ j, (τ N).1 (π N i) i j * v j) v hμ0 (h N)
    have hlin := rst91_lin (M.stateDist i₀ π τ N) (fun i => M.cost i (π N i))
      (fun i => ∑ j, (τ N).1 (π N i) i j * v j) ν
    beta_reduce at hstep hlin
    have hE := rst91_E_succ M i₀ π τ N v
    have hC : M.finiteCost ν i₀ (N + 1) π τ = M.finiteCost ν i₀ N π τ +
        ν ^ N * ∑ i, M.stateDist i₀ π τ N i * M.cost i (π N i) := by
      unfold Model.finiteCost
      rw [Finset.sum_range_succ]
      rfl
    have hstep2 : ∑ i, M.stateDist i₀ π τ N i * M.cost i (π N i) +
          ν * ∑ j, M.stateDist i₀ π τ (N + 1) j * v j ≤
        ∑ j, M.stateDist i₀ π τ N j * v j := by
      rw [hE]; linarith
    have hmul := mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hν0 N)
    rw [hC, pow_succ]
    linarith

open RobustMDP.Stationarity in
theorem rst91_L {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (i₀ : Fin n) (v : Fin n → ℝ)
    (hv : ∀ i, ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v) = v i)
    (π : Policy n A) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : M.Choice, v i₀ - ε ≤ M.infCost ν i₀ π (fun _ => P) := by
  have h1ν : 0 < 1 - ν := by linarith
  have hδ0 : 0 < ε * (1 - ν) := mul_pos hε h1ν
  have hch : ∀ a i, ∃ p ∈ M.rows a i, rst91Sig M a i v - ε * (1 - ν) < ∑ j, p j * v j :=
    fun a i => rst91_sig_approx M a i v _ hδ0
  choose p hp hpv using hch
  refine ⟨⟨p, hp⟩, ?_⟩
  have h : ∀ t i, v i ≤ M.cost i (π t i) +
      ν * ∑ j, ((fun _ : ℕ => (⟨p, hp⟩ : M.Choice)) t).1 (π t i) i j * v j +
        ν * (ε * (1 - ν)) := by
    intro t i
    have h1 : v i ≤ M.cost i (π t i) + ν * rst91Sig M (π t i) i v := by
      rw [← hv i]
      exact ciInf_le (Finite.bddBelow_range _) (π t i)
    have h2 := hpv (π t i) i
    have h3 := mul_le_mul_of_nonneg_left h2.le hν0
    show v i ≤ M.cost i (π t i) + ν * ∑ j, p (π t i) i j * v j + ν * (ε * (1 - ν))
    linarith
  have htel := rst91_tel_lo M ν hν0 i₀ π (fun _ => ⟨p, hp⟩) v (ν * (ε * (1 - ν))) h
  have hS : ∀ N, ∑ t ∈ Finset.range N, ν ^ t ≤ (1 - ν)⁻¹ := fun N => by
    rw [← tsum_geometric_of_lt_one hν0 hν1]
    exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hν0 i)
      (summable_geometric_of_lt_one hν0 hν1)
  refine rst91_lim hν0 hν1 (B := ‖v‖) fun N => ?_
  have a1 := htel N
  have a2 := rst91_fin_le_inf M ν hν0 hν1 i₀ π (fun _ => ⟨p, hp⟩) N
  obtain ⟨hμ0, hμ1⟩ := rst91_sd_prob M i₀ π (fun _ => ⟨p, hp⟩) N
  have a3 := (abs_le.1 (rst91_Ebd _ v hμ0 hμ1)).2
  have a4 := mul_le_mul_of_nonneg_left a3 (pow_nonneg hν0 N)
  have a5 := mul_le_mul_of_nonneg_left (hS N) (mul_nonneg hν0 hδ0.le)
  have a6 : ν * (ε * (1 - ν)) * (1 - ν)⁻¹ = ν * ε := by
    field_simp
  have a7 : ν * ε ≤ ε := by nlinarith
  linarith

open RobustMDP.Stationarity in
theorem rst91_U {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (i₀ : Fin n) (v : Fin n → ℝ)
    (hv : ∀ i, ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v) = v i) :
    ∃ a : Fin n → A, ∀ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => a) τ ≤ v i₀ := by
  have hex : ∀ i, ∃ a : A, M.cost i a + ν * rst91Sig M a i v =
      ⨅ a : A, (M.cost i a + ν * rst91Sig M a i v) :=
    fun i => exists_eq_ciInf_of_finite
  choose a ha using hex
  refine ⟨a, fun τ => ?_⟩
  have h : ∀ t i, M.cost i ((fun _ : ℕ => a) t i) +
      ν * ∑ j, (τ t).1 ((fun _ : ℕ => a) t i) i j * v j ≤ v i := by
    intro t i
    show M.cost i (a i) + ν * ∑ j, (τ t).1 (a i) i j * v j ≤ v i
    have h1 := rst91_sig_ge M (a i) i ((τ t).1 (a i) i) ((τ t).2 (a i) i) v
    have h2 := mul_le_mul_of_nonneg_left h1 hν0
    have h3 := (ha i).trans (hv i)
    linarith
  have htel := rst91_tel_up M ν hν0 i₀ (fun _ => a) τ v h
  refine rst91_lim hν0 hν1 (B := ‖v‖ + M.cmax / (1 - ν)) fun N => ?_
  have a1 := htel N
  have a2 := rst91_inf_le M ν hν0 hν1 i₀ (fun _ => a) τ N
  obtain ⟨hμ0, hμ1⟩ := rst91_sd_prob M i₀ (fun _ => a) τ N
  have a3 := (abs_le.1 (rst91_Ebd _ v hμ0 hμ1)).1
  have a5 := mul_le_mul_of_nonneg_left a3 (pow_nonneg hν0 N)
  have a6 : ν ^ N * M.cmax / (1 - ν) = ν ^ N * (M.cmax / (1 - ν)) := by ring
  linarith

open RobustMDP.Stationarity in
theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    (M.phiInf_PT ν i₀ = M.phiInf_PsTs ν i₀ ∧
      M.phiInf_PsTs ν i₀ = M.phiInf_PsT ν i₀ ∧
      M.phiInf_PsT ν i₀ = M.phiInf_PTs ν i₀) ∧
    ∀ N : ℕ, 0 ≤ M.phiN_PT ν i₀ N - M.phiN_PTs ν i₀ N ∧
      M.phiN_PT ν i₀ N - M.phiN_PTs ν i₀ N ≤ ν ^ N * M.cmax / (1 - ν) := by
  have hν0 : 0 ≤ ν := hν₀.le
  have hCh : Nonempty M.Choice :=
    ⟨⟨fun a i => (M.rows_nonempty a i).some, fun a i => (M.rows_nonempty a i).some_mem⟩⟩
  obtain ⟨v, hv⟩ := rst91_fix M ν hν0 hν₁
  obtain ⟨a, ha⟩ := rst91_U M ν hν0 hν₁ i₀ v hv
  have bT : ∀ π : Policy n A,
      BddAbove (Set.range fun τ : M.NaturePolicy => M.infCost ν i₀ π τ) :=
    fun π => ⟨M.cmax / (1 - ν), by rintro _ ⟨τ, rfl⟩; exact rst91_inf_bd M ν hν0 hν₁ i₀ π τ⟩
  have bTs : ∀ π : Policy n A,
      BddAbove (Set.range fun P : M.Choice => M.infCost ν i₀ π (fun _ => P)) :=
    fun π => ⟨M.cmax / (1 - ν), by rintro _ ⟨P, rfl⟩; exact rst91_inf_bd M ν hν0 hν₁ i₀ π _⟩
  have hLs : ∀ π : Policy n A, v i₀ ≤ ⨆ P : M.Choice, M.infCost ν i₀ π (fun _ => P) := by
    intro π
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, hP⟩ := rst91_L M ν hν0 hν₁ i₀ v hv π ε hε
    have : M.infCost ν i₀ π (fun _ => P) ≤ ⨆ P : M.Choice, M.infCost ν i₀ π (fun _ => P) :=
      le_ciSup (bTs π) P
    linarith
  have hL : ∀ π : Policy n A, v i₀ ≤ ⨆ τ : M.NaturePolicy, M.infCost ν i₀ π τ := fun π =>
    (hLs π).trans (ciSup_le fun P => le_ciSup (bT π) (fun _ => P))
  have lb1 : BddBelow (Set.range fun π : Policy n A =>
      ⨆ τ : M.NaturePolicy, M.infCost ν i₀ π τ) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun τ => rst91_inf_nonneg M ν hν0 i₀ π τ⟩
  have lb2 : BddBelow (Set.range fun π : Fin n → A =>
      ⨆ P : M.Choice, M.infCost ν i₀ (fun _ => π) (fun _ => P)) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun P => rst91_inf_nonneg M ν hν0 i₀ _ _⟩
  have lb3 : BddBelow (Set.range fun π : Fin n → A =>
      ⨆ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => π) τ) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun τ => rst91_inf_nonneg M ν hν0 i₀ _ τ⟩
  have lb4 : BddBelow (Set.range fun π : Policy n A =>
      ⨆ P : M.Choice, M.infCost ν i₀ π (fun _ => P)) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun P => rst91_inf_nonneg M ν hν0 i₀ π _⟩
  have e1 : M.phiInf_PT ν i₀ = v i₀ := by
    unfold Model.phiInf_PT
    apply le_antisymm
    · exact (ciInf_le lb1 (fun _ => a)).trans (ciSup_le fun τ => ha τ)
    · exact le_ciInf fun π => hL π
  have e2 : M.phiInf_PsTs ν i₀ = v i₀ := by
    unfold Model.phiInf_PsTs
    apply le_antisymm
    · exact (ciInf_le lb2 a).trans (ciSup_le fun P => ha _)
    · exact le_ciInf fun π => hLs (fun _ => π)
  have e3 : M.phiInf_PsT ν i₀ = v i₀ := by
    unfold Model.phiInf_PsT
    apply le_antisymm
    · exact (ciInf_le lb3 a).trans (ciSup_le fun τ => ha τ)
    · exact le_ciInf fun π => hL (fun _ => π)
  have e4 : M.phiInf_PTs ν i₀ = v i₀ := by
    unfold Model.phiInf_PTs
    apply le_antisymm
    · exact (ciInf_le lb4 (fun _ => a)).trans (ciSup_le fun P => ha _)
    · exact le_ciInf fun π => hLs π
  refine ⟨⟨by rw [e1, e2], by rw [e2, e3], by rw [e3, e4]⟩, fun N => ?_⟩
  have bNT : ∀ π : Policy n A,
      BddAbove (Set.range fun τ : M.NaturePolicy => M.finiteCost ν i₀ N π τ) :=
    fun π => ⟨M.cmax / (1 - ν), by
      rintro _ ⟨τ, rfl⟩
      exact (rst91_fin_le_inf M ν hν0 hν₁ i₀ π τ N).trans (rst91_inf_bd M ν hν0 hν₁ i₀ π τ)⟩
  have bNTs : ∀ π : Policy n A,
      BddAbove (Set.range fun P : M.Choice => M.finiteCost ν i₀ N π (fun _ => P)) :=
    fun π => ⟨M.cmax / (1 - ν), by
      rintro _ ⟨P, rfl⟩
      exact (rst91_fin_le_inf M ν hν0 hν₁ i₀ π _ N).trans (rst91_inf_bd M ν hν0 hν₁ i₀ π _)⟩
  have lbN1 : BddBelow (Set.range fun π : Policy n A =>
      ⨆ τ : M.NaturePolicy, M.finiteCost ν i₀ N π τ) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun τ => rst91_fin_nonneg M ν hν0 i₀ π τ N⟩
  have lbN2 : BddBelow (Set.range fun π : Policy n A =>
      ⨆ P : M.Choice, M.finiteCost ν i₀ N π (fun _ => P)) := ⟨0, by
    rintro _ ⟨π, rfl⟩
    exact Real.iSup_nonneg fun P => rst91_fin_nonneg M ν hν0 i₀ π _ N⟩
  have hA : M.phiN_PT ν i₀ N ≤ v i₀ := by
    unfold Model.phiN_PT
    exact (ciInf_le lbN1 (fun _ => a)).trans
      (ciSup_le fun τ => (rst91_fin_le_inf M ν hν0 hν₁ i₀ _ τ N).trans (ha τ))
  have hB : v i₀ - ν ^ N * M.cmax / (1 - ν) ≤ M.phiN_PTs ν i₀ N := by
    unfold Model.phiN_PTs
    refine le_ciInf fun π => ?_
    have h1 := hLs π
    have h2 : (⨆ P : M.Choice, M.infCost ν i₀ π (fun _ => P)) ≤
        (⨆ P : M.Choice, M.finiteCost ν i₀ N π (fun _ => P)) + ν ^ N * M.cmax / (1 - ν) :=
      ciSup_le fun P => (rst91_inf_le M ν hν0 hν₁ i₀ π _ N).trans (by
        have : M.finiteCost ν i₀ N π (fun _ => P) ≤
            ⨆ P : M.Choice, M.finiteCost ν i₀ N π (fun _ => P) := le_ciSup (bNTs π) P
        linarith)
    linarith
  have hC : M.phiN_PTs ν i₀ N ≤ M.phiN_PT ν i₀ N := by
    unfold Model.phiN_PTs Model.phiN_PT
    exact ciInf_mono lbN2 fun π => ciSup_le fun P => le_ciSup (bNT π) (fun _ => P)
  constructor
  · linarith
  · linarith
