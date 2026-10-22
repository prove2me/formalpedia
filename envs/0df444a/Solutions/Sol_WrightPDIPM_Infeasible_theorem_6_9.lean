-- Prove2me | solution 1 for WrightPDIPM.Infeasible.theorem_6_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:33:58.316816+00:00
-- url     : https://prove2.me/submissions/d9c933d9-a99a-4b66-9f8b-44527a36b417

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF
open WrightPDIPM.Infeasible

open Filter


section g71w_lib
open Matrix
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}

theorem g71w_alpha_mem (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    α k ∈ Set.Icc (0:ℝ) 1 ∧
    (x (k+1), lam (k+1), s (k+1)) ∈ NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
    mu (x (k+1)) (s (k+1)) ≤ (1 - 0.01 * α k) * mu (x k) (s k) := by
  have h := (hrun.alpha_greatest k).1
  rw [hrun.update_x k, hrun.update_lam k, hrun.update_s k]
  exact h

theorem g71w_pos (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    (∀ i, 0 < x k i) ∧ (∀ i, 0 < s k i) := by
  cases k with
  | zero => exact hrun.start_pos
  | succ k =>
    obtain ⟨_, h, _⟩ := g71w_alpha_mem hrun k
    exact ⟨h.2.1, h.2.2.1⟩

theorem g71w_mu_succ_le (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    mu (x (k+1)) (s (k+1)) ≤ mu (x k) (s k) := by
  obtain ⟨⟨h0, _⟩, _, h⟩ := g71w_alpha_mem hrun k
  have hmu : 0 ≤ mu (x k) (s k) := by
    unfold mu; apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun i _ => (mul_pos ((g71w_pos hrun k).1 i) ((g71w_pos hrun k).2 i)).le)
  nlinarith

theorem g71w_mu_le0 (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    mu (x k) (s k) ≤ mu (x 0) (s 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (g71w_mu_succ_le hrun k).trans ih

theorem g71w_nu_mem (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    0 ≤ nu α k ∧ nu α k ≤ 1 := by
  unfold nu
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    obtain ⟨h0, h1⟩ := (g71w_alpha_mem hrun k).1
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · nlinarith [ih.1, ih.2]

theorem g71w_nu_succ (k : ℕ) : nu α (k+1) = nu α k * (1 - α k) := by
  unfold nu; rw [Finset.prod_range_succ]

theorem g71w_rb (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    rb A b (x k) = nu α k • rb A b (x 0) := by
  induction k with
  | zero => simp [nu]
  | succ k ih =>
    rw [g71w_nu_succ, hrun.update_x k]
    have h2 := (hrun.step k).2.1
    have : rb A b (x k + α k • dx k) = (1 - α k) • rb A b (x k) := by
      unfold rb at *
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2]
      ext i; simp; ring
    rw [this, ih, smul_smul, mul_comm]

theorem g71w_rc (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    rc A c (lam k) (s k) = nu α k • rc A c (lam 0) (s 0) := by
  induction k with
  | zero => simp [nu]
  | succ k ih =>
    rw [g71w_nu_succ, hrun.update_lam k, hrun.update_s k]
    have h1 := (hrun.step k).1
    have : rc A c (lam k + α k • dlam k) (s k + α k • ds k) = (1 - α k) • rc A c (lam k) (s k) := by
      have h1' : ∀ i, (Aᵀ *ᵥ dlam k) i + ds k i = -(rc A c (lam k) (s k)) i := fun i =>
        congrFun h1 i
      unfold rc at *
      ext i
      have := h1' i
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.neg_apply] at this ⊢
      linear_combination α k * this
    rw [this, ih, smul_smul, mul_comm]

/-- the key orthogonality: with `u = ν x0 + (1-ν) xb`, `v = ν s0 + (1-ν) sb`. -/
theorem g71w_orth (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ)
    (xb : Fin n → ℝ) (lb : Fin m → ℝ) (sb : Fin n → ℝ) (hxb : A *ᵥ xb = b)
    (hsb : Aᵀ *ᵥ lb + sb = c) :
    (nu α k • x 0 + (1 - nu α k) • xb - x k) ⬝ᵥ (nu α k • s 0 + (1 - nu α k) • sb - s k) = 0 := by
  set ν := nu α k
  have hA : A *ᵥ (ν • x 0 + (1 - ν) • xb - x k) = 0 := by
    have := g71w_rb hrun k
    unfold rb at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxb]
    ext i; have := congrFun this i; simp at this ⊢; linarith
  have hS : ν • s 0 + (1 - ν) • sb - s k = Aᵀ *ᵥ (lam k - (ν • lam 0 + (1 - ν) • lb)) := by
    have := g71w_rc hrun k
    unfold rc at this
    ext i
    have h1 := congrFun this i
    have h2 := congrFun hsb i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination -h1 + (1 - ν) * h2
  rw [hS, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hA, zero_dotProduct]

end g71w_lib

section g71w_bd
open Matrix
theorem g71w_bound_core {n : ℕ} (u v x s : Fin n → ℝ)
    (horth : (u - x) ⬝ᵥ (v - s) = 0) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, 0 ≤ s i) (j : Fin n) :
    v j * x j ≤ u ⬝ᵥ v + x ⬝ᵥ s ∧ u j * s j ≤ u ⬝ᵥ v + x ⬝ᵥ s := by
  have key : ∑ i, (u i * s i + v i * x i) = u ⬝ᵥ v + x ⬝ᵥ s := by
    have : ∑ i, (u i * s i + v i * x i) = ∑ i, (u i * v i + x i * s i) - (u - x) ⬝ᵥ (v - s) := by
      unfold dotProduct; rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); simp only [Pi.sub_apply]; ring
    rw [this, horth, sub_zero, Finset.sum_add_distrib]; rfl
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ u i * s i + v i * x i := fun i _ =>
    add_nonneg (mul_nonneg (hu i) (hs i)) (mul_nonneg (hv i) (hx i))
  have hj := Finset.single_le_sum hnn (Finset.mem_univ j)
  constructor
  · nlinarith [mul_nonneg (hu j) (hs j)]
  · nlinarith [mul_nonneg (hv j) (hx j)]

theorem g71w_bounded {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (hn : 0 < n)
    (hFo : (Fo A b c).Nonempty) :
    ∃ M : ℝ, ∀ k i, |x k i| ≤ M ∧ |s k i| ≤ M := by
  obtain ⟨⟨xb, lb, sb⟩, hxb, hsb, hxbp, hsbp⟩ := hFo
  simp only at hxb hsb hxbp hsbp
  have hx0 := hrun.start_pos.1
  have hs0 := hrun.start_pos.2
  set K : ℝ := (∑ i, (x 0 i + xb i) * (s 0 i + sb i)) + x 0 ⬝ᵥ s 0 with hK
  refine ⟨∑ j, (K / min (s 0 j) (sb j) + K / min (x 0 j) (xb j)), fun k i => ?_⟩
  set ν := nu α k
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun k
  have horth := g71w_orth hrun k xb lb sb hxb hsb
  have hxk := (g71w_pos hrun k).1
  have hsk := (g71w_pos hrun k).2
  set u := ν • x 0 + (1 - ν) • xb
  set v := ν • s 0 + (1 - ν) • sb
  have hu : ∀ i, min (x 0 i) (xb i) ≤ u i ∧ u i ≤ x 0 i + xb i := fun i => by
    simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i; have := hxbp i
    constructor
    · rcases min_cases (x 0 i) (xb i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    · nlinarith
  have hv : ∀ i, min (s 0 i) (sb i) ≤ v i ∧ v i ≤ s 0 i + sb i := fun i => by
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hs0 i; have := hsbp i
    constructor
    · rcases min_cases (s 0 i) (sb i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    · nlinarith
  have hcx : ∀ i, 0 < min (x 0 i) (xb i) := fun i => lt_min (hx0 i) (hxbp i)
  have hcs : ∀ i, 0 < min (s 0 i) (sb i) := fun i => lt_min (hs0 i) (hsbp i)
  have huv : u ⬝ᵥ v + x k ⬝ᵥ s k ≤ K := by
    have h1 : u ⬝ᵥ v ≤ ∑ i, (x 0 i + xb i) * (s 0 i + sb i) := by
      unfold dotProduct
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul (hu i).2 (hv i).2 ((hcs i).le.trans (hv i).1)
        (add_pos (hx0 i) (hxbp i)).le
    have h2 : x k ⬝ᵥ s k ≤ x 0 ⬝ᵥ s 0 := by
      have := g71w_mu_le0 hrun k
      unfold mu at this
      have hnr : (0:ℝ) < n := by exact_mod_cast hn
      exact (div_le_div_iff_of_pos_right hnr).mp this
    linarith
  have hb := fun j => g71w_bound_core u v (x k) (s k) horth
    (fun i => (hcx i).le.trans (hu i).1) (fun i => (hcs i).le.trans (hv i).1)
    (fun i => (hxk i).le) (fun i => (hsk i).le) j
  have hK0 : 0 ≤ K := by
    have := hb i; nlinarith [mul_pos ((hcs i).trans_le (hv i).1) (hxk i)]
  have hterm : ∀ j ∈ Finset.univ, 0 ≤ K / min (s 0 j) (sb j) + K / min (x 0 j) (xb j) :=
    fun j _ => add_nonneg (div_nonneg hK0 (hcs j).le) (div_nonneg hK0 (hcx j).le)
  have hsingle := Finset.single_le_sum hterm (Finset.mem_univ i)
  have hxi : x k i ≤ K / min (s 0 i) (sb i) := by
    rw [le_div_iff₀ (hcs i)]
    have := (hb i).1
    nlinarith [(hv i).1, hxk i]
  have hsi : s k i ≤ K / min (x 0 i) (xb i) := by
    rw [le_div_iff₀ (hcx i)]
    have := (hb i).2
    nlinarith [(hu i).1, hsk i]
  have d1 := div_nonneg hK0 (hcs i).le
  have d2 := div_nonneg hK0 (hcx i).le
  rw [abs_of_pos (hxk i), abs_of_pos (hsk i)]
  constructor <;> linarith
end g71w_bd

/-- Theorem 6.9 (p. 123): along Algorithm IPF with an infeasible start, if `F° ≠ ∅` then the
sequence `{(xᵏ, sᵏ)}` is bounded and therefore has at least one limit point. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hFo : (Fo A b c).Nonempty) :
    (∃ M : ℝ, ∀ k i, |x k i| ≤ M ∧ |s k i| ≤ M) ∧
    ∃ q : (Fin n → ℝ) × (Fin n → ℝ), MapClusterPt q atTop (fun k => (x k, s k)) := by
  obtain ⟨M, hM⟩ := g71w_bounded hrun hn hFo
  refine ⟨⟨M, hM⟩, ?_⟩
  have hbd : Bornology.IsBounded (Metric.closedBall (0 : (Fin n → ℝ) × (Fin n → ℝ)) M) :=
    Metric.isBounded_closedBall
  have hmem : ∀ k, (x k, s k) ∈ Metric.closedBall (0 : (Fin n → ℝ) × (Fin n → ℝ)) M := by
    intro k
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM k ⟨0, hn⟩).1
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    constructor
    · exact (pi_norm_le_iff_of_nonneg hM0).mpr (fun i => by rw [Real.norm_eq_abs]; exact (hM k i).1)
    · exact (pi_norm_le_iff_of_nonneg hM0).mpr (fun i => by rw [Real.norm_eq_abs]; exact (hM k i).2)
  obtain ⟨q, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbd hmem
  exact ⟨q, MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt⟩

