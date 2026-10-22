-- Prove2me | solution 1 for QZeroSum19.LPReduce.lemma_12_pos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:25:46.066199+00:00
-- url     : https://prove2.me/submissions/64fd6c1f-3764-4d70-b1b5-f86bbb8de428

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

set_option autoImplicit false
open Matrix
open QZeroSum19.LPReduce

theorem qz_row0 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 0) = ∑ j, y (Sum.inl j) + y (Sum.inr 0) - y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 1) = -∑ j, y (Sum.inl j) - y (Sum.inr 0) + y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inl ())) =
      -(b ⬝ᵥ (fun j => y (Sum.inl j))) + α / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem qz_row3 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) (i : Fin n) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inr i)) =
      (A *ᵥ (fun j => y (Sum.inl j))) i - c i / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_simplex {m : ℕ} (y : Fin m ⊕ Fin 2 → ℝ) (hy : y ∈ stdSimplex ℝ (Fin m ⊕ Fin 2)) :
    (∀ j, 0 ≤ y (Sum.inl j)) ∧ 0 ≤ y (Sum.inr 0) ∧ 0 ≤ y (Sum.inr 1) ∧
      ∑ j, y (Sum.inl j) + y (Sum.inr 0) + y (Sum.inr 1) = 1 := by
  obtain ⟨h0, h1⟩ := hy
  refine ⟨fun j => h0 _, h0 _, h0 _, ?_⟩
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at h1
  linarith

theorem qz_h_half {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    |y' (Sum.inr 1) - 1 / 2| ≤ κ := by
  obtain ⟨-, -, -, hs⟩ := qz_simplex y' hy'
  have h0 := hle (Sum.inl 0)
  have h1 := hle (Sum.inl 1)
  rw [qz_row0] at h0
  rw [qz_row1] at h1
  rw [abs_le]
  constructor <;> linarith

theorem qz_gv_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) (y : κ → ℝ)
    (hy : y ∈ stdSimplex ℝ κ) :
    QZeroSum19.GK.gameValue M ≤ ⨆ i, (M *ᵥ y) i := by
  unfold QZeroSum19.GK.gameValue
  apply csInf_le
  · refine ⟨-(∑ i, ∑ j, |M i j|), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hz0, hz1⟩ := hz
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp only [Real.iSup_of_isEmpty]
      have : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
      linarith
    · obtain ⟨i0⟩ := hι
      refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i0)
      have h1 : |(M *ᵥ z) i0| ≤ ∑ j, |M i0 j| := by
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hz0 j)]
        have : z j ≤ 1 := by
          rw [← hz1]; exact Finset.single_le_sum (fun k _ => hz0 k) (Finset.mem_univ j)
        nlinarith [abs_nonneg (M i0 j)]
      have h2 : ∑ j, |M i0 j| ≤ ∑ i, ∑ j, |M i j| :=
        Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i0)
      have := neg_abs_le ((M *ᵥ z) i0)
      linarith
  · exact ⟨y, hy, rfl⟩

theorem qz_exists {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (M : Matrix ι κ ℝ) (t : ℝ) (ht : QZeroSum19.GK.gameValue M ≤ t) :
    ∃ y ∈ stdSimplex ℝ κ, ∀ k, (M *ᵥ y) k ≤ t := by
  have hne : (stdSimplex ℝ κ).Nonempty := ⟨(inferInstance : Nonempty (stdSimplex ℝ κ)).some.1, (inferInstance : Nonempty (stdSimplex ℝ κ)).some.2⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy, fun k => isEmptyElim k⟩
  · have hcont : Continuous (fun y : κ → ℝ => ⨆ i, (M *ᵥ y) i) := by
      have : (fun y : κ → ℝ => ⨆ i, (M *ᵥ y) i) =
          fun y => Finset.univ.sup' Finset.univ_nonempty (fun i => (M *ᵥ y) i) := by
        funext y
        exact le_antisymm (ciSup_le fun i => Finset.le_sup' (fun i => (M *ᵥ y) i) (Finset.mem_univ i))
          (Finset.sup'_le _ _ fun i _ => le_ciSup (Set.finite_range _).bddAbove i)
      rw [this]
      refine Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => ?_)
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    obtain ⟨y0, hy0, hmin⟩ := (isCompact_stdSimplex ℝ κ).exists_isMinOn hne hcont.continuousOn
    have hleast : IsLeast ((fun y => ⨆ i, (M *ᵥ y) i) '' stdSimplex ℝ κ) (⨆ i, (M *ᵥ y0) i) := by
      refine ⟨⟨y0, hy0, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hmin hz
    have hval : QZeroSum19.GK.gameValue M = ⨆ i, (M *ᵥ y0) i := hleast.csInf_eq
    refine ⟨y0, hy0, fun k => ?_⟩
    rw [hval] at ht
    exact (le_ciSup (Set.finite_range _).bddAbove k).trans ht

theorem qz_certificate {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (hR : 0 < R) (y : Fin m → ℝ) (hy : IsPrimalFeasible A c y)
    (hsum : ∑ j, y j ≤ R) (hby : α ≤ b ⬝ᵥ y) :
    let yhat : Fin m ⊕ Fin 2 → ℝ :=
      Sum.elim (fun j => y j / (2 * R)) ![1 / 2 - (∑ j, y j) / (2 * R), 1 / 2]
    yhat ∈ stdSimplex ℝ (Fin m ⊕ Fin 2) ∧ ∀ k, (gameMatrix A b c α R *ᵥ yhat) k ≤ 0 := by
  intro yhat
  obtain ⟨hAy, hy0⟩ := hy
  have hR2 : 0 < 2 * R := by linarith
  have hsum0 : 0 ≤ ∑ j, y j := Finset.sum_nonneg fun j _ => hy0 j
  have hS : (∑ j, y j) / (2 * R) ≤ 1 / 2 := by
    rw [div_le_iff₀ hR2]; linarith
  have hsub : ∑ j, y j / (2 * R) = (∑ j, y j) / (2 * R) := by rw [Finset.sum_div]
  have hu : (fun j => yhat (Sum.inl j)) = fun j => y j / (2 * R) := rfl
  have hz : yhat (Sum.inr 0) = 1 / 2 - (∑ j, y j) / (2 * R) := rfl
  have hh : yhat (Sum.inr 1) = 1 / 2 := rfl
  have hsumu : ∑ j, yhat (Sum.inl j) = (∑ j, y j) / (2 * R) := hsub
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (j | k)
    · exact div_nonneg (hy0 j) hR2.le
    · fin_cases k
      · show 0 ≤ 1 / 2 - (∑ j, y j) / (2 * R)
        linarith
      · show (0:ℝ) ≤ 1 / 2
        norm_num
  · rw [Fintype.sum_sum_type, Fin.sum_univ_two]
    show ∑ j, y j / (2 * R) + (1 / 2 - (∑ j, y j) / (2 * R) + 1 / 2) = 1
    rw [hsub]; ring
  · rintro (t | s)
    · revert t
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · rw [qz_row0, hsumu, hz, hh]; apply le_of_eq; ring
      · rw [qz_row1, hsumu, hz, hh]; apply le_of_eq; ring
    · rcases s with u | i
      · rw [qz_row2, hh]
        have : b ⬝ᵥ (fun j => yhat (Sum.inl j)) = (b ⬝ᵥ y) / (2 * R) := by
          rw [hu]; simp only [dotProduct]; rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        have : α / R * (1 / 2) - (b ⬝ᵥ y) / (2 * R) = (α - b ⬝ᵥ y) / (2 * R) := by
          field_simp
        have h2 : (α - b ⬝ᵥ y) / (2 * R) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hR2.le
        linarith
      · rw [qz_row3, hh]
        have : (A *ᵥ fun j => yhat (Sum.inl j)) i = (A *ᵥ y) i / (2 * R) := by
          rw [hu]; simp only [Matrix.mulVec, dotProduct]; rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        have : (A *ᵥ y) i / (2 * R) - c i / R * (1 / 2) = ((A *ᵥ y) i - c i) / (2 * R) := by
          field_simp
        have h2 : ((A *ᵥ y) i - c i) / (2 * R) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith [hAy i]) hR2.le
        linarith

theorem qz_eq78 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (hR : 0 < R) (hc : ∀ i, |c i| ≤ R) (hα : |α| ≤ R) (hκ : 0 ≤ κ)
    (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    let yhat : Fin m → ℝ := fun j => 2 * R * y' (Sum.inl j)
    α - 6 * R * κ ≤ b ⬝ᵥ yhat ∧ ∀ i, (A *ᵥ yhat) i ≤ c i + 6 * R * κ := by
  intro yhat
  have hh := qz_h_half A b c α R κ y' hy' hle
  rw [abs_le] at hh
  have key : ∀ a : ℝ, |a| ≤ R → -(2 * R * κ) ≤ a * (2 * y' (Sum.inr 1) - 1) ∧
      a * (2 * y' (Sum.inr 1) - 1) ≤ 2 * R * κ := by
    intro a ha
    have h1 : |a * (2 * y' (Sum.inr 1) - 1)| ≤ R * (2 * κ) := by
      rw [abs_mul]
      have : |2 * y' (Sum.inr 1) - 1| ≤ 2 * κ := by
        rw [abs_le]; constructor <;> linarith [hh.1, hh.2]
      exact mul_le_mul ha this (abs_nonneg _) hR.le
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hbu : b ⬝ᵥ yhat = 2 * R * (b ⬝ᵥ (fun j => y' (Sum.inl j))) := by
    simp only [yhat, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hAu : ∀ i, (A *ᵥ yhat) i = 2 * R * (A *ᵥ (fun j => y' (Sum.inl j))) i := by
    intro i
    simp only [yhat, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · have h2 := hle (Sum.inr (Sum.inl ()))
    rw [qz_row2] at h2
    have h3 : α / R * y' (Sum.inr 1) * R = α * y' (Sum.inr 1) := by field_simp
    have := (key α hα).1
    rw [hbu]
    nlinarith
  · intro i
    have h2 := hle (Sum.inr (Sum.inr i))
    rw [qz_row3] at h2
    have h3 : c i / R * y' (Sum.inr 1) * R = c i * y' (Sum.inr 1) := by field_simp
    have := (key (c i) (hc i)).2
    rw [hAu]
    nlinarith

theorem qz_weak {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (r κ : ℝ) (yhat : Fin m → ℝ) (x : Fin n → ℝ) (hyhat : ∀ j, 0 ≤ yhat j)
    (hκ : 0 ≤ κ) (hAy : ∀ i, (A *ᵥ yhat) i ≤ c i + κ) (hx : IsDualFeasible A b x)
    (hxr : ∑ i, x i ≤ r) :
    b ⬝ᵥ yhat ≤ (fun i => c i + κ) ⬝ᵥ x ∧ (fun i => c i + κ) ⬝ᵥ x ≤ c ⬝ᵥ x + r * κ := by
  obtain ⟨hxd, hx0⟩ := hx
  constructor
  · calc b ⬝ᵥ yhat ≤ (Aᵀ *ᵥ x) ⬝ᵥ yhat := by
          simp only [dotProduct]
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hxd j) (hyhat j)
      _ = x ⬝ᵥ (A *ᵥ yhat) := by
          rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
      _ ≤ (fun i => c i + κ) ⬝ᵥ x := by
          rw [dotProduct_comm]
          simp only [dotProduct]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hAy i) (hx0 i)
  · have : (fun i => c i + κ) ⬝ᵥ x = c ⬝ᵥ x + κ * ∑ i, x i := by
      simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]
    nlinarith

theorem qz_value_le_zero {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (α R : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (t : ℝ) (h : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ t) :
    QZeroSum19.GK.gameValue (gameMatrix A b c α R) ≤ t :=
  (qz_gv_le _ y' hy').trans (ciSup_le h)

theorem qz_pos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α : ℝ) (hLP : LPStanding A b c R r OPT) :
    0 < QZeroSum19.GK.gameValue (gameMatrix A b c α R) → OPT < α := by
  intro hv
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy, hsum, hby⟩ := hLP.opt_attained
  obtain ⟨hs, hk⟩ := qz_certificate A b c α R hLP.R_pos y hy hsum (by linarith)
  have := qz_value_le_zero A b c α R _ hs 0 hk
  linarith

theorem qz_small {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α ε : ℝ) (hLP : LPStanding A b c R r OPT) (hα : |α| ≤ R) (hε : 0 < ε) :
    QZeroSum19.GK.gameValue (gameMatrix A b c α R) ≤ 2 * epsGame ε R r → α - ε ≤ OPT := by
  intro hv
  have hR := hLP.R_pos
  obtain ⟨x, hx, hxr, hcx⟩ := hLP.dual_attained
  have hr : 0 ≤ r := le_trans (Finset.sum_nonneg fun i _ => hx.2 i) hxr
  have hr1 : 0 < 6 * R * (r + 1) := by positivity
  have hκ : 0 ≤ epsGame ε R r := div_nonneg hε.le hr1.le
  have hκe : 6 * R * (r + 1) * epsGame ε R r = ε := by
    unfold epsGame; field_simp
  haveI : Nonempty (Fin m ⊕ Fin 2) := ⟨Sum.inr 0⟩
  obtain ⟨y', hy', hle⟩ := qz_exists _ _ hv
  obtain ⟨h1, h2⟩ := qz_eq78 A b c α R (epsGame ε R r) hR hLP.c_le_R hα hκ y' hy' hle
  have hyhat : ∀ j, 0 ≤ 2 * R * y' (Sum.inl j) := fun j =>
    mul_nonneg (by linarith) ((qz_simplex y' hy').1 j)
  obtain ⟨w1, w2⟩ := qz_weak A b c r (6 * R * epsGame ε R r) _ x hyhat
    (by positivity) h2 hx hxr
  rw [hcx] at w2
  nlinarith

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α : ℝ) (hLP : LPStanding A b c R r OPT) :
    0 < QZeroSum19.GK.gameValue (gameMatrix A b c α R) → OPT < α := qz_pos A b c R r OPT α hLP
