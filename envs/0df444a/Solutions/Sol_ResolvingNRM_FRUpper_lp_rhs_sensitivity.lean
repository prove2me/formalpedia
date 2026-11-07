-- Prove2me | solution 1 for ResolvingNRM.FRUpper.lp_rhs_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:08:25.949563+00:00
-- url     : https://prove2.me/submissions/77609e6a-7fbe-4be9-9ea7-8b03d0dbd1a1

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (b b' : Fin m → ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    piValue A r b lam - piValue A r b' lam ≤
      ∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * max (b l - b' l) 0 := by
  set S := ∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * max (b l - b' l) 0
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => (hlam j).le
  have hrj : ∀ j, 0 ≤ r j := fun j => hr j
  -- r_j ≤ rmax_l * A_lj when A_lj > 0
  have hrmax : ∀ l j, 0 < A l j → r j ≤ ResolvingNRM.FRUpper.rmaxRes A r l * A l j := by
    intro l j hlj
    have hb : BddAbove (Set.range fun j => if 0 < A l j then r j / A l j else 0) :=
      (Set.finite_range _).bddAbove
    have := le_ciSup hb j
    simp only [hlj, if_true] at this
    unfold ResolvingNRM.FRUpper.rmaxRes
    rw [div_le_iff₀ hlj] at this
    exact this
  have hrmax0 : ∀ l, 0 ≤ ResolvingNRM.FRUpper.rmaxRes A r l := by
    intro l
    unfold ResolvingNRM.FRUpper.rmaxRes
    apply Real.iSup_nonneg
    intro j
    split_ifs with h
    · exact div_nonneg (hrj j) h.le
    · exact le_refl _
  -- bounded above
  have hbdd : BddAbove {v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ b' ∧ 0 ≤ y ∧ y ≤ lam ∧ v = r ⬝ᵥ y} := by
    refine ⟨r ⬝ᵥ lam, ?_⟩
    rintro v ⟨y, -, -, hy2, rfl⟩
    simp only [dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy2 j) (hrj j)
  have hne : ({v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ b ∧ 0 ≤ y ∧ y ≤ lam ∧ v = r ⬝ᵥ y}).Nonempty := by
    refine ⟨0, 0, ?_, le_refl _, fun j => hlam0 j, by simp⟩
    simpa using hb
  suffices key : piValue A r b lam ≤ piValue A r b' lam + S by linarith
  unfold piValue
  apply csSup_le hne
  rintro v ⟨y, hAy, hy0, hyl, rfl⟩
  -- construct y'
  set u : Fin m → ℝ := fun l => ∑ j, A l j * y j with hu
  have hAy' : ∀ l, u l ≤ b l := by
    intro l; have := hAy l; simpa [Matrix.mulVec, dotProduct] using this
  have hu0 : ∀ l, 0 ≤ u l := fun l =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA l j) (hy0 j)
  set D : Fin m → ℝ := fun l => max (u l - b' l) 0 with hD
  set θ : Fin m → ℝ := fun l => D l / u l with hθ
  have hD0 : ∀ l, 0 ≤ D l := fun l => le_max_right _ _
  have hDu : ∀ l, D l ≤ u l := fun l => max_le (by linarith [show (0:ℝ) ≤ b' l from hb' l]) (hu0 l)
  have hθ0 : ∀ l, 0 ≤ θ l := fun l => div_nonneg (hD0 l) (hu0 l)
  have hθ1 : ∀ l, θ l ≤ 1 := by
    intro l
    rcases (hu0 l).eq_or_lt with h | h
    · simp [hθ, ← h]
    · exact (div_le_one h).mpr (hDu l)
  have huθ : ∀ l, u l * θ l = D l := by
    intro l
    rcases (hu0 l).eq_or_lt with h | h
    · have : D l = 0 := le_antisymm (by linarith [hDu l]) (hD0 l)
      simp [← h, this]
    · simp only [hθ]; field_simp
  set σ : Fin n → ℝ := fun j => ∑ l, if 0 < A l j then θ l else 0 with hσ
  set f : Fin n → ℝ := fun j => max 0 (1 - σ j) with hf
  set y' : Fin n → ℝ := fun j => y j * f j with hy'
  have hσθ : ∀ l j, 0 < A l j → θ l ≤ σ j := by
    intro l j h
    have : (if 0 < A l j then θ l else 0) ≤ σ j := by
      apply Finset.single_le_sum (f := fun l => if 0 < A l j then θ l else 0)
        (fun i _ => by split_ifs <;> simp [hθ0 i]) (Finset.mem_univ l)
    simpa [h] using this
  have hσ0 : ∀ j, 0 ≤ σ j := fun j =>
    Finset.sum_nonneg fun l _ => by split_ifs <;> simp [hθ0 l]
  have hf0 : ∀ j, 0 ≤ f j := fun j => le_max_left _ _
  have hf1 : ∀ j, f j ≤ 1 := fun j => max_le (by norm_num) (by linarith [hσ0 j])
  have hfθ : ∀ l j, 0 < A l j → f j ≤ 1 - θ l := by
    intro l j h
    exact max_le (by linarith [hθ1 l]) (by linarith [hσθ l j h])
  -- feasibility of y'
  have hfeas : A *ᵥ y' ≤ b' := by
    intro l
    simp only [Matrix.mulVec, dotProduct]
    have step : ∀ j, A l j * y' j ≤ A l j * y j * (1 - θ l) := by
      intro j
      rcases (hA l j).eq_or_lt with h | h
      · simp [← h]
      · simp only [hy']
        have := hfθ l j h
        have hp : 0 ≤ A l j * y j := mul_nonneg h.le (hy0 j)
        nlinarith
    calc ∑ j, A l j * y' j ≤ ∑ j, A l j * y j * (1 - θ l) := Finset.sum_le_sum fun j _ => step j
      _ = u l - u l * θ l := by rw [← Finset.sum_mul]; ring
      _ = u l - D l := by rw [huθ]
      _ ≤ b' l := by simp only [hD]; rw [sub_le_iff_le_add]; exact by
                        rcases le_total (u l - b' l) 0 with h | h
                        · rw [max_eq_right h]; linarith
                        · rw [max_eq_left h]; linarith
  have hy'0 : 0 ≤ y' := fun j => mul_nonneg (hy0 j) (hf0 j)
  have hy'l : y' ≤ lam := fun j => by
    have : y' j ≤ y j := by
      simp only [hy']; have h1 := hf1 j; have h2 : 0 ≤ y j := hy0 j; nlinarith
    exact this.trans (hyl j)
  have hv' : r ⬝ᵥ y' ≤ sSup {v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ b' ∧ 0 ≤ y ∧ y ≤ lam ∧
      v = r ⬝ᵥ y} := le_csSup hbdd ⟨y', hfeas, hy'0, hy'l, rfl⟩
  -- revenue loss
  have hloss : r ⬝ᵥ y - r ⬝ᵥ y' ≤ S := by
    have e1 : r ⬝ᵥ y - r ⬝ᵥ y' = ∑ j, r j * y j * (1 - f j) := by
      simp only [dotProduct, hy', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∀ j, r j * y j * (1 - f j) ≤
        ∑ l, (if 0 < A l j then ResolvingNRM.FRUpper.rmaxRes A r l * A l j * y j * θ l else 0) := by
      intro j
      have h1 : 1 - f j ≤ σ j := by
        have : 1 - σ j ≤ f j := le_max_right _ _
        linarith
      have hry : 0 ≤ r j * y j := mul_nonneg (hrj j) (hy0 j)
      calc r j * y j * (1 - f j) ≤ r j * y j * σ j := mul_le_mul_of_nonneg_left h1 hry
        _ = ∑ l, (if 0 < A l j then r j * y j * θ l else 0) := by
            simp only [hσ, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
        _ ≤ _ := by
            apply Finset.sum_le_sum
            intro l _
            split_ifs with h
            · have := hrmax l j h
              have : 0 ≤ y j * θ l := mul_nonneg (hy0 j) (hθ0 l)
              nlinarith
            · exact le_refl _
    have e3 : ∑ j, ∑ l, (if 0 < A l j then
        ResolvingNRM.FRUpper.rmaxRes A r l * A l j * y j * θ l else 0)
        = ∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * D l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← huθ]
      simp only [hu, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · ring
      · have : A l j = 0 := le_antisymm (not_lt.mp h) (hA l j)
        simp [this]
    have e4 : ∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * D l ≤ S := by
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_left _ (hrmax0 l)
      exact max_le_max (by linarith [hAy' l]) (le_refl _)
    rw [e1]
    calc _ ≤ _ := Finset.sum_le_sum fun j _ => e2 j
      _ = _ := e3
      _ ≤ S := e4
  linarith
