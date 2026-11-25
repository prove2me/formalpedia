-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T03:06:45.535362+00:00
-- url     : https://prove2.me/submissions/aa88abe6-72da-41fd-bded-9773d415f4fc

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

theorem lemma_1 (T : ℕ) (hT : Even T) (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) :
    mpdDisc x ≤ 1 := by
  obtain ⟨m, rfl⟩ := hT
  set s := Tuple.sort x with hs
  have hmono : Monotone (x ∘ s) := Tuple.monotone_sort x
  let φ : Fin m × Fin 2 ≃ Fin (m + m) :=
    (finProdFinEquiv.trans (finCongr (by omega : m * 2 = m + m))).trans s
  have hφ : ∀ k : Fin m, ∀ j : Fin 2, φ (k, j) = s ⟨j + 2 * k, by omega⟩ := by
    intro k j; simp [φ, finProdFinEquiv]
  let w : Fin (m + m) → Bool := fun t => decide ((φ.symm t).2 = 1)
  let A : Fin m ≃ {t // w t = false} :=
    { toFun := fun k => ⟨φ (k, 0), by simp [w]⟩
      invFun := fun t => (φ.symm t.1).1
      left_inv := fun k => by simp
      right_inv := fun t => by
        obtain ⟨t, ht⟩ := t
        have h2 : (φ.symm t).2 = 0 := by
          have : ¬ (φ.symm t).2 = 1 := by simpa [w] using ht
          omega
        apply Subtype.ext
        simp only
        conv_rhs => rw [← φ.apply_symm_apply t]
        rw [← h2] }
  let B : Fin m ≃ {t // w t = true} :=
    { toFun := fun k => ⟨φ (k, 1), by simp [w]⟩
      invFun := fun t => (φ.symm t.1).1
      left_inv := fun k => by simp
      right_inv := fun t => by
        obtain ⟨t, ht⟩ := t
        have h2 : (φ.symm t).2 = 1 := by simpa [w] using ht
        apply Subtype.ext
        simp only
        conv_rhs => rw [← φ.apply_symm_apply t]
        rw [← h2] }
  have hcard : (Finset.univ.filter (fun t => w t = false)).card = (m + m) / 2 := by
    rw [← Fintype.card_subtype, ← Fintype.card_congr A]; simp; omega
  have hnn : ∀ w' : Fin (m + m) → Bool, 0 ≤ PigeonholeDesign.Upper.discrepancy x w' := fun w' =>
    Real.iInf_nonneg (fun e => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  have h1 : mpdDisc x ≤ PigeonholeDesign.Upper.discrepancy x w := by
    unfold mpdDisc
    exact ciInf_le ⟨0, by rintro _ ⟨w', rfl⟩; exact hnn w'.1⟩ (⟨w, hcard⟩ :
      {w : Fin (m + m) → Bool // (Finset.univ.filter (fun t => w t = false)).card = (m + m) / 2})
  let e : {t // w t = false} ≃ {t // w t = true} := A.symm.trans B
  have h2 : PigeonholeDesign.Upper.discrepancy x w ≤
      ∑ a : {t // w t = false}, dist (x a) (x (e a)) := by
    unfold PigeonholeDesign.Upper.discrepancy
    exact ciInf_le ⟨0, by rintro _ ⟨e', rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ e
  -- extended monotone sequence
  let f : ℕ → ℝ := fun n => if h : n < m + m then x (s ⟨n, h⟩) else 1
  have fmono : Monotone f := by
    intro a b hab
    simp only [f]
    split_ifs with ha hb hb
    · exact hmono (show (⟨a, ha⟩ : Fin (m+m)) ≤ ⟨b, hb⟩ from hab)
    · exact (hx _).2
    · omega
    · exact le_rfl
  have h3 : ∑ a : {t // w t = false}, dist (x a) (x (e a)) =
      ∑ k ∈ Finset.range m, (f (2 * k + 1) - f (2 * k)) := by
    rw [← Equiv.sum_comp A, ← Fin.sum_univ_eq_sum_range (fun k => f (2 * k + 1) - f (2 * k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have he : e (A k) = B k := by simp [e]
    rw [he]
    show dist (x (φ (k, 0))) (x (φ (k, 1))) = _
    rw [hφ, hφ, Real.dist_eq, abs_sub_comm]
    have hk1 : 2 * (k : ℕ) + 1 < m + m := by omega
    have hk0 : 2 * (k : ℕ) < m + m := by omega
    simp only [f, dif_pos hk1, dif_pos hk0]
    have hle : x (s ⟨2 * k, hk0⟩) ≤ x (s ⟨2 * k + 1, hk1⟩) :=
      hmono (show (⟨2 * k, hk0⟩ : Fin (m+m)) ≤ ⟨2 * k + 1, hk1⟩ from by
        simp [Fin.le_def])
    simp only [Fin.val_zero, Fin.val_one, zero_add] at *
    rw [abs_of_nonneg (by
      have : (⟨1 + 2 * (k:ℕ), by omega⟩ : Fin (m+m)) = ⟨2 * k + 1, hk1⟩ := by ext; simp; omega
      rw [this]; linarith)]
    have : (⟨1 + 2 * (k:ℕ), by omega⟩ : Fin (m+m)) = ⟨2 * k + 1, hk1⟩ := by ext; simp; omega
    rw [this]
  have h4 : ∑ k ∈ Finset.range m, (f (2 * k + 1) - f (2 * k)) ≤
      ∑ k ∈ Finset.range m, (f (2 * (k + 1)) - f (2 * k)) :=
    Finset.sum_le_sum (fun k _ => by have := fmono (show 2 * k + 1 ≤ 2 * (k + 1) by omega); linarith)
  rw [Finset.sum_range_sub (fun k => f (2 * k))] at h4
  have hfm : f (2 * m) = 1 := by simp only [f]; rw [dif_neg (by omega)]
  have hf0 : 0 ≤ f 0 := by
    simp only [f]; split_ifs
    · exact (hx _).1
    · norm_num
  simp only [mul_zero] at h4
  linarith

end PigeonholeDesign.Upper.Supplement

open PigeonholeDesign.Upper.Supplement in
theorem solution (T : ℕ) (hT : Even T) (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) :
    mpdDisc x ≤ 1 :=
  PigeonholeDesign.Upper.Supplement.lemma_1 T hT x hx
