-- Prove2me | solution 1 for SkipFreeFluct.MBI.mbiQ_skipFree_QMatrix
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:47:05.193148+00:00
-- url     : https://prove2.me/submissions/f6b11d8e-fa1b-4c77-9163-a4fb9f77c53c

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

open SkipFreeFluct.MBI in
theorem solution (P : MBIParams) (hP : P.Valid) :
    IsStateSpace (Set.Ici 0) ∧ IsQMatrix (Set.Ici 0) (mbiQ P) ∧
      SkipFreeDown (Set.Ici 0) (mbiQ P) := by
  obtain ⟨hα, hmu, hmu1, hmu0, hmu1z, hp, hβ, hnu, hnu0, hnu1, hq⟩ := hP
  refine ⟨⟨Set.ordConnected_Ici, 0, by simp, 1, by simp, by norm_num⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold mbiQ
    simp only [hx, hy, and_self, if_true]
    split_ifs with h1 h2 h3
    · have : (0 : ℝ) ≤ x := by exact_mod_cast hx
      have := hmu (y - x + 1).toNat; have := hnu (y - x).toNat
      positivity
    · exact absurd h2.symm hxy
    · have : (0 : ℝ) ≤ x := by exact_mod_cast hx
      positivity
    · exact le_rfl
  · intro x hx
    simp only [Set.mem_Ici] at hx
    have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    set f : Set.Ici (0 : ℤ) → ℝ := fun y => if (y : ℤ) ≠ x then mbiQ P x y else 0 with hf
    set F : ℤ → ℝ := (Set.Ici (0 : ℤ)).indicator (fun y => if y ≠ x then mbiQ P x y else 0)
      with hF
    set φ : ℕ → ℤ := fun j => x - 1 + j with hφ
    have hφi : Function.Injective φ := fun a b h => by simp [hφ] at h; exact_mod_cast h
    have hsupp : ∀ y ∉ Set.range φ, F y = 0 := by
      intro y hy
      have : y < x - 1 := by
        by_contra hc; push_neg at hc
        exact hy ⟨(y - (x - 1)).toNat, by simp [hφ]; omega⟩
      simp only [hF, Set.indicator, Set.mem_Ici]
      split_ifs with h1 h2 <;> try rfl
      unfold mbiQ
      simp only [hx, h1, and_self, if_true]
      split_ifs <;> first | rfl | omega
    set h : ℕ → ℝ := fun j => P.alpha * x * P.mu j + P.beta * P.nu (j - 1) with hh
    have hnush : HasSum (fun j => P.nu (j - 1)) 1 := by
      rw [← hasSum_nat_add_iff' 1]
      simpa [hnu0] using hnu1
    have hhs : HasSum h (P.alpha * x * 1 + P.beta * 1) :=
      (hmu1.mul_left _).add (hnush.mul_left _)
    have hbound : ∀ j, F (φ j) ≤ h j ∧ 0 ≤ F (φ j) := by
      intro j
      have hmj := hmu j
      have hnj := hnu (j - 1)
      have hmain : ∀ j, 0 ≤ h j := fun j => by
        have := hmu j; have := hnu (j - 1); simp only [hh]; positivity
      simp only [hF, Set.indicator, Set.mem_Ici, hφ]
      split_ifs with h1 h2
      · unfold mbiQ
        simp only [hx, h1, and_self, if_true]
        rcases j with _ | _ | j
        · have e1 : ¬ (x + 1 ≤ x - 1) := by omega
          have e2 : ¬ (x - 1 = x) := by omega
          simp only [Nat.cast_zero, add_zero] at h1 ⊢
          simp only [e1, e2, if_false, if_true]
          have : 0 ≤ P.mu 0 * P.alpha * x := by positivity
          simp only [hh, Nat.zero_sub, hnu0, mul_zero, add_zero]
          exact ⟨by linarith, this⟩
        · exfalso; apply h2; push_cast; ring
        · have e1 : x + 1 ≤ x - 1 + ((j + 2 : ℕ) : ℤ) := by push_cast; omega
          simp only [e1, if_true]
          have e3 : (x - 1 + ((j + 2 : ℕ) : ℤ) - x + 1).toNat = j + 2 := by omega
          have e4 : (x - 1 + ((j + 2 : ℕ) : ℤ) - x).toNat = j + 2 - 1 := by omega
          rw [e3, e4]
          simp only [hh]
          have := hmu (j + 2); have := hnu (j + 2 - 1)
          constructor
          · linarith
          · positivity
      · exact ⟨hmain _, le_rfl⟩
      · exact ⟨hmain _, le_rfl⟩
    have hsumF : Summable (F ∘ φ) :=
      Summable.of_nonneg_of_le (fun j => (hbound j).2) (fun j => (hbound j).1) hhs.summable
    have hsF : Summable F := (hφi.summable_iff hsupp).mp hsumF
    have hsf : Summable f :=
      (summable_subtype_iff_indicator (f := fun y : ℤ => if y ≠ x then mbiQ P x y else 0)).mpr hsF
    refine ⟨hsf, ?_⟩
    unfold offDiagSum rate
    rw [tsum_subtype (Set.Ici (0 : ℤ)) (fun y => if y ≠ x then mbiQ P x y else 0)]
    rw [← hφi.tsum_eq (fun y hy => by_contra fun h' => hy ?_ ) ]
    · have hle : ∑' j, F (φ j) ≤ ∑' j, h j :=
        Summable.tsum_le_tsum (fun j => (hbound j).1) hsumF hhs.summable
      rw [hhs.tsum_eq] at hle
      have hxx : mbiQ P x x = -(P.alpha + P.p) * x - (P.beta + P.q) := by
        unfold mbiQ; simp [hx]
      rw [hxx]
      have : 0 ≤ P.p * x := mul_nonneg hp hx'
      change ∑' j, F (φ j) ≤ _
      nlinarith
    · exact hsupp _ h' |> fun h0 => absurd h0 hy
  · intro x hx
    simp only [Set.mem_Ici] at hx
    refine ⟨fun h1 => ?_, fun y hy hyx => ?_⟩
    · simp only [Set.mem_Ici] at h1
      unfold mbiQ
      have e1 : ¬ (x + 1 ≤ x - 1) := by omega
      have e2 : ¬ (x - 1 = x) := by omega
      simp only [hx, h1, and_self, if_true, e1, e2, if_false]
      have : (0 : ℝ) < x := by exact_mod_cast (show (0:ℤ) < x by omega)
      positivity
    · simp only [Set.mem_Ici] at hy
      unfold mbiQ
      have e1 : ¬ (x + 1 ≤ y) := by omega
      have e2 : ¬ (y = x) := by omega
      have e3 : ¬ (y = x - 1) := by omega
      simp [hx, hy, e1, e2, e3]
