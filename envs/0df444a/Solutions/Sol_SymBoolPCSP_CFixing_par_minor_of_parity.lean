-- Prove2me | solution 1 for SymBoolPCSP.CFixing.par_minor_of_parity
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T18:25:41.685889+00:00
-- url     : https://prove2.me/submissions/f0ba82b0-f95d-4902-9060-8b61d01444e0

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_FinsetParts_exists_parts_card_eq

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_par_minor_of_parity

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw; rw [Finset.card_filter]

theorem hw_neg_add {k : ℕ} (y : Fin k → Bool) : hw (neg y) + hw y = k := by
  rw [hw_eq_sum, hw_eq_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => show (if neg y i = true then 1 else 0) +
    (if y i = true then 1 else 0) = 1 by unfold neg; split_ifs <;> simp_all)]
  simp

end Aux_par_minor_of_parity

open Aux_par_minor_of_parity in
/-- Parity as a minor: let `f : {0,1}^L → {0,1}` be folded with `f(0,…,0) = 0`, let `L₁` be odd, `T ⊆ [L]` and `C ∈ ℕ`. If `f(e_X) = |X| mod 2` for every `X ⊆ T` with `|X| ≥ C`, and `|T| ≥ L₁(C + 1)`, then `Par_{L₁}` is a minor of `f`: there is `π : [L] → [L₁]` with `f(y_{π(1)}, …, y_{π(L)}) = Par_{L₁}(y)` for all `y ∈ {0,1}^{L₁}`. -/
theorem par_minor_of_parity {L L₁ : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (h0 : f (fun _ => false) = false) (hL₁ : Odd L₁) (T : Finset (Fin L)) (C : ℕ)
    (hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1))
    (hT : L₁ * (C + 1) ≤ T.card) :
    ∃ π : Fin L → Fin L₁, ∀ y : Fin L₁ → Bool, f (fun i => y (π i)) = Par L₁ y := by
  classical
  obtain ⟨m, hCm, hmC, hm⟩ : ∃ m, C ≤ m ∧ m ≤ C + 1 ∧ m % 2 = 1 := by
    by_cases hC : C % 2 = 1
    · exact ⟨C, le_rfl, by omega, hC⟩
    · exact ⟨C + 1, by omega, le_rfl, by omega⟩
  have hL1pos : 0 < L₁ := hL₁.pos
  obtain ⟨X', hX'T, hX'c⟩ := Finset.exists_subset_card_eq
    (show L₁ * m ≤ T.card from le_trans (Nat.mul_le_mul_left _ hmC) hT)
  obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq X' (fun _ : Fin L₁ => m)
    (by rw [hX'c]; simp)
  let π : Fin L → Fin L₁ := fun i => if hi : i ∈ X' then (hu i hi).exists.choose else ⟨0, hL1pos⟩
  have hπ : ∀ i ∈ X', ∀ j, π i = j ↔ i ∈ Y j := by
    intro i hi j
    simp only [π, dif_pos hi]
    constructor
    · rintro rfl; exact (hu i hi).exists.choose_spec
    · intro h; exact (hu i hi).unique (hu i hi).exists.choose_spec h
  have key : ∀ y : Fin L₁ → Bool, y ⟨0, hL1pos⟩ = false →
      f (fun i => y (π i)) = Par L₁ y := by
    intro y hy0
    set Z := X'.filter (fun i => y (π i) = true) with hZdef
    have hZ : (fun i => y (π i)) = indicator Z := by
      funext i
      simp only [indicator, hZdef, mem_filter]
      by_cases hi : i ∈ X'
      · simp [hi]
      · simp [hi, π, hy0]
    have hZc : Z.card = m * hw y := by
      rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
      rw [hw_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have : Z.filter (fun i => π i = j) = if y j = true then Y j else ∅ := by
        ext i
        simp only [hZdef, mem_filter]
        split_ifs with hyj
        · constructor
          · rintro ⟨⟨hi, _⟩, hij⟩; exact (hπ i hi j).mp hij
          · intro hi
            have hiX := hYX j hi
            have hij := (hπ i hiX j).mpr hi
            exact ⟨⟨hiX, by rw [hij]; exact hyj⟩, hij⟩
        · simp only [Finset.notMem_empty, iff_false]
          rintro ⟨⟨_, hy⟩, hij⟩
          rw [hij] at hy; exact hyj hy
      rw [this]
      split_ifs <;> simp [hYc]
    rw [hZ]
    by_cases hyz : hw y = 0
    · have hZe : Z = ∅ := by rw [← Finset.card_eq_zero, hZc, hyz, mul_zero]
      have hind : indicator (∅ : Finset (Fin L)) = fun _ => false := by
        funext i; simp [indicator]
      rw [hZe, hind, h0]
      unfold Par; rw [hyz]; rfl
    · rw [hpar Z ((Finset.filter_subset _ _).trans hX'T)
        (by rw [hZc]; exact hCm.trans (Nat.le_mul_of_pos_right _ (by omega)))]
      unfold Par
      rw [hZc, Nat.mul_mod, hm, one_mul, Nat.mod_mod]
  refine ⟨π, fun y => ?_⟩
  cases hy : y ⟨0, hL1pos⟩
  · exact key y hy
  · rw [hfold]
    have hn : neg (fun i => y (π i)) = fun i => (neg y) (π i) := rfl
    rw [hn, key (neg y) (by simp [neg, hy])]
    unfold Par
    have h1 := hw_neg_add y
    obtain ⟨t, ht⟩ := hL₁
    have h2 : hw (neg y) % 2 = 1 ↔ ¬ hw y % 2 = 1 := by omega
    simp only [h2, decide_not, Bool.not_not]

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L L₁ : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (h0 : f (fun _ => false) = false) (hL₁ : Odd L₁) (T : Finset (Fin L)) (C : ℕ)
    (hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1))
    (hT : L₁ * (C + 1) ≤ T.card) :
    ∃ π : Fin L → Fin L₁, ∀ y : Fin L₁ → Bool, f (fun i => y (π i)) = Par L₁ y :=
  SymBoolPCSP.CFixing.par_minor_of_parity f hfold h0 hL₁ T C hpar hT
