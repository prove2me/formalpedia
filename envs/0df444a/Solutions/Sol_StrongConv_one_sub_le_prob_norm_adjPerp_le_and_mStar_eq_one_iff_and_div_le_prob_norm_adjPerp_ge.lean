-- Prove2me | solution 1 for StrongConv.one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:49:09.940394+00:00
-- url     : https://prove2.me/submissions/624e98af-e0e9-43d2-8313-13f7d32764e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_of_lt_rhoStair
import Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_rhoStair
import Mathlib

section
section
open Filter

namespace StrongConv
namespace W2Sec3

theorem uniformProb_add_ge_one {X : Type*} [Fintype X] [Nonempty X] (E F : X → Prop)
    (h : ∀ x, E x ∨ F x) : 1 ≤ uniformProb E + uniformProb F := by
  classical
  unfold uniformProb
  have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [← add_div, le_div_iff₀ hpos, one_mul]
  have : (Finset.univ.filter E) ∪ (Finset.univ.filter F) = Finset.univ := by
    ext x; simp [h x]
  have h2 := Finset.card_union_le (Finset.univ.filter E) (Finset.univ.filter F)
  rw [this, Finset.card_univ] at h2
  exact_mod_cast h2

theorem sqrt_pos' (d : ℕ) (hd : 2 ≤ d) : 1 < Real.sqrt (2 * d - 1) := by
  have : (2:ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.lt_sqrt (by norm_num)]
  linarith

theorem mStar_spec (d : ℕ) (hd : 2 ≤ d) :
    1 ≤ mStar d ∧ (2 * (mStar d : ℝ) - 1 ≤ Real.sqrt (2 * d - 1)) ∧
      Real.sqrt (2 * d - 1) < 2 * ((mStar d : ℝ) + 1) - 1 := by
  have h1 := sqrt_pos' d hd
  unfold mStar
  have hnn : 0 ≤ (Real.sqrt (2 * d - 1) + 1) / 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.le_floor; push_cast; linarith
  · have := Nat.floor_le hnn; linarith
  · have := Nat.lt_floor_add_one ((Real.sqrt (2 * d - 1) + 1) / 2); linarith

theorem mStar_le (d : ℕ) (hd : 2 ≤ d) : mStar d ≤ d - 1 := by
  obtain ⟨-, h2, -⟩ := mStar_spec d hd
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs : Real.sqrt (2 * d - 1) < 2 * d - 1 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  have h3 : (mStar d : ℝ) < d := by linarith
  have : mStar d < d := by exact_mod_cast h3
  omega

theorem rho_mStar (d : ℕ) (hd : 2 ≤ d) : rhoStair d (mStar d) = 2 * Real.sqrt (2 * d - 1) := by
  obtain ⟨-, h2, -⟩ := mStar_spec d hd
  unfold rhoStair; rw [if_pos h2]

theorem rho_one (d : ℕ) (hd : 2 ≤ d) : rhoStair d 1 = 2 * Real.sqrt (2 * d - 1) := by
  have := sqrt_pos' d hd
  unfold rhoStair; rw [if_pos (by push_cast; linarith)]

theorem rho_gap (d : ℕ) (hd : 2 ≤ d) :
    2 * Real.sqrt (2 * d - 1) < rhoStair d (mStar d + 1) := by
  obtain ⟨h1, -, h3⟩ := mStar_spec d hd
  unfold rhoStair
  rw [if_neg (by push_cast; linarith)]
  push_cast
  set s := Real.sqrt (2 * d - 1) with hs
  have hs2 : s ^ 2 = 2 * d - 1 := by
    rw [hs, Real.sq_sqrt]; have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set a : ℝ := 2 * ((mStar d : ℝ) + 1) - 1 with ha
  have hapos : 0 < a := by linarith [sqrt_pos' d hd]
  have : a + s ^ 2 / a > 2 * s := by
    rw [gt_iff_lt, ← sub_pos]
    have : a + s ^ 2 / a - 2 * s = (a - s) ^ 2 / a := by field_simp; ring
    rw [this]; apply div_pos (by nlinarith) hapos
  rw [hs2] at this
  convert this using 2


theorem upper (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
      1 - c / (N : ℝ) ^ mStar d ≤
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖adjPerp σ‖ ≤ 2 * Real.sqrt (2 * d - 1) + ε) := by
  obtain ⟨C, hC, -⟩ := prob_norm_adjPerp_ge_rhoStair d hd
  have hgap := rho_gap d hd
  set ρ := 2 * Real.sqrt (2 * d - 1) with hρ
  set ε' := min ε ((rhoStair d (mStar d + 1) - ρ) / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  have hε'1 : ε' ≤ ε := min_le_left _ _
  have hε'2 : ε' < rhoStair d (mStar d + 1) - rhoStair d (mStar d) := by
    rw [rho_mStar d hd]; have := min_le_right ε ((rhoStair d (mStar d + 1) - ρ) / 2); linarith
  have hm := mStar_le d hd
  refine ⟨C / ε' ^ (4 * (mStar d + 1)) * Real.log (2 * Real.exp 1 / ε'), fun N hN => ?_⟩
  have h := hC (mStar d) le_rfl hm ε' hε'pos hε'2 N hN
  rw [rho_mStar d hd] at h
  have hadd := uniformProb_add_ge_one
    (fun σ : Fin d → Equiv.Perm (Fin N) => ‖adjPerp σ‖ ≤ 2 * Real.sqrt (2 * d - 1) + ε)
    (fun σ : Fin d → Equiv.Perm (Fin N) => 2 * Real.sqrt (2 * d - 1) + ε' ≤ ‖adjPerp σ‖)
    (fun σ => by
      by_cases hh : 2 * Real.sqrt (2 * d - 1) + ε' ≤ ‖adjPerp σ‖
      · exact Or.inr hh
      · left; push Not at hh; linarith)
  have hNpos : (0 : ℝ) < (N : ℝ) ^ mStar d := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have : C / ((N : ℝ) ^ mStar d * ε' ^ (4 * (mStar d + 1))) * Real.log (2 * Real.exp 1 / ε')
      = C / ε' ^ (4 * (mStar d + 1)) * Real.log (2 * Real.exp 1 / ε') / (N : ℝ) ^ mStar d := by
    have : 0 < ε' ^ (4 * (mStar d + 1)) := by positivity
    field_simp
  rw [this] at h
  linarith

theorem lower (d : ℕ) (hd : 2 ≤ d) (hm : mStar d = 1) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < rhoStair d 2 - rhoStair d 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
        c / (N : ℝ) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖) := by
  have h := prob_norm_adjPerp_ge_of_lt_rhoStair d hd 2 (by omega) hd (2 * Real.sqrt (2 * d - 1) + ε)
    (by rw [rho_one d hd] at hε2; linarith) (1/2) (by norm_num)
  refine ⟨1/2, by norm_num, h.mono fun N hN => ?_⟩
  norm_num at hN ⊢
  exact hN


theorem mStar_eq_one_iff (d : ℕ) (hd : 2 ≤ d) : mStar d = 1 ↔ d ≤ 4 := by
  obtain ⟨h1, h2, h3⟩ := mStar_spec d hd
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ Real.sqrt (2 * d - 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * d - 1) ^ 2 = 2 * d - 1 := Real.sq_sqrt (by linarith)
  constructor
  · intro h
    rw [h] at h3
    push_cast at h3
    have : (d : ℝ) < 5 := by nlinarith
    have : d < 5 := by exact_mod_cast this
    omega
  · intro h
    have hd4 : (d : ℝ) ≤ 4 := by exact_mod_cast h
    have : Real.sqrt (2 * d - 1) < 3 := by nlinarith
    have hlt : (mStar d : ℝ) < 2 := by linarith
    have : mStar d < 2 := by exact_mod_cast hlt
    omega

end W2Sec3

theorem one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge_dev
    (d : ℕ) (hd : 2 ≤ d) :
    (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
      1 - c / (N : ℝ) ^ mStar d ≤
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖adjPerp σ‖ ≤ 2 * Real.sqrt (2 * d - 1) + ε)) ∧
    (mStar d = 1 ↔ d ≤ 4) ∧
    (mStar d = 1 → ∀ ε : ℝ, 0 < ε → ε < rhoStair d 2 - rhoStair d 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
        c / (N : ℝ) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖)) :=
  ⟨W2Sec3.upper d hd, W2Sec3.mStar_eq_one_iff d hd,
    fun hm ε hε hε2 => W2Sec3.lower d hd hm ε hε hε2⟩

end StrongConv

end
end

section
open StrongConv

open Filter


theorem solution
    (d : ℕ) (hd : 2 ≤ d) :
    (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
      1 - c / (N : ℝ) ^ mStar d ≤
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖adjPerp σ‖ ≤ 2 * Real.sqrt (2 * d - 1) + ε)) ∧
    (mStar d = 1 ↔ d ≤ 4) ∧
    (mStar d = 1 → ∀ ε : ℝ, 0 < ε → ε < rhoStair d 2 - rhoStair d 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
        c / (N : ℝ) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖)) := by
  exact StrongConv.one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge_dev d hd

end
