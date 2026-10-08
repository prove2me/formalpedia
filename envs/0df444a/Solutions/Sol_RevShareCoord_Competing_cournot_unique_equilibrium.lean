-- Prove2me | solution 1 for RevShareCoord.Competing.cournot_unique_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:07:01.416995+00:00
-- url     : https://prove2.me/submissions/1225fd91-be4d-4979-a23f-29dc055b568d

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

set_option autoImplicit false

namespace CournotAux836

open Finset RevShareCoord.Competing

theorem profit_update {n : ℕ} (β w : ℝ) (q : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    retailerProfit (cournotRevenue β) 1 (fun _ => w) (Function.update q i x) i
      = x * (1 - w - β * (∑ j, q j - q i)) - x * x := by
  have hs : ∑ j ∈ univ.erase i, Function.update q i x j = ∑ j, q j - q i := by
    rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) x q)]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [retailerProfit, cournotRevenue, Function.update_self, hs]
  ring

theorem profit_self {n : ℕ} (β w : ℝ) (q : Fin n → ℝ) (i : Fin n) :
    retailerProfit (cournotRevenue β) 1 (fun _ => w) q i
      = q i * (1 - w - β * (∑ j, q j - q i)) - q i * q i := by
  have := profit_update β w q i (q i)
  rwa [Function.update_eq_self] at this

/-- Best-response dichotomy. -/
theorem br {A p : ℝ} (hp : 0 ≤ p) (h : ∀ x : ℝ, 0 ≤ x → x * A - x * x ≤ p * A - p * p) :
    (0 ≤ A ∧ 2 * p = A) ∨ (A < 0 ∧ p = 0) := by
  rcases le_or_gt 0 A with hA | hA
  · left
    refine ⟨hA, ?_⟩
    have := h (A / 2) (by linarith)
    nlinarith [sq_nonneg (2 * p - A)]
  · right
    refine ⟨hA, ?_⟩
    have := h 0 le_rfl
    nlinarith

theorem den_pos {n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) : 0 < 2 + β * ((n : ℝ) - 1) := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end CournotAux836

open Finset RevShareCoord.Competing in
theorem solution {n : ℕ} (β w : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hw : w < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => w) (fun _ => cournotQN β n w) ∧
      ∀ q : Fin n → ℝ, IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
        q = fun _ => cournotQN β n w := by
  have hD := CournotAux836.den_pos (n := n) β hβ0 hβ1
  set a := cournotQN β n w with ha_def
  have ha : a * (2 + β * ((n : ℝ) - 1)) = 1 - w := by
    rw [ha_def, cournotQN]; field_simp
  have ha0 : 0 ≤ a := by
    rw [ha_def, cournotQN]; exact div_nonneg (by linarith) hD.le
  refine ⟨⟨fun _ => ha0, ?_⟩, ?_⟩
  · intro i x hx
    rw [CournotAux836.profit_update, CournotAux836.profit_self]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [sq_nonneg (x - a)]
  · intro q ⟨hq0, hq⟩
    set T := ∑ j, q j with hT
    have hcase : ∀ i, (0 ≤ 1 - w - β * T ∧ (2 - β) * q i = 1 - w - β * T) ∨
        (1 - w - β * T < 0 ∧ q i = 0) := by
      intro i
      have h := CournotAux836.br (A := 1 - w - β * (T - q i)) (hq0 i) (fun x hx => by
        have := hq i x hx
        rw [CournotAux836.profit_update, CournotAux836.profit_self] at this
        linarith)
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; constructor <;> nlinarith [hq0 i]
      · right; refine ⟨?_, h2⟩; rw [h2] at h1; linarith
    have hC : 0 ≤ 1 - w - β * T := by
      by_contra hneg
      push Not at hneg
      have hz : ∀ i, q i = 0 := fun i => by
        rcases hcase i with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1 (not_le.mpr hneg)
        · exact h2
      have : T = 0 := by rw [hT]; simp [hz]
      rw [this] at hneg; linarith
    have h2 : (2:ℝ) - β ≠ 0 := by linarith
    set c := (1 - w - β * T) / (2 - β) with hc
    have hc2 : (2 - β) * c = 1 - w - β * T := by rw [hc]; field_simp
    have hval : ∀ i, q i = c := fun i => by
      rcases hcase i with ⟨_, h2'⟩ | ⟨h1, _⟩
      · rw [hc, eq_div_iff h2]; linarith
      · linarith
    have hT' : T = n * c := by
      rw [hT]; simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    funext i
    rw [hval i]
    rw [hT'] at hc2
    rw [ha_def, cournotQN, eq_div_iff hD.ne']
    linarith
