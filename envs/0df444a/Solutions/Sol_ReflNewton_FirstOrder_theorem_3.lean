-- Prove2me | solution 1 for ReflNewton.FirstOrder.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:02:08.884677+00:00
-- url     : https://prove2.me/submissions/66a82885-fc9d-4b8b-ba22-365fb3b5c183

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_FirstOrder_Setting
open Filter Topology

open ReflNewton.FirstOrder in
theorem solution {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : ℕ → E n)
    (hx : ∀ k, x k ∈ intBox l u) (hcc : IsConstraintCompatible l u f x s) :
    let br : ℕ → Fin n → EReal := fun k j =>
      if 0 < s k j then
        if u j = ⊤ then ⊤ else (((u j).toReal - x k j) / s k j : ℝ)
      else if s k j < 0 then
        if l j = ⊥ then ⊤ else (((l j).toReal - x k j) / s k j : ℝ)
      else ⊤
    ∃ c : ℝ, 0 < c ∧ ∀ k j,
      br k j = ((|vVec l u f (x k) j| / |s k j| : ℝ) : EReal) →
        (c : EReal) ≤ br k j := by
  intro br
  obtain ⟨K, hK⟩ := (isBounded_iff_forall_norm_le).mp hcc
  have hK0 : ∀ k, ‖dInvSq l u f (x k) (s k)‖ ≤ K := fun k => hK _ ⟨k, rfl⟩
  refine ⟨1 / (|K| + 1), by positivity, ?_⟩
  intro k j hbr
  set r := |vVec l u f (x k) j| / |s k j| with hr
  -- r > 0
  have hrpos : 0 < r := by
    obtain ⟨hl, hu⟩ := hx k j
    have hbr' := hbr
    simp only [br] at hbr'
    split_ifs at hbr' with h1 h2 h3 h4
    · exact absurd hbr' (EReal.top_ne_coe r)
    · have hune : u j ≠ ⊤ := h2
      have hunb : u j ≠ ⊥ := ne_bot_of_gt hu
      have hxu : x k j < (u j).toReal := by
        rw [← EReal.coe_toReal hune hunb] at hu
        exact EReal.coe_lt_coe_iff.mp hu
      have heq : ((u j).toReal - x k j) / s k j = r := EReal.coe_injective hbr'
      rw [← heq]
      exact div_pos (by linarith) h1
    · exact absurd hbr' (EReal.top_ne_coe r)
    · have hlne : l j ≠ ⊥ := h4
      have hlnt : l j ≠ ⊤ := ne_top_of_lt hl
      have hlx : (l j).toReal < x k j := by
        rw [← EReal.coe_toReal hlnt hlne] at hl
        exact EReal.coe_lt_coe_iff.mp hl
      have heq : ((l j).toReal - x k j) / s k j = r := EReal.coe_injective hbr'
      rw [← heq]
      exact div_pos_of_neg_of_neg (by linarith) h3
    · exact absurd hbr' (EReal.top_ne_coe r)
  have hv : vVec l u f (x k) j ≠ 0 := by
    intro h; rw [hr, h, abs_zero, zero_div] at hrpos; exact lt_irrefl _ hrpos
  have hs : s k j ≠ 0 := by
    intro h; rw [hr, h, abs_zero, div_zero] at hrpos; exact lt_irrefl _ hrpos
  have hcoord : |s k j| / |vVec l u f (x k) j| ≤ |K| := by
    have h1 := PiLp.norm_apply_le (dInvSq l u f (x k) (s k)) j
    have h2 : (dInvSq l u f (x k) (s k)) j = s k j / |vVec l u f (x k) j| := rfl
    rw [h2, Real.norm_eq_abs, abs_div, abs_abs] at h1
    exact (h1.trans (hK0 k)).trans (le_abs_self K)
  rw [hbr]
  apply EReal.coe_le_coe_iff.mpr
  have hva : 0 < |vVec l u f (x k) j| := abs_pos.mpr hv
  have hsa : 0 < |s k j| := abs_pos.mpr hs
  have hinv : r = 1 / (|s k j| / |vVec l u f (x k) j|) := by rw [hr, one_div_div]
  rw [hinv]
  apply one_div_le_one_div_of_le (div_pos hsa hva)
  linarith
