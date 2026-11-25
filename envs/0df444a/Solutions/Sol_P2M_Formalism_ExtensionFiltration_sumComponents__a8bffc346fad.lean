-- Prove2me | solution 1 for P2M_Formalism_ExtensionFiltration_sumComponents__a8bffc346fad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:13.291334+00:00
-- url     : https://prove2.me/submissions/aca8f6df-80f6-4393-a310-e9070cc32db3

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CombinedAverageDegreeBoundOf
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SumComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : SumComponents := by
  intro ι _ _ T D A cs X cc z ρ R1 R2 Bn δ' h δ dc degc hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1
    hR1 hR2 hBn hδ' hδ hdc hh hdeg havg
  have ha0 : 0 ≤ T - 3 * D - 4 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hK0 : 0 ≤ A * Real.log (max A 1) :=
    mul_nonneg hA.le (Real.log_nonneg (le_max_right _ _))

  have hlog : ∀ x : ℝ, 0 ≤ x → A * Real.log (2 + x) ≤ x + A * Real.log (max A 1) + 2 := by
    intro x hx
    have hpos : 0 < 2 + x := by linarith
    rcases le_or_gt 1 A with h1 | h1
    · rw [max_eq_left h1]
      have h2 : Real.log ((2 + x) / A) ≤ (2 + x) / A - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hpos hA)
      rw [Real.log_div hpos.ne' hA.ne'] at h2
      have h3 : A * (Real.log (2 + x) - Real.log A) ≤ A * ((2 + x) / A - 1) :=
        mul_le_mul_of_nonneg_left h2 hA.le
      have h4 : A * ((2 + x) / A - 1) = 2 + x - A := by
        field_simp
      linarith
    · rw [max_eq_right h1.le, Real.log_one, mul_zero]
      have h2 : Real.log (2 + x) ≤ 2 + x - 1 := Real.log_le_sub_one_of_pos hpos
      linarith [mul_le_mul_of_nonneg_left h2 hA.le,
        mul_nonneg (sub_nonneg.2 h1.le) (by linarith : (0:ℝ) ≤ 1 + x)]
  set N : ℝ := (T - 3 * D - 4) * cs + 2 * cs * (3 * D + 4) + (A * Real.log (max A 1) + 2)
    + R1 + 2 * z * R2 with hN
  have hwpos : ∀ c, 0 < Bn * δ c := fun c => mul_pos hBn (by linarith [(hδ c).1])
  have hper : ∀ c, Bn * δ c * ((T - 3 * D - 4) * (h c + cs) - N) ≤ degc c := by
    intro c
    have habs : |h c| ≤ h c + 2 * cs := by
      rcases abs_cases (h c) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hh c]
    have hl := hlog |h c| (abs_nonneg _)
    have hm : (3 * D + 4) * |h c| ≤ (3 * D + 4) * (h c + 2 * cs) :=
      mul_le_mul_of_nonneg_left habs (by linarith)
    have hf : (T - 3 * D - 4) * (h c + cs) - N ≤
        T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2 := by
      have e : (T - 3 * D - 4) * (h c + cs) - N = T * h c - (3 * D + 4) * (h c + 2 * cs)
          - (A * Real.log (max A 1) + 2) - R1 - 2 * z * R2 := by
        rw [hN]; ring
      rw [e]; linarith
    calc Bn * δ c * ((T - 3 * D - 4) * (h c + cs) - N)
        ≤ Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1
            - 2 * z * R2) := mul_le_mul_of_nonneg_left hf (hwpos c).le
      _ ≤ degc c := hdeg c
  set W : ℝ := ∑ c, Bn * δ c with hWdef
  set S : ℝ := ∑ c, dc c with hSdef
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  set m : ℝ := max 0 ((1 - ρ) * cs - X - cc) with hmdef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  have hm0 : 0 ≤ m := le_max_left _ _
  have hmge : (1 - ρ) * cs - X - cc ≤ m := le_max_right _ _
  have hsum1 : ∑ c, Bn * δ c * ((T - 3 * D - 4) * (h c + cs) - N) ≤ ∑ c, degc c :=
    Finset.sum_le_sum (fun c _ => hper c)
  have hsplit : ∑ c, Bn * δ c * ((T - 3 * D - 4) * (h c + cs) - N)
      = ∑ c, Bn * δ c * ((T - 3 * D - 4) * (h c + cs)) - N * W := by
    rw [hWdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have hlow : Bn * δ' * ((T - 3 * D - 4) * ∑ c, (h c + cs))
      ≤ ∑ c, Bn * δ c * ((T - 3 * D - 4) * (h c + cs)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    have h1 : 0 ≤ (T - 3 * D - 4) * (h c + cs) := mul_nonneg ha0 (by linarith [hh c])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hδ c).1 hBn.le) h1
  have havg' : m * n ≤ ∑ c, (h c + cs) := (le_div_iff₀ hn).1 havg
  have hδρ : ∀ c, (1 - ρ) * δ c ≤ δ' := by
    intro c
    have h1 := (hδ c).2
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  have hW : (1 - ρ) * W ≤ n * (Bn * δ') := by
    calc (1 - ρ) * W = ∑ c, Bn * ((1 - ρ) * δ c) := by
          rw [hWdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by ring)
      _ ≤ ∑ _c : ι, Bn * δ' :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hδρ c) hBn.le)
      _ = n * (Bn * δ') := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hWS : W ≤ S := Finset.sum_le_sum (fun c _ => (hdc c).1)
  have hW0 : 0 < W := Finset.sum_pos (fun c _ => hwpos c) Finset.univ_nonempty
  have hS0 : 0 < S := lt_of_lt_of_le hW0 hWS
  have e1 : Bn * δ' * ((T - 3 * D - 4) * (m * n))
      ≤ Bn * δ' * ((T - 3 * D - 4) * ∑ c, (h c + cs)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left havg' ha0)
      (mul_nonneg hBn.le hδ'.le)
  have e2 : (T - 3 * D - 4) * m * ((1 - ρ) * W) ≤ (T - 3 * D - 4) * m * (n * (Bn * δ')) :=
    mul_le_mul_of_nonneg_left hW (mul_nonneg ha0 hm0)
  have hmain : W * ((T - 3 * D - 4) * m * (1 - ρ) - N) ≤ ∑ c, degc c := by
    linarith [hsum1, hsplit, hlow, e1, e2]

  have hm1 : (1 - 2 * ρ) * cs - X - cc ≤ (1 - ρ) * m := by
    linarith [mul_le_mul_of_nonneg_left hmge (by linarith : (0:ℝ) ≤ 1 - ρ),
      mul_nonneg (mul_nonneg hρ0 hρ0) hcs, mul_nonneg hρ0 (by linarith : (0:ℝ) ≤ X + cc)]
  have hm2 : (T - 3 * D - 4) * ((1 - 2 * ρ) * cs - X - cc) ≤ (T - 3 * D - 4) * ((1 - ρ) * m) :=
    mul_le_mul_of_nonneg_left hm1 ha0
  have hm3 : (T - 3 * D - 4) * (2 * ρ * cs + X + cc) ≤ T * (2 * ρ * cs + X + cc) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcsTz : 0 ≤ cs * T * z := mul_nonneg (mul_nonneg hcs hT0) hz0
  have hzR : 0 ≤ z * R2 := mul_nonneg hz0 hR2
  have hPN : -(T * (X + cc)) - cs * (6 * D + 10 + T * (z + 2 * ρ)) - (A * Real.log (max A 1) + 4)
      - R1 - 2 * z * R2 ≤ (T - 3 * D - 4) * m * (1 - ρ) - N := by
    rw [hN]; linarith [hm2, hm3, hcsTz]
  have hL : -(T * (X + cc)) - cs * (6 * D + 10 + T * (z + 2 * ρ)) - (A * Real.log (max A 1) + 4)
      - R1 - 2 * z * R2 ≤ 0 := by
    linarith [mul_nonneg hT0 (by linarith : (0:ℝ) ≤ X + cc),
      mul_nonneg hcs (by positivity : (0:ℝ) ≤ 6 * D + 10 + T * (z + 2 * ρ))]
  rw [le_div_iff₀ hS0]
  by_cases hq : 0 ≤ (T - 3 * D - 4) * m * (1 - ρ) - N
  · linarith [mul_nonneg hW0.le hq, mul_le_mul_of_nonneg_right hL hS0.le]
  · have h1 := mul_le_mul_of_nonpos_right hWS (le_of_lt (not_le.1 hq))
    have h2 := mul_le_mul_of_nonneg_right hPN hS0.le
    linarith [h1, h2, hmain]
end Formalism.ExtensionFiltration
