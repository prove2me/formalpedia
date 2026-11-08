-- Prove2me | solution 1 for OnlineGND.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:34:08.31441+00:00
-- url     : https://prove2.me/submissions/b1e08ee8-2f2f-4863-bd20-fbddeab535ec

import Definitions.Def_OnlineGND_DoS

namespace Aux_OnlineGND_l1

theorem rpow_split (y a : ℝ) (hy : 0 ≤ y) (ha : 1 ≤ a) : y ^ a = y * y ^ (a - 1) := by
  rcases hy.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by linarith), zero_mul]
  · rw [Real.rpow_sub_one h.ne']
    field_simp

end Aux_OnlineGND_l1

open OnlineGND in
theorem solution {E : Type*} [Fintype E] (σ ξ α : E → ℝ) (e : E) (hσ : 0 ≤ σ e) (hξ : 0 < ξ e)
    (hα : 1 ≤ α e) (x : ℝ) (hx : x = 0 ∨ 1 ≤ x) :
    1 / 2 * hFun σ ξ α e x ≤ dosCost σ ξ α e x ∧
      dosCost σ ξ α e x ≤
        max (qPar σ ξ α e) 1 * (ξ e * qPar σ ξ α e ^ (α e - 1)) * x + ξ e * x ^ α e ∧
      max (qPar σ ξ α e) 1 * (ξ e * qPar σ ξ α e ^ (α e - 1)) * x + ξ e * x ^ α e ≤
        max (qPar σ ξ α e) 1 * hFun σ ξ α e x := by
  have hq0 : 0 ≤ qPar σ ξ α e := Real.rpow_nonneg (div_nonneg hσ hξ.le) _
  have hqa : qPar σ ξ α e ^ α e = σ e / ξ e := by
    unfold qPar
    rw [one_div, Real.rpow_inv_rpow (div_nonneg hσ hξ.le) (by linarith)]
  have hσeq : σ e = ξ e * qPar σ ξ α e ^ α e := by
    rw [hqa]; field_simp
  obtain ⟨q, hq⟩ : ∃ q, q = qPar σ ξ α e := ⟨_, rfl⟩
  rw [← hq] at hq0 hσeq ⊢
  unfold hFun
  rw [← hq]
  have hM1 : 1 ≤ max q 1 := le_max_right _ _
  have hMq : q ≤ max q 1 := le_max_left _ _
  have hqp : 0 ≤ q ^ (α e - 1) := Real.rpow_nonneg hq0 _
  have hsplitq := Aux_OnlineGND_l1.rpow_split q (α e) hq0 hα
  rcases hx with hx | hx
  · subst hx
    have h0 : (0 : ℝ) ^ α e = 0 := Real.zero_rpow (by linarith)
    unfold dosCost
    simp only [if_true, h0]
    refine ⟨by simp, by simp, by simp⟩
  · have hx0 : x ≠ 0 := by linarith
    unfold dosCost
    rw [if_neg hx0, hσeq]
    have hxp : 0 ≤ x ^ α e := Real.rpow_nonneg (by linarith) _
    have hsplitx := Aux_OnlineGND_l1.rpow_split x (α e) (by linarith) hα
    have hkey : q ^ (α e - 1) * x ≤ q ^ α e + x ^ α e := by
      rcases le_or_gt q x with h | h
      · have : q ^ (α e - 1) ≤ x ^ (α e - 1) := Real.rpow_le_rpow hq0 h (by linarith)
        have hxp1 : 0 ≤ x ^ (α e - 1) := Real.rpow_nonneg (by linarith) _
        nlinarith
      · nlinarith
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · have : q ^ α e ≤ max q 1 * q ^ (α e - 1) * x := by
        rw [hsplitq]
        have h1 : q * q ^ (α e - 1) ≤ max q 1 * q ^ (α e - 1) :=
          mul_le_mul_of_nonneg_right hMq hqp
        have h2 : 0 ≤ max q 1 * q ^ (α e - 1) := by positivity
        nlinarith
      nlinarith
    · have : 0 ≤ ξ e * x ^ α e := by positivity
      nlinarith
