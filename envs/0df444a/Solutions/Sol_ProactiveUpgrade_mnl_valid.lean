-- Prove2me | solution 1 for ProactiveUpgrade.mnl_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:59:58.480006+00:00
-- url     : https://prove2.me/submissions/4df695e3-1cbe-4c80-bae0-582d5cb5f713

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_mnlModel

open ProactiveUpgrade in
theorem solution {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (hb : 0 < b) (p : Fin m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hp : StrictMono p) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    IsValid (mnlModel a b p lam) ∧
      ∀ (i : Fin m), i.val + 1 < m →
        0 < (mnlModel a b p lam).q i ∧ (mnlModel a b p lam).q i < 1 := by
  have hD : 0 < 1 + ∑ k, Real.exp (a k - b * p k) := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => (Real.exp_pos (a k - b * p k)).le)
    linarith
  have hq : ∀ (i : Fin m), i.val + 1 < m →
      0 < (mnlModel a b p lam).q i ∧ (mnlModel a b p lam).q i < 1 := by
    intro i h
    show 0 < mnlQ a b p i ∧ mnlQ a b p i < 1
    unfold mnlQ
    rw [dif_pos h]
    have hij : i < succIdx i h := by
      rw [Fin.lt_iff_val_lt_val]
      show i.val < i.val + 1
      omega
    have hpij := hp hij
    have hE : Real.exp (a (succIdx i h) - b * p (succIdx i h)) <
        Real.exp (a (succIdx i h) - b * p i) := by
      rw [Real.exp_lt_exp]
      nlinarith [mul_lt_mul_of_pos_left hpij hb]
    have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase (succIdx i h), Real.exp (a k - b * p k) :=
      Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    have hE2 := Real.exp_pos (a (succIdx i h) - b * p (succIdx i h))
    have hden : 0 < 1 + Real.exp (a (succIdx i h) - b * p i) +
        ∑ k ∈ Finset.univ.erase (succIdx i h), Real.exp (a k - b * p k) := by
      have := Real.exp_pos (a (succIdx i h) - b * p i)
      linarith
    refine ⟨div_pos (sub_pos.mpr hE) hden, (div_lt_one hden).mpr ?_⟩
    linarith
  refine ⟨⟨hp_pos, hp, fun i => ?_, ?_, ?_, fun i h => ?_, ⟨hlam0, hlam1⟩⟩, hq⟩
  · exact div_nonneg (Real.exp_pos _).le hD.le
  · exact div_pos one_pos hD
  · show mnlBeta0 a b p + ∑ i, mnlBeta a b p i = 1
    unfold mnlBeta0 mnlBeta
    rw [← Finset.sum_div, ← add_div, div_self hD.ne']
  · exact ⟨(hq i h).1.le, (hq i h).2.le⟩
