-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_log_partition_jensen
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:14.44403+00:00
-- url     : https://prove2.me/submissions/e08d7c81-b965-4718-86d8-4c5639199d41

import Theorems.Thm_ZeroFreeRRG_Hardcore_size_biased_log_jensen
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_weights_sum_one
import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t) (d n : ℕ)
    [Nonempty (Matching n d)] :
    Real.log (an m d n t) ≤ plantedPinnedE m t s d n (fun M _ _ => Real.log (normZ m t M)) := by
  classical
  let T : ℝ := ∑ M : Matching n d, normZ m t M
  let N : ℝ := Fintype.card (Matching n d)
  have hN : N ≠ 0 := by dsimp [N]; exact_mod_cast Fintype.card_ne_zero
  have hZ (M : Matching n d) : 0 < normZ m t M := normalized_partition_positive m hm t ht d n M
  have hT : T ≠ 0 := by
    have hh : 0 < T := by
      dsimp [T]
      apply Finset.sum_pos'
      · intro M hM
        exact (hZ M).le
      · exact ⟨Classical.choice ‹Nonempty (Matching n d)›,Finset.mem_univ _,hZ _⟩
    exact ne_of_gt hh
  have han : an m d n t = T/N := by rfl
  have hsum (M : Matching n d) : (∑ σ : Fin n → m.Spin, planted m t M σ) = normZ m t M/T := by
    simp only [planted, ← Finset.sum_div]
    change normZ m t M / (N * an m d n t) = normZ m t M / T
    rw [han]
    field_simp
  have hEq : plantedPinnedE m t s d n (fun M _ _ => Real.log (normZ m t M)) =
      (∑ M : Matching n d, normZ m t M * Real.log (normZ m t M))/T := by
    unfold plantedPinnedE
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro M hM
    calc
      _ = (∑ σ : Fin n → m.Spin, planted m t M σ) * Real.log (normZ m t M) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro σ hσ
        calc
          _ = (planted m t M σ * Real.log (normZ m t M)) * (∑ U : Finset (Fin n), revealProb s U) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U hU
            ring
          _ = _ := by rw [reveal_weights_sum_one n s,mul_one]
      _ = _ := by rw [hsum]; ring
  rw [han,hEq]
  exact size_biased_log_jensen (fun M : Matching n d => normZ m t M) hZ
