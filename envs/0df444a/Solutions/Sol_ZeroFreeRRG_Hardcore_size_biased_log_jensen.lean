-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_biased_log_jensen
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:14.341446+00:00
-- url     : https://prove2.me/submissions/661c57fe-cb70-4906-ac35-6cced813bc48

import Mathlib
set_option autoImplicit false
open Set
open scoped Classical BigOperators

theorem solution {I : Type} [Fintype I] [Nonempty I] (x : I → ℝ) (hx : ∀ i, 0 < x i) :
    Real.log ((∑ i, x i) / (Fintype.card I : ℝ)) ≤
      (∑ i, x i * Real.log (x i)) / (∑ i, x i) := by
  classical
  let N : ℝ := Fintype.card I
  let T : ℝ := ∑ i, x i
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hT : 0 < T := by
    dsimp [T]
    apply Finset.sum_pos'
    · intro i hi
      exact (hx i).le
    · exact ⟨Classical.choice ‹Nonempty I›,Finset.mem_univ _,hx _⟩
  have hw : (∑ _i : I, (1/N:ℝ)) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp [N] at *
    field_simp
  have hj := Real.convexOn_mul_log.map_sum_le (t := Finset.univ) (w := fun _ : I => (1/N:ℝ))
    (p := x) (fun i hi => (div_pos (by norm_num) hN).le) hw (fun i hi => (hx i).le)
  simp only [smul_eq_mul,← Finset.mul_sum] at hj
  have hj' : (T/N)*Real.log (T/N) ≤ (∑ i, x i*Real.log (x i))/N := by
    simpa only [T,one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hj
  have hh := mul_le_mul_of_nonneg_left hj' hN.le
  have hN0 : N ≠ 0 := ne_of_gt hN
  field_simp at hh
  have hh' : T * Real.log (T/N) ≤ ∑ i, x i*Real.log (x i) := by nlinarith
  exact (le_div_iff₀ hT).2 (by simpa [mul_comm] using hh')
