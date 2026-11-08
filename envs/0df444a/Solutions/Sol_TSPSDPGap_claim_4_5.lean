-- Prove2me | solution 1 for TSPSDPGap.claim_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:09:54.228215+00:00
-- url     : https://prove2.me/submissions/1f948148-c8a4-46cc-87e1-91175e8b43e6

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
open scoped Kronecker

namespace Aux_TSPclaim45
open TSPSDPGap

lemma diagY (g n : ℕ) (hn : (n : ℝ) ≠ 0) (x : Fin n × Fin n) : Ymat g n x x = 1 / n := by
  rw [Ymat, Matrix.of_apply, if_pos rfl, if_pos rfl]
  field_simp <;> ring

lemma traceY (g n : ℕ) (hn : (n : ℝ) ≠ 0) (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ)
    (c : Fin n × Fin n → ℝ) (hM : ∀ x z, x ≠ z → M x z = 0) (hc : ∀ x, M x x = c x) :
    Matrix.trace (M * Ymat g n) = ∑ x, c x * (1 / n) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [hc, diagY g n hn]
  · intro z _ hz
    rw [hM x z (Ne.symm hz), zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

end Aux_TSPclaim45

open TSPSDPGap in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ j : Fin n,
      Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ Matrix.single j j (1 : ℝ)) * Ymat g n) = 1) ∧
    (∀ j : Fin n,
      Matrix.trace ((Matrix.single j j (1 : ℝ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Ymat g n) = 1) := by
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [Aux_TSPclaim45.traceY g n hn _ (fun x => if j = x.2 then 1 else 0)]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [hn]
    · intro x z hxz
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases h1 : x.1 = z.1
      · by_cases h2 : j = x.2 ∧ j = z.2
        · exact absurd (Prod.ext h1 (h2.1.symm.trans h2.2)) hxz
        · simp [h2]
      · simp [h1]
    · intro x
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases h : j = x.2 <;> simp [h]
  · rw [Aux_TSPclaim45.traceY g n hn _ (fun x => if j = x.1 then 1 else 0)]
    · rw [Fintype.sum_prod_type]
      simp [hn]
    · intro x z hxz
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases h1 : j = x.1 ∧ j = z.1
      · by_cases h2 : x.2 = z.2
        · exact absurd (Prod.ext (h1.1.symm.trans h1.2) h2) hxz
        · simp [h2]
      · simp [h1]
    · intro x
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases h : j = x.1 <;> simp [h]
