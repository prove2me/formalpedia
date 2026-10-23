-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hankel_six_not_extreme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:21.158992+00:00
-- url     : https://prove2.me/submissions/c844500c-c073-4b80-ac53-e3e875169c38

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma X7H6_pairing_sub {n : ℕ} (a b : Part n) (y : Part n → ℝ) :
    pairing (Finsupp.single a (1:ℝ) - Finsupp.single b 1) y = y a - y b := by
  unfold pairing
  rw [Finsupp.sum_sub_index (fun _ _ _ => by ring)]
  simp

lemma X7H6_symm {d : ℕ} (g : Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, g i j = (1/2) * ∑ i, ∑ j, (g i j + g j i) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => g j i)]
  ring

lemma X7H6_sm {d : ℕ} (x : Fin d → ℝ) (l : List ℕ) (h) :
    spectralMoments x (⟨l, h⟩ : Part l.sum) = (l.map (fun k => ∑ i, x i ^ k)).prod := rfl

/-- p1 p5 - p3^2 ≥ 0 on nonnegative spectra. -/
lemma X7H6_15 {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i ^ 5) * (∑ i, x i ^ 1) - (∑ i, x i ^ 3) * (∑ i, x i ^ 3) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [X7H6_symm]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
  have := mul_nonneg (mul_nonneg (hx i) (hx j)) (sq_nonneg (x i ^ 2 - x j ^ 2))
  nlinarith [this]

lemma X7H6_15_42 {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i ^ 5) * (∑ i, x i ^ 1) - (∑ i, x i ^ 4) * (∑ i, x i ^ 2) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [X7H6_symm]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
  have h1 := mul_nonneg (mul_nonneg (hx i) (hx j)) (sq_nonneg (x i - x j))
  have h2 : 0 ≤ x i ^ 2 + x i * x j + x j ^ 2 := by nlinarith [hx i, hx j, mul_nonneg (hx i) (hx j)]
  have := mul_nonneg h1 h2
  nlinarith [this]

lemma X7H6_42_33 {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ (∑ i, x i ^ 4) * (∑ i, x i ^ 2) - (∑ i, x i ^ 3) * (∑ i, x i ^ 3) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [X7H6_symm]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
  have := sq_nonneg (x i * x j * (x i - x j))
  nlinarith [this]

def X7H6_P51 : Part 6 := ⟨[5,1], by decide⟩
def X7H6_P42 : Part 6 := ⟨[4,2], by decide⟩
def X7H6_P33 : Part 6 := ⟨[3,3], by decide⟩

lemma X7H6_ne1 : X7H6_P42 ≠ X7H6_P51 := by
  intro h; have := congrArg Subtype.val h; simp [X7H6_P42, X7H6_P51] at this
lemma X7H6_ne2 : X7H6_P42 ≠ X7H6_P33 := by
  intro h; have := congrArg Subtype.val h; simp [X7H6_P42, X7H6_P33] at this

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    b51-b33 ∈ psdCone 6 ∧ b51-b33 ∉ allCone 6 ∧ ¬ Extreme (psdCone 6) (b51-b33) := by
  have e51 : b51 - b33 = (Finsupp.single X7H6_P51 (1:ℝ) - Finsupp.single X7H6_P33 1 : Coeff 6) := rfl
  set P42 := X7H6_P42
  let u : Coeff 6 := Finsupp.single X7H6_P51 (1:ℝ) - Finsupp.single P42 1
  let w : Coeff 6 := Finsupp.single P42 (1:ℝ) - Finsupp.single X7H6_P33 1
  refine ⟨?_, ?_, ?_⟩
  · intro d _ x hx
    rw [e51, X7H6_pairing_sub]
    have := X7H6_15 x hx
    simpa [spectralMoments, X7H6_P51, X7H6_P33] using this
  · intro h
    have := h 2 (by norm_num) ![2, -1]
    rw [e51, X7H6_pairing_sub] at this
    simp [spectralMoments, X7H6_P51, X7H6_P33, Fin.sum_univ_succ] at this
    norm_num at this
  · rintro ⟨_, _, hext⟩
    have hu : u ∈ psdCone 6 := by
      intro d _ x hx
      simp only [u]; rw [X7H6_pairing_sub]
      have := X7H6_15_42 x hx
      simpa [spectralMoments, P42, X7H6_P42, X7H6_P51, X7H6_P33] using this
    have hw : w ∈ psdCone 6 := by
      intro d _ x _
      simp only [w]; rw [X7H6_pairing_sub]
      have := X7H6_42_33 x
      simpa [spectralMoments, P42, X7H6_P42, X7H6_P51, X7H6_P33] using this
    obtain ⟨a, b, _, _, hua, _⟩ := hext u hu w hw (by rw [e51]; simp [u, w])
    have := congrArg (fun f => f P42) hua
    simp [u, e51, P42, Finsupp.single_apply, X7H6_ne1, X7H6_ne2] at this


end
