-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hankel_four_extreme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:19.395909+00:00
-- url     : https://prove2.me/submissions/2e65ddcc-6b47-4dee-8af3-0fac4b125d0c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma X7H4_pairing_sub {n : ℕ} (a b : Part n) (y : Part n → ℝ) :
    pairing (Finsupp.single a (1:ℝ) - Finsupp.single b 1) y = y a - y b := by
  unfold pairing
  rw [Finsupp.sum_sub_index (fun _ _ _ => by ring)]
  simp

lemma X7H4_pairing_add {n : ℕ} (u w : Coeff n) (y : Part n → ℝ) :
    pairing (u + w) y = pairing u y + pairing w y := by
  unfold pairing
  rw [Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)]

lemma X7H4_symm {d : ℕ} (g : Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, g i j = (1/2) * ∑ i, ∑ j, (g i j + g j i) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => g j i)]
  ring

lemma X7H4_13 {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i ^ 3) * (∑ i, x i ^ 1) - (∑ i, x i ^ 2) * (∑ i, x i ^ 2) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [X7H4_symm]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
  have := mul_nonneg (mul_nonneg (hx i) (hx j)) (sq_nonneg (x i - x j))
  nlinarith [this]

def X7H4_P4 : Part 4 := ⟨[4], by decide⟩
def X7H4_P31 : Part 4 := ⟨[3,1], by decide⟩
def X7H4_P22 : Part 4 := ⟨[2,2], by decide⟩
def X7H4_P211 : Part 4 := ⟨[2,1,1], by decide⟩
def X7H4_P1111 : Part 4 := ⟨[1,1,1,1], by decide⟩

lemma X7H4_part (p : Part 4) : p = X7H4_P4 ∨ p = X7H4_P31 ∨ p = X7H4_P22 ∨
    p = X7H4_P211 ∨ p = X7H4_P1111 := by
  have : p.val = [4] ∨ p.val = [3,1] ∨ p.val = [2,2] ∨ p.val = [2,1,1] ∨
      p.val = [1,1,1,1] := by
    obtain ⟨l, h1, h2, h3⟩ := p
    simp only
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩
    · simp at h3
    · simp at h3; simp [h3]
    · simp at h1 h2 h3
      have : (a = 3 ∧ b = 1) ∨ (a = 2 ∧ b = 2) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · simp at h1 h2 h3
      have : a = 2 ∧ b = 1 ∧ c = 1 := by omega
      obtain ⟨rfl, rfl, rfl⟩ := this; simp
    · simp at h2 h3
      have : a = 1 ∧ b = 1 ∧ c = 1 ∧ e = 1 := by omega
      obtain ⟨rfl, rfl, rfl, rfl⟩ := this; simp
    · exfalso; simp at h2 h3; omega
  rcases this with h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))

lemma X7H4_ne_of_val {p q : Part 4} (h : p.val ≠ q.val) : p ≠ q := fun e => h (congrArg Subtype.val e)

@[simp] lemma X7H4_ne_P4_P31 : X7H4_P4 ≠ X7H4_P31 := X7H4_ne_of_val (by simp [X7H4_P4, X7H4_P31])
@[simp] lemma X7H4_ne_P4_P22 : X7H4_P4 ≠ X7H4_P22 := X7H4_ne_of_val (by simp [X7H4_P4, X7H4_P22])
@[simp] lemma X7H4_ne_P4_P211 : X7H4_P4 ≠ X7H4_P211 := X7H4_ne_of_val (by simp [X7H4_P4, X7H4_P211])
@[simp] lemma X7H4_ne_P4_P1111 : X7H4_P4 ≠ X7H4_P1111 := X7H4_ne_of_val (by simp [X7H4_P4, X7H4_P1111])
@[simp] lemma X7H4_ne_P31_P4 : X7H4_P31 ≠ X7H4_P4 := X7H4_ne_of_val (by simp [X7H4_P31, X7H4_P4])
@[simp] lemma X7H4_ne_P31_P22 : X7H4_P31 ≠ X7H4_P22 := X7H4_ne_of_val (by simp [X7H4_P31, X7H4_P22])
@[simp] lemma X7H4_ne_P31_P211 : X7H4_P31 ≠ X7H4_P211 := X7H4_ne_of_val (by simp [X7H4_P31, X7H4_P211])
@[simp] lemma X7H4_ne_P31_P1111 : X7H4_P31 ≠ X7H4_P1111 := X7H4_ne_of_val (by simp [X7H4_P31, X7H4_P1111])
@[simp] lemma X7H4_ne_P22_P4 : X7H4_P22 ≠ X7H4_P4 := X7H4_ne_of_val (by simp [X7H4_P22, X7H4_P4])
@[simp] lemma X7H4_ne_P22_P31 : X7H4_P22 ≠ X7H4_P31 := X7H4_ne_of_val (by simp [X7H4_P22, X7H4_P31])
@[simp] lemma X7H4_ne_P22_P211 : X7H4_P22 ≠ X7H4_P211 := X7H4_ne_of_val (by simp [X7H4_P22, X7H4_P211])
@[simp] lemma X7H4_ne_P22_P1111 : X7H4_P22 ≠ X7H4_P1111 := X7H4_ne_of_val (by simp [X7H4_P22, X7H4_P1111])
@[simp] lemma X7H4_ne_P211_P4 : X7H4_P211 ≠ X7H4_P4 := X7H4_ne_of_val (by simp [X7H4_P211, X7H4_P4])
@[simp] lemma X7H4_ne_P211_P31 : X7H4_P211 ≠ X7H4_P31 := X7H4_ne_of_val (by simp [X7H4_P211, X7H4_P31])
@[simp] lemma X7H4_ne_P211_P22 : X7H4_P211 ≠ X7H4_P22 := X7H4_ne_of_val (by simp [X7H4_P211, X7H4_P22])
@[simp] lemma X7H4_ne_P211_P1111 : X7H4_P211 ≠ X7H4_P1111 := X7H4_ne_of_val (by simp [X7H4_P211, X7H4_P1111])
@[simp] lemma X7H4_ne_P1111_P4 : X7H4_P1111 ≠ X7H4_P4 := X7H4_ne_of_val (by simp [X7H4_P1111, X7H4_P4])
@[simp] lemma X7H4_ne_P1111_P31 : X7H4_P1111 ≠ X7H4_P31 := X7H4_ne_of_val (by simp [X7H4_P1111, X7H4_P31])
@[simp] lemma X7H4_ne_P1111_P22 : X7H4_P1111 ≠ X7H4_P22 := X7H4_ne_of_val (by simp [X7H4_P1111, X7H4_P22])
@[simp] lemma X7H4_ne_P1111_P211 : X7H4_P1111 ≠ X7H4_P211 := X7H4_ne_of_val (by simp [X7H4_P1111, X7H4_P211])

lemma X7H4_pairing (f : Coeff 4) (y : Part 4 → ℝ) :
    pairing f y = f X7H4_P4 * y X7H4_P4 + f X7H4_P31 * y X7H4_P31 + f X7H4_P22 * y X7H4_P22
      + f X7H4_P211 * y X7H4_P211 + f X7H4_P1111 * y X7H4_P1111 := by
  classical
  unfold pairing
  rw [Finsupp.sum_of_support_subset f
    (s := {X7H4_P4, X7H4_P31, X7H4_P22, X7H4_P211, X7H4_P1111})
    (fun p _ => by rcases X7H4_part p with rfl | rfl | rfl | rfl | rfl <;> simp) _
    (fun _ _ => by ring)]
  rw [Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_pair (by simp)]
  ring

lemma X7H4_const (u : Coeff 4) (d : ℕ) :
    pairing u (spectralMoments (fun _ : Fin d => (1:ℝ))) =
      u X7H4_P4 * d + u X7H4_P31 * d^2 + u X7H4_P22 * d^2 + u X7H4_P211 * d^3
        + u X7H4_P1111 * d^4 := by
  rw [X7H4_pairing]
  simp [spectralMoments, X7H4_P4, X7H4_P31, X7H4_P22, X7H4_P211, X7H4_P1111]
  ring

lemma X7H4_key (u w : Coeff 4) (hu : u ∈ psdCone 4) (hw : w ∈ psdCone 4)
    (h : u + w = b31 - b22) : ∃ a : ℝ, 0 ≤ a ∧ u = a • (b31 - b22) := by
  have e : b31 - b22 = (Finsupp.single X7H4_P31 (1:ℝ) - Finsupp.single X7H4_P22 1 : Coeff 4) :=
    rfl
  have zero : ∀ d : ℕ, 0 < d → pairing u (spectralMoments (fun _ : Fin d => (1:ℝ))) = 0 := by
    intro d hd
    have h1 := hu d hd (fun _ => 1) (fun _ => by norm_num)
    have h2 := hw d hd (fun _ => 1) (fun _ => by norm_num)
    have h3 := congrArg (fun f => pairing f (spectralMoments (fun _ : Fin d => (1:ℝ)))) h
    simp only [X7H4_pairing_add, e, X7H4_pairing_sub] at h3
    simp [spectralMoments, X7H4_P31, X7H4_P22] at h3
    ring_nf at h3
    linarith
  have z1 := zero 1 (by norm_num)
  have z2 := zero 2 (by norm_num)
  have z3 := zero 3 (by norm_num)
  have z4 := zero 4 (by norm_num)
  rw [X7H4_const] at z1 z2 z3 z4
  push_cast at z1 z2 z3 z4
  have c4 : u X7H4_P4 = 0 := by linarith
  have c211 : u X7H4_P211 = 0 := by linarith
  have c1111 : u X7H4_P1111 = 0 := by linarith
  have c22 : u X7H4_P22 = - u X7H4_P31 := by linarith
  have pos := hu 2 (by norm_num) ![1, 2] (by intro i; fin_cases i <;> norm_num)
  rw [X7H4_pairing, c4, c211, c1111, c22] at pos
  simp [spectralMoments, X7H4_P4, X7H4_P31, X7H4_P22, X7H4_P211, X7H4_P1111,
    Fin.sum_univ_succ] at pos
  refine ⟨u X7H4_P31, ?_, ?_⟩
  · norm_num at pos
    change u X7H4_P31 * 25 ≤ u X7H4_P31 * 27 at pos
    linarith
  · ext p
    rw [e]
    rcases X7H4_part p with rfl | rfl | rfl | rfl | rfl <;>
      simp [c4, c211, c1111, c22]

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    b31-b22 ∈ psdCone 4 ∧ b31-b22 ∉ allCone 4 ∧ Extreme (psdCone 4) (b31-b22) := by
  have e : b31 - b22 = (Finsupp.single X7H4_P31 (1:ℝ) - Finsupp.single X7H4_P22 1 : Coeff 4) :=
    rfl
  have mem : b31 - b22 ∈ psdCone 4 := by
    intro d _ x hx
    rw [e, X7H4_pairing_sub]
    have := X7H4_13 x hx
    simpa [spectralMoments, X7H4_P31, X7H4_P22] using this
  refine ⟨mem, ?_, ?_, mem, ?_⟩
  · intro h
    have := h 2 (by norm_num) ![1, -1]
    rw [e, X7H4_pairing_sub] at this
    simp [spectralMoments, X7H4_P31, X7H4_P22, Fin.sum_univ_succ] at this
    norm_num at this
  · intro h0
    have := congrArg (fun f => f X7H4_P31) h0
    rw [e] at this
    simp at this
  · intro u hu w hw huw
    obtain ⟨a, ha, rfl⟩ := X7H4_key u w hu hw huw
    obtain ⟨b, hb, rfl⟩ := X7H4_key w _ hw hu (by rw [add_comm]; exact huw)
    exact ⟨a, b, ha, hb, rfl, rfl⟩


end
