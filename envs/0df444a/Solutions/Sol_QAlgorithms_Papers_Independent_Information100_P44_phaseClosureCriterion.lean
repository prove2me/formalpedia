-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.phaseClosureCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:27:29.765046+00:00
-- url     : https://prove2.me/submissions/568da6e5-0404-4b41-b6e3-9e0fb2c32123

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_signs {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    ∀ s : Finset ι, (∀ j ∈ s, 0 ≤ a j ∧ a j ≤ M) →
    ∃ ε : ι → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ |∑ j ∈ s, ε j * a j| ≤ M := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simpa using hM⟩
  | insert j s hj ih =>
    intro h
    obtain ⟨ε, hε, hS⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨h0, h1⟩ := h j (Finset.mem_insert_self j s)
    set S := ∑ i ∈ s, ε i * a i with hSdef
    refine ⟨Function.update ε j (if 0 ≤ S then -1 else 1), ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst hij; simp only [Function.update_self]; split_ifs <;> simp
      · rw [Function.update_of_ne hij]; exact hε i
    · rw [Finset.sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update ε j (if 0 ≤ S then -1 else 1) i * a i = S := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (fun h => hj (by rw [← h]; exact hi))]
      rw [this]
      rw [abs_le] at hS ⊢
      split_ifs with hs <;> constructor <;> linarith

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    (∃ z : Fin n → ℂ, (∀ k, ‖z k‖ = a k) ∧ ∑ k, z k = 0) ↔
      ∀ k, a k ≤ ∑ j ∈ Finset.univ.erase k, a j := by
  constructor
  · rintro ⟨z, hz, hsum⟩ k
    have hk : z k = -∑ j ∈ Finset.univ.erase k, z j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
      linear_combination hsum
    rw [← hz k, hk, norm_neg]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun j _ => hz j)
  · intro h
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
    set s := Finset.univ.erase m with hs
    obtain ⟨ε, hε, hsig⟩ := g52c_signs a (a m) (ha m) s
      (fun j _ => ⟨ha j, hm j (Finset.mem_univ j)⟩)
    let term : ℝ → Fin n → ℂ := fun θ j =>
      if ε j = 1 then (a j : ℂ) else (a j : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    let w : ℝ → ℂ := fun θ => ∑ j ∈ s, term θ j
    have hcont : Continuous fun θ => ‖w θ‖ := by
      apply Continuous.norm
      apply continuous_finsetSum
      intro j _
      simp only [term]
      split_ifs
      · exact continuous_const
      · fun_prop
    have hw0 : ‖w 0‖ = ∑ j ∈ s, a j := by
      have : w 0 = ((∑ j ∈ s, a j : ℝ) : ℂ) := by
        simp only [w, term]; push_cast
        apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact Finset.sum_nonneg (fun j _ => ha j)
    have hwpi : ‖w Real.pi‖ = |∑ j ∈ s, ε j * a j| := by
      have : w Real.pi = ((∑ j ∈ s, ε j * a j : ℝ) : ℂ) := by
        simp only [w, term]; push_cast
        apply Finset.sum_congr rfl; intro j _
        rcases hε j with h1 | h1
        · simp [h1]
        · rw [if_neg (by rw [h1]; norm_num), h1, Complex.exp_pi_mul_I]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hmem : a m ∈ Set.Icc (‖w Real.pi‖) (‖w 0‖) := by
      rw [hw0, hwpi]; exact ⟨hsig, h m⟩
    obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' Real.pi_pos.le hcont.continuousOn hmem
    refine ⟨fun k => if k = m then -w θ else term θ k, ?_, ?_⟩
    · intro k
      by_cases hk : k = m
      · simp only [hk, if_true, norm_neg]; exact hθ
      · simp only [hk, if_false, term]
        split_ifs
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha k)]
        · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (ha k)]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
      simp only [if_true]
      have : ∑ x ∈ Finset.univ.erase m, (if x = m then -w θ else term θ x) = w θ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      rw [this]; ring
