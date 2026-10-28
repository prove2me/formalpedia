-- Prove2me | solution 1 for RegretMatching.Main.step_M3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:23:06.140655+00:00
-- url     : https://prove2.me/submissions/a7ea99c4-9be9-48ce-bdde-76e3367618ff

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open RegretMatching.Main in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (t v : ℕ), 1 ≤ t → 1 ≤ v → ∀ (h : Fin (t + v) → (∀ i, S i)) (j k : S i),
      |regretR u h i j k - regretR u (fun τ : Fin t => h (Fin.castAdd v τ)) i j k|
        ≤ C * ((v : ℝ) / t) := by
  have s0 : ∀ i, S i := fun i => Classical.arbitrary (S i)
  have hM0 : 0 ≤ M i := (abs_nonneg _).trans (hM i s0)
  refine ⟨4 * M i, ?_⟩
  intro t v ht hv h j k
  set g : (∀ i, S i) → ℝ := fun s => if s i = j then u i (Function.update s i k) - u i s else 0
    with hgdef
  have hg : ∀ s, |g s| ≤ 2 * M i := by
    intro s
    simp only [hgdef]
    split_ifs
    · have h1 := hM i (Function.update s i k)
      have h2 := hM i s
      exact (abs_sub _ _).trans (by linarith)
    · simp; linarith
  have hsumbound : ∀ (n : ℕ) (q : Fin n → (∀ i, S i)), |∑ τ, g (q τ)| ≤ 2 * M i * n := by
    intro n q
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n)) (fun τ => |g (q τ)|) (2 * M i)
      (fun τ _ => hg (q τ))
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at this
    linarith
  have hD : ∀ (n : ℕ) (q : Fin n → (∀ i, S i)),
      regretD u q i j k = (1 / (n : ℝ)) * ∑ τ, g (q τ) := by
    intro n q
    unfold regretD
    rw [Finset.sum_filter]
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ τ : Fin t, g (h (Fin.castAdd v τ)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ τ : Fin v, g (h (Fin.natAdd t τ)) := ⟨_, rfl⟩
  have hAb : |A| ≤ 2 * M i * t := hA ▸ hsumbound t (fun τ => h (Fin.castAdd v τ))
  have hBb : |B| ≤ 2 * M i * v := hB ▸ hsumbound v (fun τ => h (Fin.natAdd t τ))
  have h1 : regretD u h i j k = (1 / ((t : ℝ) + v)) * (A + B) := by
    rw [hD, Fin.sum_univ_add, hA, hB]
    push_cast
    rfl
  have h2 : regretD u (fun τ : Fin t => h (Fin.castAdd v τ)) i j k = (1 / (t : ℝ)) * A := by
    rw [hD, hA]
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  have hvp : (0 : ℝ) < v := by exact_mod_cast hv
  have hdiff : |regretD u h i j k - regretD u (fun τ : Fin t => h (Fin.castAdd v τ)) i j k|
      ≤ 4 * M i * ((v : ℝ) / t) := by
    rw [h1, h2]
    have he : 1 / ((t : ℝ) + v) * (A + B) - 1 / (t : ℝ) * A =
        ((t : ℝ) * B - v * A) / ((t : ℝ) * (t + v)) := by
      field_simp
      ring
    have he2 : 4 * M i * ((v : ℝ) / t) = 4 * M i * v * (t + v) / ((t : ℝ) * (t + v)) := by
      field_simp
    rw [he, he2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * (t + v))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 : |(t : ℝ) * B| ≤ t * (2 * M i * v) := by
      rw [abs_mul, abs_of_pos htp]
      exact mul_le_mul_of_nonneg_left hBb htp.le
    have e2 : |(v : ℝ) * A| ≤ v * (2 * M i * t) := by
      rw [abs_mul, abs_of_pos hvp]
      exact mul_le_mul_of_nonneg_left hAb hvp.le
    have e3 := abs_sub ((t : ℝ) * B) (v * A)
    nlinarith [mul_nonneg (mul_nonneg hM0 hvp.le) hvp.le]
  unfold regretR
  exact (abs_max_sub_max_le_abs _ _ _).trans hdiff
