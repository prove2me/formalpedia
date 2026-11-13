-- Prove2me | solution 1 for RestrictedAP.Counting.theorem_1_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:20:28.020386+00:00
-- url     : https://prove2.me/submissions/b8430587-3175-4a54-9a3d-76c1af40053d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Theorems.Thm_RestrictedAP_Counting_claim_5_14_monotone
import Theorems.Thm_RestrictedAP_Counting_lemma_5_27_uniform

section
set_option autoImplicit false

namespace RestrictedAP.Counting.Dev.R14
open RestrictedAP.Counting

/-- The indicator function of a set `A ⊆ Σ^n`. -/
noncomputable def ind {Sig : Type} [DecidableEq Sig] {n : ℕ} (A : Finset (Fin n → Sig)) : (Fin n → Sig) → ℝ :=
  fun x => if x ∈ A then 1 else 0

theorem ind_01 {Sig : Type} [DecidableEq Sig] {n : ℕ} (A : Finset (Fin n → Sig)) (x : Fin n → Sig) :
    ind A x = 0 ∨ ind A x = 1 := by
  unfold ind; split_ifs <;> simp

theorem tripleProb_eq_Delta1 {Sig : Type} [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (n : ℕ) (A : Finset (Fin n → Sig)) :
    tripleProb μ n A = Delta1 μ (ind A) := by
  unfold tripleProb Delta1 ind
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h1 : (fun i => (t i).1) ∈ A <;> by_cases h2 : (fun i => (t i).2.1) ∈ A <;>
    by_cases h3 : (fun i => (t i).2.2) ∈ A <;> simp [h1, h2, h3]

theorem expect_ind {Sig : Type} [Fintype Sig] [DecidableEq Sig] (ν : Sig → ℝ) (n : ℕ)
    (A : Finset (Fin n → Sig)) :
    expect (tensorPow ν n) (ind A) = ∑ x ∈ A, tensorPow ν n x := by
  unfold expect ind
  simp [mul_ite, Finset.sum_ite_mem]

theorem tensorPow_nonneg {Ω : Type} (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (n : ℕ)
    (t : Fin n → Ω) : 0 ≤ tensorPow μ n t :=
  Finset.prod_nonneg fun i _ => hμ (t i)

theorem Delta1_nonneg {Sig : Type} [Fintype Sig] {n : ℕ} (μ : Sig × Sig × Sig → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (g : (Fin n → Sig) → ℝ) (hg : ∀ x, g x = 0 ∨ g x = 1) :
    0 ≤ Delta1 μ g := by
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rcases hg x with h | h <;> simp [h]
  unfold Delta1
  exact Finset.sum_nonneg fun t _ => mul_nonneg (tensorPow_nonneg μ hμ n t)
    (mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hg0 _))

/-- A distribution on a finite set has a minimum non-zero atom `α₀`, with `α₀ ≤ 1`. -/
theorem exists_minAtom {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : IsDist μ) :
    ∃ α₀ : ℝ, IsMinAtom μ α₀ ∧ α₀ ≤ 1 := by
  classical
  set S : Finset Ω := Finset.univ.filter (fun x => μ x ≠ 0) with hS
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hz : ∀ x, μ x = 0 := fun x => by
      by_contra hx
      have : x ∈ S := by simp [hS, hx]
      simp [h] at this
    have := hμ.2
    simp [hz] at this
  have hne' : (S.image μ).Nonempty := hne.image μ
  obtain ⟨x₀, hx₀S, hx₀⟩ := Finset.mem_image.mp ((S.image μ).min'_mem hne')
  have hx₀ne : μ x₀ ≠ 0 := by simpa [hS] using hx₀S
  refine ⟨(S.image μ).min' hne', ⟨?_, ?_, x₀, hx₀⟩, ?_⟩
  · rw [← hx₀]
    exact lt_of_le_of_ne (hμ.1 x₀) (Ne.symm hx₀ne)
  · intro x hx
    exact (S.image μ).min'_le _ (Finset.mem_image.mpr ⟨x, by simp [hS, hx], rfl⟩)
  · rw [← hx₀, ← hμ.2]
    exact Finset.single_le_sum (fun x _ => hμ.1 x) (Finset.mem_univ x₀)

/-- The final numerical comparison. -/
theorem final_bound (s α α₀ d B : ℝ) (hs : 0 < s) (hα : 0 < α) (hsα₀ : s ≤ α₀) (hα₀ : α₀ ≤ 1)
    (hd : α ≤ d) (hB : 0 ≤ B) (k : ℕ) :
    s ^ (2 * B / (α * s ^ k)) ≤ α₀ ^ (2 * B / (d * α₀ ^ k)) := by
  have hs1 : s ≤ 1 := hsα₀.trans hα₀
  have hα₀pos : 0 < α₀ := hs.trans_le hsα₀
  have hsk : 0 < s ^ k := pow_pos hs k
  have hsk' : s ^ k ≤ α₀ ^ k := pow_le_pow_left₀ hs.le hsα₀ k
  have hden : α * s ^ k ≤ d * α₀ ^ k := mul_le_mul hd hsk' hsk.le (hα.le.trans hd)
  have hX : 2 * B / (d * α₀ ^ k) ≤ 2 * B / (α * s ^ k) :=
    div_le_div_of_nonneg_left (by linarith) (mul_pos hα hsk) hden
  have hX0 : 0 ≤ 2 * B / (d * α₀ ^ k) :=
    div_nonneg (by linarith) (mul_nonneg (hα.le.trans hd) (pow_nonneg hα₀pos.le k))
  calc s ^ (2 * B / (α * s ^ k)) ≤ s ^ (2 * B / (d * α₀ ^ k)) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs1 hX
    _ ≤ α₀ ^ (2 * B / (d * α₀ ^ k)) := Real.rpow_le_rpow hs.le hsα₀ hX0

end RestrictedAP.Counting.Dev.R14

namespace RestrictedAP.Counting
open RestrictedAP.Counting.Dev.R14 in
theorem chk_theorem_1_4 (m : ℕ) (s α : ℝ) (hs : 0 < s) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ → IsDist ν →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        AtomsAtLeast μ s → ¬ DistHasEmbedding ℤ μ →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Sig),
          α ≤ ∑ x ∈ A, tensorPow ν n x → β ≤ tripleProb μ n A := by
  obtain ⟨B, c, hc, H⟩ := lemma_5_27_uniform m s α hs hα
  refine ⟨s ^ (2 * (B : ℝ) / (α * s ^ B)) * s ^ (B + 1) * c,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hs _) (pow_pos hs _)) hc, ?_⟩
  intro Sig _ _ hcard μ ν hμ _hν hmarg hdiag hatoms hemb
  refine ⟨0, fun n _ A hA => ?_⟩
  obtain ⟨α₀, hmin, hα₀1⟩ := exists_minAtom μ hμ
  have hsα₀ : s ≤ α₀ := by
    obtain ⟨x, hx⟩ := hmin.2.2
    rw [← hx]
    exact hatoms x (by rw [hx]; exact hmin.1.ne')
  rw [← expect_ind] at hA
  let δ' : ℕ → ℝ → ℝ := fun _ η => if α ≤ η then s ^ (B + 1) * c else 0
  have hyp : ∀ (η : ℝ) (g : (Fin n → Sig) → ℝ), (∀ x, g x = 0 ∨ g x = 1) →
      Resilient ν B (1 / 2) g → η ≤ expect (tensorPow ν n) g → δ' B η ≤ Delta1 μ g := by
    intro η g hg hres hη
    simp only [δ']
    split_ifs with h
    · exact H Sig hcard μ ν hμ hmarg hdiag hemb hatoms n B le_rfl g hg hres (h.trans hη)
    · exact Delta1_nonneg μ hμ.1 g hg
  have hmain := claim_5_14_monotone Sig μ ν hμ hmarg hdiag hemb α₀ hmin n B δ' hyp (ind A)
    (ind_01 A) (hα.trans_le hA)
  have hδ' : δ' B (expect (tensorPow ν n) (ind A)) = s ^ (B + 1) * c := by
    simp only [δ', if_pos hA]
  rw [hδ'] at hmain
  rw [tripleProb_eq_Delta1]
  refine le_trans ?_ hmain
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (final_bound s α α₀ _ B hs hα hsα₀ hα₀1 hA (Nat.cast_nonneg B) B)
    (mul_nonneg (pow_nonneg hs.le _) hc.le)

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_theorem_1_4 := @RestrictedAP.Counting.chk_theorem_1_4
