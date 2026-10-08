-- Prove2me | solution 1 for PolicyGradTheory.ProjGA.gradient_mapping_stationarity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:29:20.400586+00:00
-- url     : https://prove2.me/submissions/62975453-4492-45f6-a356-e4747f62975a

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

set_option autoImplicit false

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem PGPA5b02f405_convex {S A : Type*} [Fintype A] :
    Convex ℝ (simplexSet S A) := by
  intro x hx y hy a b ha hb hab
  simp only [simplexSet, IsPolicy, asPolicy, Set.mem_setOf_eq] at hx hy ⊢
  intro s
  refine ⟨fun c => ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := (hx s).1 c
    have := (hy s).1 c
    positivity
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hx s).2, (hy s).2]
    linarith

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem PGPA5b02f405_vi {S A : Type*} [Fintype S] [Fintype A]
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj) (z : EuclideanSpace ℝ (S × A)) :
    ∀ w ∈ simplexSet S A, inner ℝ (z - Proj z) (w - Proj z) ≤ 0 := by
  have hp := (hProj z).1
  have hmin := (hProj z).2
  have hne : Nonempty (simplexSet S A) := ⟨⟨Proj z, hp⟩⟩
  have hbdd : BddBelow (Set.range fun w : simplexSet S A => ‖z - (w : EuclideanSpace ℝ (S × A))‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hinf : ‖z - Proj z‖ = ⨅ w : simplexSet S A, ‖z - (w : EuclideanSpace ℝ (S × A))‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w : simplexSet S A => hmin w.1 w.2)
    · exact ciInf_le hbdd (⟨Proj z, hp⟩ : simplexSet S A)
  exact (norm_eq_iInf_iff_real_inner_le_zero PGPA5b02f405_convex hp).1 hinf

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (β : ℝ) (hβ : 0 ≤ β)
    (hsmooth : ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ μ) π - gradient (directValue P r γ μ) π'‖ ≤ β * ‖π - π'‖)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (η : ℝ) (hη : 0 < η) (ε : ℝ) (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (hG : ‖(1 / η) • (Proj (π + η • gradient (directValue P r γ μ) π) - π)‖ ≤ ε) :
    ∀ δ : EuclideanSpace ℝ (S × A),
      Proj (π + η • gradient (directValue P r γ μ) π) + δ ∈ simplexSet S A → ‖δ‖ ≤ 1 →
        inner ℝ δ (gradient (directValue P r γ μ)
          (Proj (π + η • gradient (directValue P r γ μ) π))) ≤ ε * (η * β + 1) := by
  intro δ hδC hδ
  set g := gradient (directValue P r γ μ) π with hg
  set p := Proj (π + η • g) with hpdef
  set g' := gradient (directValue P r γ μ) p with hg'
  have hp : p ∈ simplexSet S A := (hProj (π + η • g)).1
  have hvi := PGPA5b02f405_vi Proj hProj (π + η • g) (p + δ) hδC
  rw [← hpdef, add_sub_cancel_left] at hvi
  -- ‖p - π‖ ≤ η ε
  have hnorm : ‖p - π‖ ≤ η * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hG
    rw [one_div, inv_mul_le_iff₀ hη] at hG
    exact hG
  have hvi' : η * inner ℝ δ g ≤ inner ℝ δ (p - π) := by
    have e : π + η • g - p = η • g - (p - π) := by abel
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_comm δ g,
      real_inner_comm δ (p - π)] at hvi
    linarith
  have h1 : inner ℝ δ (p - π) ≤ η * ε := by
    calc inner ℝ δ (p - π) ≤ ‖δ‖ * ‖p - π‖ := real_inner_le_norm _ _
      _ ≤ 1 * (η * ε) := by
          apply mul_le_mul hδ hnorm (norm_nonneg _) zero_le_one
      _ = η * ε := one_mul _
  have ha : inner ℝ δ g ≤ ε := by
    have : η * inner ℝ δ g ≤ η * ε := le_trans hvi' h1
    exact le_of_mul_le_mul_left this hη
  have h2 : inner ℝ δ (g' - g) ≤ β * (η * ε) := by
    calc inner ℝ δ (g' - g) ≤ ‖δ‖ * ‖g' - g‖ := real_inner_le_norm _ _
      _ ≤ 1 * (β * ‖p - π‖) := by
          apply mul_le_mul hδ (hsmooth p hp π hπ) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (β * (η * ε)) := by
          gcongr
      _ = β * (η * ε) := one_mul _
  have hsplit : inner ℝ δ g' = inner ℝ δ g + inner ℝ δ (g' - g) := by
    rw [inner_sub_right]; ring
  rw [hsplit]
  nlinarith
