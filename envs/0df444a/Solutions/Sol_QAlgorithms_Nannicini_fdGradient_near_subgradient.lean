-- Prove2me | solution 1 for QAlgorithms.Nannicini.fdGradient_near_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:25:16.818627+00:00
-- url     : https://prove2.me/submissions/fd143b80-4758-4668-a5ad-b3c9c7c2ffe9

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open QAlgorithms

private lemma endpoint_mem {d : ℕ} (η : ℝ) (hη : 0 ≤ η)
    (x : Fin d → ℝ) (j : Fin d) :
    x + η • Pi.single j 1 ∈ ballL1 x η ∧
      x - η • Pi.single j 1 ∈ ballL1 x η := by
  constructor <;> simp [ballL1, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.single_apply, apply_ite abs, abs_of_nonneg hη]

theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (_hf : ConvexOn ℝ (ballL1 x η) f)
    (g : Module.Dual ℝ (Fin d → ℝ)) (hg : IsEpsSubgradOn (ballL1 x η) f 0 x g) :
    ∑ j : Fin d, |g (Pi.single j 1) - fdGradient η f x j| ≤
      2⁻¹ * η * fdLaplacian η f x := by
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hcoord (j : Fin d) :
      |g (Pi.single j 1) - fdGradient η f x j| ≤
        (f (x + η • Pi.single j 1) - 2 * f x + f (x - η • Pi.single j 1)) /
          (2 * η) := by
    obtain ⟨hp, hm⟩ := endpoint_mem η hη.le x j
    have hgp := hg _ hp
    have hgm := hg _ hm
    simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, map_smul,
      smul_eq_mul, sub_zero] at hgp hgm
    rw [abs_le]
    dsimp [fdGradient]
    constructor
    · rw [← neg_le_neg_iff, neg_neg]
      apply (le_div_iff₀ (by positivity : 0 < 2 * η)).2
      field_simp
      nlinarith
    · apply (le_div_iff₀ (by positivity : 0 < 2 * η)).2
      field_simp
      nlinarith
  calc
    _ ≤ ∑ j : Fin d,
        (f (x + η • Pi.single j 1) - 2 * f x + f (x - η • Pi.single j 1)) /
          (2 * η) := Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by
      simp only [fdLaplacian, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
