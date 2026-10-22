-- Prove2me | solution 1 for SOSInference.Means.closest_point_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:26:07.486739+00:00
-- url     : https://prove2.me/submissions/00123751-390f-4298-a98b-2ac36223e1c7

import Mathlib
import Definitions.Def_SOSInference_Means_sos
set_option autoImplicit false

open SOSInference.Means
open scoped RealInnerProductSpace

lemma uu_sq (l : ℕ) (x lam a : E l) :
    -⟪lam, a⟫ + ‖x - a‖ ^ 2 = ‖a - x - (1 / 2 : ℝ) • lam‖ ^ 2 - ⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 := by
  have h1 : ‖a - x - (1 / 2 : ℝ) • lam‖ ^ 2
      = ‖a - x‖ ^ 2 - 2 * ⟪a - x, (1 / 2 : ℝ) • lam⟫ + ‖(1 / 2 : ℝ) • lam‖ ^ 2 :=
    norm_sub_sq_real _ _
  have h2 : ⟪a - x, (1 / 2 : ℝ) • lam⟫ = (1 / 2) * ⟪a - x, lam⟫ := real_inner_smul_right _ _ _
  have h3 : ‖(1 / 2 : ℝ) • lam‖ ^ 2 = ‖lam‖ ^ 2 / 4 := by
    rw [norm_smul]; simp; ring
  have h4 : ‖x - a‖ = ‖a - x‖ := norm_sub_rev _ _
  have h5 : ⟪lam, a⟫ = ⟪lam, x⟫ + ⟪a - x, lam⟫ := by
    rw [real_inner_comm lam (a - x), inner_sub_right]
    ring
  rw [h1, h2, h3, h4, h5]
  ring

theorem solution {l : ℕ} (x lam : E l) :
    IsLeast (Set.range fun a : E l => -⟪lam, a⟫ + ‖x - a‖ ^ 2) (-⟪lam, x⟫ - ‖lam‖ ^ 2 / 4) ∧
    -⟪lam, x + (1 / 2 : ℝ) • lam⟫ + ‖x - (x + (1 / 2 : ℝ) • lam)‖ ^ 2 =
      -⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 ∧
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → E l),
      -⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 ≤ ⨅ j, (-⟪lam, z j⟫ + ‖x - z j‖ ^ 2) := by
  have hat : -⟪lam, x + (1 / 2 : ℝ) • lam⟫ + ‖x - (x + (1 / 2 : ℝ) • lam)‖ ^ 2
      = -⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 := by
    rw [uu_sq]
    have : x + (1 / 2 : ℝ) • lam - x - (1 / 2 : ℝ) • lam = 0 := by abel
    rw [this]; simp
  refine ⟨⟨⟨x + (1 / 2 : ℝ) • lam, hat⟩, ?_⟩, hat, ?_⟩
  · rintro _ ⟨a, rfl⟩
    show _ ≤ -⟪lam, a⟫ + ‖x - a‖ ^ 2
    rw [uu_sq]
    have := sq_nonneg ‖a - x - (1 / 2 : ℝ) • lam‖
    linarith
  · intro ι _ _ z
    apply le_ciInf
    intro j
    rw [uu_sq]
    have := sq_nonneg ‖z j - x - (1 / 2 : ℝ) • lam‖
    linarith
