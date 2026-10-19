-- Prove2me | solution 1 for SoficGroups.KunActualSelectedCentralizerFiniteModel.nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/4e63db2a-8a77-42d5-b945-f65ac6ee0068

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_map_one
import Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_multiplicative
import Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_separated

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedCentralizerFiniteModel
open Filter Topology
namespace SoficGroups.KunActualSelectedCentralizerFiniteModel
theorem _root_.solution
    {J : Type} [Group J] (F : Finset J)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (ι : Type) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (hp : ∀ n, p n 1 = 1)
    (t : ℕ → ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hdefect : ∀ᶠ n in atTop,
      ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
        SoficGroups.permutationCommutationDefect
          (σ n) (p n j) ≤ t n)
    (hexp : ∀ᶠ n in atTop, ∀ E : Finset (V n),
      h * min (E.card : ℝ)
        ((Fintype.card (V n) : ℝ) - E.card) ≤
          (SoficGroups.boundary (σ n) E : ℝ))
    (hsmall : ∀ᶠ n in atTop,
      (10 : ℝ) * t n < h * Fintype.card (V n))
    (himprove : ∀ᶠ n in atTop,
      SoficGroups.HasAlmostCentralizerImprovement (σ n) (t n))
    (hmul : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F,
      5 * SoficGroups.permutationDistance
        (p n (x * y)) (p n x * p n y) ≤ Fintype.card (V n))
    (hsep : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card (V n) <
        5 * SoficGroups.permutationDistance (p n x) (p n y)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by
  have hgood := hdefect.and
    (hexp.and (hsmall.and (himprove.and (hmul.and hsep))))
  obtain ⟨n, hn⟩ := hgood.exists
  obtain ⟨hdefect_n, hexp_n, hsmall_n,
    himprove_n, hmul_n, hsep_n⟩ := hn
  let f := trackedCompletedAlmostCentralizer
    (σ n) (p n) F (t n) hdefect_n
  refine ⟨SoficGroups.expandingCentralizerFiniteModelOfImprovement
    F (σ n) (t n) h hpositive hexp_n hsmall_n himprove_n
      f ?_ ?_ ?_⟩
  · exact trackedCompletedAlmostCentralizer_map_one
      (σ n) (p n) (hp n) F (t n) hdefect_n
  · exact trackedCompletedAlmostCentralizer_multiplicative
      (σ n) (p n) F (t n) hdefect_n hmul_n
  · exact trackedCompletedAlmostCentralizer_separated
      (σ n) (p n) F (t n) hdefect_n hsep_n
end SoficGroups.KunActualSelectedCentralizerFiniteModel
