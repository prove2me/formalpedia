-- Prove2me | solution 1 for SoficGroups.KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/ab4a53de-4b8f-422d-a018-634397d869c5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_goodPermutationGraph_subset
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_permutationGraph_sdiff_goodPermutationGraph_le
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_goodPermutationGraph_ge_card_sub_twice_bad
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_boundary_goodPermutationGraph_le_commutationDefect_add
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_hasAlmostCentralizerImprovement_zero
import Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
import Theorems.Thm_SoficGroups_KunRootedUniversalToleranceNumerics_rooted_graph_boundary_lt_of_slow_tolerance
import Theorems.Thm_SoficGroups_KunRootedUniversalToleranceNumerics_rooted_graph_coefficient_small
import Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_exists_completed_goodPermutationGraph_sparse_cut

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniformCompletedRootRadiusImprovement
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
namespace SoficGroups.KunUniformCompletedRootRadiusImprovement
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (h α : ℝ) (hpositive : 0 < h) (hα : 0 < α) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [Nonempty V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V)
        (tolerance : ℕ) (B : Finset V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      (∀ A : Finset V,
        h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
            (SoficGroups.boundary σ A : ℝ)) →
      (5 * (4 + h *
        (216 / ((S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) +
            1 / (S.card : ℝ))) * (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ)) →
      (tolerance = 0 ∨
        (0 < (tolerance : ℝ) ∧
          α ≤ h * (tolerance : ℝ) /
            (2 * (h + 8 * (S.card : ℝ)) *
              (Fintype.card V : ℝ)) ∧
          2 * (S.card : ℝ) * (B.card : ℝ) ≤
            (tolerance : ℝ) ∧
          ∀ a g : G,
            (w a).length + (w g).length +
                (w (a * g)).length ≤ r →
              ∀ x : V, x ∉ B →
                φ (a * g) x = (φ a * φ g) x)) →
      SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by
  classical
  letI : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let d : ℝ := S.card
  let q : ℝ := kazhdanMarkovContractionFactor P S
  let γ : ℝ := d * (1 - q) ^ 2 / 288
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  have hq : q < 1 := by
    exact kazhdanMarkovContractionFactor_lt_one
      P S ⟨1, honeS⟩
  have hγpair :=
    SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
      hd hq
  have hγ : 0 < γ := by
    simpa only [γ] using hγpair.1
  have hγsmall :
      216 * γ < (S.card : ℝ) * (1 - q) ^ 2 := by
    simpa only [γ, d] using hγpair.2
  obtain ⟨r, hspectral⟩ :=
    SoficGroups.KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
      P S honeS hcover hsymmetric w γ α hγ hα
        (by simpa only [q] using hγsmall)
  refine ⟨r, ?_⟩
  intro V _ _ _ σ φ tolerance B hword hone hgenerator
    hexp hslow hcase
  rcases hcase with htzero | ⟨ht, htarget, hbadS, hlocal⟩
  · subst tolerance
    exact SoficGroups.KunCompletedPrunedComponent.hasAlmostCentralizerImprovement_zero σ
  have hbad :
      2 * (Fintype.card (↥S) : ℝ) * (B.card : ℝ) ≤
        (tolerance : ℝ) := by
    simpa only [Fintype.card_coe] using hbadS
  have hslowq :
      5 * (4 + h *
        (216 / ((Fintype.card (↥S) : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card (↥S) : ℝ))) *
            (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ) := by
    simpa only [Fintype.card_coe, q] using hslow
  apply
    SoficGroups.KunUniversalGoodRootReferenceCuts.hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
      σ tolerance h q hpositive hq B
      (fun p => goodPermutationGraph p B) hexp
      hbad
      (fun p => goodPermutationGraph_subset p B)
      (fun p => card_permutationGraph_sdiff_goodPermutationGraph_le p B)
      (fun p =>
        boundary_goodPermutationGraph_le_commutationDefect_add σ p B)
      hslowq
  intro p hp
  let T : Finset (V × V) := goodPermutationGraph p B
  have hcard :
      (Fintype.card V : ℝ) - 2 * (B.card : ℝ) ≤
        (T.card : ℝ) := by
    exact card_goodPermutationGraph_ge_card_sub_twice_bad p B
  have hboundary :
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) ≤
          3 * (tolerance : ℝ) := by
    have hbound :=
      boundary_goodPermutationGraph_le_commutationDefect_add σ p B
    have hbound_real :
        (SoficGroups.boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) ≤
          (SoficGroups.permutationCommutationDefect σ p : ℝ) +
            2 * (Fintype.card (↥S) : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hbound
    have hp_real :
        (SoficGroups.permutationCommutationDefect σ p : ℝ) ≤
          2 * (tolerance : ℝ) := by
      exact_mod_cast hp
    linarith
  have hsparse :
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) <
          γ * (T.card : ℝ) := by
    have hslowS :
        5 * (4 + h *
          (216 / (d * (1 - q) ^ 2) + 1 / d)) *
            (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ) := by
      simpa only [d, q] using hslow
    have hbad' :
        2 * d * (B.card : ℝ) ≤ (tolerance : ℝ) := by
      simpa only [d] using hbadS
    have hs :=
      SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
        hpositive hd hq ht hbad' hcard hboundary hslowS
    simpa only [γ] using hs
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    have hnonnegative :
        0 ≤ (SoficGroups.boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) := by
      positivity
    have hpositiveT : 0 < (T.card : ℝ) := by
      nlinarith
    exact_mod_cast hpositiveT
  obtain ⟨U, hreference, _hclose, hcut⟩ :=
    hspectral V σ φ hword hone hgenerator p B hlocal hT hsparse
  refine ⟨U, ?_, ?_⟩
  · simpa only [T, q, Fintype.card_coe] using hreference
  · calc
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) U : ℝ) ≤
          α * (U.card : ℝ) := hcut
      _ ≤ (h * (tolerance : ℝ) /
          (2 * (h + 8 * (Fintype.card (↥S) : ℝ)) *
            (Fintype.card V : ℝ))) * (U.card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [Fintype.card_coe] using htarget
end SoficGroups.KunUniformCompletedRootRadiusImprovement
