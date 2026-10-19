-- Prove2me | solution 1 for SoficGroups.KunActualTwicePrunedFirstFactorRootBad.twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/070e8c87-87ca-4a86-8784-47fa431d1fed

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_mem_generator_pow_of_chosen_word_length
import Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_deleted_density_relative_survivors
import Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_mem_generator_pow_of_chosen_word_length
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_completedRestriction_mul_distance_le_failure_add_deleted
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_firstFactor_completed_mul_distance_le_canonical_matched
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_density_relative_survivors

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualTwicePrunedFirstFactorRootBad
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K) (hone : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (nhds 0))
    (D : (n : ℕ) → Finset
      {x : Fin (A.model (ν n)).size // x ∈ C n})
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C n).card)
      atTop (nhds 0))
    (a g : K) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a * g, (1 : J))) (C n))
            (Finset.univ \ D n))
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a, (1 : J))) (C n))
            (Finset.univ \ D n) *
           completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (g, (1 : J))) (C n))
            (Finset.univ \ D n)))
      atTop (nhds 0) := by
  classical
  let W : ℕ → Type := fun n =>
    {x : Fin (A.model (ν n)).size // x ∈ C n}
  let Z : (n : ℕ) → Finset (W n) := fun n => Finset.univ \ D n
  let B : ℕ → ℕ := fun n =>
    (C n ∩ SoficGroups.matchedRadiusBad
      (Q n) (sourceProductRadiusLabels S F (r n))
      ((A.model (ν n)).action)
      (canonicalProductRadiusBad
        A S hsymmetric hgenerates F (ν n) (r n))).card
  have hdeletedW : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (W n))
      atTop (nhds 0) := by
    simpa only [W, Fintype.card_coe] using hdeleted
  have hBW : Tendsto
      (fun n => (B n : ℝ) / Fintype.card (W n))
      atTop (nhds 0) := by
    simpa only [B, W, Fintype.card_coe] using hmatched
  have hBfinal : Tendsto
      (fun n => (B n : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    exact density_relative_survivors W D hZ hdeletedW B hBW
  have hDfinal : Tendsto
      (fun n => ((D n).card : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    exact deleted_density_relative_survivors W D hZ hdeletedW
  have hupper : Tendsto
      (fun n => (B n : ℝ) / (Z n).card +
        2 * ((D n).card : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    convert hBfinal.add (hDfinal.const_mul 2) using 1 <;>
      simp [mul_div_assoc]
  let w : K → List ↥S :=
    symmetricGeneratorWord S hsymmetric hgenerates
  have hw : ∀ b : K, ((w b).map fun i : ↥S => (i : K)).prod = b :=
    symmetricGeneratorWord_prod S hsymmetric hgenerates
  have hlarge : ∀ᶠ n in atTop,
      max (w a).length (max (w g).length (w (a * g)).length) ≤ r n :=
    Filter.tendsto_atTop.1 hr _
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      SoficGroups.normalizedHamming_nonneg _ _)
    ?_ hupper
  filter_upwards [hlarge] with n hn
  have ha : a ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  have hg : g ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  have hag : a * g ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  let p : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (a, (1 : J))) (C n)
  let q : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (g, (1 : J))) (C n)
  let s : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (a * g, (1 : J))) (C n)
  have hfirst :
      SoficGroups.permutationDistance s (p * q) ≤ B n := by
    exact firstFactor_completed_mul_distance_le_canonical_matched
      A S hsymmetric hgenerates F (ν n) (r n)
      (Q n) (C n) (hC n) a g ha hg hag
  have hfailure :
      (Finset.univ.filter fun x : W n =>
        s x ≠ p (q x)).card ≤ B n := by
    calc
      (Finset.univ.filter fun x : W n =>
        s x ≠ p (q x)).card =
          SoficGroups.permutationDistance s (p * q) := by
        unfold SoficGroups.permutationDistance hammingDist
        congr 1
      _ ≤ B n := hfirst
  have hdist := completedRestriction_mul_distance_le_failure_add_deleted
    p q s (Z n)
  have hcomplement :
      (Finset.univ \ Z n : Finset (W n)) = D n := by
    ext x
    simp [Z]
  have hnat :
      SoficGroups.permutationDistance
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) ≤
        B n + 2 * (D n).card := by
    rw [hcomplement] at hdist
    omega
  have hreal :
      (SoficGroups.permutationDistance
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) : ℝ) ≤
        (B n : ℝ) + 2 * (D n).card := by
    exact_mod_cast hnat
  have hnormalized := div_le_div_of_nonneg_right hreal
    (show (0 : ℝ) ≤ ((Z n).card : ℝ) by positivity)
  change
    SoficGroups.normalizedHamming
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) ≤
      (B n : ℝ) / (Z n).card +
        2 * ((D n).card : ℝ) / (Z n).card
  simpa [SoficGroups.normalizedHamming,
    SoficGroups.permutationDistance, Fintype.card_coe, add_div,
    mul_div_assoc] using hnormalized
end SoficGroups.KunActualTwicePrunedFirstFactorRootBad
