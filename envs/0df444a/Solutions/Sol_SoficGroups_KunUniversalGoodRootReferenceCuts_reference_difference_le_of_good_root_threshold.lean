-- Prove2me | solution 1 for SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_of_good_root_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/b8e4c237-3728-4eac-b96d-89b2bed1f912

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_reference_difference_le_symmDiff_add_missing

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff
namespace SoficGroups.KunUniversalGoodRootReferenceCuts
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V)
    (B : Finset V) (T U : Finset (V × V))
    (t : ℕ) (q : ℝ) (hq : q < 1)
    (hsub : T ⊆ SoficGroups.permutationGraph p)
    (hmissing :
      (SoficGroups.permutationGraph p \ T).card ≤ 2 * B.card)
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤ (t : ℝ))
    (hdefect : SoficGroups.permutationCommutationDefect σ p ≤ 2 * t)
    (hboundary :
      SoficGroups.boundary (fun i => (σ i).prodCongr (σ i)) T ≤
        SoficGroups.permutationCommutationDefect σ p +
          2 * Fintype.card ι * B.card)
    (hthreshold :
      ((U ∆ T).card : ℝ) ≤
        72 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) /
            ((Fintype.card ι : ℝ) * (1 - q) ^ 2)) :
    (((U \ SoficGroups.permutationGraph p).card +
      (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) ≤
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ)) * (t : ℝ) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hden : 0 < (Fintype.card ι : ℝ) * (1 - q) ^ 2 :=
    mul_pos hd (sq_pos_of_pos (sub_pos.mpr hq))
  have hdefect_real :
      (SoficGroups.permutationCommutationDefect σ p : ℝ) ≤
        2 * (t : ℝ) := by
    exact_mod_cast hdefect
  have hboundary_real :
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) T : ℝ) ≤
          3 * (t : ℝ) := by
    have hbound :
        (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) ≤
            (SoficGroups.permutationCommutationDefect σ p : ℝ) +
              2 * (Fintype.card ι : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hboundary
    linarith
  have hmissing_real :
      ((SoficGroups.permutationGraph p \ T).card : ℝ) ≤
        (t : ℝ) / (Fintype.card ι : ℝ) := by
    have hm :
        ((SoficGroups.permutationGraph p \ T).card : ℝ) ≤
          2 * (B.card : ℝ) := by
      exact_mod_cast hmissing
    apply (le_div_iff₀ hd).2
    nlinarith
  have htransfer :
      (((U \ SoficGroups.permutationGraph p).card +
        (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) ≤
          ((U ∆ T).card : ℝ) +
            ((SoficGroups.permutationGraph p \ T).card : ℝ) := by
    exact_mod_cast reference_difference_le_symmDiff_add_missing
      U T (SoficGroups.permutationGraph p) hsub
  calc
    (((U \ SoficGroups.permutationGraph p).card +
      (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) ≤
        ((U ∆ T).card : ℝ) +
          ((SoficGroups.permutationGraph p \ T).card : ℝ) := htransfer
    _ ≤ 72 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) /
            ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          (t : ℝ) / (Fintype.card ι : ℝ) :=
      add_le_add hthreshold hmissing_real
    _ ≤ 72 * (3 * (t : ℝ)) /
          ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          (t : ℝ) / (Fintype.card ι : ℝ) := by
      gcongr
    _ = (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ)) * (t : ℝ) := by
      ring
end SoficGroups.KunUniversalGoodRootReferenceCuts
