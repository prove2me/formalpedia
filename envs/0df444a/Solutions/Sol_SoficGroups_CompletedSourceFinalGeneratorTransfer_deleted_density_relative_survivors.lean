-- Prove2me | solution 1 for SoficGroups.CompletedSourceFinalGeneratorTransfer.deleted_density_relative_survivors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/5cdda6b3-6cbd-4aa9-bcab-518ed8d7ba55

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_surviving_card_ratio_tendsto_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
namespace SoficGroups.CompletedSourceFinalGeneratorTransfer
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((D n).card : ℝ) /
          (Finset.univ \ D n : Finset (V n)).card)
      atTop (nhds 0) := by
  have hcover :=
    surviving_card_ratio_tendsto_one V D hZ hdeleted
  have hquotient : Tendsto
      ((fun n => ((D n).card : ℝ) / Fintype.card (V n)) /
        (fun n =>
          ((Finset.univ \ D n : Finset (V n)).card : ℝ) /
            Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [zero_div] using
      hdeleted.div hcover (by norm_num : (1 : ℝ) ≠ 0)
  convert hquotient using 1
  funext n
  have hN : Fintype.card (V n) ≠ 0 := by
    obtain ⟨x, _⟩ := hZ n
    exact Finset.card_ne_zero.mpr
      (show (Finset.univ : Finset (V n)).Nonempty from
        ⟨x, Finset.mem_univ x⟩)
  have hNreal : (Fintype.card (V n) : ℝ) ≠ 0 := by
    exact_mod_cast hN
  have hZreal :
      ((Finset.univ \ D n : Finset (V n)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (hZ n)
  change
    ((D n).card : ℝ) /
        (Finset.univ \ D n : Finset (V n)).card =
      (((D n).card : ℝ) / Fintype.card (V n)) /
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n))
  field_simp [hNreal, hZreal]
end SoficGroups.CompletedSourceFinalGeneratorTransfer
