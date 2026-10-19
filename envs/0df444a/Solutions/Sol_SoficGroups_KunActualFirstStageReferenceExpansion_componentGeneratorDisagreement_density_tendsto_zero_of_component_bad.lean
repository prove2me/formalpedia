-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/fca42768-99a3-4ed3-ba2b-41da63d73103

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_le_card_mul_component_bad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hdensity : Tendsto
      (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun n =>
        (Fintype.card ι : ℝ) *
          (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0) := by
    simpa using hdensity.const_mul (Fintype.card ι : ℝ)
  apply squeeze_zero'
    (Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))
    (Eventually.of_forall fun n => ?_)
    hlimit
  have hnat :=
    componentGeneratorDisagreement_le_card_mul_component_bad
      (C n) (B n) (σref n) (σact n) (hbad n)
  have hreal :
      (componentGeneratorDisagreement
        (C n) (σref n) (σact n) : ℝ) ≤
        (Fintype.card ι : ℝ) *
          ((C n ∩ B n).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (componentGeneratorDisagreement
      (C n) (σref n) (σact n) : ℝ) / (C n).card ≤
        ((Fintype.card ι : ℝ) *
          ((C n ∩ B n).card : ℝ)) / (C n).card :=
          div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = (Fintype.card ι : ℝ) *
          (((C n ∩ B n).card : ℝ) / (C n).card) := by ring
end SoficGroups.KunActualFirstStageReferenceExpansion
