-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.close_residual_inter_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/fe08cd8d-77e5-465f-b24e-0b7ab0637b02

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution {V : Type*} [DecidableEq V]
    (R T U : Finset V) (hTR : T ⊆ R)
    (hclose : 3 * (U ∆ T).card < T.card) :
    (R ∩ U).Nonempty ∧
      U.card ≤ 2 * (R ∩ U).card ∧
      (R ∩ U).card < 2 * T.card := by
  classical
  have hmissing :
      (T \ U).card ≤ (U ∆ T).card :=
    Finset.card_le_card
      (Finset.symmDiff_subset_sdiff' (s := U) (t := T))
  have hexcess :
      (U \ T).card ≤ (U ∆ T).card :=
    Finset.card_le_card
      (Finset.symmDiff_subset_sdiff (s := U) (t := T))
  have hTinter :
      (T ∩ U).card ≤ (R ∩ U).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hTR (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  have hUinter :
      (U ∩ T).card ≤ (R ∩ U).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hTR (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
  have hTsplit := Finset.card_sdiff_add_card_inter T U
  have hUsplit := Finset.card_sdiff_add_card_inter U T
  have hintercomm : (T ∩ U).card = (U ∩ T).card := by
    rw [Finset.inter_comm]
  have hPsub : (R ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hPpos : 0 < (R ∩ U).card := by omega
  exact ⟨Finset.card_pos.mp hPpos, by omega, by omega⟩
end SoficGroups.KunResidualExpanderDecomposition
