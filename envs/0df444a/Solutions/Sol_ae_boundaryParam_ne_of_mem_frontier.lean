-- Prove2me | solution 1 for ae_boundaryParam_ne_of_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:09.405362+00:00
-- url     : https://prove2.me/submissions/060e2101-04cb-43a5-92c4-b271da4820cd

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) → Omega.boundaryParam t ≠ xi := by
  rw [← Omega.boundaryParam_range] at hxi
  obtain ⟨s, rfl⟩ := hxi
  obtain ⟨t0, ht0, hrep⟩ :=
    Function.Periodic.exists_mem_Ico₀ Omega.boundaryParam_periodic
      Real.two_pi_pos s
  have ht0ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ t0 :=
    MeasureTheory.volume.ae_ne t0
  have hendae : ∀ᵐ t ∂MeasureTheory.volume,
      t ≠ 2 * Real.pi := MeasureTheory.volume.ae_ne (2 * Real.pi)
  filter_upwards [ht0ae, hendae] with t hne0 hneEnd
  intro ht heq
  have ht' := uIoc_subset_uIcc ht
  rw [uIcc_of_le Real.two_pi_pos.le] at ht'
  have htIco : t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨ht'.1, lt_of_le_of_ne ht'.2 hneEnd⟩
  apply hne0
  exact Omega.boundaryParam_injOn htIco ht0 (heq.trans hrep)
