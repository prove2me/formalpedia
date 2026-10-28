-- Prove2me | solution 1 for ShapiroSDDP.Convergence.scenario_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:17:45.611821+00:00
-- url     : https://prove2.me/submissions/aa576a9c-acf7-4057-8537-83f5201c8751

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_Sampling

open MeasureTheory

open ShapiroSDDP.Convergence ProbabilityTheory Filter in
theorem solution (I : Instance) {M : ℕ} (hM : 0 < M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Fin M → Ω → Scen I)
    (hX : IsUniformIID I P X) :
    ∀ᵐ w ∂P, ∀ (s : Scen I) (K : ℕ), ∃ k, K ≤ k ∧ ∃ i, X k i w = s := by
  set i0 : Fin M := ⟨0, hM⟩
  have hind : iIndepFun (fun k => X k i0) P :=
    hX.2.1.precomp (g := fun k : ℕ => (k, i0)) (fun a b h => (Prod.mk.inj h).1)
  rw [ae_all_iff]
  intro s
  set A : ℕ → Set Ω := fun k => X k i0 ⁻¹' {s} with hA
  have hmeas : ∀ k, MeasurableSet (A k) := fun k => hX.1 k i0 (measurableSet_singleton s)
  have hiA : iIndepSet A P := by
    rw [iIndepSet_iff_meas_biInter hmeas]
    intro S
    exact hind.measure_inter_preimage_eq_mul S (sets := fun _ => {s})
      (fun _ _ => measurableSet_singleton s)
  have hPA : ∀ k, P (A k) = (Fintype.card (Scen I) : ENNReal)⁻¹ := fun k => hX.2.2 k i0 s
  have hsum : ∑' k, P (A k) = ⊤ := by
    simp only [hPA]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have h1 := measure_limsup_eq_one hmeas hiA hsum
  have hL : ∀ᵐ w ∂P, w ∈ limsup A atTop := by
    refine (ae_iff_measure_eq (p := fun w => w ∈ limsup A atTop)
      (MeasurableSet.measurableSet_limsup hmeas).nullMeasurableSet).mpr ?_
    rw [measure_univ]
    exact h1
  filter_upwards [hL] with w hw
  intro K
  rw [mem_limsup_iff_frequently_mem, frequently_atTop] at hw
  obtain ⟨k, hk, hkA⟩ := hw K
  exact ⟨k, hk, i0, hkA⟩
