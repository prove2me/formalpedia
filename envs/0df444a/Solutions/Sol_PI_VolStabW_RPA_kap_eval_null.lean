-- Prove2me | solution 1 for PI.VolStabW.RPA.kap_eval_null
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:45.817769+00:00
-- url     : https://prove2.me/submissions/413fbe91-9e52-4106-9113-847a19702a94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Theorems.Thm_PI_VolStabW_RPA_eS_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}
variable (m L)
variable [∀ i, SigmaFinite (m i)]
variable {m L}
namespace PI.VolStabW.RPA
theorem _root_.solution {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by
  classical
  have hs : MeasurableSet {x : ∀ j, W j | x i ∈ A} := measurable_pi_apply i hA
  unfold kap
  rw [Measure.map_apply (eS S).symm.measurable hs]
  by_cases hi : i ∈ S
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = ((fun f => f ⟨i, hi⟩) ⁻¹' A) ×ˢ (Set.univ : Set (∀ j : {j // j ∉ S}, W j)) := by
      ext p
      simp [eS_symm_apply, hi]
    have hR : Rm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Rm
      apply Measure.pi_eval_preimage_null
      simpa [mu, hi] using h
    rw [hpre, Measure.prod_prod, hR, zero_mul]
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = (Set.univ : Set (∀ j : {j // j ∈ S}, W j)) ×ˢ ((fun f => f ⟨i, hi⟩) ⁻¹' A) := by
      ext p
      simp [eS_symm_apply, hi]
    have h' : (m i).restrict (L i) A = 0 := by simpa [mu, hi] using h
    have hQ : Qm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hh
      · haveI : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hh j.1 j.2)
        have h6 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1) ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
          rw [← Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA, Measure.infinitePi_map_eval]
          simp [Pn, h']
        simp [Measure.smul_apply, h6]
      · simp
    rw [hpre, Measure.prod_prod, hQ, mul_zero]
end PI.VolStabW.RPA
