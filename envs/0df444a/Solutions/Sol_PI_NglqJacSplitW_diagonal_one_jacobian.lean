-- Prove2me | solution 1 for PI.NglqJacSplitW.diagonal_one_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:53.533942+00:00
-- url     : https://prove2.me/submissions/f33a1a59-46c1-4f6b-98b1-ca9772b267d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
import Theorems.Thm_PI_NglqJacSplitW_image_update_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Function Topology
open scoped ENNReal NNReal Pointwise
open PI PI.NglqJacSplitW
namespace PI.NglqJacSplitW
theorem _root_.solution : DiagOne := by
  intro F _ _ _ _ _ _ ι _ _ mι bι i a ha ν hν S hS
  have hpi : mι = @MeasurableSpace.pi ι (fun _ => F) (fun _ => borel F) := by
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    rw [bι.measurable_eq]
    exact (Pi.borelSpace (ι := ι) (X := fun _ => F)).measurable_eq.symm
  subst hpi
  letI mF : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := hν
  set μ : Measure F := Measure.addHaar with hμ
  set P : Measure (ι → F) := Measure.pi fun _ => μ with hP
  set m' : ℝ≥0 := distribHaarChar F (Units.mk0 a ha) with hm'
  have hmod : modF F a = (m' : ℝ≥0∞) := by simp [modF, ha, hm']
  set φ := scaleAt i a ha with hφ
  have himg : ∀ T : Set (ι → F), φ '' T = φ.symm ⁻¹' T := fun T => by
    rw [Set.image_eq_preimage_of_inverse (fun x => φ.symm_apply_apply x)
      (fun x => φ.apply_symm_apply x)]
  have hφm : Measurable φ.symm := φ.symm.continuous.measurable
  have hscal : ∀ t : Set F, μ ((fun y => a * y) '' t) = m' * μ t := fun t => by
    rw [distribHaarChar_mul μ (Units.mk0 a ha) t, ← Set.image_smul]
    rfl
  set μs : ι → Measure F := update (fun _ => μ) i (m' • μ) with hμs
  have hsf : ∀ j, SigmaFinite (μs j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self]
      infer_instance
    · simp only [hμs, update_of_ne hj]
      infer_instance
  have hA : Measure.pi μs = Measure.map φ.symm P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hs), ← himg]
    rw [show ((φ : (ι → F) → (ι → F)) '' univ.pi s) =
        (fun x => update x i (a * x i)) '' univ.pi s from rfl, image_update_pi i a ha s, hP,
      Measure.pi_pi]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hscal]
    · simp only [hμs, update_of_ne hj]
  have hB : Measure.pi μs = m' • P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, hP, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
      ← Finset.mul_prod_erase Finset.univ (fun j => μs j (s j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => μ (s j)) (Finset.mem_univ i)]
    have herase : ∏ j ∈ Finset.univ.erase i, μs j (s j) = ∏ j ∈ Finset.univ.erase i, μ (s j) :=
      Finset.prod_congr rfl fun j hj => by
        simp only [hμs, update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [herase]
    simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    ring
  have hmap : Measure.map φ.symm P = m' • P := hA.symm.trans hB
  have hPS : P (φ '' S) = m' * P S := by
    rw [himg, ← Measure.map_apply hφm hS, hmap, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
  have hνP : ν = ν.addHaarScalarFactor P • P := Measure.isAddLeftInvariant_eq_smul ν P
  show ν (φ '' S) = modF F a * ν S
  rw [hmod, hνP, Measure.smul_apply, Measure.smul_apply, hPS, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul]
  ring
end PI.NglqJacSplitW
