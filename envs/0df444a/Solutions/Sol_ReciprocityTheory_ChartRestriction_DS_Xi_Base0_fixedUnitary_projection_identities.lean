-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_projection_identities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:30.400521+00:00
-- url     : https://prove2.me/submissions/9d63d29f-917f-4426-ac1a-d644324628b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_Pk_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_one_sub_mul_Pk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) :
    hᴴ * h = 1 ∧ h * Pk k = Pk k ∧ hᴴ * Pk k = Pk k ∧ Pk k * h = Pk k := by
  obtain ⟨hU, -, hv⟩ := hh
  have hU' : hᴴ * Hpk k 0 * h = Hpk k 0 := hU
  have hcol : ∀ i, h i (iK k) = if i = iK k then 1 else 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have hP : h * Pk k = Pk k := by
    ext i j
    by_cases hj : iK k = j
    · subst hj
      by_cases hi : i = iK k
      · subst hi
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol]
      · have hi' : iK k ≠ i := fun e => hi e.symm
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol, hi, hi']
    · simp [Pk, Matrix.mul_apply, Matrix.single_apply, hj]
  have hsP : hᴴ * Pk k = Pk k := by
    have e1 : hᴴ * Hpk k 0 * h * Pk k = Hpk k 0 * Pk k := by rw [hU']
    rw [Matrix.mul_assoc, hP, hpk0, Matrix.mul_assoc, one_sub_mul_Pk, Matrix.mul_neg] at e1
    exact neg_inj.mp e1
  have hPh : Pk k * h = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, hP, hsP, hPh⟩
  have e2 := hU'
  rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hsP, hPh] at e2
  exact sub_left_inj.mp e2
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
