-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.mem_fixedUnitary_of_unitary_fixes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:16:58.883799+00:00
-- url     : https://prove2.me/submissions/3c1a9d4a-27ef-4829-8b3d-943d0a7ffbd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_Pk_conjTranspose

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
theorem _root_.solution {k : ℕ} {R : Mat k 0} (hu : Rᴴ * R = 1) (hP : R * Pk k = Pk k) : R ∈ U0 k := by
  have hsP : Rᴴ * Pk k = Pk k := by
    calc Rᴴ * Pk k = Rᴴ * (R * Pk k) := by rw [hP]
      _ = Pk k := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hPR : Pk k * R = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, fun a => a.elim0, ?_⟩
  · show Rᴴ * Hpk k 0 * R = Hpk k 0
    rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, Matrix.mul_smul, Matrix.smul_mul,
      hsP, hPR]
  · ext i
    have := congrFun (congrFun hP i) (iK k)
    simpa [Pk, Matrix.mul_apply, Matrix.single_apply, Matrix.mulVec, dotProduct, bvec,
      Pi.single_apply, eq_comm] using this
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
