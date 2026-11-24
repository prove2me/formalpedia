-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.hpk0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:14.232424+00:00
-- url     : https://prove2.me/submissions/4359b764-479b-4a37-b269-a60504cd6668

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight

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
theorem _root_.solution (k : ℕ) : Hpk k 0 = 1 - 2 • Pk k := by
  ext i j
  have hi := i.isLt
  have hle : i.val ≤ k := by omega
  by_cases hij : i = j
  · subst hij
    by_cases hik : i.val = k
    · simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik]
      norm_num
    · have hik' : k ≠ i.val := fun h => hik h.symm
      simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik, hik', hle]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hv]
    omega
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
