-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.iic_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:15.926579+00:00
-- url     : https://prove2.me/submissions/4840da4f-0d6d-4b95-ac9f-08f650207c91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd

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
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
