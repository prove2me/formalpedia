-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iK_0f89b4e76fef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:54.110499+00:00
-- url     : https://prove2.me/submissions/db6015ce-c440-4f7c-917f-fd2e437cc79a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_iW_ne_iK


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
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (hk : 1 ≤ k) : phiV' k 0 0 (iK k) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, (iW_ne_iK hk).symm]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
