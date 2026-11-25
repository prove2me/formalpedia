-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.haar_univ_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:31.092512+00:00
-- url     : https://prove2.me/submissions/5b06dac8-a468-45dc-8763-b00601f8c52d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_inWb_iK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_Tz_iK

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
theorem _root_.solution (hCW : CompactW) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ν Set.univ < ∞ := by
  obtain ⟨U, hU⟩ : ∃ U : Set (Mt k 0), U = U0 k := ⟨_, rfl⟩
  have hK : IsCompact U := by rw [hU]; exact hCW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hc : ν Uᶜ = 0 := by rw [hU]; exact hν.conc
  have h1 : ν U < ∞ := hν.finite_compact _ hK
  have h2 := measure_union_le (μ := ν) U Uᶜ
  rw [Set.union_compl_self, hc, add_zero] at h2
  exact lt_of_le_of_lt h2 h1
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
