-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.bStepBase_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:07.80783+00:00
-- url     : https://prove2.me/submissions/f0414098-c2ff-4e8a-b645-02b8309007cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_BStepSuccOf

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
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) : BStepBase := by
  obtain ⟨-, -, -, -, hNB, -⟩ := hB2
  intro k _ δ _
  refine ⟨1, one_pos, fun s _ z _ _ μN hμ => ?_⟩
  set o : Mt k 0 := ((1 : Mat k 0) : Mt k 0) with ho
  have hc : μN ({o}ᶜ : Set (Mt k 0)) = 0 := by
    have h := hμ.conc; rw [hNB k] at h; exact h
  have hr : μN.restrict {o} = μN :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [Set.compl_def] using hc))
  unfold IInt
  rw [← hr, lintegral_singleton]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (hμ.finite_compact _ isCompact_singleton)
end ReciprocityTheory.ChartRestriction.DS.Xi
