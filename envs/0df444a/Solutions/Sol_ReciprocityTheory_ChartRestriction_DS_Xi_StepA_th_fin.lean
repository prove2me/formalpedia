-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:32.388511+00:00
-- url     : https://prove2.me/submissions/df079a11-3f85-47bc-955b-3ca136ea4d34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_ga_yx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_tm_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_chF_meas

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k) (t : Fin (1 + r' + 1) → ℝ)
    (hν : CHCond (1 + r') fun l => t l - s0N (1 + r') (k - 1) l) :
    (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) < ∞ := by
  obtain ⟨-, -, -, -, -, hCL, -, hInv, -⟩ := hB2
  obtain ⟨hF1, hF2⟩ := hF k r' hk
  have hpt : ∀ x : HPar k r', (∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) =
      ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
        (hcoord k r' (ThFin.tm k r' x)) := by
    intro x
    unfold ThFin.chF
    refine Finset.prod_congr rfl fun l _ => ?_
    have hd : 0 ≤ de (hcoord k r' (ThFin.tm k r' x)) l := Real.sqrt_nonneg _
    have he : ((2 : ℕ) : ℝ) * (-t l / 2) =
        -(s0N (1 + r') (k - 1) l + (t l - s0N (1 + r') (k - 1) l)) := by
      push_cast; ring
    rw [ThFin.ga_yx hCL hInv k r' x l, hF1, ← Real.rpow_natCast, ← Real.rpow_mul hd, he]
  calc (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2)))
      = ∫⁻ x : HPar k r', ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
          (hcoord k r' (ThFin.tm k r' x)) := lintegral_congr hpt
    _ = ∫⁻ y, ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l) y :=
        (hF2.comp (ThFin.tm_mp k r')).lintegral_comp (ThFin.chF_meas _ _ _)
    _ < ∞ := hCH (1 + r') (k - 1) _ hν
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
