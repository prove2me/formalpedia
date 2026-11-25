-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKH.integral_Ssum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:31.675503+00:00
-- url     : https://prove2.me/submissions/139de3c0-375c-4f41-99ff-bb3eaa9a471e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKH_isBlock_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_Ek
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_integrable_of_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_integral_Ek_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKH
variable {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKH
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (A : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (Ssum T μ x A) (muK ε) ∧ ∫ k, Ssum T μ x A k ∂(muK ε) = 0 := by
  have hI : ∀ a b : Fin n, Integrable (fun k => (if b < a then (1 : ℂ) else -1) •
      InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k) (muK ε) := fun a b =>
    InfKA.integrable_of_cont ((InfKA.continuous_Ek T μ hx (InfKA.entryCLM a b) A
      (Matrix.single a b 1)).const_smul (if b < a then (1 : ℂ) else -1))
  refine ⟨integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI a b, ?_⟩
  unfold Ssum
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI a b]
  refine sum_eq_zero fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => hI a b]
  refine sum_eq_zero fun b hb => ?_
  rw [integral_smul (if b < a then (1 : ℂ) else -1)
    (fun k => InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k), InfKA.integral_Ek_block T μ hx _ A (isBlock_single (mem_filter.mp hb).2.1), smul_zero]
end ReciprocityTheory.ChartRestriction.DS.S7.InfKH
