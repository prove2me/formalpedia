-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_opPowH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:54.450245+00:00
-- url     : https://prove2.me/submissions/ce170f24-189f-415f-a5c8-bedda93c2041

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_DH

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (hg : ContDiffOn ℂ ∞ g (Wset n))
    (m : ℕ) (a b : Fin n) : ContDiffOn ℂ ∞ (opPow (fun a b => DH (M a b)) m a b g) (Wset n) := by
  induction m generalizing a b with
  | zero =>
    simp only [opPow]
    split_ifs
    · exact hg
    · exact contDiff_zero_fun.contDiffOn
  | succ m ih =>
    simp only [opPow]
    have : (∑ c, DH (M a c) (opPow (fun a b => DH (M a b)) m c b g)) =
        fun p => ∑ c, DH (M a c) (opPow (fun a b => DH (M a b)) m c b g) p := by
      funext p; simp [Finset.sum_apply]
    rw [this]
    exact ContDiffOn.sum fun c _ => sm_DH _ (ih c b)
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
