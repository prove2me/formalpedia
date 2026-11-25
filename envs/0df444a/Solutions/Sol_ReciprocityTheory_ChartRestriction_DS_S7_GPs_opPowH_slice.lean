-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPowH_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:25:26.834944+00:00
-- url     : https://prove2.me/submissions/dd6cc381-77b0-4792-ae45-b879e26b1118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_isOpen_kappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_dAtW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_DH_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_opPowH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_lhol_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_congr


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
    (m : ℕ) : ∀ a b, ∀ p ∈ Wset n, opPow (fun a b => DH (M a b)) m a b g p =
      opPow (fun a b => Lhol (M a b)) m a b (fun y => g (y, p.2)) p.1 := by
  induction m with
  | zero =>
    intro a b p hp
    simp only [opPow]
    split_ifs <;> rfl
  | succ m ih =>
    intro a b p hp
    simp only [opPow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [DH_slice (M a c) (dAtW (sm_opPowH M hg m c b) hp)]
    have hV : IsOpen {y : Matrix (Fin n) (Fin n) ℂ | (y, p.2) ∈ Wset n} :=
      isOpen_kappaOpenNeighbourhood.preimage (continuous_id.prodMk continuous_const)
    exact GPs.lhol_congr hV (fun y hy => ih c b (y, p.2) hy) (M a c) hp
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
