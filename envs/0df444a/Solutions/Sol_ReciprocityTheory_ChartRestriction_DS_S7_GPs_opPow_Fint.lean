-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_Fint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:14.190153+00:00
-- url     : https://prove2.me/submissions/317b8257-a99e-4146-8b22-ba76782cc7cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_DH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_lhol_Fint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_Fint_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_opPowH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_lhol_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset
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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hg : ContDiffOn ℂ ∞ g (Wset n)) (m : ℕ) : ∀ a b, ∀ z ∈ Ps1.Uset ε,
      opPow (fun a b => Lhol (M a b)) m a b (Fint T g) z = Fint T (opPow (fun a b => DH (M a b)) m a b g) z := by
  induction m with
  | zero =>
    intro a b z hz
    simp only [opPow]
    split_ifs
    · rfl
    · simp [Fint]
  | succ m ih =>
    intro a b z hz
    simp only [opPow, Finset.sum_apply]
    rw [Fint_sum T Finset.univ _ (fun c _ => sm_DH (M a c) (sm_opPowH M hg m c b)) hz]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GPs.lhol_congr (Ps1.isOpen_Uset (ε := ε)) (fun y hy => ih c b y hy) (M a c) hz]
    exact lhol_Fint T (sm_opPowH M hg m c b) (M a c) hz
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
