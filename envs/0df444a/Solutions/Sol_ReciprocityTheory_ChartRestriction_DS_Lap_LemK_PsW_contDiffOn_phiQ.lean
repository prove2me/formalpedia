-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.contDiffOn_phiQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:16.307515+00:00
-- url     : https://prove2.me/submissions/82ba35e3-c6ee-4257-892b-b6216523f8ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiff_lead
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiff_lead


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ ω (PhiQ μ) (OmegaSet n : Set 𝕄) := by
  show ContDiffOn ℂ ω (fun y : 𝕄 => ∏ i : Fin n, lead ((i : ℕ) + 1) y ^ (-(μ i - muNext μ i)))
    (OmegaSet n : Set 𝕄)
  refine contDiffOn_prod fun i _ => ?_
  have hne : ∀ y ∈ (OmegaSet n : Set 𝕄), lead ((i : ℕ) + 1) y ≠ 0 := fun y hy =>
    (show ∀ j : Fin n, lead ((j : ℕ) + 1) y ≠ 0 from hy) i
  have hg : ContDiffOn ℂ ω (fun y : 𝕄 => lead ((i : ℕ) + 1) y) (OmegaSet n : Set 𝕄) :=
    (contDiff_lead _).contDiffOn
  rcases Int.eq_nat_or_neg (-(μ i - muNext μ i)) with ⟨k, hk | hk⟩
  · simp only [hk, zpow_natCast]
    exact hg.pow k
  · simp only [hk, _root_.zpow_neg, zpow_natCast]
    exact (hg.pow k).inv fun y hy => pow_ne_zero _ (hne y hy)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
