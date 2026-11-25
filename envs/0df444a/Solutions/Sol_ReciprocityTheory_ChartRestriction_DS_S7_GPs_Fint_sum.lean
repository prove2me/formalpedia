-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.Fint_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:23.096021+00:00
-- url     : https://prove2.me/submissions/824ca6ab-868e-49b6-a74c-57bdf1e0b386

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_int_int

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
variable [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) {ι : Type*} (s : Finset ι)
    (G : ι → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hG : ∀ i ∈ s, ContDiffOn ℂ ∞ (G i) (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Fint T (∑ i ∈ s, G i) x = ∑ i ∈ s, Fint T (G i) x := by
  unfold Fint
  rw [← Finset.smul_sum]
  congr 1
  simp only [Finset.sum_apply, Finset.sum_smul]
  exact integral_finset_sum s fun i hi => int_int T (hG i hi) hx
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
