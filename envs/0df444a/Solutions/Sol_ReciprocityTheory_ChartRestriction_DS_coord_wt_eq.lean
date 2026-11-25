-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coord_wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:04.307806+00:00
-- url     : https://prove2.me/submissions/32751bd5-2bb2-4809-8ab8-1165bc83b5a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coord_comp_sg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {ν : Fin n → ℝ} {f : Fock n}
    (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) {s : Finset (Fin (n * n))}
    (hs : (fockBasis n).coord s f ≠ 0) : ν = fockWt ε s := by
  funext c
  have h1 : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c) f =
      ((ν c : ℝ) : ℂ) * (fockBasis n).coord s f := by
    rw [LinearMap.comp_apply, hf c, map_smul, smul_eq_mul]
  rw [coord_comp_sg, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := mul_right_cancel₀ hs h1
  exact_mod_cast h2.symm
end ReciprocityTheory.ChartRestriction.DS
