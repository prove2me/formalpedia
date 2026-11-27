-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_cartan_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:50.942328+00:00
-- url     : https://prove2.me/submissions/e8bc7222-b778-439b-bda7-e9c268a2fe0e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    (∀ a : Fin n, ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1)) *ᵥ
      (fun _ : Unit => (1 : ℂ)) = (((0 : Fin n → ℝ) a : ℝ) : ℂ) • (fun _ : Unit => (1 : ℂ))) ∧
    (∀ a b : Fin n, a < b → ε a = ε b →
      ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) *ᵥ
        (fun _ : Unit => (1 : ℂ)) = 0) ∧
    (fun _ : Unit => (1 : ℂ)) ≠ 0 ∧
    Formalism.REAL.KHighest ε (kunits (trivialKType ε)) 0 (trivialKType ε).w ∧ (trivialKType ε).w ≠ 0 := by
  refine ⟨fun a => by ext; simp, fun a b _ _ => by ext; simp, fun h => by simpa using congrFun h (), ?_, ?_⟩
  · exact ⟨fun a => (trivialKType ε).w_wt a, fun a b hab he => (trivialKType ε).w_hw a b hab he⟩
  · show (1 : ℂ) ≠ 0; exact one_ne_zero
end ReciprocityTheory.ChartRestriction.DS.HW
