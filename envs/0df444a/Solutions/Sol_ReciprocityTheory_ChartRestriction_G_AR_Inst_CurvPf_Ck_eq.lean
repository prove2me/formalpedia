-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.Ck_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:54.022474+00:00
-- url     : https://prove2.me/submissions/acf75c91-3555-432a-88e0-33491752d681

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_TelePoint
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) :
    Ck X b z u τ k = ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < k ∧ (k : ℕ) ≤ j then
      (Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2) else 0 := by
  calc Ck X b z u τ k
      = ∑ a : Fin r, if (a : ℕ) < k then (Dsg X a)⁻¹ *
          ∑ j : Fin r, (if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0) else 0 :=
        sum_castLE' (Nat.le_of_lt_succ k.isLt) (fun a : Fin r => (Dsg X a)⁻¹ *
          ∑ j : Fin r, if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0)
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < k
      · rw [if_pos ha, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : (k : ℕ) ≤ (j : ℕ)
        · rw [if_pos hj, if_pos ⟨ha, hj⟩]
        · rw [if_neg hj, if_neg (fun h => hj h.2), mul_zero]
      · rw [if_neg ha, eq_comm]
        exact Finset.sum_eq_zero fun j _ => if_neg (fun h => ha h.1)
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
