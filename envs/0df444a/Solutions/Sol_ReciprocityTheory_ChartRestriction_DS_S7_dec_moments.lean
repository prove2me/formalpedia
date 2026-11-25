-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dec_moments
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:03.966938+00:00
-- url     : https://prove2.me/submissions/142e526c-b404-4d68-bfc9-861dcd3ee312

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_zero_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_mass
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_mean
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_rhs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_var


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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (i : ℕ) (hi : i ≤ n) :
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 = 1) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) = 0) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) ∧
    (∀ J : {J : Finset (Fin n) // J.card = i},
        |∑ j ∈ J.1, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y)) := by
  have hd : ∀ a, Y a a = 0 := fun a => dm_zero_of_eq hYp a a rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := dm_mass hU hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J = 1 := by exact_mod_cast h
    exact h2
  · have h := dm_mean hU hY hd hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) = 0 := by
      exact_mod_cast h
    exact h2
  · have h := (dm_var hU hY hd hi).trans (dm_rhs hY i)
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) ^ 2 =
        ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 := by
      exact_mod_cast h
    exact h2
  · intro J
    exact dm_range hU hY hYp J.1
end ReciprocityTheory.ChartRestriction.DS.S7
