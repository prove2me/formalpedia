-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_prod_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:26.886711+00:00
-- url     : https://prove2.me/submissions/f14533db-3f20-4bf5-8164-3b513226c3b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (y : 𝒰) {p : ℕ} (f : Fin p → 𝒰) :
    y * (List.ofFn f).prod - (List.ofFn f).prod * y =
      ∑ j, (List.ofFn (Function.update f j (y * f j - f j * y))).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h0 : (List.ofFn (Function.update f 0 (y * f 0 - f 0 * y))).prod =
        (y * f 0 - f 0 * y) * (List.ofFn fun i : Fin p => f i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ j' : Fin p,
        (List.ofFn (Function.update f j'.succ (y * f j'.succ - f j'.succ * y))).prod =
          f 0 * (List.ofFn (Function.update (fun i : Fin p => f i.succ) j'
            (y * f j'.succ - f j'.succ * y))).prod := by
      intro j'
      have e1 : (fun i : Fin p => Function.update f j'.succ (y * f j'.succ - f j'.succ * y) i.succ) =
          Function.update (fun i => f i.succ) j' (y * f j'.succ - f j'.succ * y) := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ (y * f j'.succ - f j'.succ * y) 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2]
    have hih := ih (fun i => f i.succ)
    rw [Fin.sum_univ_succ, h0, Finset.sum_congr rfl (fun j' _ => hs j'), ← Finset.mul_sum, ← hih,
      List.ofFn_succ, List.prod_cons]
    noncomm_ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
