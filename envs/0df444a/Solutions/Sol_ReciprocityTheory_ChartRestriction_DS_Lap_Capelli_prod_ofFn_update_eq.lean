-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.prod_ofFn_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:24.911812+00:00
-- url     : https://prove2.me/submissions/885b0719-d02b-4d3d-96c9-1f24fb2c14fa

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
theorem _root_.solution {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) :
    ∃ A B : 𝒰, ∀ v, (List.ofFn (Function.update f j v)).prod = A * v * B := by
  induction p with
  | zero => exact j.elim0
  | succ p ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · refine ⟨1, (List.ofFn fun i : Fin p => f i.succ).prod, fun v => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) j'
      refine ⟨f 0 * A, B, fun v => ?_⟩
      have e1 : (fun i : Fin p => Function.update f j'.succ v i.succ) =
          Function.update (fun i => f i.succ) j' v := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ v 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2, h]
      simp only [mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
