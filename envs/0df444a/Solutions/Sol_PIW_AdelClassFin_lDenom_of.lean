-- Prove2me | solution 1 for PIW.AdelClassFin.lDenom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:44.793722+00:00
-- url     : https://prove2.me/submissions/9f224223-5dcb-4f4d-9956-f2da678a8a31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_DictLat_iv_single
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h : DDenom) : LDenom := by
  intro I y
  have hL : ∀ l ∈ I.L, l ∈ ivSub I (denomSub I h) := fun l hl => by
    show ∃ m : ℕ, 0 < m ∧ (m : I.E ⊗[I.F] Af I.F) • iv I l ∈ I.Lf
    exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact DictLat.iv_mem I hl⟩
  have htop : ivSub I (denomSub I h) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    exact fun l hl => hL l hl
  have hei : ∀ i, Pi.single i (1 : I.E ⊗[I.F] Af I.F) ∈ denomSub I h := by
    intro i
    have hs : Pi.single i (1 : I.E) ∈ ivSub I (denomSub I h) := by
      rw [htop]
      exact Submodule.mem_top
    rw [← DictLat.iv_single]
    exact hs
  have hyeq : y = ∑ i, y i • Pi.single i (1 : I.E ⊗[I.F] Af I.F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y ∈ denomSub I h := by
    rw [hyeq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hei i)
  exact hy
end PIW.AdelClassFin
