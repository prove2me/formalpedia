-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.detB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:44.218875+00:00
-- url     : https://prove2.me/submissions/328ea284-798d-4983-b083-b1842a94fcd5

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {b : ℕ} (N : Matrix (Fin (b + 2)) (Fin (b + 2)) k) (h0 : ∀ j, j ≠ Fin.last _ → N 0 j = 0)
    (h1 : ∀ i, N (mid i) 0 = 0) : N.det = -N 0 (Fin.last _) * N (Fin.last _) 0 * (N.submatrix mid mid).det := by
  rw [det_succ_row_zero, Finset.sum_eq_single (Fin.last _) (fun j _ hj => by rw [h0 j hj]; simp) (by simp),
    Fin.succAbove_last, det_succ_column_zero, Finset.sum_eq_single (Fin.last _) (fun i _ hi => by
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      have := h1 i
      simp only [mid] at this
      simp [this]) (by simp), Fin.succAbove_last]
  have : (N.submatrix Fin.succ Fin.castSucc).submatrix Fin.castSucc Fin.succ = N.submatrix mid mid := by
    ext i j; rfl
  rw [this]
  simp only [Fin.val_last, submatrix_apply, Fin.succ_last, Fin.castSucc_zero, pow_succ]
  have : ((-1 : k) ^ b) * (-1) ^ b = 1 := by rw [← mul_pow]; simp
  linear_combination (-N 0 (Fin.last (b + 1)) * N (Fin.last (b + 1)) 0 * (N.submatrix mid mid).det) * this
end PositivityTheory.ThKG.Std
