-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.detA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:15.975911+00:00
-- url     : https://prove2.me/submissions/5bb1a03a-6ee7-4db6-a542-1475987d9048

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_PositivityTheory_ThKG_Std_detB
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
theorem _root_.solution {b : ℕ} (N : Matrix (Fin (b + 2)) (Fin (b + 2)) k) (h0 : ∀ i, i ≠ 0 → N i (Fin.last _) = 0)
    (h1 : ∀ j, N (Fin.last _) (mid j) = 0) : N.det = -N 0 (Fin.last _) * N (Fin.last _) 0 * (N.submatrix mid mid).det := by
  have hm : ∀ i : Fin b, (mid i).rev = mid i.rev := fun i => Fin.ext (by simp [mid]; omega)
  have := detB ((N.submatrix Fin.revPerm Fin.revPerm)ᵀ) (fun j hj => h0 _ fun h => hj (by simpa using congrArg Fin.rev h))
    (fun i => by simpa [hm] using h1 i.rev)
  rw [det_transpose, det_submatrix_equiv_self] at this
  rw [this, ← det_submatrix_equiv_self Fin.revPerm (N.submatrix mid mid), ← det_transpose ((N.submatrix mid mid).submatrix _ _)]
  congr 2
  · simp
  · simp
  · ext i j; simp [hm]
end PositivityTheory.ThKG.Std
