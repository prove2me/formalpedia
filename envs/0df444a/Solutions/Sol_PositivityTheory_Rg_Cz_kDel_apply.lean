-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kDel_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:25.696066+00:00
-- url     : https://prove2.me/submissions/44125978-654f-42b8-8658-5bb028c6f005

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Theorems.Thm_PositivityTheory_Rg_Cz_kSum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (v : Fin n → P) :
    kDel T b θ v = ∑ i, T (b i) (θ (Matrix.vecCons (b i) v)) := by
  unfold kDel
  rw [kSum_apply]
  rfl
end PositivityTheory.Rg.Cz
