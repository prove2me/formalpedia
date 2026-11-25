-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.pr_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:35.134369+00:00
-- url     : https://prove2.me/submissions/a17c49a1-df1d-4fbd-bb39-11a5070db6b7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution {x y : Pr H n} (h1 : (x.1 : ι) = y.1) (h2 : x.2.1 = y.2.1) (h3 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨⟨τ, hτ⟩, i, c⟩ := x
  obtain ⟨⟨τ', hτ'⟩, i', c'⟩ := y
  dsimp only at h1 h2 h3
  subst h1 h2
  rw [Fin.ext h3]
end PositivityTheory.Rg.Cz.KTy
