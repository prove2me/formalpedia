-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.deg_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:10.122725+00:00
-- url     : https://prove2.me/submissions/9a662ddf-9470-4f6c-aa5f-742f72172169

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
variable {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) : Deg E (d + 1) g := by
  induction hg with
  | one d => exact Deg.one _
  | add _ _ ih1 ih2 => exact Deg.add ih1 ih2
  | smul c _ ih => exact Deg.smul c ih
  | om p _ ih => exact Deg.om p ih
  | perm σ _ ih => exact Deg.perm σ ih
end PositivityTheory.Rg.Cz.HeightVanishing
