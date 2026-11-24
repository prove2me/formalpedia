-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:27.384322+00:00
-- url     : https://prove2.me/submissions/6a325a8a-a074-448a-8f1f-fe2b4d59ffb5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution (p : P) (g : P → ℂ) : ∏ q, g q = g p * ∏ q ∈ Finset.univ.erase p, g q :=
  (Finset.mul_prod_erase _ g (Finset.mem_univ p)).symm
end PositivityTheory.Rg.Cz.TGK
