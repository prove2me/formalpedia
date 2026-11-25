-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.cLam_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:07.571091+00:00
-- url     : https://prove2.me/submissions/47025084-36f9-4e62-92bd-e4b971f8c1e6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC

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
theorem _root_.solution (lam : TV n M P →ₗ[ℂ] ℂ) (v : TV n M P) : lam v = ∑ I, cLam lam I (v I) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  rfl
end PositivityTheory.Rg.Cz.TGK
