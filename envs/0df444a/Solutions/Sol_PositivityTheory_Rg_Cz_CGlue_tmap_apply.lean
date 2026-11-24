-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.tmap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:50.235042+00:00
-- url     : https://prove2.me/submissions/c902fb01-4f24-4b5f-886f-edb45e722d3e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) :
    tmap Jh f = ∑ I, f I ⊗ₜ (fun m => Jh m I) := by
  simp [tmap]
end PositivityTheory.Rg.Cz.CGlue
