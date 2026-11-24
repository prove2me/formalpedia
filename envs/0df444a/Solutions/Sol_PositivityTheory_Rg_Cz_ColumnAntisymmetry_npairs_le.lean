-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.npairs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:38.952797+00:00
-- url     : https://prove2.me/submissions/2ae03410-523e-41de-8488-b4941fd96d85

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_rk_le
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_sum_rk

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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) : npairs col ≤ ∑ p, ((top : ℕ) - I p) := by
  rw [← sum_rk col I hI]
  exact Finset.sum_le_sum fun p _ => rk_le col top htop I hI p
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
