-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:21.978798+00:00
-- url     : https://prove2.me/submissions/79880b9c-f940-4b24-bba7-a39292b423e2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_zero

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
variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution {d : ℕ} (s : Finset (Fin m)) (f : Fin m → Module.End ℂ (TV n M (Fin m)))
    (hf : ∀ i ∈ s, Deg E d (f i)) : Deg E d (∑ i ∈ s, f i) := by
  classical
  exact Finset.sum_induction f (Deg E d) (fun _ _ ha hb => Deg.add ha hb) (deg_zero d) hf
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
