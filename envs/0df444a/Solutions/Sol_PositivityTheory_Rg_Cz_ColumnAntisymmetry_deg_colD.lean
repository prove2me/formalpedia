-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_colD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:52.986168+00:00
-- url     : https://prove2.me/submissions/3008b483-b26c-4f36-bb23-550d2b065c0d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_factor
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_prod
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_npairs_eq

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
theorem _root_.solution {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) :
    Deg E (npairs col) (colD E col : Module.End ℂ (TV n M (Fin m))) := by
  have h := deg_prod m
    (fun j => (List.ofFn fun i : Fin m => if i < j ∧ col i = col j then xJ E i - xJ E j + 1 else 1).prod)
    (fun j => ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0)
    (fun j => deg_prod m _ _ (fun i => deg_factor i j _))
  rw [npairs_eq] at h
  exact h
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
