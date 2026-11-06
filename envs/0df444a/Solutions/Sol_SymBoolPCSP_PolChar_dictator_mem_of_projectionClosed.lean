-- Prove2me | solution 1 for SymBoolPCSP.PolChar.dictator_mem_of_projectionClosed
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T19:32:47.675393+00:00
-- url     : https://prove2.me/submissions/b04a4992-462e-48bf-8fd2-a2334ed6837b

import Mathlib
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

theorem dictator_mem_of_projectionClosed {D : Type} (F : FunFamily D)
    (hpc : ProjectionClosed F) (hid : ContainsId F) {R : ℕ} (j : Fin R) :
    (fun y : Fin R → D => y j) ∈ F R := by
  have hR : 0 < R := Fin.pos j
  exact hpc 1 R one_pos hR _ hid (fun _ => j)

end SymBoolPCSP.PolChar

open SymBoolPCSP.PolChar PCSPBLPAff.Symmetric in
theorem solution {D : Type} (F : FunFamily D)
    (hpc : ProjectionClosed F) (hid : ContainsId F) {R : ℕ} (j : Fin R) :
    (fun y : Fin R → D => y j) ∈ F R :=
  SymBoolPCSP.PolChar.dictator_mem_of_projectionClosed F hpc hid j
