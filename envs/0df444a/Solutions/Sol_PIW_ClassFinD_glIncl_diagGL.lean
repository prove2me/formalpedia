-- Prove2me | solution 1 for PIW.ClassFinD.glIncl_diagGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:10.696883+00:00
-- url     : https://prove2.me/submissions/2e448834-460a-4842-9359-5c4450fb34ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Theorems.Thm_PIW_ClassFinD_diagGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain
namespace PIW.ClassFinD
theorem _root_.solution (F : Type) [Field F] [NumberField F] (n : ℕ) (f : Fin n → Fˣ) :
    glIncl F n (diagGL n f) =
      diagGL n (fun i => Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (f i)) := by
  apply Units.ext
  ext i j
  simp [diagGL_val, Matrix.diagonal_apply, glIncl, apply_ite]
end PIW.ClassFinD
