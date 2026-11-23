-- Prove2me | solution 1 for PIW.ClassFinD.Icf.v_unit_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:49.370872+00:00
-- url     : https://prove2.me/submissions/9690c07e-6d84-4194-88df-5f646e4853b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Theorems.Thm_PIW_ClassFinD_Icf_v_unit_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PIW.ClassFinD.Icf
theorem _root_.solution (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := by
  intro h
  have := v_unit_mul_inv b w
  rw [h, zero_mul] at this
  exact zero_ne_one this
end PIW.ClassFinD.Icf
