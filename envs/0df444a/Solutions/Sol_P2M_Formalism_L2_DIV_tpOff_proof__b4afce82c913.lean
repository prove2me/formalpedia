-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:57:26.270157+00:00
-- url     : https://prove2.me/submissions/82c37271-fff0-4e5f-acfc-2210c7d57fbe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_eps_mul_unit
import Theorems.Thm_Formalism_L2_DIV_b_eps_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E) := by
  rw [← b_eps_mul_unit v u hu]
  exact Ideal.mul_mem_right _ _ (b_eps_mem v P hP)
end Formalism.L2.DIV
