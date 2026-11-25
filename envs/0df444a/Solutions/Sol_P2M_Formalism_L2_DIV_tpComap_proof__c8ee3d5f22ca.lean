-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_tpComap_proof__c8ee3d5f22ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:19.893526+00:00
-- url     : https://prove2.me/submissions/dce2053d-0ad0-4c84-8e16-0fa263cbac33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_under_elt
import Theorems.Thm_Formalism_L2_DIV_b_comap

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E)
    (hc : toRInt F E c ∈ P.asIdeal.map (toRInt F E)) : c ∈ P.asIdeal := by
  obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
  exact b_comap P.asIdeal D hD0 hD c hc
end Formalism.L2.DIV
