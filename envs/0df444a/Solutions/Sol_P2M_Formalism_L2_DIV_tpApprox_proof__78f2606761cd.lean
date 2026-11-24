-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_tpApprox_proof__78f2606761cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:12.434806+00:00
-- url     : https://prove2.me/submissions/7a69fe26-29fc-4feb-bdaf-0506aabd6794

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_mul_mem_map
import Theorems.Thm_Formalism_L2_DIV_b_approx
import Theorems.Thm_Formalism_L2_DIV_b_under_elt

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E) :
    ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
  obtain ⟨b, t, h⟩ := b_approx D hD0 s
  refine ⟨b, ?_⟩
  rw [h, add_sub_cancel_left]
  exact b_mul_mem_map _ _ hD t
end Formalism.L2.DIV
