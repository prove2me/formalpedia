-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_eT_central_d02055daf099
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:56.830323+00:00
-- url     : https://prove2.me/submissions/345fde19-afcf-4f4d-bc4c-002edd207b88

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (a : MonoidAlgebra K Γ) : eT K Γ * a = a * eT K Γ :=
  commute_of_single _ (fun g => by
    apply MonoidAlgebra.coeff_injective
    ext h
    rw [coeff_mul_single_apply, coeff_single_mul_apply, eT_coeff, eT_coeff, mul_one, one_mul]) a
end Formalism.BasicNotions.Examples₂.NZ
