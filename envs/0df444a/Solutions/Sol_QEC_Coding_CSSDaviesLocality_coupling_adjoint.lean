-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.coupling_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:17.182499+00:00
-- url     : https://prove2.me/submissions/96700f78-7a34-465a-bbca-0f2aa9b63239

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
namespace QEC.Coding.CSSDaviesLocality
theorem _root_.solution (q : ι) (a : Axis) : LinearMap.adjoint (coupling q a) = coupling q a :=
  adjoint_toHermitianQubitOperator_eq_self _
end QEC.Coding.CSSDaviesLocality
