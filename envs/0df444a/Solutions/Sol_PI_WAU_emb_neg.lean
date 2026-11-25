-- Prove2me | solution 1 for PI.WAU.emb_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:49.301821+00:00
-- url     : https://prove2.me/submissions/a3320e8f-82d5-44e3-88ac-b54ee21ba2f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Theorems.Thm_PI_WAU_coord_emb
import Theorems.Thm_PI_WAU_coord_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
namespace PI.WAU
theorem _root_.solution (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]
end PI.WAU
