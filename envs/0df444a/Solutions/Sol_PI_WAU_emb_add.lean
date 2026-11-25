-- Prove2me | solution 1 for PI.WAU.emb_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:49.011586+00:00
-- url     : https://prove2.me/submissions/44a9c988-b3fd-487e-8a4f-c545850cf42a

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
theorem _root_.solution (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add, coord_emb, coord_emb, coord_emb]
end PI.WAU
