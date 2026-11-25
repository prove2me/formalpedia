-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:51.816007+00:00
-- url     : https://prove2.me/submissions/395ae769-8375-4ca4-ba7b-e030c4468470

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_stabClassFinite_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_restrict_of
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_SigConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (hMono : ClassSetMono) (hIdx : ClassSetFinIdx)
    (hMap : ClassSetMap) (hTop : KgNhd) (hSig : SigConj) (hE : FrameExists) (hIso : FrameIso)
    (hG : FrameGram) (hRat : FrameRat) (hLev : LevelStep) : StabClassFinite :=
  stabClassFinite_of hMono hIdx hMap hTop hSig
    (fun I S hS => restrict_of hE hIso hG hRat hLev I S hS)
end PI.UnitaryGroupMassFormula.InHHClassFin
