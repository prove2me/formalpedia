-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:50.882818+00:00
-- url     : https://prove2.me/submissions/9b0e1c84-e8d6-4186-816d-b77abb62473f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK
namespace Formalism.L2.Pj.QAt.TieLD
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
  unfold LiesOver at hw
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' la.asIdeal w.asIdeal la.ne_bot]
  apply Ideal.IsDedekindDomain.ramificationIdx'_ne_zero <;>
    first
          | exact la.ne_bot
          | exact w.ne_bot
          | exact hlo
          | exact w.isPrime
          | infer_instance
          | exact Ideal.map_le_iff_le_comap.mpr hw.ge
          | exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact (Ideal.map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact Ideal.map_ne_bot_of_ne_bot la.ne_bot
          | exact (trivial : True)
end Formalism.L2.Pj.QAt.TieLD
