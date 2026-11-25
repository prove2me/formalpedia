-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.Bf_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:52.877931+00:00
-- url     : https://prove2.me/submissions/0f46d8a3-aed5-4b38-b322-52effb9295b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_smul_left
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_sum_left
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution {k : ℕ} (b : Fin k → Fin M → A ⊗[F] E) (x y : Fin k → A) :
    Bf σ J (∑ a, x a • b a) (∑ c, y c • b c) = ∑ a, ∑ c, x a * (Bf σ J (b a) (b c) * y c) := by
  rw [Bf_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Bf_smul_right]
  ring
end PI.VolSemiDirect.W.Cj
