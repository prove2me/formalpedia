-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.Bf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:01.226394+00:00
-- url     : https://prove2.me/submissions/21eeac83-7099-4bfd-9a8e-aeca0d75ea18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
import Theorems.Thm_PI_VolSemiDirect_W_Cj_sigR_algebraMap
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trace_algebraMap_mul

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
theorem _root_.solution (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J (c • u) v = c * Bf σ J u v := by
  have h : hR A σ J (c • u) v = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]
end PI.VolSemiDirect.W.Cj
