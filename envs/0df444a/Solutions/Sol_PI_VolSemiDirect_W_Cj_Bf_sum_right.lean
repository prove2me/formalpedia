-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.Bf_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:47.964998+00:00
-- url     : https://prove2.me/submissions/3248e7ee-0adf-4907-b178-d0858f600e40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq

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
theorem _root_.solution {k : ℕ} (u : Fin M → A ⊗[F] E) (y : Fin k → Fin M → A ⊗[F] E) :
    Bf σ J u (∑ a, y a) = ∑ a, Bf σ J u (y a) := by
  have h : hR A σ J u (∑ a, y a) = ∑ a, hR A σ J u (y a) := by
    simp only [hR, Formalism.UG.hform, Finset.sum_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf
  rw [h, _root_.map_sum]
end PI.VolSemiDirect.W.Cj
