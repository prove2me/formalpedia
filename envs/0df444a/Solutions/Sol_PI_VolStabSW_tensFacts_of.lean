-- Prove2me | solution 1 for PI.VolStabSW.tensFacts_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:55.40157+00:00
-- url     : https://prove2.me/submissions/7948e91a-a5d1-468d-b15e-01cf698a7d77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Theorems.Thm_PI_VolStabSW_TensAllW_isOpen_linIndep
import Theorems.Thm_PI_VolStabSW_continuous_gramR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW
namespace PI.VolStabSW
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) :
    TensFacts F E σ M J a R := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_,
    isOpen_linIndep (Module.finBasis F E) R hU hL⟩
  · exact isClosed_HermR (R := R) σ a
  · exact continuous_gramR (R := R) σ J
  · exact fun X => gramR_mem (R := R) σ hσ J hJ X
end PI.VolStabSW
