-- Prove2me | solution 1 for PI.VolStabW.RestrProdG.t2_tensor_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:35.12312+00:00
-- url     : https://prove2.me/submissions/61ce1250-72e9-4932-ad05-3342b7b27f91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdG
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_crd
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_eq_sum_crd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdG
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']
end PI.VolStabW.RestrProdG
