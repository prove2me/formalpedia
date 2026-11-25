-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.crd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:00.0066+00:00
-- url     : https://prove2.me/submissions/ec3f369c-4412-4db9-99f6-28b06d77995c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_sum
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_eq_sum_crd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (y z : R ⊗[F] E) (k : Fin d) :
    crd b R (y * z) k = ∑ i, ∑ j, crd b R y i * crd b R z j *
      algebraMap F R (b.repr (b i * b j) k) := by
  conv_lhs => rw [eq_sum_crd b R y, eq_sum_crd b R z]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, crd_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [crd, map_smul, Finsupp.smul_apply, Algebra.TensorProduct.basis_repr_tmul, smul_eq_mul,
    Finsupp.mapRange_apply, one_mul]
end PI.VolStabW.FiniteThetaCoordinates
