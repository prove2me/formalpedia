-- Prove2me | solution 1 for PI.VolStabW.repr_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:42.433979+00:00
-- url     : https://prove2.me/submissions/e4c4e482-5c5a-43a9-b67c-c4f9a8a56753

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW
theorem _root_.solution {ι ι' : Type} [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E) (z : Fv F v ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr z k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j *
        algebraMap F (Fv F v) (b.repr (c j) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) c).sum_repr z]
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.smul_apply, Finsupp.mapRange_apply]
end PI.VolStabW
