-- Prove2me | solution 1 for PI.VolStabW.intA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:18.68278+00:00
-- url     : https://prove2.me/submissions/15c3e613-dee5-4c31-8a9d-b6d3ed2f5b76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Theorems.Thm_PI_VolStabW_intA_sum
import Theorems.Thm_PI_VolStabW_intA_smul
import Theorems.Thm_PI_VolStabW_intA_incl
import Theorems.Thm_PI_VolStabW_incl_eq_tmul
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
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
variable {b v}
namespace PI.VolStabW
theorem _root_.solution (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, PositiveNearLattice.eq_sum_crd b (Fv F v) w, Finset.sum_mul_sum]
  refine intA_sum _ _ fun i _ => intA_sum _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← incl_eq_tmul]
  exact intA_smul (mul_mem (hz i) (hw j)) (intA_incl _ (hg i j))
end PI.VolStabW
