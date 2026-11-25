-- Prove2me | solution 1 for PI.VolStabW.intA_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:23.763805+00:00
-- url     : https://prove2.me/submissions/d15cfd60-483b-48fd-a8d2-95f89d5cb686

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Theorems.Thm_PI_VolStabW_intA_sum
import Theorems.Thm_PI_VolStabW_intA_smul
import Theorems.Thm_PI_VolStabW_intA_incl
import Theorems.Thm_PI_VolStabW_incl_eq_tmul
import Theorems.Thm_PI_VolStabW_sigR_incl
import Theorems.Thm_PI_VolStabW_sigR_smul
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
theorem _root_.solution (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, map_sum]
  refine intA_sum _ _ fun i _ => ?_
  rw [sigR_smul, ← incl_eq_tmul, sigR_incl]
  exact intA_smul (hz i) (intA_incl _ (hg i))
end PI.VolStabW
