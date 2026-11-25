-- Prove2me | solution 1 for PI.VolStabW.intA_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:29.001817+00:00
-- url     : https://prove2.me/submissions/ba764f21-8299-4cd6-a2ab-f35b123f835a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Theorems.Thm_PI_VolStabW_intA_zero
import Theorems.Thm_PI_VolStabW_intA_add

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
theorem _root_.solution {ι : Type} (t : Finset ι) (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ t, intA b v (f i)) :
    intA b v (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using intA_zero
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact intA_add (hf x (Finset.mem_insert_self x t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.VolStabW
