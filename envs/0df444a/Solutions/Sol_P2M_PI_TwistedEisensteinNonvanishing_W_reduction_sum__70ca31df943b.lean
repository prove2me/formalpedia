-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:24.674114+00:00
-- url     : https://prove2.me/submissions/dafa290e-41fd-49fb-9754-a3af4feb5a55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_redP_zero__1dd274e30ba1
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_add__59831082df14
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [redP_zero']
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      reduction_add' (hf i (Finset.mem_insert_self i s))
        (ia_sum (P := P) s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
end PI.TwistedEisensteinNonvanishing.W
