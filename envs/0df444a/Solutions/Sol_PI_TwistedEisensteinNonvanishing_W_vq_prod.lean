-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.vq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:48.824095+00:00
-- url     : https://prove2.me/submissions/6f934cdb-a7d4-4046-b266-391087d21dff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_one

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
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {P}
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ≠ 0) :
    vq P (∏ i ∈ s, f i) = ∑ i ∈ s, vq P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vq_one hN hp hq
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vq_mul hN hp hq (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
end PI.TwistedEisensteinNonvanishing.W
