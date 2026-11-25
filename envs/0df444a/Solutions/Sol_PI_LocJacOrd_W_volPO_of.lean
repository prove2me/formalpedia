-- Prove2me | solution 1 for PI.LocJacOrd.W.volPO_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:13.76185+00:00
-- url     : https://prove2.me/submissions/101ea063-bcae-4ef4-b416-6f5549ad1378

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
import Theorems.Thm_PI_LocJacOrd_W_alp_ne_zero
import Theorems.Thm_PI_LocJacOrd_W_absV_pow
import Theorems.Thm_PI_LocJacOrd_W_Ar_alp_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocJacOrd.W
theorem _root_.solution (hB : BoxScale) (hA : AbsMul) : VolPO (E := E) v := by
  intro r m hfin μ hμ hO l
  have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPOrd (E := E) v r l =
      Set.univ.pi fun _ : Unit => {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v} := by
    ext z
    simp only [PPOrd, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [hset, hB v Unit hfin μ (fun _ => alp v r l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v r l)), hO]
  simp only [Finset.univ_unique, Finset.prod_singleton, absV_pow v hA]
  ring
end PI.LocJacOrd.W
