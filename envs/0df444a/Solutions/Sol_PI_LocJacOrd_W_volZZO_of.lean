-- Prove2me | solution 1 for PI.LocJacOrd.W.volZZO_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:24.798693+00:00
-- url     : https://prove2.me/submissions/e590bac2-0b2f-49f7-84af-4a26b01ad810

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
import Theorems.Thm_PI_LocJacOrd_W_alp_ne_zero
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
theorem _root_.solution (hB : BoxScale) (hA : AbsMul) : VolZZO (E := E) v := by
  intro r m hfin μ hμ hO
  have hset : ZZOrd (E := E) v r =
      Set.univ.pi fun p : Fin (r + 1) × Fin (r + 1) =>
        {c | sc (E := E) v (alp v r p.1 * alp v r p.2) * c ∈ OEv (E := E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  rw [hset, hB v _ hfin μ (fun p => alp v r p.1 * alp v r p.2)
    (fun p => mul_ne_zero (alp_ne_zero v r p.1) (alp_ne_zero v r p.2)), hO,
    Fintype.prod_prod_type]
  simp only [(hA v).1]
end PI.LocJacOrd.W
