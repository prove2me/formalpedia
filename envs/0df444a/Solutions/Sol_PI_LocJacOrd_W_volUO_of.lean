-- Prove2me | solution 1 for PI.LocJacOrd.W.volUO_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:18.707518+00:00
-- url     : https://prove2.me/submissions/ab4e00bb-bb0b-4a01-848b-a2ffdeb980a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
import Theorems.Thm_PI_LocJacOrd_W_secondCountable_Fv
import Theorems.Thm_PI_LocJacOrd_W_locallyCompact_Fv
import Theorems.Thm_PI_LocJacOrd_W_alp_ne_zero
import Theorems.Thm_PI_LocJacOrd_W_absV_inv
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
theorem _root_.solution (hB : BoxScale) (hA : AbsMul) : VolUO (E := E) v := by
  intro r m hfin μ hμ hO
  have hset : UO (E := E) v r =
      Set.univ.pi fun q : UIdx r =>
        {c | sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * c ∈ OEv (E := E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  have e1 := hB v (UIdx r) hfin μ (fun q => (alp v r q.1.1)⁻¹ * alp v r q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v r q.1.1)) (alp_ne_zero v r q.1.2))
  rw [← hset, hO] at e1
  have : SecondCountableTopology (Fv F v) := secondCountable_Fv F v
  have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  unfold localVolumeOrdinary
  rw [Measure.prod_prod, ENNReal.toReal_mul, e1, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [(hA v).1, absV_inv v hA _ (alp_ne_zero v r q.1.1)]
  simp only [mul_inv, inv_pow, inv_inv, div_eq_mul_inv, mul_pow]
  ring
end PI.LocJacOrd.W
