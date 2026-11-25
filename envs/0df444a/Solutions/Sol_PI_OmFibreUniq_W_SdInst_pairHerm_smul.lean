-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.pairHerm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:08.741552+00:00
-- url     : https://prove2.me/submissions/6bd4e802-4ff1-4949-8af5-e76698400fd9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.OmFibreUniq.W.SdInst
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) (c : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (c • S) T = c * pairHerm (Fv F v) σ a S T := by
  unfold pairHerm
  have h : ∑ i, ∑ j, ((c • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j *
      (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i =
      c • ∑ i, ∑ j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j *
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact smul_mul_assoc c _ _
  rw [h, map_smul, smul_eq_mul]
  ring
end PI.OmFibreUniq.W.SdInst
