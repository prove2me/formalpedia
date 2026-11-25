-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.pairHerm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:07.102809+00:00
-- url     : https://prove2.me/submissions/002845cb-1083-4311-913d-d8bc9ae11d77

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
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S T = pairHerm (Fv F v) σ a T S := by
  unfold pairHerm
  have h : ∑ i, ∑ j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j * (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i =
      ∑ i, ∑ j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [h]
end PI.OmFibreUniq.W.SdInst
