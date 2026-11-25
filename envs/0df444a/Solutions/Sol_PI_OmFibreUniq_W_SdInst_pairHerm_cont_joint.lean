-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.pairHerm_cont_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:02.540213+00:00
-- url     : https://prove2.me/submissions/25554ccd-d2fa-4ed7-b1a5-2dec30606d98

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
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) :
    Continuous (fun p : HermR (Fv F v) σ a × HermR (Fv F v) σ a =>
      pairHerm (Fv F v) σ a p.1 p.2) := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) := by
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  unfold pairHerm
  refine continuous_const.mul (htr.comp (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => ?_))
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem j i)
end PI.OmFibreUniq.W.SdInst
