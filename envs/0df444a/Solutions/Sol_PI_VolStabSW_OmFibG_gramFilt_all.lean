-- Prove2me | solution 1 for PI.VolStabSW.OmFibG.gramFilt_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:19.946496+00:00
-- url     : https://prove2.me/submissions/2dd8a6c9-137b-4bca-b517-4fef3b58fd6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
import Theorems.Thm_PI_VolStabSW_OmFibG_gramFilt_gen
import Theorems.Thm_PI_VolStabSW_OmFibG_gramFilt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OmFibG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW.OmFibG
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (a : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (x : Fin a → Fin M → Fv F v ⊗[F] E) (hx : LinearIndependent (Fv F v ⊗[F] E) x) :
    FiltConcl σ hσ M J hJ a v d b x := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact gramFilt_zero σ hσ M J hJ v d b x
  · exact gramFilt_gen σ hσ M J hJ hdet a ha v d b x hx
end PI.VolStabSW.OmFibG
