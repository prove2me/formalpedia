-- Prove2me | solution 1 for PI.OmFibreUniq.W.omUnique_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:59.2088+00:00
-- url     : https://prove2.me/submissions/e0cb76d9-8013-43e4-bc90-d172e42d0676

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OmFibreUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Theorems.Thm_PI_OmFibreUniq_W_dX_haar
import Theorems.Thm_PI_OmFibreUniq_W_dT_haar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
namespace PI.OmFibreUniq.W
theorem _root_.solution (h0 : SdEx) (h1 : FibEx) (h4 : FibUniq) : OmUnique σ J ψ v a := by
  intro hS
  obtain ⟨hX, hT⟩ := h0 σ J ψ v a hS
  exact ⟨h1 σ J v a hS.1 hS.2.1 _ _ (dX_haar σ J ψ v a hX) (dT_haar σ ψ v a hT),
    fun fib fib' h h' => h4 σ J v a _ _ (dT_haar σ ψ v a hT) fib fib' h h'⟩
end PI.OmFibreUniq.W
