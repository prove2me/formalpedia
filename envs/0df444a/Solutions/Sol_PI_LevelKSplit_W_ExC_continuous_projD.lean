-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.continuous_projD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:58.277406+00:00
-- url     : https://prove2.me/submissions/8f1b0a2a-3697-4c16-a690-4a81c1e5657e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) :
    Continuous (projD (Af F) σ J Y D s) := by
  classical
  unfold projD
  refine continuous_finsetSum _ fun a _ => ?_
  have hc : Continuous fun y : Fin n → Af F ⊗[F] E => covR (Af F) σ J (D a) ⬝ᵥ y := by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => Continuous.mul continuous_const (continuous_apply i)
  exact (continuous_if_const _ (fun _ => hc) (fun _ => continuous_const)).smul continuous_const
end PI.LevelKSplit.W.ExC
