-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.isClosed_spanR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:51.142158+00:00
-- url     : https://prove2.me/submissions/33e7d296-67ba-406b-b8fa-621579e755b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_mem_spanR_iff
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_projD

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
theorem _root_.solution {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) := by
  have h : (spanR (F := F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) =
      {y | y = projD (Af F) σ J Y D s y} := Set.ext fun y => mem_spanR_iff Y D hD s y
  rw [h]
  exact isClosed_eq continuous_id (continuous_projD Y D s)
end PI.LevelKSplit.W.ExC
