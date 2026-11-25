-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.isClosed_stabT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:25.253723+00:00
-- url     : https://prove2.me/submissions/9343203c-8052-47dc-bbb2-4acdbece3b3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_lin
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT


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
theorem _root_.solution {a : ℕ} (X : Fin a → Fin n → E) :
    IsClosed (stabT (Af F) σ J X : Set (HA (Af F) σ J)) := by
  have h : (stabT (Af F) σ J X : Set (HA (Af F) σ J)) =
      ⋂ b, {g | lin (Af F) σ J g (ratV (F := F) (Af F) (X b)) = ratV (F := F) (Af F) (X b)} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact mem_stabT (Af F) σ J X g
  rw [h]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin _) continuous_const
end PI.LevelKSplit.W.ExC
