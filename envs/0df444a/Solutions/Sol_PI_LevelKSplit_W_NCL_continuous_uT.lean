-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.continuous_uT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:47.063823+00:00
-- url     : https://prove2.me/submissions/b989c360-f7eb-42f0-be1a-7d50ba49c3f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousLevLMat
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_lin
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_hR
import Theorems.Thm_PI_VolStabSW_continuous_hR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
set_option maxHeartbeats 800000
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (P : Frame E M r) (a b : Fin r) :
    Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := by
  have h1 : Continuous fun g : HA (Af F) σ J => lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b)) :=
    PI.LevelKSplit.W.ExC.continuous_lin _
  have h0 : Continuous fun g : HA (Af F) σ J =>
      ((ratV (F := F) (Af F) (P.f a), lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b))) :
        (Fin M → Af F ⊗[F] E) × (Fin M → Af F ⊗[F] E)) :=
    continuous_const.prodMk h1
  have h3 := PI.VolStabSW.continuous_hR (R := Af F) σ J
  have h2 := h3.comp h0
  unfold uT
  simp only [Matrix.of_apply]
  split_ifs
  · exact h2
  · exact continuous_const
  · exact continuous_const
end PI.LevelKSplit.W.NCL
