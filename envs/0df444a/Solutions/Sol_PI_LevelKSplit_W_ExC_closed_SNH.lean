-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.closed_SNH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:04.668412+00:00
-- url     : https://prove2.me/submissions/17798c3f-32d3-404e-bbb5-6ab9597b3daf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_dual_frame_pairing
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_uniFlag
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_Nsub
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_stabT

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
theorem _root_.solution (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) :
    IsClosed (Ssub (Af F) σ J P : Set (HA (Af F) σ J)) ∧
      IsClosed (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∧
      IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J)) :=
  ⟨isClosed_uniFlag (F0 P) (dualFrameAlt P T) (dual_frame_pairing hJ hinv P T hP), isClosed_Nsub hJ hinv P T hP,
    isClosed_stabT (tupH P)⟩
end PI.LevelKSplit.W.ExC
