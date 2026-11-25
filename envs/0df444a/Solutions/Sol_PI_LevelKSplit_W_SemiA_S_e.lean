-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.S_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:22.702822+00:00
-- url     : https://prove2.me/submissions/73f016af-4024-405c-a74e-555eac13efb0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_F0_castSucc
import Theorems.Thm_PI_LevelKSplit_W_SemiA_span_frame_castSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈
      spanR (F := F) R P.e {a | a < b} := by
  have hu : UniC R σ J (F0 P) g := hg
  have h := hu (Fin.castSucc b)
  rw [F0_castSucc, span_frame_castSucc] at h
  exact h
end PI.LevelKSplit.W.SemiA
