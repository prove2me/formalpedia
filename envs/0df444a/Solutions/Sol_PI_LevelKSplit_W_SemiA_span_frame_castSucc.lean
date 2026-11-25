-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.span_frame_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:54.756435+00:00
-- url     : https://prove2.me/submissions/526e8f4c-3de9-466a-8000-81c2bed791e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_F0_castSucc

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
theorem _root_.solution (b : Fin r) :
    spanR (F := F) R (F0 P) {c | c < Fin.castSucc b} = spanR (F := F) R P.e {a | a < b} := by
  unfold spanR
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcl : c ≠ Fin.last r := Fin.ne_last_of_lt hc
    refine ⟨c.castPred hcl, ?_, ?_⟩
    · show c.castPred hcl < b
      rw [← Fin.castSucc_lt_castSucc_iff, Fin.castSucc_castPred]
      exact hc
    · show ratV (F := F) R (P.e (c.castPred hcl)) = ratV (F := F) R (F0 P c)
      rw [← F0_castSucc, Fin.castSucc_castPred]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Fin.castSucc a, Fin.castSucc_lt_castSucc_iff.2 ha, ?_⟩
    simp only [F0_castSucc]
end PI.LevelKSplit.W.SemiA
