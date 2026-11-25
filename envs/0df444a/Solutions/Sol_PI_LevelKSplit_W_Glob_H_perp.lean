-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.H_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:00.800483+00:00
-- url     : https://prove2.me/submissions/96290a30-58e5-4e06-81a8-40cc8301908a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Theorems.Thm_PI_LevelKSplit_W_Glob_hR_ratV_left
import Theorems.Thm_PI_LevelKSplit_W_Glob_covR_ratV
import Theorems.Thm_PI_LevelKSplit_W_Glob_H_fix_e
import Theorems.Thm_PI_LevelKSplit_W_Glob_H_fix_f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R σ J}
namespace PI.LevelKSplit.W.Glob
theorem _root_.solution {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (w : Fin n → E)
    (hw : ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) (b : Fin r) :
    covR R σ J (P.e b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 ∧
      covR R σ J (P.f b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
  have key : ∀ u : Fin n → E, lin R σ J k (ratV (F := F) R u) = ratV (F := F) R u →
      hE σ J u w = 0 → covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
    intro u hu h0
    calc covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w)
        = hR R σ J (lin R σ J k (ratV (F := F) R u)) (lin R σ J k (ratV (F := F) R w)) := by
          rw [hu, hR_ratV_left]
      _ = hR R σ J (ratV (F := F) R u) (ratV (F := F) R w) := by rw [hR_lin]
      _ = 0 := by rw [hR_ratV_left, covR_ratV, h0, map_zero]
  exact ⟨key _ (H_fix_e P k hk b) (hw b).1, key _ (H_fix_f P k hk b) (hw b).2⟩
end PI.LevelKSplit.W.Glob
