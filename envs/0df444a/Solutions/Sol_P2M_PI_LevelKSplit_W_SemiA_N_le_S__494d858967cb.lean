-- Prove2me | solution 1 for P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:58.678628+00:00
-- url     : https://prove2.me/submissions/2fb7b72a-95c0-4981-999c-17eec908bb38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution (hP : P.IsStd σ J T) : Nsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  obtain ⟨h1, h2⟩ := hg
  have hz : ∀ a : Fin r, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0 := by
    intro a
    have := hP.2.2.2.1 a
    unfold hR ratV hE at *
    unfold Formalism.UG.hform sigR JR inclR at *
    have h3 := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)) this
    simpa [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum,
      map_mul] using h3
  unfold Ssub uniFlag F0
  intro b
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · have key := h2 (ratV (F := F) R P.z) hz
    simp only [Fin.snoc_last]
    unfold spanR at key ⊢
    refine Submodule.span_mono ?_ key
    rintro x ⟨a, -, rfl⟩
    exact ⟨Fin.castSucc a, Fin.castSucc_lt_last a, by simp⟩
  · simp only [Fin.snoc_castSucc]
    unfold UniC at h1
    have key := h1 b'
    unfold spanR at key ⊢
    refine Submodule.span_mono ?_ key
    rintro x ⟨a, ha, rfl⟩
    exact ⟨Fin.castSucc a, Fin.castSucc_lt_castSucc_iff.mpr ha, by simp⟩
end PI.LevelKSplit.W.SemiA
