-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.piG_of_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:34.173015+00:00
-- url     : https://prove2.me/submissions/771ab4e8-61d8-4cb9-82c3-3ecb6c14cd13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_h
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_LevelKSplit_W_SemiA_lin_piG
import Theorems.Thm_PI_LevelKSplit_W_SemiA_spanR_le
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_of_N


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
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {n : HA R σ J} (hn : n ∈ Nsub R σ J P) (hg : n ∈ Ssub R σ J P) :
    piG hσσ hJ hP n hg = 1 := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  obtain ⟨-, hn2⟩ := hn
  refine hext fun x => ?_
  rw [lin_piG, lin_one]
  refine SemiG.Dat.Pi_of_N H (fun v hv => spanR_le Set.univ (hn2 v fun a => ?_)) x
  have h1 := hv a
  rwa [datR_h] at h1
end PI.LevelKSplit.W.SemiA
