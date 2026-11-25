-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.piG_of_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:28.54116+00:00
-- url     : https://prove2.me/submissions/cec9de70-7ec0-4e04-ae20-92b9c27e6289

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_LevelKSplit_W_SemiA_lin_piG
import Theorems.Thm_PI_LevelKSplit_W_SemiA_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_of_fix


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
theorem _root_.solution {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (hg : h ∈ Ssub R σ J P) :
    piG hσσ hJ hP h hg = h := by
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
  unfold Hsub at hh
  rw [mem_stabT] at hh
  have he : ∀ a, lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := fun a => by
    have h1 := hh (Fin.castAdd r (Fin.castSucc a))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at h1
  have hz : lin R σ J h (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    have h1 := hh (Fin.castAdd r (Fin.last r))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_last] at h1
  have hf : ∀ a, lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := fun a => by
    have h1 := hh (Fin.natAdd (r + 1) a)
    rwa [tupH, Fin.append_right] at h1
  refine hext fun x => ?_
  rw [lin_piG]
  exact SemiG.Dat.Pi_of_fix H ⟨he, hz⟩ hf (uni_lin h) x
end PI.LevelKSplit.W.SemiA
