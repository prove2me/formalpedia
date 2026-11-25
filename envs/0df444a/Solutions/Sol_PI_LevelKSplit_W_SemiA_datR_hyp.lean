-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.datR_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:18.801802+00:00
-- url     : https://prove2.me/submissions/3d6e6b08-cca5-4ce3-a446-a65fe9c0796d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_h
import Theorems.Thm_PI_LevelKSplit_W_SemiA_sigR_inclR
import Theorems.Thm_PI_LevelKSplit_W_SemiA_hR_ratV

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
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datR R σ J P T).Hyp := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hP
  obtain ⟨hJ1, -⟩ := hJ
  have hh : ∀ x y : Fin M → E, (datR R σ J P T).h (ratV (F := F) R x) (ratV (F := F) R y) =
      inclR (F := F) R (hE σ J x y) := by
    intro x y
    rw [datR_h, hR_ratV]
  have hne : algebraMap F E (-T) ≠ 0 := (map_ne_zero (algebraMap F E)).2 (neg_ne_zero.2 hT)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show sigR R σ (sigR R σ x) = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro i j
    show sigR R σ (JR R J j i) = JR R J i j
    simp only [JR, Matrix.map_apply, sigR_inclR, hJ1 i j]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
    rw [hh, hee, map_zero]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
    rw [hh, hff, map_zero]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
    rw [hh, hef]
    split_ifs <;> simp
  · intro a
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
    rw [hh, hez, map_zero]
  · intro a
    show (datR R σ J P T).h (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
    rw [hh, hfz, map_zero]
  · show inclR (F := F) R ((algebraMap F E (-T))⁻¹) *
        (datR R σ J P T).h (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hh, hzz, ← map_mul, inv_mul_cancel₀ hne, map_one]
end PI.LevelKSplit.W.SemiA
