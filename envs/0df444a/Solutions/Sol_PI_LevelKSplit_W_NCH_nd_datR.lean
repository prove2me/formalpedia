-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.nd_datR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:58.171422+00:00
-- url     : https://prove2.me/submissions/fe15ac21-8ee3-48de-8c52-e6feb0ddc228

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (hJ : IsHermND σ J) : ND (datR R σ J P T) := by
  intro x hx
  have hJx : JR R J *ᵥ x = 0 := by
    funext i
    have h1 := hx (Pi.single i (1 : R ⊗[F] E))
    have hs : ∀ k, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) =
        (Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k := fun k => by
      rcases eq_or_ne k i with rfl | hk
      · rw [Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hk, map_zero]
    change ∑ k, ∑ j, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) * JR R J k j *
      x j = 0 at h1
    simp only [Pi.single_apply, zero_mul] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  rw [← Matrix.one_mulVec x, ← hJi (R := R) hJ, ← Matrix.mulVec_mulVec, hJx, Matrix.mulVec_zero]
end PI.LevelKSplit.W.NCH
