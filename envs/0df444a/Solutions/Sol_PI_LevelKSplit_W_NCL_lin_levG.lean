-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.lin_levG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:55.879559+00:00
-- url     : https://prove2.me/submissions/8e8ddff9-1cea-465e-a90e-a9a80c7b1718

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (g : HA R σ J) :
    lin R σ J (levG hσσ hJ hP g) = levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) := by
  first
  | rfl
  | (unfold lin; simp [levG, levU, HA.mat]; exact Matrix.toLin'_toMatrix' _)
  | (unfold lin; simp [levG, levU, HA.mat]; exact LinearMap.ext fun x => LinearMap.toMatrix'_mulVec _ x)
end PI.LevelKSplit.W.NCL
