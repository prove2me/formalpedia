-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.H_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:13.670146+00:00
-- url     : https://prove2.me/submissions/2e3c5d70-efc6-4787-b020-58afd2318a6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_Glob_H_fix_e
import Theorems.Thm_PI_LevelKSplit_W_SemiA_H_fix_e


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
variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  PI.LevelKSplit.W.SemiA.H_fix_e hh' a
end PI.LevelKSplit.W.NCH
