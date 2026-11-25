-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.H_he
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:01.927785+00:00
-- url     : https://prove2.me/submissions/03afebbc-20a4-4f0b-b3aa-83e9d73c9b4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_NCH_H_e
import Theorems.Thm_PI_LevelKSplit_W_SemiA_uni_lin


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
theorem _root_.solution {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) (v : Fin M → R ⊗[F] E) :
    (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J h v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := by
  rw [← uni_lin h ((datR R σ J P T).e a) v, H_e hJ H hh hh' a]
end PI.LevelKSplit.W.NCH
