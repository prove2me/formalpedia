-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.Z_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:43.540664+00:00
-- url     : https://prove2.me/submissions/e9da0f13-0abf-4718-85d3-48e33c2bb3f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_NCH_nd_datR
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_fix
import Theorems.Thm_PI_LevelKSplit_W_NCH_fix_f_mem
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
theorem _root_.solution {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
  fix_f_mem H (nd_datR hJ) (uni_lin z) (fun v hv => Z_fix hJ H hh hz hv) a
end PI.LevelKSplit.W.NCH
