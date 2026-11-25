-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.centre_le_unipotent_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:17.53517+00:00
-- url     : https://prove2.me/submissions/08c204d7-e98d-42b4-9d01-d2e331213a10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT
import Theorems.Thm_PI_LevelKSplit_W_NCH_xp_e


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
theorem _root_.solution : PI.LevelKSplit.W.NC.Zsub R σ J P ≤ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P :=
  fun z hz => ⟨hz.1, (mem_stabT R σ J P.e z).2 fun a => hz.2 _ (xp_e H a)⟩
end PI.LevelKSplit.W.NCH
