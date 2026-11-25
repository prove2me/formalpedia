-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.unipotent_radical_fixes_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:28.996731+00:00
-- url     : https://prove2.me/submissions/5aa4e29e-b90d-443e-912b-84261711544f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT


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
theorem _root_.solution {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) (a : Fin r) :
    lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  (mem_stabT R σ J P.e g).1 hg.2 a
end PI.LevelKSplit.W.NCH
