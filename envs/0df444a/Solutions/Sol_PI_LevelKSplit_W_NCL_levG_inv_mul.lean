-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levG_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:36.001559+00:00
-- url     : https://prove2.me/submissions/c9e90355-a0f0-457f-a889-2c49c8ba8268

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_NCL_levG_mem
import Theorems.Thm_PI_LevelKSplit_W_NCL_levG_e
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
theorem _root_.solution (n : HA R σ J) (hn : n ∈ Nsub R σ J P) :
    (levG hσσ hJ hP n)⁻¹ * n ∈ LevelUnipotentSubgroup R σ J P := by
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).inv_mem
    (levG_mem hσσ hJ hP n).1) hn, (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  rw [lin_mul, ← levG_e hσσ hJ hP n hn b, lin_inv_lin]
end PI.LevelKSplit.W.NCL
