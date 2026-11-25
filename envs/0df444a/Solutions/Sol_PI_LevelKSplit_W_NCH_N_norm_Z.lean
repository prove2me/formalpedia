-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.N_norm_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:36.044213+00:00
-- url     : https://prove2.me/submissions/4c31b073-a789-48cf-b513-d12cbecb4b07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_N_xp
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_fix

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
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Nsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P :=
  ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hg hz.1) ((Nsub R σ J P).inv_mem hg),
    fun v hv => by
      rw [lin_mul, lin_mul, Z_fix hJ H hh hz (N_xp hJ H hh ((Nsub R σ J P).inv_mem hg) hv), lin_lin_inv]⟩
end PI.LevelKSplit.W.NCH
