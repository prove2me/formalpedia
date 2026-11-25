-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.H_comm_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:39.601826+00:00
-- url     : https://prove2.me/submissions/82e8dc40-81ff-4212-95ab-62069ce67ea7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_fix_span
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_fix
import Theorems.Thm_PI_LevelKSplit_W_NCH_Z_f
import Theorems.Thm_PI_LevelKSplit_W_NCH_H_e
import Theorems.Thm_PI_LevelKSplit_W_NCH_H_f
import Theorems.Thm_PI_LevelKSplit_W_NCH_H_xp
import Theorems.Thm_PI_LevelKSplit_W_NCH_ext_Xp_f
import Theorems.Thm_PI_LevelKSplit_W_SemiA_ext_lin


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
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ = z := by
  have hgi : g⁻¹ ∈ Hsub R σ J P := (Hsub R σ J P).inv_mem hg
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  refine ext_Xp_f H (Φ := lin R σ J (g * z * g⁻¹)) (Ψ := lin R σ J z) (fun v hv => ?_)
    (fun a => ?_) v
  · rw [lin_mul, lin_mul, Z_fix hJ H hh hz (H_xp hJ H hh hgi hv), lin_lin_inv, Z_fix hJ H hh hz hv]
  · rw [lin_mul, lin_mul, H_f hJ H hh hgi a]
    have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
        (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
    rw [e, map_add, H_f hJ H hh hg a, fix_span (H_e hJ H hh hg) (Z_f hJ H hh hz a)]
end PI.LevelKSplit.W.NCH
