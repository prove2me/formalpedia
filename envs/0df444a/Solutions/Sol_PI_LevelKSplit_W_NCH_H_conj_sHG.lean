-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.H_conj_sHG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:38.027063+00:00
-- url     : https://prove2.me/submissions/5a8ebd1a-c856-4ec1-9a69-303c763ab7aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_uni_lin
import Theorems.Thm_PI_LevelKSplit_W_NCH_lin_sHG
import Theorems.Thm_PI_LevelKSplit_W_NCH_H_e
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiA_ext_lin
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
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {y : Fin r → Fin M → R ⊗[F] E}
    (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hyh : ∀ a, IsWp (datR R σ J P T) ((fun b => lin R σ J g (y b)) a)) :
    g * sHG hJ H hh hy * g⁻¹ = sHG hJ H hh hyh := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul, lin_sHG, lin_sHG, sL_apply, sL_apply]
  have hu : ∀ x x', (datR R σ J P T).h (lin R σ J g x) (lin R σ J g x') =
      (datR R σ J P T).h x x' := uni_lin g
  have e1 : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := fun a => by
    rw [← hu, H_e hJ H hh hg a, lin_lin_inv]
  have e2 : ∀ b, (datR R σ J P T).h (y b) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h (lin R σ J g (y b)) v := fun b => by
    rw [← hu, lin_lin_inv]
  have luv : ∀ a, lin R σ J g (uv (datR R σ J P T) half y a) =
      uv (datR R σ J P T) half (fun b => lin R σ J g (y b)) a := fun a => by
    simp only [uv, cf, map_add, map_sum, map_smul, H_e hJ H hh hg, hu]
  simp only [map_add, map_sub, map_sum, map_smul, e1, e2, luv, H_e hJ H hh hg, lin_lin_inv]
end PI.LevelKSplit.W.NCH
