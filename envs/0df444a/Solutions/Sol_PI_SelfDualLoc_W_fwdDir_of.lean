-- Prove2me | solution 1 for PI.SelfDualLoc.W.fwdDir_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:09.256239+00:00
-- url     : https://prove2.me/submissions/ad1f717e-c4d3-4d8d-82af-7ed5d571db0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfDirs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Theorems.Thm_PI_SelfDualLoc_W_hform_incl
import Theorems.Thm_PI_SelfDualLoc_W_inclE_mem_Oloc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem hform_add_left_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x x' y : Fin m → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
private theorem hform_add_right_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x y y' : Fin m → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem hform_smul_left_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (c : A) (x y : Fin m → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private theorem hform_smul_right_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (c : A) (x y : Fin m → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private theorem hform_zero_left' {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (y : Fin m → A) : hform σ J 0 y = 0 := by
  simp [hform]
private theorem hform_zero_right' {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x : Fin m → A) : hform σ J x 0 = 0 := by
  simp [hform]
end PI.SelfDualLoc.W
end
end

set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.SelfDualLoc.W
theorem _root_.solution (hS : SigInt) : FwdDir := by
  intro F E _ _ _ _ _ n σ J v Lb hLb y hy z hz
  unfold hloc
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨b, hb, rfl⟩ := hy'
    induction hz using Submodule.span_induction with
    | mem z hz' =>
      obtain ⟨a, ha, rfl⟩ := hz'
      dsimp only
      rw [hform_incl]
      exact inclE_mem_Oloc v (hLb a ha b hb)
    | zero => rw [hform_zero_left']; exact zero_mem _
    | add z z' _ _ h1 h2 => rw [hform_add_left_self_dual_local_basis]; exact add_mem h1 h2
    | smul c z _ h =>
      rw [Subring.smul_def, hform_smul_left_self_dual_local_basis]
      exact mul_mem (hS F E σ v c c.2) h
  | zero => rw [hform_zero_right']; exact zero_mem _
  | add y y' _ _ h1 h2 => rw [hform_add_right_self_dual_local_basis]; exact add_mem h1 h2
  | smul c y _ h =>
    rw [Subring.smul_def, hform_smul_right_self_dual_local_basis]
    exact mul_mem c.2 h
end PI.SelfDualLoc.W
