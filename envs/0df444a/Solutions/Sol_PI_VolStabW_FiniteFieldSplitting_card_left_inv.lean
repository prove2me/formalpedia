-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.card_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:57.455944+00:00
-- url     : https://prove2.me/submissions/7f0bde12-990e-4062-8ed8-7218664e5fd8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_exists_left_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun W ↦ W * P
      map_add' := fun x y ↦ Matrix.add_mul x y P
      map_smul' := fun c x ↦ Matrix.smul_mul c x P }
  have hf : ∀ W, f W = W * P := fun _ ↦ rfl
  have hsurj : Function.Surjective f := fun Z ↦ ⟨Z * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_matrix,
    Module.finrank_matrix] at hrk
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * (M - a) := by
    rw [Nat.mul_sub]
    omega
  let e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W ↦ ⟨W.1 - L, by
        rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun Z ↦ ⟨Z.1 + L, by
        have h0 := Z.2
        rw [LinearMap.mem_ker, hf] at h0
        rw [Matrix.add_mul, h0, hL, zero_add]⟩
      left_inv := fun W ↦ by
        apply Subtype.ext
        simp
      right_inv := fun Z ↦ by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker]
end PI.VolStabW.FiniteFieldSplitting
