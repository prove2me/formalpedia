-- Prove2me | solution 1 for QCQPTightness.MultHull.system_18_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:29:48.756392+00:00
-- url     : https://prove2.me/submissions/244bebd3-94ad-4b39-b315-ce27d20837f8

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Definitions.Def_QCQPTightness_MultHull_Kron
set_option autoImplicit false
open QCQPTightness.MultHull Matrix

theorem solution {N m k n : ℕ} (P : QCQP N m) (h : k * n = N) (hkm : m + 2 ≤ k)
    (x : Fin N → ℝ) (z : Fin n → ℝ) :
    ∃ y : Fin k → ℝ, y ⬝ᵥ y = 1 ∧
      (P.A₀ *ᵥ x + P.b₀) ⬝ᵥ kronVec h y z = 0 ∧
      ∀ i, (P.A i *ᵥ x + P.b i) ⬝ᵥ kronVec h y z = 0 := by
  have hadd : ∀ y1 y2 : Fin k → ℝ, kronVec h (y1 + y2) z = kronVec h y1 z + kronVec h y2 z := by
    intro y1 y2; funext i; simp [kronVec, add_mul]
  have hsmul : ∀ (a : ℝ) (y : Fin k → ℝ), kronVec h (a • y) z = a • kronVec h y z := by
    intro a y; funext i; simp [kronVec, mul_assoc]
  let f : (Fin k → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × ℝ) :=
    { toFun := fun y => (fun i => (P.A i *ᵥ x + P.b i) ⬝ᵥ kronVec h y z,
                         (P.A₀ *ᵥ x + P.b₀) ⬝ᵥ kronVec h y z)
      map_add' := by intro y1 y2; ext <;> simp [hadd, dotProduct_add]
      map_smul' := by intro a y; ext <;> simp [hsmul, dotProduct_smul] }
  have hker : LinearMap.ker f ≠ ⊥ :=
    f.ker_ne_bot_of_finrank_lt (by simp [Module.finrank_prod]; omega)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hyf : f y = 0 := hy
  have hpos : 0 < y ⬝ᵥ y := by
    refine lt_of_le_of_ne ?_ (fun h0 => hy0 (dotProduct_self_eq_zero.mp h0.symm))
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  set s := Real.sqrt (y ⬝ᵥ y) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : s * s = y ⬝ᵥ y := Real.mul_self_sqrt hpos.le
  refine ⟨s⁻¹ • y, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  · have := congrArg Prod.snd hyf
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_zero] at this
    rw [hsmul, dotProduct_smul, this, smul_zero]
  · intro i
    have := congrFun (congrArg Prod.fst hyf) i
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
    rw [hsmul, dotProduct_smul, this, smul_zero]
