-- Prove2me | solution 1 for PadicInt.exists_forall_exists_apply_eq_pow_smul_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/edcc59b9-e5a0-5d0d-81d7-99e8323f6785

import Mathlib
import Theorems.Thm_PadicInt_addMonoidHom_map_smul_of_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective

set_option autoImplicit false

open scoped PadicInt

theorem solution
    (p : ℕ) [Fact p.Prime] {n : ℕ} (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (hf : Function.Injective f) :
    ∃ N : ℕ, ∀ v : Fin n → ℤ_[p], ∃ w : Fin n → ℤ_[p], f w = (p : ℤ_[p]) ^ N • v := by
  classical

  let fl : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun c x => PadicInt.addMonoidHom_map_smul_of_free p f c x }
  have hfl : ∀ v, fl v = f v := fun v => rfl
  set M : Matrix (Fin n) (Fin n) ℤ_[p] := LinearMap.toMatrix' fl with hM
  have hMv : ∀ v, M.mulVec v = f v := fun v => by rw [hM, LinearMap.toMatrix'_mulVec]; rfl

  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hMv] at hv0
    exact hv (hf (by rw [hv0, map_zero]))

  refine ⟨(M.det).valuation, fun v => ⟨M.adjugate.mulVec (((PadicInt.unitCoeff hdet)⁻¹ : ℤ_[p]ˣ) • v), ?_⟩⟩
  have hsc : ∀ (c : ℤ_[p]) (u : Fin n → ℤ_[p]), (c • (1 : Matrix (Fin n) (Fin n) ℤ_[p])).mulVec u = c • u := by
    intro c u; ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.smul_apply, Finset.sum_ite_eq]
  rw [← hMv, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hsc, Units.smul_def, smul_smul]
  congr 1
  have hspec := PadicInt.unitCoeff_spec hdet
  nth_rw 1 [hspec]
  rw [mul_assoc, mul_comm ((p : ℤ_[p]) ^ _), ← mul_assoc, Units.mul_inv, one_mul]

end S_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective
end P2MW
export P2MW.S_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective (solution)
