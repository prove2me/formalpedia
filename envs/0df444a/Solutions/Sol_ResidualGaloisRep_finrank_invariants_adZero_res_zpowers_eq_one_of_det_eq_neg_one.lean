-- Prove2me | solution 1 for ResidualGaloisRep.finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/348e0e0c-dedc-53be-a793-b5ab6d12e519

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Theorems.Thm_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one

set_option autoImplicit false

open Polynomial Module

noncomputable section

namespace P2mEInf

variable {k : Type} [Field k]

lemma charpoly_eq_of_mul_self_eq_one (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1)
    (hdet : LinearMap.det (ρbar.ρ σ) = -1) :
    LinearMap.charpoly (ρbar.ρ σ) = (X - C (1 : k)) * (X - C (-1 : k)) := by
  classical
  set f : Module.End k ρbar.V := ρbar.ρ σ with hf
  have hff : f * f = 1 := by rw [hf, ← map_mul, hσ, map_one]
  let b := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  set A : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b f with hA
  have hAA : A * A = 1 := by
    rw [hA, ← LinearMap.toMatrix_mul, hff, LinearMap.toMatrix_one]
  have hdetA : A.det = -1 := by rw [hA, LinearMap.det_toMatrix, hdet]
  have hchA : A.charpoly = X ^ 2 - C A.trace * X + C A.det := Matrix.charpoly_fin_two A

  have hCH := Matrix.aeval_self_charpoly A
  rw [hchA] at hCH
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow] at hCH
  have htrA : A.trace = 0 := by
    have hsq : A ^ 2 = 1 := by rw [sq, hAA]
    rw [hsq, hdetA] at hCH
    have h2 : (algebraMap k (Matrix (Fin 2) (Fin 2) k)) A.trace * A = 0 := by
      have := hCH
      rw [map_neg, map_one, sub_add_eq_add_sub, add_neg_cancel, zero_sub, neg_eq_zero] at this
      exact this
    have h3 : A.trace = 0 ∨ A = 0 := by
      simpa [Algebra.algebraMap_eq_smul_one] using h2
    rcases h3 with h3 | h3
    · exact h3
    · exfalso
      rw [h3, Matrix.det_zero] at hdetA
      exact one_ne_zero (neg_eq_zero.mp hdetA.symm)
  rw [← LinearMap.charpoly_toMatrix f b, ← hA, hchA, htrA, hdetA]
  simp only [map_zero, zero_mul, sub_zero, map_neg, map_one]
  ring

lemma mem_invariants_res_zpowers_iff (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (v : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    v ∈ (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants ↔
      v ∈ LinearMap.ker (ρbar.adZeroRep σ - 1) := by
  rw [Representation.mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    Module.End.one_apply]
  constructor
  · intro h
    have := h ⟨σ, Subgroup.mem_zpowers σ⟩
    simpa [Rep.coe_res_obj_ρ'] using this
  · intro h g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hg : g = ⟨σ, Subgroup.mem_zpowers σ⟩ ^ m := by
      apply Subtype.ext
      simp [hm]

    have key : ∀ (T : (Module.End k (LinearMap.ker (LinearMap.trace k ρbar.V)))ˣ),
        (T : Module.End k _) v = v → ∀ n : ℤ, ((T ^ n : _ˣ) : Module.End k _) v = v := by
      intro T hT n
      have hpos : ∀ n : ℕ, ((T ^ n : _ˣ) : Module.End k _) v = v := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, Units.val_mul, Module.End.mul_apply, hT, ih]
      rcases Int.eq_nat_or_neg n with ⟨n, rfl | rfl⟩
      · exact_mod_cast hpos n
      · rw [zpow_neg, zpow_natCast]
        have := hpos n
        calc ((T ^ n)⁻¹ : _ˣ).val v = ((T ^ n)⁻¹ : _ˣ).val (((T ^ n : _ˣ) : Module.End k _) v) := by
              rw [this]
          _ = v := by
              rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
                Module.End.one_apply]
    set ρ' := (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ with hρ'
    have e : ρ' g = ((ρ'.toHomUnits g : _ˣ) : Module.End k _) := rfl
    have hσ' : ((ρ'.toHomUnits ⟨σ, Subgroup.mem_zpowers σ⟩ : _ˣ) : Module.End k _) v = v := by
      show ρ' ⟨σ, Subgroup.mem_zpowers σ⟩ v = v
      rw [hρ', Rep.coe_res_obj_ρ']
      exact h
    rw [e, hg, map_zpow]
    exact key _ hσ' m

theorem finrank_invariants_eq_one (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1)
    (hdet : LinearMap.det (ρbar.ρ σ) = -1) :
    Module.finrank k (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants = 1 := by
  have hne : (1 : k) ≠ -1 := by
    intro h
    apply h2
    have : (2 : k) = 1 + 1 := by norm_num
    rw [this]
    nth_rewrite 2 [h]
    rw [add_neg_cancel]
  have hker := ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq h2 ρbar σ hne
    (charpoly_eq_of_mul_self_eq_one ρbar σ hσ hdet)
  have heq : (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants =
      LinearMap.ker (ρbar.adZeroRep σ - 1) := by
    ext v
    exact mem_invariants_res_zpowers_iff ρbar σ v
  rw [heq, hker]

end P2mEInf

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1)
    (hdet : LinearMap.det (ρbar.ρ σ) = -1) :
    Module.finrank k (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants = 1 :=
  P2mEInf.finrank_invariants_eq_one h2 ρbar σ hσ hdet

end

end S_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
end P2MW
export P2MW.S_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one (solution)
