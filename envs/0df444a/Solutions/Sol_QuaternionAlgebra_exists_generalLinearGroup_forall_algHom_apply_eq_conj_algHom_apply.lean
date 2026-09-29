-- Prove2me | solution 1 for QuaternionAlgebra.exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/04611ed7-1a53-566b-8bf6-205eea351c35

import Mathlib
import Theorems.Thm_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply

set_option autoImplicit false

open scoped Quaternion MatrixGroups

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re imK imJ imI Basis"
namespace SNEmbedProof
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

abbrev qI : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩

abbrev qJ : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩

abbrev qK : ℍ[ℚ, a, b] := ⟨0, 0, 0, 1⟩

theorem qI_mul_qI : (qI : ℍ[ℚ, a, b]) * qI = (a : ℍ[ℚ, a, b]) := by ext <;> simp
theorem qJ_mul_qJ : (qJ : ℍ[ℚ, a, b]) * qJ = (b : ℍ[ℚ, a, b]) := by ext <;> simp
theorem qI_mul_qJ : (qI : ℍ[ℚ, a, b]) * qJ = qK := by ext <;> simp
theorem qJ_mul_qI : (qJ : ℍ[ℚ, a, b]) * qI = -qK := by ext <;> simp

theorem eq_smul_basis (x : ℍ[ℚ, a, b]) :
    x = x.re • (1 : ℍ[ℚ, a, b]) + x.imI • qI + x.imJ • qJ + x.imK • qK := by
  ext <;> simp

def gen : Fin 4 → ℍ[ℚ, a, b] := ![1, qI, qJ, qK]

@[scoped simp] theorem gen_zero : (gen 0 : ℍ[ℚ, a, b]) = 1 := rfl
@[scoped simp] theorem gen_one : (gen 1 : ℍ[ℚ, a, b]) = qI := rfl
@[scoped simp] theorem gen_two : (gen 2 : ℍ[ℚ, a, b]) = qJ := rfl
@[scoped simp] theorem gen_three : (gen 3 : ℍ[ℚ, a, b]) = qK := rfl

theorem eq_sum_smul_gen (x : ℍ[ℚ, a, b]) :
    x = ∑ s : Fin 4, (![x.re, x.imI, x.imJ, x.imK] s) • gen s := by
  conv_lhs => rw [eq_smul_basis x]
  simp [Fin.sum_univ_four, gen]

section Field

variable (K : Type) [Field K] [CharZero K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

variable (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K)

theorem map_ratCast (q : ℚ) : ι (q : ℍ[ℚ, a, b]) = (q : K) • (1 : M2) := by
  rw [show ((q : ℍ[ℚ, a, b])) = algebraMap ℚ ℍ[ℚ, a, b] q from rfl, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one, ← algebraMap_smul K q, eq_ratCast]

theorem map_qsmul (q : ℚ) (x : ℍ[ℚ, a, b]) : ι (q • x) = (q : K) • ι x := by
  rw [map_smul, ← algebraMap_smul K q, eq_ratCast]

theorem imI_sq : ι qI * ι qI = (a : K) • (1 : M2) := by
  rw [← map_mul, qI_mul_qI, map_ratCast]

theorem imJ_sq : ι qJ * ι qJ = (b : K) • (1 : M2) := by
  rw [← map_mul, qJ_mul_qJ, map_ratCast]

theorem imI_mul_imJ : ι qI * ι qJ = ι qK := by
  rw [← map_mul, qI_mul_qJ]

theorem imJ_mul_imI : ι qJ * ι qI = -(ι qI * ι qJ) := by
  rw [← map_mul, qJ_mul_qI, map_neg, imI_mul_imJ]

theorem eq_zero_of_smul_one_add_smul_eq_zero {I J : M2} {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hI : I * I = α • (1 : M2)) (hJ : J * J = β • (1 : M2)) (hJI : J * I = -(I * J))
    {c d : K} (h : c • (1 : M2) + d • I = 0) : c = 0 ∧ d = 0 := by

  have h1 : J * (c • (1 : M2) + d • I) * J = β • (c • (1 : M2) - d • I) := by
    have e1 : J * I * J = -(β • I) := by
      rw [hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hJ, mul_smul_comm, smul_mul_assoc, e1,
      smul_sub, smul_comm c β, smul_neg, smul_comm d β, sub_eq_add_neg]
  rw [h, mul_zero, zero_mul] at h1
  have h2 : c • (1 : M2) - d • I = 0 := by
    rcases smul_eq_zero.mp h1.symm with hb | hb
    · exact absurd hb hβ
    · exact hb

  have hc2 : (2 * c) • (1 : M2) = 0 := by
    have := congrArg₂ (· + ·) h h2
    simp only [add_zero] at this
    rw [mul_smul, two_smul, ← this]
    abel
  have hc : c = 0 := by
    rcases smul_eq_zero.mp hc2 with h3 | h3
    · simpa using h3
    · exact absurd h3 one_ne_zero
  refine ⟨hc, ?_⟩
  rw [hc, zero_smul, zero_add] at h

  have h4 : (d * α) • (1 : M2) = 0 := by
    have := congrArg (· * I) h
    simp only [smul_mul_assoc, hI, zero_mul, smul_smul] at this
    exact this
  rcases smul_eq_zero.mp h4 with h5 | h5
  · rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h6
    · exact absurd h6 hα
  · exact absurd h5 one_ne_zero

theorem linearIndependent_map_gen (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (fun s : Fin 4 => ι (gen s)) := by
  have hα : (a : K) ≠ 0 := by exact_mod_cast ha
  have hβ : (b : K) ≠ 0 := by exact_mod_cast hb
  set I : M2 := ι qI with hIdef
  set J : M2 := ι qJ with hJdef
  have hI : I * I = (a : K) • (1 : M2) := imI_sq K ι
  have hJ : J * J = (b : K) • (1 : M2) := imJ_sq K ι
  have hJI : J * I = -(I * J) := imJ_mul_imI K ι
  have hIJ : I * J = -(J * I) := by rw [hJI, neg_neg]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • (1 : M2) + g 1 • I + g 2 • J + g 3 • (I * J) = 0 := by
    have : ∑ s : Fin 4, g s • ι (gen s) = g 0 • (1 : M2) + g 1 • I + g 2 • J + g 3 • (I * J) := by
      simp only [Fin.sum_univ_four, gen_zero, gen_one, gen_two, gen_three, map_one, ← imI_mul_imJ, hIdef, hJdef]
    rw [← this]; exact hg

  have hconjI : I * (g 0 • (1 : M2) + g 1 • I + g 2 • J + g 3 • (I * J)) * I =
      (a : K) • (g 0 • (1 : M2) + g 1 • I - g 2 • J - g 3 • (I * J)) := by
    have e1 : I * J * I = -((a : K) • J) := by
      rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
    have e2 : I * (I * J) * I = -((a : K) • (I * J)) := by
      rw [← mul_assoc, hI, smul_mul_assoc, one_mul, smul_mul_assoc, hJI, smul_neg]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [hI, smul_mul_assoc, one_mul, e1, e2]
    simp only [smul_sub, smul_add, smul_neg, smul_comm (g _) (a : K)]
    abel
  rw [hsum, mul_zero, zero_mul] at hconjI
  have hY : g 0 • (1 : M2) + g 1 • I - g 2 • J - g 3 • (I * J) = 0 := by
    rcases smul_eq_zero.mp hconjI.symm with h | h
    · exact absurd h hα
    · exact h

  have hplus : (2 : K) • (g 0 • (1 : M2) + g 1 • I) = 0 := by
    have := congrArg₂ (· + ·) hsum hY
    simp only [add_zero] at this
    rw [two_smul, ← this]
    abel
  have hminus : (2 : K) • (g 2 • J + g 3 • (I * J)) = 0 := by
    have := congrArg₂ (· - ·) hsum hY
    simp only [sub_zero] at this
    rw [two_smul, ← this]
    abel
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hplus' : g 0 • (1 : M2) + g 1 • I = 0 := by
    rcases smul_eq_zero.mp hplus with h | h
    · exact absurd h h2
    · exact h
  have hminus' : g 2 • J + g 3 • (I * J) = 0 := by
    rcases smul_eq_zero.mp hminus with h | h
    · exact absurd h h2
    · exact h
  obtain ⟨h0, h1⟩ := eq_zero_of_smul_one_add_smul_eq_zero K hα hβ hI hJ hJI hplus'

  have hminus'' : (b : K) • (g 2 • (1 : M2) + g 3 • I) = 0 := by
    have := congrArg (· * J) hminus'
    simp only [add_mul, smul_mul_assoc, zero_mul, mul_assoc, hJ, mul_smul_comm, mul_one] at this
    rw [smul_add, smul_comm (b : K) (g 2), smul_comm (b : K) (g 3)]
    exact this
  have hminus''' : g 2 • (1 : M2) + g 3 • I = 0 := by
    rcases smul_eq_zero.mp hminus'' with h | h
    · exact absurd h hβ
    · exact h
  obtain ⟨h2', h3⟩ := eq_zero_of_smul_one_add_smul_eq_zero K hα hβ hI hJ hJI hminus'''
  intro s
  fin_cases s
  · exact h0
  · exact h1
  · exact h2'
  · exact h3

theorem map_eq_sum (x : ℍ[ℚ, a, b]) :
    ι x = ∑ s : Fin 4, ((![x.re, x.imI, x.imJ, x.imK] s : ℚ) : K) • ι (gen s) := by
  conv_lhs => rw [eq_sum_smul_gen x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_qsmul]

end Field

end QuaternionAlgebra.SNEmbedProof
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.QuaternionAlgebra P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.QuaternionAlgebra.SNEmbedProof"
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.QuaternionAlgebra"

open QuaternionAlgebra.SNEmbedProof in
theorem solution
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (K : Type) [Field K] [CharZero K]
    (ι₀ ι₁ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) :
    ∃ g : GL (Fin 2) K, ∀ x : ℍ[ℚ, a, b],
      ι₁ x = (g : Matrix (Fin 2) (Fin 2) K) * ι₀ x * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  classical

  have hli := linearIndependent_map_gen K ι₀ ha hb
  have hcard : Fintype.card (Fin 4) = Module.finrank K (Matrix (Fin 2) (Fin 2) K) := by
    simp [Module.finrank_matrix]
  let B : Module.Basis (Fin 4) K (Matrix (Fin 2) (Fin 2) K) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ s, B s = ι₀ (gen s) := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s

  let φ : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K := B.constr K fun s => ι₁ (gen s)
  have hφB : ∀ s, φ (ι₀ (gen s)) = ι₁ (gen s) := fun s => by
    rw [← hB]; exact B.constr_basis K _ s
  have hφ : ∀ x : ℍ[ℚ, a, b], φ (ι₀ x) = ι₁ x := fun x => by
    rw [map_eq_sum K ι₀ x, map_sum, map_eq_sum K ι₁ x]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, hφB]
  have hone : φ 1 = 1 := by
    have := hφ 1
    rwa [map_one ι₀, map_one ι₁] at this
  have hmulB : ∀ s t, φ (ι₀ (gen s) * ι₀ (gen t)) = φ (ι₀ (gen s)) * φ (ι₀ (gen t)) := fun s t => by
    rw [← map_mul, hφ, hφ, hφ, map_mul]
  have hmul : ∀ x y : Matrix (Fin 2) (Fin 2) K, φ (x * y) = φ x * φ y := by
    rw [LinearMap.map_mul_iff]
    refine B.ext fun s => B.ext fun t => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.coe_comp,
      Function.comp_apply, hB]
    exact hmulB s t
  let f : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K := AlgHom.ofLinearMap φ hone hmul
  obtain ⟨u, hu⟩ := Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj K (Fin 2) f
  refine ⟨u, fun x => ?_⟩
  rw [← hφ x]
  exact hu (ι₀ x)

end S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
end P2MW
export P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply (solution)
