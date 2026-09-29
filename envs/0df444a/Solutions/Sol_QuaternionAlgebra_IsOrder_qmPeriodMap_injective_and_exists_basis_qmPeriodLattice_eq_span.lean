-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c9ec680b-c6e8-5b59-ae62-a43efeccfc4e

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Quaternion

namespace QMPeriodLatticeFull

section Anticomm

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem aux_two [Nontrivial A] [NoZeroSMulDivisors ℝ A] {I J : A} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hII : I * I = a • (1 : A)) (hJJ : J * J = b • (1 : A)) (hJI : J * I = -(I * J))
    {x y : ℝ} (h : x • (1 : A) + y • I = 0) : x = 0 ∧ y = 0 := by

  have h2 : J * (x • (1 : A) + y • I) * J = b • (x • (1 : A) - y • I) := by
    have : J * I * J = -(b • I) := by
      rw [hJI, neg_mul, mul_assoc, hJJ]; simp
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hJJ, mul_smul_comm, smul_mul_assoc, this]
    simp only [smul_sub, smul_add, smul_neg, smul_smul, sub_eq_add_neg, mul_comm _ b]
  rw [h, mul_zero, zero_mul] at h2
  have h3 : x • (1 : A) - y • I = 0 := by
    rcases smul_eq_zero.mp h2.symm with hb0 | h0
    · exact absurd hb0 hb
    · exact h0
  have hx : (2 * x) • (1 : A) = 0 := by
    have := congrArg₂ (· + ·) h h3
    simp only [add_zero] at this
    rw [mul_smul, two_smul]; rw [← this]; abel
  have hx0 : x = 0 := by
    rcases smul_eq_zero.mp hx with h0 | h0
    · linarith
    · exact absurd h0 one_ne_zero
  refine ⟨hx0, ?_⟩
  rw [hx0, zero_smul, zero_add] at h
  rcases smul_eq_zero.mp h with hy | hI
  · exact hy
  · exfalso; apply ha
    have : a • (1 : A) = 0 := by rw [← hII, hI, mul_zero]
    rcases smul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 one_ne_zero

theorem aux_four [Nontrivial A] [NoZeroSMulDivisors ℝ A] {I J : A} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hII : I * I = a • (1 : A)) (hJJ : J * J = b • (1 : A)) (hJI : J * I = -(I * J))
    {x y z w : ℝ} (h : x • (1 : A) + y • I + z • J + w • (I * J) = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by

  have hIJI : I * J * I = -(a • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hII]; simp
  have hIIJI : I * (I * J) * I = -(a • (I * J)) := by
    rw [← mul_assoc, hII, smul_mul_assoc, one_mul, smul_mul_assoc, hJI, smul_neg]
  have h2 : I * (x • (1 : A) + y • I + z • J + w • (I * J)) * I =
      a • (x • (1 : A) + y • I - z • J - w • (I * J)) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hII, hIJI, hIIJI, one_mul]
    simp only [smul_sub, smul_add, smul_smul, smul_neg, mul_comm _ a, sub_eq_add_neg]
  rw [h, mul_zero, zero_mul] at h2
  have h3 : x • (1 : A) + y • I - z • J - w • (I * J) = 0 := by
    rcases smul_eq_zero.mp h2.symm with h0 | h0
    · exact absurd h0 ha
    · exact h0

  have hsum : (2 * x) • (1 : A) + (2 * y) • I = 0 := by
    have := congrArg₂ (· + ·) h h3
    simp only [add_zero] at this
    rw [mul_smul, mul_smul, two_smul, two_smul, ← this]; abel
  have hdiff : z • J + w • (I * J) = 0 := by
    have := congrArg₂ (· - ·) h h3
    simp only [sub_zero] at this
    have e : x • (1 : A) + y • I + z • J + w • (I * J) - (x • (1 : A) + y • I - z • J - w • (I * J)) =
        (2 : ℝ) • (z • J + w • (I * J)) := by
      rw [two_smul]; abel
    rw [e] at this
    rcases smul_eq_zero.mp this with h0 | h0
    · norm_num at h0
    · exact h0
  obtain ⟨hx, hy⟩ := aux_two ha hb hII hJJ hJI hsum

  have h4 : (z • J + w • (I * J)) * J = b • (z • (1 : A) + w • I) := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hJJ, mul_assoc, hJJ]
    simp [smul_add, smul_smul, mul_comm]
  rw [hdiff, zero_mul] at h4
  have h5 : z • (1 : A) + w • I = 0 := by
    rcases smul_eq_zero.mp h4.symm with h0 | h0
    · exact absurd h0 hb
    · exact h0
  obtain ⟨hz, hw⟩ := aux_two ha hb hII hJJ hJI h5
  exact ⟨by linarith, by linarith, hz, hw⟩

end Anticomm

section Splitting

variable {a b : ℚ}

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

def qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
def qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩

theorem qi_mul_qi : (qi : ℍ[ℚ, a, b]) * qi = algebraMap ℚ ℍ[ℚ, a, b] a := by
  ext <;> simp [qi, QuaternionAlgebra.algebraMap_eq]
theorem qj_mul_qj : (qj : ℍ[ℚ, a, b]) * qj = algebraMap ℚ ℍ[ℚ, a, b] b := by
  ext <;> simp [qj, QuaternionAlgebra.algebraMap_eq]
theorem qj_mul_qi : (qj : ℍ[ℚ, a, b]) * qi = -(qi * qj) := by
  ext <;> simp [qi, qj]

theorem quat_decomp (x : ℍ[ℚ, a, b]) :
    x = x.re • (1 : ℍ[ℚ, a, b]) + x.imI • qi + x.imJ • qj + x.imK • (qi * qj) := by
  ext <;> simp [qi, qj]

noncomputable def fourVec (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) : Fin 4 → M2 := ![1, ι qi, ι qj, ι qi * ι qj]

theorem linearIndependent_fourVec (ha : a ≠ 0) (hb : b ≠ 0) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) :
    LinearIndependent ℝ (fourVec ι) := by
  have hII : ι qi * ι qi = (a : ℝ) • (1 : M2) := by
    rw [← map_mul, qi_mul_qi, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Rat.cast_smul_eq_qsmul]
  have hJJ : ι qj * ι qj = (b : ℝ) • (1 : M2) := by
    rw [← map_mul, qj_mul_qj, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Rat.cast_smul_eq_qsmul]
  have hJI : ι qj * ι qi = -(ι qi * ι qj) := by
    rw [← map_mul, qj_mul_qi, map_neg, map_mul]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • (1 : M2) + g 1 • ι qi + g 2 • ι qj + g 3 • (ι qi * ι qj) = 0 := by
    simpa [fourVec, Fin.sum_univ_four] using hg
  obtain ⟨h0, h1, h2, h3⟩ := aux_four (Rat.cast_ne_zero.mpr ha) (Rat.cast_ne_zero.mpr hb) hII hJJ hJI hsum
  intro i
  fin_cases i <;> assumption

end Splitting

section Phi

open Matrix

noncomputable def Phi (τ : ℂ) : M2 →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun M := (M.map (algebraMap ℝ ℂ)).mulVec ![τ, 1]
  map_add' M N := by simp [Matrix.map_add, Matrix.add_mulVec]
  map_smul' c M := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Matrix.smul_apply, mul_add,
        mul_assoc]

theorem Phi_apply (τ : ℂ) (M : M2) : Phi τ M = (M.map (algebraMap ℝ ℂ)).mulVec ![τ, 1] := rfl

theorem Phi_apply_zero (τ : ℂ) (M : M2) : Phi τ M 0 = (M 0 0 : ℂ) * τ + M 0 1 := by
  simp [Phi_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Phi_apply_one (τ : ℂ) (M : M2) : Phi τ M 1 = (M 1 0 : ℂ) * τ + M 1 1 := by
  simp [Phi_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem real_pair_eq_zero {τ : ℂ} (hτ : τ.im ≠ 0) {p q : ℝ} (h : (p : ℂ) * τ + q = 0) :
    p = 0 ∧ q = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im] at him
  have hp : p = 0 := by
    rcases mul_eq_zero.mp him with h0 | h0
    · exact h0
    · exact absurd h0 hτ
  refine ⟨hp, ?_⟩
  rw [hp] at h
  simpa using h

theorem Phi_injective {τ : ℂ} (hτ : τ.im ≠ 0) : Function.Injective (Phi τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro M hM
  have h0 := congrFun hM 0
  have h1 := congrFun hM 1
  rw [Phi_apply_zero, Pi.zero_apply] at h0
  rw [Phi_apply_one, Pi.zero_apply] at h1
  obtain ⟨h00, h01⟩ := real_pair_eq_zero hτ h0
  obtain ⟨h10, h11⟩ := real_pair_eq_zero hτ h1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem finrank_fin_two_complex : Module.finrank ℝ (Fin 2 → ℂ) = 4 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  simp

theorem finrank_M2 : Module.finrank ℝ M2 = 4 := by
  simp [Module.finrank_matrix]

theorem Phi_surjective {τ : ℂ} (hτ : τ.im ≠ 0) : Function.Surjective (Phi τ) := by
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_M2.trans finrank_fin_two_complex.symm) (f := Phi τ)).mp (Phi_injective hτ)
  exact this

end Phi

section Lattice

variable {a b : ℚ}

open QuaternionAlgebra

theorem qmPeriodMap_eq_Phi (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) (τ : UpperHalfPlane) (x : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ x = Phi (τ : ℂ) (ι x) := rfl

theorem span_fourVec (ha : a ≠ 0) (hb : b ≠ 0) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) :
    Submodule.span ℝ (Set.range (fourVec ι)) = ⊤ :=
  (linearIndependent_fourVec ha hb ι).span_eq_top_of_card_eq_finrank (by simp [finrank_M2])

theorem injective_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hlin := linearIndependent_fourVec ha hb ι
  rw [Fintype.linearIndependent_iff] at hlin
  have hdec := quat_decomp x
  have : (x.re : ℝ) • (1 : M2) + (x.imI : ℝ) • ι qi + (x.imJ : ℝ) • ι qj + (x.imK : ℝ) • (ι qi * ι qj)
      = 0 := by
    have h := congrArg ι hdec
    rw [hx, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_one, map_mul] at h
    simp only [Rat.cast_smul_eq_qsmul]
    exact h.symm
  have h4 := hlin (![x.re, x.imI, x.imJ, x.imK] ∘ (fun i => i)) ?_
  · have h0 := h4 0; have h1 := h4 1; have h2 := h4 2; have h3 := h4 3
    simp at h0 h1 h2 h3
    rw [hdec]; simp [h0, h1, h2, h3]
  · simpa [fourVec, Fin.sum_univ_four] using this

end Lattice

section T1

variable {a b : ℚ}

open QuaternionAlgebra

theorem fourVec_mem_range (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) (m : Fin 4) : ∃ q : ℍ[ℚ, a, b], ι q = fourVec ι m := by
  fin_cases m
  · exact ⟨1, by simp [fourVec]⟩
  · exact ⟨qi, by simp [fourVec]⟩
  · exact ⟨qj, by simp [fourVec]⟩
  · exact ⟨qi * qj, by simp [fourVec]⟩

theorem top_le_span_periods (ha : a ≠ 0) (hb : b ≠ 0) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) (τ : UpperHalfPlane)
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) :
    ⊤ ≤ Submodule.span ℝ (Set.range fun m => qmPeriodMap ι τ (B m)) := by

  set ψ : ℍ[ℚ, a, b] →ₗ[ℚ] (Fin 2 → ℂ) := ((Phi (τ : ℂ)).restrictScalars ℚ) ∘ₗ ι.toLinearMap with hψ
  have hψ_apply : ∀ x, ψ x = qmPeriodMap ι τ x := fun x => rfl

  have hq : ∀ q : ℍ[ℚ, a, b], ψ q ∈ Submodule.span ℝ (Set.range fun m => qmPeriodMap ι τ (B m)) := by
    intro q
    have hmem : q ∈ Submodule.span ℚ (Set.range B) := by rw [B.span_eq]; trivial
    have h1 : ψ q ∈ (Submodule.span ℚ (Set.range B)).map ψ := Submodule.mem_map_of_mem hmem
    rw [Submodule.map_span, ← Set.range_comp] at h1
    have h2 := Submodule.span_le_restrictScalars ℚ ℝ (Set.range (ψ ∘ B)) h1
    exact h2
  intro v _
  obtain ⟨M, rfl⟩ := Phi_surjective (τ := (τ : ℂ)) τ.im_ne_zero v
  have hM : M ∈ Submodule.span ℝ (Set.range (fourVec ι)) := by rw [span_fourVec ha hb ι]; trivial
  have h3 : Phi (τ : ℂ) M ∈ (Submodule.span ℝ (Set.range (fourVec ι))).map (Phi (τ : ℂ)) :=
    Submodule.mem_map_of_mem hM
  rw [Submodule.map_span] at h3
  refine (Submodule.span_le.mpr ?_) h3
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  obtain ⟨q, hq'⟩ := fourVec_mem_range ι m
  rw [← hq']
  exact hq q

theorem T1' (ha : a ≠ 0) (hb : b ≠ 0) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] M2) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBΛ : Submodule.span ℤ (Set.range B) = Λ)
    (τ : UpperHalfPlane) :
    Function.Injective (qmPeriodMap ι τ) ∧
      (∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), qmPeriodLattice ι Λ τ = Submodule.span ℤ (Set.range e)) ∧
      DiscreteTopology (qmPeriodLattice ι Λ τ) ∧
      Submodule.span ℝ (qmPeriodLattice ι Λ τ : Set (Fin 2 → ℂ)) = ⊤ := by
  have hle := top_le_span_periods ha hb ι τ B
  set bE := basisOfTopLeSpanOfCardEqFinrank (fun m => qmPeriodMap ι τ (B m)) hle
    (by simp [finrank_fin_two_complex]) with hbE
  have hcoe : ⇑bE = fun m => qmPeriodMap ι τ (B m) := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have hlat : qmPeriodLattice ι Λ τ = Submodule.span ℤ (Set.range bE) := by
    rw [qmPeriodLattice, ← hBΛ, Submodule.map_span, ← Set.range_comp, hcoe]
    rfl
  refine ⟨?_, ⟨bE, hlat⟩, ?_, ?_⟩
  · exact (Phi_injective τ.im_ne_zero).comp (injective_of_ne_zero ha hb ι)
  · rw [hlat]; infer_instance
  · rw [hlat]
    apply top_le_iff.mp
    calc (⊤ : Submodule ℝ (Fin 2 → ℂ)) = Submodule.span ℝ (Set.range bE) := bE.span_eq.symm
      _ ≤ _ := Submodule.span_mono Submodule.subset_span

end T1

end QMPeriodLatticeFull

open QuaternionAlgebra in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    Function.Injective (qmPeriodMap ι τ) ∧
      (∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), qmPeriodLattice ι Λ τ = Submodule.span ℤ (Set.range e)) ∧
      DiscreteTopology (qmPeriodLattice ι Λ τ) ∧
      Submodule.span ℝ (qmPeriodLattice ι Λ τ : Set (Fin 2 → ℂ)) = ⊤ := by
  obtain ⟨B, -, hBΛ⟩ := hΛ.exists_basis_span_eq
  exact QMPeriodLatticeFull.T1' ha hb ι Λ B hBΛ τ

end S_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span (solution)
