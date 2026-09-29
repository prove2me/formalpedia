-- Prove2me | solution 1 for QuaternionAlgebra.exists_eq_smul_one_of_forall_mem_awayUnits_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/44a74342-c549-504b-8fc6-1959cd0b1d14

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace CentScalar

section TwoByTwo

variable {K : Type*} [Field K]

theorem exists_eq_smul_one_add_smul_of_commute (X Y : Matrix (Fin 2) (Fin 2) K)
    (hX : ∀ c : K, X ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (h : Y * X = X * Y) :
    ∃ α β : K, Y = α • (1 : Matrix (Fin 2) (Fin 2) K) + β • X := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hq : X 0 1 = 0
  · by_cases hs : X 1 0 = 0
    ·
      have hd : X 0 0 ≠ X 1 1 := by
        intro hd
        apply hX (X 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.one_apply, hq, hs, hd]
      have hd' : X 0 0 - X 1 1 ≠ 0 := sub_ne_zero.2 hd
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1) * X 0 0, (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;> simp [hq, hs]
      ·
        rw [hq] at e01
        have : Y 0 1 * (X 1 1 - X 0 0) = 0 := by linear_combination e01
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h1
        · exact absurd (sub_eq_zero.1 h1).symm hd
      ·
        rw [hs] at e10
        have : Y 1 0 * (X 0 0 - X 1 1) = 0 := by linear_combination e10
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h1
        · exact absurd h1 hd'
      ·
        field_simp
        ring
    ·
      refine ⟨Y 0 0 - Y 1 0 / X 1 0 * X 0 0, Y 1 0 / X 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;> simp [hq]
      ·
        rw [hq] at e00
        have : Y 0 1 * X 1 0 = 0 := by linear_combination e00
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h1
        · exact absurd h1 hs
      · field_simp
      ·
        field_simp
        linear_combination e10
  ·
    refine ⟨Y 0 0 - Y 0 1 / X 0 1 * X 0 0, Y 0 1 / X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;> simp
    · field_simp
    ·
      field_simp
      linear_combination -e00
    ·
      field_simp
      linear_combination -e01

end TwoByTwo

section Quat

variable {a b : ℚ}

def qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
def qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩

theorem qi_mul_qj_ne : (qi : ℍ[ℚ, a, b]) * qj ≠ qj * qi := by
  intro h
  have := congrArg QuaternionAlgebra.imK h
  simp [qi, qj] at this
  norm_num at this

end Quat

section Main

variable {a₁ b₁ : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem main (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (v : HeightOneSpectrum (𝓞 ℚ))
    (hspan : Submodule.span ℚ (Units.val '' (CerednikDrinfeld.CosetGraph.awayUnits R₁ v : Set (ℍ[ℚ, a₁, b₁])ˣ)) =
      (⊤ : Submodule ℚ ℍ[ℚ, a₁, b₁]))
    (K₀ : Type) [Field K₀] [CharZero K₀]
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (g : Matrix (Fin 2) (Fin 2) K₀)
    (hg : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v →
        g * ι₀ (x : ℍ[ℚ, a₁, b₁]) = ι₀ (x : ℍ[ℚ, a₁, b₁]) * g) :
    ∃ c : K₀, g = c • (1 : Matrix (Fin 2) (Fin 2) K₀) := by

  have hcomm : ∀ h : ℍ[ℚ, a₁, b₁], g * ι₀ h = ι₀ h * g := by
    intro h
    have hh : h ∈ Submodule.span ℚ (Units.val '' (CosetGraph.awayUnits R₁ v : Set (ℍ[ℚ, a₁, b₁])ˣ)) := by
      rw [hspan]; trivial
    induction hh using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact hg x hx
    | zero => rw [map_zero, mul_zero, zero_mul]
    | add u w _ _ hu hw => rw [map_add, mul_add, add_mul, hu, hw]
    | smul c u _ hu => rw [map_smul, mul_smul_comm, smul_mul_assoc, hu]
  by_contra hne
  push Not at hne
  obtain ⟨α, β, hI⟩ := exists_eq_smul_one_add_smul_of_commute g (ι₀ qi) hne (hcomm qi).symm
  obtain ⟨α', β', hJ⟩ := exists_eq_smul_one_add_smul_of_commute g (ι₀ qj) hne (hcomm qj).symm
  have hIJ : ι₀ qi * ι₀ qj = ι₀ qj * ι₀ qi := by
    rw [hI, hJ]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  apply qi_mul_qj_ne (a := a₁) (b := b₁)
  apply hι₀
  rw [map_mul, map_mul, hIJ]

end Main

end CentScalar

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (K₀ : Type) [Field K₀] [CharZero K₀]
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀) :
    ∀ g : Matrix (Fin 2) (Fin 2) K₀,
      (∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v →
        g * ι₀ (x : ℍ[ℚ, a₁, b₁]) = ι₀ (x : ℍ[ℚ, a₁, b₁]) * g) →
      ∃ c : K₀, g = c • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
  intro g hg
  exact CentScalar.main R₁ v
    (CerednikDrinfeld.CosetGraph.span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt hdef R₁ hR₁ r hrr v hv)
    K₀ ι₀ hι₀ g hg

end S_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute
end P2MW
export P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute (solution)
