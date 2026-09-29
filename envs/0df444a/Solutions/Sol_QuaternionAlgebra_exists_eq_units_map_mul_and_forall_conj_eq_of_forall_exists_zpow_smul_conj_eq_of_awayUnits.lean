-- Prove2me | solution 1 for QuaternionAlgebra.exists_eq_units_map_mul_and_forall_conj_eq_of_forall_exists_zpow_smul_conj_eq_of_awayUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6a1ed117-053f-5aaf-8016-5bd4990f4260

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_eq_units_map_mul_and_forall_conj_eq_of_forall_exists_zpow_smul_conj_eq_of_awayUnits
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (K₀ : Type) [Field K₀] [CharZero K₀]
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (h : ∀ γ : ↥Γt, ∃ k k' : ℤ,
      ((r : K₀) ^ k) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) =
        ((r : K₀) ^ k') • ((g' : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
          ((g'⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) :
    ∃ c : K₀ˣ, g' = Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom c * g ∧
      ∀ u : Matrix.GeneralLinearGroup (Fin 2) K₀, g' * u * g'⁻¹ = g * u * g⁻¹ := by
  classical

  have hrK : (r : K₀) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  let Mat := Matrix (Fin 2) (Fin 2) K₀
  let sc : K₀ˣ →* Matrix.GeneralLinearGroup (Fin 2) K₀ := Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
  let ru : K₀ˣ := Units.mk0 (r : K₀) hrK
  let U : ↥Γt → Matrix.GeneralLinearGroup (Fin 2) K₀ := fun γ =>
    Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ)

  have hcen : ∀ (d : K₀ˣ) (w : Matrix.GeneralLinearGroup (Fin 2) K₀), sc d * w = w * sc d := by
    intro d w
    apply Units.ext
    simp only [Units.val_mul, sc, Units.coe_map, MonoidHom.coe_coe]
    exact Algebra.commutes _ _

  have hsc : ∀ k : ℤ, ((sc (ru ^ k) : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
      ((r : K₀) ^ k) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
    intro k
    simp only [sc, ru, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    exact Algebra.algebraMap_eq_smul_one _
  have hU : ∀ γ : ↥Γt, ((U γ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
      ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := by
    intro γ; rfl

  have hGL : ∀ γ : ↥Γt, ∃ k k' : ℤ, sc (ru ^ k) * (g * U γ * g⁻¹) = sc (ru ^ k') * (g' * U γ * g'⁻¹) := by
    intro γ
    obtain ⟨k, k', hk⟩ := h γ
    refine ⟨k, k', Units.ext ?_⟩
    simp only [Units.val_mul, hsc, hU, smul_one_mul]
    exact hk

  have hdet : ∀ k k' : ℤ, (∃ w w' : Matrix.GeneralLinearGroup (Fin 2) K₀,
      Matrix.GeneralLinearGroup.det w = Matrix.GeneralLinearGroup.det w' ∧
      sc (ru ^ k) * w = sc (ru ^ k') * w') → k = k' := by
    rintro k k' ⟨w, w', hww, hkk⟩
    have h1 := congrArg Matrix.GeneralLinearGroup.det hkk
    rw [map_mul, map_mul, hww] at h1
    have h2 : Matrix.GeneralLinearGroup.det (sc (ru ^ k)) = Matrix.GeneralLinearGroup.det (sc (ru ^ k')) :=
      mul_right_cancel h1
    have h3 : ((r : K₀) ^ k) ^ 2 = ((r : K₀) ^ k') ^ 2 := by
      have := congrArg (fun u : K₀ˣ => (u : K₀)) h2
      simp only [Matrix.GeneralLinearGroup.val_det_apply, hsc, Matrix.det_smul, Matrix.det_one, mul_one,
        Fintype.card_fin] at this
      exact this

    have h4 : ((r : ℚ) ^ (k * 2)) = ((r : ℚ) ^ (k' * 2)) := by
      apply (algebraMap ℚ K₀).injective
      rw [map_zpow₀, map_zpow₀, map_natCast, zpow_mul, zpow_mul]
      exact_mod_cast h3
    have hr1 : (1 : ℚ) < (r : ℚ) := by exact_mod_cast (Fact.out : r.Prime).one_lt
    have h5 : k * 2 = k' * 2 := (zpow_right_injective₀ (zero_lt_one.trans hr1) hr1.ne') h4
    omega

  have hcomm : ∀ γ : ↥Γt, g'⁻¹ * g * U γ = U γ * (g'⁻¹ * g) := by
    intro γ
    obtain ⟨k, k', hk⟩ := hGL γ
    have hkk : k = k' := by
      refine hdet k k' ⟨g * U γ * g⁻¹, g' * U γ * g'⁻¹, ?_, hk⟩
      simp only [map_mul, map_inv, mul_inv_cancel_comm]
    subst hkk
    have hk' : g * U γ * g⁻¹ = g' * U γ * g'⁻¹ := mul_left_cancel hk

    have := congrArg (fun w => g'⁻¹ * w * g) hk'
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] at this

    simpa [mul_assoc] using this

  obtain ⟨c, hc⟩ := QuaternionAlgebra.exists_eq_smul_one_of_forall_mem_awayUnits_commute hrr hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ v hv
    K₀ ι₀ hι₀ ((g'⁻¹ * g : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) (by
      intro x hx
      have := congrArg (fun w : Matrix.GeneralLinearGroup (Fin 2) K₀ => (w : Matrix (Fin 2) (Fin 2) K₀))
        (hcomm ⟨x, (hΓt x).mpr hx⟩)
      simpa only [Units.val_mul, hU] using this)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact (g'⁻¹ * g).ne_zero hc
  have hH : g'⁻¹ * g = sc (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hc]
    simp only [sc, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  have hconj : ∀ (d : K₀ˣ) (w : Matrix.GeneralLinearGroup (Fin 2) K₀), sc d * w * (sc d)⁻¹ = w := by
    intro d w
    rw [hcen, mul_inv_cancel_right]
  have hg' : g' = sc (Units.mk0 c hc0)⁻¹ * g := by
    rw [map_inv, eq_inv_mul_iff_mul_eq, hcen, ← hH, mul_inv_cancel_left]
  refine ⟨(Units.mk0 c hc0)⁻¹, hg', fun u => ?_⟩
  rw [hg', mul_inv_rev]
  calc sc (Units.mk0 c hc0)⁻¹ * g * u * (g⁻¹ * (sc (Units.mk0 c hc0)⁻¹)⁻¹)
      = sc (Units.mk0 c hc0)⁻¹ * (g * u * g⁻¹) * (sc (Units.mk0 c hc0)⁻¹)⁻¹ := by simp only [mul_assoc]
    _ = g * u * g⁻¹ := hconj _ _

end S_QuaternionAlgebra_exists_eq_units_map_mul_and_forall_conj_eq_of_forall_exists_zpow_smul_conj_eq_of_awayUnits
end P2MW
export P2MW.S_QuaternionAlgebra_exists_eq_units_map_mul_and_forall_conj_eq_of_forall_exists_zpow_smul_conj_eq_of_awayUnits (solution)
