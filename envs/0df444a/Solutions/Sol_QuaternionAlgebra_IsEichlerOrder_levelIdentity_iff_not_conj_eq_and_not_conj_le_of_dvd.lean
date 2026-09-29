-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2d7086fc-95d0-5aa1-8d69-db1ed6e25b88

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace T2bReduce
theorem partG
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) :=
  QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_forall_mul_star_mem_imp_mem hB Λ hΛ R hR hRΛ J' hJ' ℓ hℓ t ht hnt

theorem partL
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ))
    (T : (ℍ[ℚ, a, b])ˣ) (hT : (T : ℍ[ℚ, a, b]) = t) :
    (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) ↔
      ((¬ ∀ z : ℍ[ℚ, a, b],
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
        (¬ ∀ r ∈ R,
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ)) :=
  QuaternionAlgebra.IsEichlerOrder.forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' w hwR hwn hwnorm ℓ hℓ hℓN t ht hnt T hT

end T2bReduce

open T2bReduce in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ))
    (T : (ℍ[ℚ, a, b])ˣ) (hT : (T : ℍ[ℚ, a, b]) = t) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      ((¬ ∀ z : ℍ[ℚ, a, b],
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
        (¬ ∀ r ∈ R,
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ)) := by
  rw [partG hB Λ hΛ R hR hRΛ J' hJ' ℓ hℓ t ht hnt]
  exact partL hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' w hwR hwn hwnorm ℓ hℓ hℓN t ht hnt T hT

end S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd (solution)
