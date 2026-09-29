-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.natCard_sublattice_qmPeriodLattice_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e40c708f-5f24-517f-9bb1-6a171deed574

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_sublattice_qmPeriodLattice_eq_add_one
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

namespace F3c13

variable {a b : ℚ}

theorem ne_zero_and_ne_zero {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

theorem mem_span_smul_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (m : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ↔
      ∃ y ∈ Λ, x = (m : ℤ) • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u + v, Λ.add_mem hu hv, by simp [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨c • u, Λ.smul_mem c hu, by rw [smul_comm]⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem qmPeriodMap_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) (x y : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (x * y) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ y) := by
  rw [qmPeriodMap_apply, qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

theorem relIndex_eq_sq_iff {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q') (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ↔
      ((∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) := by
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓ : ℓ.Prime := Fact.out
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hlt : 1 < ℓ ^ 2 := Nat.one_lt_pow two_ne_zero hℓ.one_lt
  set Lℓ := (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup with hLℓ
  have h4 : Lℓ.relIndex Λ.toAddSubgroup = ℓ ^ 4 := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ hℓ.pos
  have hLJ : Lℓ ≤ J.toAddSubgroup := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := (mem_span_smul_iff ℓ x).1 hx; exact hℓJ y hy
  have hJΛ' : J.toAddSubgroup ≤ Λ.toAddSubgroup := fun x hx => hJΛ hx
  have hmul : Lℓ.relIndex J.toAddSubgroup * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 := by
    rw [AddSubgroup.relIndex_mul_relIndex Lℓ J.toAddSubgroup Λ.toAddSubgroup hLJ hJΛ', h4]
  have hmem := QuaternionAlgebra.IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne hB Λ hΛ ℓ hℓq hℓq' J hJΛ hℓJ hleft
  rw [← hLℓ] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  constructor
  · intro hidx
    refine ⟨?_, ?_⟩
    · by_contra hne
      push Not at hne
      have hle : J.toAddSubgroup ≤ Lℓ := fun x hx => (mem_span_smul_iff ℓ x).2 (by
        obtain ⟨y, hy, hxy⟩ := hne x hx; exact ⟨y, hy, hxy⟩)
      have h1 : Lℓ.relIndex J.toAddSubgroup = 1 := AddSubgroup.relIndex_eq_one.2 hle
      rw [h1, hidx, one_mul] at hmul
      have : ℓ ^ 2 * 1 = ℓ ^ 2 * ℓ ^ 2 := by rw [mul_one, ← pow_add]; exact hmul
      exact hlt.ne (mul_left_cancel₀ (pow_ne_zero 2 hℓ0) this)
    · intro hJ
      rw [hJ, AddSubgroup.relIndex_self] at hidx
      exact hlt.ne hidx
  · rintro ⟨⟨x, hxJ, hx⟩, hne⟩
    rcases hmem with h | h | h
    · exfalso
      rw [AddSubgroup.relIndex_eq_one] at h
      obtain ⟨y, hy, hxy⟩ := (mem_span_smul_iff ℓ x).1 (h hxJ)
      exact hx ⟨y, hy, hxy⟩
    · rw [h] at hmul
      have : ℓ ^ 2 * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 * ℓ ^ 2 := by rw [hmul, ← pow_add]
      exact mul_left_cancel₀ (pow_ne_zero 2 hℓ0) this
    · exfalso
      rw [h] at hmul
      have : ℓ ^ 4 * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 * 1 := by rw [hmul, mul_one]
      have h1 := mul_left_cancel₀ (pow_ne_zero 4 hℓ0) this
      rw [AddSubgroup.relIndex_eq_one] at h1
      exact hne (le_antisymm hJΛ fun x hx => h1 hx)

end F3c13

open F3c13 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    Nat.card {M : Submodule ℤ (Fin 2 → ℂ) //
        M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2} = ℓ + 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  set φ := qmPeriodMap ι τ with hφdef
  have hφ : Function.Injective φ :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  have hLτ : qmPeriodLattice ι Λ τ = Λ.map φ := rfl

  let PL := {J : Submodule ℤ ℍ[ℚ, a, b] //
      J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ}
  have hPL : Nat.card PL = ℓ + 1 :=
    (QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq hqq' hB Λ hΛ ℓ hℓq hℓq').1
  rw [← hPL]
  apply Nat.card_congr

  refine
    { toFun := fun M => ⟨M.1.comap φ ⊓ Λ, ?_⟩
      invFun := fun J => ⟨J.1.map φ, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  ·
    obtain ⟨hMle, hℓM, hstab, hidx⟩ := M.2
    have hJΛ : M.1.comap φ ⊓ Λ ≤ Λ := inf_le_right
    have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ M.1.comap φ ⊓ Λ := fun y hy =>
      Submodule.mem_inf.2 ⟨Submodule.mem_comap.2 (by
          rw [map_zsmul]; exact hℓM _ (by rw [hLτ]; exact Submodule.mem_map_of_mem hy)),
        Λ.smul_mem _ hy⟩
    have hleft : ∀ m ∈ Λ, ∀ x ∈ M.1.comap φ ⊓ Λ, m * x ∈ M.1.comap φ ⊓ Λ := fun m hm x hx =>
      Submodule.mem_inf.2 ⟨Submodule.mem_comap.2 (by
          rw [qmPeriodMap_mul]; exact hstab m hm _ (Submodule.mem_comap.1 (Submodule.mem_inf.1 hx).1)),
        hO.mul_mem hm (Submodule.mem_inf.1 hx).2⟩
    have hmapJ : (M.1.comap φ ⊓ Λ).map φ = M.1 := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hx.1
      · intro v hv
        have hv' := hMle hv
        rw [hLτ, Submodule.mem_map] at hv'
        obtain ⟨x, hx, rfl⟩ := hv'
        exact ⟨x, ⟨hv, hx⟩, rfl⟩
    have hidxJ : (M.1.comap φ ⊓ Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
      rw [← AddSubgroup.relIndex_map_map_of_injective (f := (φ : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ))) _ _ hφ,
        ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hmapJ, ← hLτ]
      exact hidx
    exact ⟨hJΛ, hℓJ, hleft, (relIndex_eq_sq_iff hB Λ hΛ ℓ hℓq hℓq' _ hJΛ hℓJ hleft).1 hidxJ⟩
  ·
    obtain ⟨hJΛ, hℓJ, hleft, hprop⟩ := J.2
    have hidxJ := (relIndex_eq_sq_iff hB Λ hΛ ℓ hℓq hℓq' _ hJΛ hℓJ hleft).2 hprop
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hLτ]; exact Submodule.map_mono hJΛ
    · intro v hv
      rw [hLτ, Submodule.mem_map] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      rw [← map_zsmul]; exact Submodule.mem_map_of_mem (hℓJ y hy)
    · intro y hy v hv
      rw [Submodule.mem_map] at hv ⊢
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨y * x, hleft y hy x hx, by rw [qmPeriodMap_mul]⟩
    · rw [hLτ, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
        AddSubgroup.relIndex_map_map_of_injective (f := (φ : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ))) _ _ hφ]
      exact hidxJ
  ·
    intro M
    apply Subtype.ext
    show (M.1.comap φ ⊓ Λ).map φ = M.1
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.1
    · intro v hv
      have hv' := M.2.1 hv
      rw [hLτ, Submodule.mem_map] at hv'
      obtain ⟨x, hx, rfl⟩ := hv'
      exact ⟨x, ⟨hv, hx⟩, rfl⟩
  ·
    intro J
    apply Subtype.ext
    show (J.1.map φ).comap φ ⊓ Λ = J.1
    rw [Submodule.comap_map_eq_of_injective hφ, inf_eq_left]
    exact J.2.1

end S_QuaternionAlgebra_IsMaximalOrder_natCard_sublattice_qmPeriodLattice_eq_add_one
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_sublattice_qmPeriodLattice_eq_add_one (solution)
