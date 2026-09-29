-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/148bcde5-5471-55a7-837d-cae80a61bf66

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
import Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
import Theorems.Thm_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_le_mul_mem_relIndex_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"
set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

namespace Q3aSub13

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

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    have h2 := add_star_eq_coe_trd x
    rw [ht] at h2
    have h3 : star x = ((t : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← h2]; abel
    rw [h3, zsmul_eq_mul, mul_one]
    norm_cast
  rw [h]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

theorem nrd_intCast_smul (n : ℤ) (y : ℍ[ℚ, a, b]) : nrd ((n : ℤ) • y) = (n : ℚ) ^ 2 * nrd y := by
  have : (n : ℤ) • y = ((n : ℚ) : ℍ[ℚ, a, b]) * y := by
    rw [coe_mul_eq_smul]; norm_cast
  rw [this, QuaternionAlgebra.nrd_mul, nrd_coe]

theorem not_prime_eq_sq_mul {ℓ : ℕ} (hℓ : ℓ.Prime) (n : ℤ) : (ℓ : ℚ) ≠ (ℓ : ℚ) ^ 2 * n := by
  intro h
  have h' : (ℓ : ℤ) * 1 = (ℓ : ℤ) * ((ℓ : ℤ) * n) := by
    have : ((ℓ : ℤ) : ℚ) * 1 = (((ℓ : ℤ) * ((ℓ : ℤ) * n) : ℤ) : ℚ) := by push_cast; linear_combination h
    exact_mod_cast this
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have h1 : (1 : ℤ) = ℓ * n := mul_left_cancel₀ hℓ0 h'
  have : (ℓ : ℤ) ∣ 1 := ⟨n, h1⟩
  have : (ℓ : ℤ).natAbs ∣ 1 := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr this
  simp at this
  exact hℓ.one_lt.ne' (by exact_mod_cast this)

theorem not_prime_eq_mul {ℓ : ℕ} (hℓ : ℓ.Prime) (n : ℤ) : (1 : ℚ) ≠ n * (ℓ : ℚ) := by
  intro h
  have h1 : (1 : ℤ) = n * ℓ := by exact_mod_cast h
  have : (ℓ : ℤ) ∣ 1 := ⟨n, by rw [h1, mul_comm]⟩
  have : (ℓ : ℤ).natAbs ∣ 1 := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr this
  simp at this
  exact hℓ.one_lt.ne' (by exact_mod_cast this)

theorem mem_span_smul_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (m : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ↔
      ∃ y ∈ Λ, x = (m : ℤ) • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u + v, Λ.add_mem hu hv, by simp [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨c • u, Λ.smul_mem c hu, by rw [smul_comm]⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

section Main

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

theorem leftIdeal_props (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (s : ℍ[ℚ, a, b]) (hs : s ∈ Λ) (hns : nrd s = (ℓ : ℚ))
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ x, x ∈ J ↔ ∃ y ∈ Λ, y * s = x) :
    J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
  have hO : IsOrder Λ := hΛ.isOrder
  have hJΛ : J ≤ Λ := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := (hJ x).1 hx; exact hO.mul_mem hy hs
  have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := by
    intro y hy
    refine (hJ _).2 ⟨y * star s, hO.mul_mem hy (star_mem hO hs), ?_⟩
    rw [mul_assoc, star_mul_eq_coe_nrd, hns, mul_coe_eq_smul]
    norm_cast
  have hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := (hJ x).1 hx
    exact (hJ _).2 ⟨m * y, hO.mul_mem hm hy, by rw [mul_assoc]⟩
  refine ⟨hJΛ, hℓJ, hleft, ?_⟩

  have hsJ : s ∈ J := (hJ s).2 ⟨1, hO.one_mem, one_mul s⟩
  have ex1 : ¬ ∃ y ∈ Λ, s = (ℓ : ℤ) • y := by
    rintro ⟨y, hy, hsy⟩
    obtain ⟨⟨-, n, -, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hy
    have := congrArg nrd hsy
    rw [hns, nrd_intCast_smul, hn] at this
    exact not_prime_eq_sq_mul hℓ n (by exact_mod_cast this)
  have ex2 : ¬ (1 : ℍ[ℚ, a, b]) ∈ J := by
    intro h1
    obtain ⟨y, hy, hy1⟩ := (hJ 1).1 h1
    obtain ⟨⟨-, n, -, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hy
    have := congrArg nrd hy1
    rw [QuaternionAlgebra.nrd_mul, hn, hns, nrd_one] at this
    exact not_prime_eq_mul hℓ n this.symm

  set Lℓ := (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup with hLℓ
  have h4 : Lℓ.relIndex Λ.toAddSubgroup = ℓ ^ 4 :=
    QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ hℓ.pos
  have hLJ : Lℓ ≤ J.toAddSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_span_smul_iff ℓ x).1 hx
    exact hℓJ y hy
  have hJΛ' : J.toAddSubgroup ≤ Λ.toAddSubgroup := fun x hx => hJΛ hx
  have hmul : Lℓ.relIndex J.toAddSubgroup * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 := by
    rw [AddSubgroup.relIndex_mul_relIndex Lℓ J.toAddSubgroup Λ.toAddSubgroup hLJ hJΛ', h4]
  have hℓ0 : (ℓ : ℕ) ≠ 0 := hℓ.ne_zero

  have hJ_ne_bot : Lℓ.relIndex J.toAddSubgroup ≠ 1 := by
    intro h1
    rw [AddSubgroup.relIndex_eq_one] at h1
    obtain ⟨y, hy, hsy⟩ := (mem_span_smul_iff ℓ s).1 (h1 hsJ)
    exact ex1 ⟨y, hy, hsy⟩
  have hJ_ne_top : J.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 1 := by
    intro h1
    rw [AddSubgroup.relIndex_eq_one] at h1
    exact ex2 (h1 hO.one_mem)
  rcases em (ℓ = q ∨ ℓ = q') with hram | hunr
  ·
    obtain ⟨-, htri⟩ :=
      QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ ℓ hram
    have hJP : ∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n := by
      rcases htri J hJΛ hℓJ hleft with h | h | h
      · exact absurd ((h s).1 hsJ) (by rintro ⟨y, hy, hsy⟩; exact ex1 ⟨y, hy, hsy⟩)
      · exact h
      · exact absurd (h ▸ hO.one_mem : (1 : ℍ[ℚ, a, b]) ∈ J) ex2
    obtain ⟨L₀, hL₀Λ, hℓL₀, hL₀left, hL₀idx⟩ :=
      QuaternionAlgebra.IsMaximalOrder.exists_submodule_le_mul_mem_relIndex_eq_sq hqq' hB Λ hΛ ℓ hℓ
    have hcast : ∀ y : ℍ[ℚ, a, b], (ℓ : ℤ) • y = (ℓ : ℚ) • y := fun y => by
      rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
    have hℓL₀' : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ L₀ := fun y hy => by
      rw [hcast]; exact hℓL₀ ⟨y, hy⟩
    have hL₀left' : ∀ m ∈ Λ, ∀ x ∈ L₀, m * x ∈ L₀ := fun m hm x hx => hL₀left ⟨m, hm⟩ x hx
    have hlt : 1 < ℓ ^ 2 := Nat.one_lt_pow two_ne_zero hℓ.one_lt
    have hL₀P : ∀ x, x ∈ L₀ ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n := by
      rcases htri L₀ hL₀Λ hℓL₀' hL₀left' with h | h | h
      · exfalso
        have hEq : L₀.toAddSubgroup = Lℓ := by
          ext x
          rw [hLℓ]
          show x ∈ L₀ ↔ x ∈ Submodule.span ℤ _
          rw [h x, mem_span_smul_iff]
        rw [hEq, h4] at hL₀idx
        have : ℓ ^ 2 * ℓ ^ 2 = ℓ ^ 2 * 1 := by
          rw [mul_one, ← pow_add]; exact hL₀idx
        exact absurd (mul_left_cancel₀ (pow_ne_zero 2 hℓ0) this) hlt.ne'
      · exact h
      · exfalso
        rw [h, AddSubgroup.relIndex_self] at hL₀idx
        exact hlt.ne hL₀idx
    have hJL₀ : J = L₀ := by
      ext x; rw [hJP x, hL₀P x]
    rw [hJL₀]; exact hL₀idx
  · push_neg at hunr
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hmem := QuaternionAlgebra.IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne hB Λ hΛ ℓ hunr.1 hunr.2
      J hJΛ hℓJ hleft
    rw [← hLℓ] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h hJ_ne_bot
    · rw [h] at hmul
      have : ℓ ^ 2 * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 * ℓ ^ 2 := by rw [hmul, ← pow_add]
      exact mul_left_cancel₀ (pow_ne_zero 2 hℓ0) this
    · rw [h] at hmul
      have : ℓ ^ 4 * J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 * 1 := by rw [hmul, mul_one]
      exact absurd (mul_left_cancel₀ (pow_ne_zero 4 hℓ0) this) hJ_ne_top

theorem qmPeriodMap_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) (x y : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (x * y) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ y) := by
  rw [qmPeriodMap_apply, qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

theorem sub_of_rep (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (s : ℍ[ℚ, a, b]) (hs : s ∈ Λ) (hns : nrd s = (ℓ : ℚ))
    (M : Submodule ℤ (Fin 2 → ℂ)) (hM : ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) :
    M ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
      (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
      M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 := by
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  have hφ : Function.Injective (qmPeriodMap ι τ) :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  let J : Submodule ℤ ℍ[ℚ, a, b] := Λ.map ((LinearMap.mulRight ℚ s).restrictScalars ℤ)
  have hJ : ∀ x, x ∈ J ↔ ∃ y ∈ Λ, y * s = x := by
    intro x
    simp only [J, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.mulRight_apply]
  obtain ⟨hJΛ, hℓJ, hleft, hidx⟩ := leftIdeal_props hqq' hB Λ hΛ ℓ hℓ s hs hns J hJ
  have hMJ : M = J.map (qmPeriodMap ι τ) := by
    ext v
    rw [hM, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y * s, (hJ _).2 ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩; obtain ⟨y, hy, rfl⟩ := (hJ x).1 hx; exact ⟨y, hy, rfl⟩
  have hL : qmPeriodLattice ι Λ τ = Λ.map (qmPeriodMap ι τ) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hMJ, hL]; exact Submodule.map_mono hJΛ
  · intro v hv
    rw [hL, Submodule.mem_map] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    rw [hMJ, Submodule.mem_map]
    exact ⟨(ℓ : ℤ) • y, hℓJ y hy, by rw [map_zsmul]⟩
  · intro y hy v hv
    rw [hMJ, Submodule.mem_map] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨y * x, hleft y hy x hx, by rw [qmPeriodMap_mul]⟩
  · rw [hMJ, hL]
    simp only [Submodule.map_toAddSubgroup]
    rw [AddSubgroup.relIndex_map_map_of_injective (f := (qmPeriodMap ι τ : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)))
      J.toAddSubgroup Λ.toAddSubgroup hφ]
    exact hidx

theorem rep_unique (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (S : Finset ℍ[ℚ, a, b]) (hS : ∀ x ∈ S, x ∈ Λ ∧ nrd x = (ℓ : ℚ))
    (hSrep : ∀ y : ℍ[ℚ, a, b], y ∈ Λ → nrd y = (ℓ : ℚ) →
      ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * x = y)
    (s : ℍ[ℚ, a, b]) (hs : s ∈ S) (s' : ℍ[ℚ, a, b]) (hs' : s' ∈ S)
    (h : ∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * s') = v)) :
    s = s' := by
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  have hφ : Function.Injective (qmPeriodMap ι τ) :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  obtain ⟨hsΛ, hns⟩ := hS s hs
  obtain ⟨hs'Λ, hns'⟩ := hS s' hs'
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have nrd0 : nrd (0 : ℍ[ℚ, a, b]) = 0 := by simp [nrd]
  have hs0 : s ≠ 0 := fun h0 => by rw [h0, nrd0] at hns; exact hℓ0 hns.symm
  have hs'0 : s' ≠ 0 := fun h0 => by rw [h0, nrd0] at hns'; exact hℓ0 hns'.symm
  obtain ⟨y, hy, hys⟩ : ∃ y ∈ Λ, y * s = s' := by
    obtain ⟨y, hy, e⟩ := (h (qmPeriodMap ι τ (1 * s'))).2 ⟨1, hO.one_mem, rfl⟩
    exact ⟨y, hy, by apply hφ; rw [e, one_mul]⟩
  obtain ⟨y', hy', hy's⟩ : ∃ y' ∈ Λ, y' * s' = s := by
    obtain ⟨y', hy', e⟩ := (h (qmPeriodMap ι τ (1 * s))).1 ⟨1, hO.one_mem, rfl⟩
    exact ⟨y', hy', by apply hφ; rw [e, one_mul]⟩
  have cancel : ∀ (z t : ℍ[ℚ, a, b]), t ≠ 0 → z * t = t → z = 1 := by
    intro z t ht hzt
    obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t ht
    have : (z - 1) * t = 0 := by rw [sub_mul, one_mul, hzt, sub_self]
    rw [← hu, Units.mul_left_eq_zero] at this
    exact sub_eq_zero.mp this
  have hyy' : y * y' = 1 := cancel _ s' hs'0 (by rw [mul_assoc, hy's, hys])
  have hy'y : y' * y = 1 := cancel _ s hs0 (by rw [mul_assoc, hys, hy's])
  have hunit : IsUnitOf Λ y := ⟨hy, y', hy', hyy', hy'y⟩
  have hny : nrd y = 1 := by
    have := congrArg nrd hys
    rw [QuaternionAlgebra.nrd_mul, hns, hns'] at this
    have : nrd y * (ℓ : ℚ) = 1 * (ℓ : ℚ) := by rw [one_mul]; exact this
    exact mul_right_cancel₀ hℓ0 this
  obtain ⟨x, -, huniq⟩ := hSrep s' hs'Λ hns'
  have e1 := huniq s ⟨hs, y, hunit, hny, hys⟩
  have e2 := huniq s' ⟨hs', 1, ⟨hO.one_mem, 1, hO.one_mem, mul_one 1, mul_one 1⟩, nrd_one, one_mul s'⟩
  exact e1.trans e2.symm

end Main

end Q3aSub13

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

noncomputable section

namespace QMHecke12

variable {a b : ℚ}

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    have h2 := add_star_eq_coe_trd x
    rw [ht] at h2
    have h3 : star x = ((t : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← h2]; abel
    rw [h3, zsmul_eq_mul, mul_one]
    norm_cast
  rw [h]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

theorem ne_zero_of_hB {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; have := congrArg QuaternionAlgebra.imI h; simp at this
    obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB _ hi
    have hsq : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by
      ext <;> simp [ha]
    rw [← hu] at hsq
    have : (u * u : (ℍ[ℚ, a, b])ˣ) = u * u := rfl
    have h2 : ((u * u : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 0 := by rw [Units.val_mul]; exact hsq
    exact (u * u).ne_zero h2
  · intro hb
    have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; have := congrArg QuaternionAlgebra.imJ h; simp at this
    obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB _ hj
    have hsq : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by
      ext <;> simp [hb]
    rw [← hu] at hsq
    have h2 : ((u * u : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 0 := by rw [Units.val_mul]; exact hsq
    exact (u * u).ne_zero h2

theorem qmPeriodMap_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) (y s : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (y * s) = ((ι y).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ s) := by
  simp only [qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

private theorem _root_.QMHecke12.map_toAddSubgroup {M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →ₗ[ℤ] N) (p : Submodule ℤ M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map f.toAddMonoidHom := by
  ext x; simp [Submodule.mem_map, AddSubgroup.mem_map]

p2m_export "QMHecke12" "map_toAddSubgroup"
section Forward

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
  (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)

include hqq' hB hΛ hι hℓ in

theorem exists_generator (M : Submodule ℤ (Fin 2 → ℂ))
    (hMle : M ≤ qmPeriodLattice ι Λ τ)
    (hMℓ : ∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M)
    (hMst : ∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hMidx : M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) :
    ∃ s₁ ∈ Λ, nrd s₁ = (ℓ : ℚ) ∧ ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s₁) = v := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_of_hB hB
  have hinj : Function.Injective (qmPeriodMap ι τ) :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  set φ := qmPeriodMap ι τ with hφ

  let J : Submodule ℤ ℍ[ℚ, a, b] := Λ ⊓ M.comap φ
  have memJ : ∀ x, x ∈ J ↔ x ∈ Λ ∧ φ x ∈ M := fun x => Iff.rfl
  have hJΛ : J ≤ Λ := inf_le_left
  have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := fun y hy =>
    (memJ _).2 ⟨Λ.smul_mem _ hy, by rw [map_zsmul]; exact hMℓ _ (Submodule.mem_map_of_mem hy)⟩
  have hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := fun m hm x hx =>
    (memJ _).2 ⟨hO.mul_mem hm ((memJ x).1 hx).1, by rw [hφ, qmPeriodMap_mul]; exact hMst m hm _ ((memJ x).1 hx).2⟩
  have hJmap : J.map φ = M := by
    apply le_antisymm
    · rintro v ⟨x, hx, rfl⟩; exact ((memJ x).1 hx).2
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map.1 (hMle hv))
      exact ⟨x, (memJ x).2 ⟨hx, hv⟩, rfl⟩
  have hidx : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
    rw [← AddSubgroup.relIndex_map_map_of_injective J.toAddSubgroup Λ.toAddSubgroup (f := φ.toAddMonoidHom) hinj,
      ← map_toAddSubgroup, ← map_toAddSubgroup, hJmap]
    exact hMidx
  obtain ⟨s₀, hs₀, hn₀, hJ⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ hΛ ℓ hℓ J hJΛ hℓJ hleft hidx

  have key : ∃ s₁ ∈ Λ, nrd s₁ = (ℓ : ℚ) ∧ ∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ m ∈ Λ, x = m * s₁ := by
    rcases hn₀ with hn₀ | hn₀
    · exact ⟨s₀, hs₀, hn₀, hJ⟩
    · obtain ⟨u, ⟨hu, v, hv, huv, hvu⟩, hnu⟩ := QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_neg_one hB Λ hΛ
      refine ⟨u * s₀, hO.mul_mem hu hs₀, by rw [QuaternionAlgebra.nrd_mul, hnu, hn₀]; ring, fun x => (hJ x).trans ?_⟩
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * v, hO.mul_mem hm hv, by rw [mul_assoc, ← mul_assoc v, hvu, one_mul]⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * u, hO.mul_mem hm hu, by rw [mul_assoc]⟩
  obtain ⟨s₁, hs₁, hn₁, hJ₁⟩ := key
  refine ⟨s₁, hs₁, hn₁, fun v => ?_⟩
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map.1 (hMle hv))
    obtain ⟨m, hm, rfl⟩ := (hJ₁ x).1 ((memJ x).2 ⟨hx, hv⟩)
    exact ⟨m, hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ((memJ _).1 ((hJ₁ _).2 ⟨y, hy, rfl⟩)).2

include hqq' hB hΛ hι hℓ in

theorem exists_rep (S : Finset ℍ[ℚ, a, b])
    (hSrep : ∀ y : ℍ[ℚ, a, b], y ∈ Λ → nrd y = (ℓ : ℚ) →
      ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * x = y)
    (M : Submodule ℤ (Fin 2 → ℂ))
    (hMle : M ≤ qmPeriodLattice ι Λ τ)
    (hMℓ : ∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M)
    (hMst : ∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hMidx : M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) :
    ∃ s ∈ S, ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v := by
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨s₁, hs₁, hn₁, hM⟩ := exists_generator hqq' hB Λ hΛ ι hι τ ℓ hℓ M hMle hMℓ hMst hMidx
  obtain ⟨s, ⟨hsS, u, ⟨hu, w, hw, huw, hwu⟩, -, hus⟩, -⟩ := hSrep s₁ hs₁ hn₁
  refine ⟨s, hsS, fun v => (hM v).trans ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y * u, hO.mul_mem hy hu, by rw [mul_assoc, hus]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y * w, hO.mul_mem hy hw, ?_⟩
    rw [← hus, mul_assoc, ← mul_assoc w, hwu, one_mul]

include hB hι in

theorem homothety (s : ℍ[ℚ, a, b]) (hns : nrd s = (ℓ : ℚ)) (hℓ' : ℓ.Prime) :
    ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι s ∧ 0 < g.det.val ∧
      ∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔
        v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ) := by
  obtain ⟨ha, hb⟩ := ne_zero_of_hB hB
  have hdet : (ι s).det = (ℓ : ℝ) := by
    rw [QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι s, hns]; push_cast; rfl
  have hpos : 0 < (ι s).det := by rw [hdet]; exact_mod_cast hℓ'.pos
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (ι s) hpos.ne'
  have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = ι s := rfl
  have hgdet : 0 < g.det.val := by
    show 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [hg]; exact hpos
  obtain ⟨-, h2, -⟩ :=
    QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι Λ s g hg hgdet τ
  exact ⟨g, hg, hgdet, fun v => (h2 v).symm⟩

end Forward

end QMHecke12

end

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (S : Finset ℍ[ℚ, a, b]) (hS : ∀ x ∈ S, x ∈ Λ ∧ nrd x = (ℓ : ℚ))
    (hSrep : ∀ y : ℍ[ℚ, a, b], y ∈ Λ → nrd y = (ℓ : ℚ) →
      ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * x = y) :

    (∀ M : Submodule ℤ (Fin 2 → ℂ),
      (M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) ↔
      ∃ s ∈ S, ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ∧

    (∀ s ∈ S, ∀ s' ∈ S,
      (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * s') = v)) → s = s') ∧

    (∀ s ∈ S, ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι s ∧ 0 < g.det.val ∧
      ∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔
        v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ)) := by
  refine ⟨fun M => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨hMle, hMℓ, hMst, hMidx⟩ := h
    exact QMHecke12.exists_rep hqq' hB Λ hΛ ι hι τ ℓ hℓ S hSrep M hMle hMℓ hMst hMidx
  · obtain ⟨s, hs, hM⟩ := h
    exact Q3aSub13.sub_of_rep hqq' hB Λ hΛ ι hι τ ℓ hℓ s (hS s hs).1 (hS s hs).2 M hM
  · intro s hs s' hs' h
    exact Q3aSub13.rep_unique hqq' hB Λ hΛ ι hι τ ℓ hℓ S hS hSrep s hs s' hs' h
  · intro s hs
    exact QMHecke12.homothety hB Λ ι hι τ ℓ s (hS s hs).2 hℓ

end S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq (solution)
