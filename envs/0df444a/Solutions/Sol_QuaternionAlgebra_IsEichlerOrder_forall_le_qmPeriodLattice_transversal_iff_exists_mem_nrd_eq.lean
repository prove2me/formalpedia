-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c796a927-18c4-50c0-9995-d781b80b4788

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
import Theorems.Thm_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
import Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace Q3aR15

theorem a_ne_zero {a b : ℚ} {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') : a ≠ 0 := by
  intro ha
  have hu := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) (by
    intro h; have := congrArg QuaternionAlgebra.imI h; simp at this)
  have hn : nrd (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) = 0 := by simp [nrd, ha]
  obtain ⟨u, hu'⟩ := hu
  have h1 : nrd ((u : ℍ[ℚ, a, b]) * ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by rw [Units.mul_inv]; simp [nrd]
  rw [QuaternionAlgebra.nrd_mul, hu', hn, zero_mul] at h1
  exact zero_ne_one h1

theorem b_ne_zero {a b : ℚ} {q q' : ℕ} [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') : b ≠ 0 := by
  intro hb
  have hu := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) (by
    intro h; have := congrArg QuaternionAlgebra.imJ h; simp at this)
  have hn : nrd (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) = 0 := by simp [nrd, hb]
  obtain ⟨u, hu'⟩ := hu
  have h1 : nrd ((u : ℍ[ℚ, a, b]) * ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by rw [Units.mul_inv]; simp [nrd]
  rw [QuaternionAlgebra.nrd_mul, hu', hn, zero_mul] at h1
  exact zero_ne_one h1

theorem star_mem {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [h, ht]
  refine Λ.sub_mem ?_ hx
  have : ((t : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]
  exact Λ.smul_mem t hΛ.one_mem

theorem natCast_smul_eq_mul_star_mul {a b : ℚ} (t y : ℍ[ℚ, a, b]) (ℓ : ℕ) (ht : nrd t = (ℓ : ℚ)) :
    (ℓ : ℤ) • y = (y * star t) * t := by
  rw [mul_assoc, star_mul_eq_coe_nrd, ht, ← QuaternionAlgebra.coe_commutes, zsmul_eq_mul]
  norm_cast

theorem qmPeriodMap_mul {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) (m x : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (m * x) = ((ι m).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ x) := by
  simp only [qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

theorem span_image_mul_toAddSubgroup {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b]) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => y * t) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup =
      Λ.toAddSubgroup.map (AddMonoidHom.mulRight t) := by
  have h1 : (fun y : ℍ[ℚ, a, b] => y * t) = ⇑(LinearMap.mulRight ℤ t) := by
    funext y; simp [LinearMap.mulRight_apply]
  rw [h1, Submodule.span_image, Submodule.span_eq, Submodule.map_toAddSubgroup]
  rfl

theorem span_image_smul_toAddSubgroup {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℤ) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => n • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup =
      Λ.toAddSubgroup.map (DistribSMul.toAddMonoidHom ℍ[ℚ, a, b] n) := by
  have h1 : (fun y : ℍ[ℚ, a, b] => n • y) = ⇑(DistribSMul.toLinearMap ℤ ℍ[ℚ, a, b] n) := by
    funext y; rfl
  rw [h1, Submodule.span_image, Submodule.span_eq, Submodule.map_toAddSubgroup]
  rfl

theorem fg_of_smul_le {a b : ℚ} {Λ J' : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : Λ.FG) (N : ℕ) (hN : N ≠ 0)
    (hJ'N : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) : J'.FG := by
  let f : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := DistribSMul.toLinearMap ℤ ℍ[ℚ, a, b] (N : ℤ)
  have hf : Function.Injective f := by
    intro x y h
    have h' : ((N : ℤ) : ℚ) • x = ((N : ℤ) : ℚ) • y := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact h
    exact smul_right_injective ℍ[ℚ, a, b] (by exact_mod_cast hN : ((N : ℤ) : ℚ) ≠ 0) h'
  have hle : J'.map f ≤ Λ := by
    rintro x ⟨y, hy, rfl⟩; exact hJ'N y hy
  haveI : IsNoetherian ℤ ↥Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  have hfg : (J'.map f).FG := by
    have h1 : ((J'.map f).comap Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map Λ.subtype
    rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
  exact Submodule.fg_of_fg_map_injective f hf hfg

end Q3aR15

open Q3aR15 in

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :

    (∀ M : Submodule ℤ (Fin 2 → ℂ),
      (M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
        (∀ v ∈ qmPeriodLattice ι J' τ, (ℓ : ℂ) • v ∈ M → v ∈ qmPeriodLattice ι Λ τ)) ↔
      ∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
        (∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ∧
        (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ m ∈ M, (ℓ : ℂ) • w + m = v) ↔
          ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v)) ∧

    (∀ t t' : ℍ[ℚ, a, b], t ∈ R → t' ∈ R → nrd t = (ℓ : ℚ) → nrd t' = (ℓ : ℚ) →
      (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) →
      (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * t') = v)) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * t = t') ∧

    (∀ t : ℍ[ℚ, a, b], t ∈ R → nrd t = (ℓ : ℚ) →
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι t ∧ 0 < g.det.val ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ)) ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι J' (g • τ))) := by
  classical
  obtain ⟨hJ'Λ, hJ'left, hJ'N, hJ'idx, hRchar⟩ := hJ'
  have ha : a ≠ 0 := a_ne_zero hB
  have hb : b ≠ 0 := b_ne_zero hB
  have hinj : Function.Injective (qmPeriodMap ι τ) :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hΛ.isOrder ha hb ι τ).1
  have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ.pos
  refine ⟨fun M => ?_, ?_, ?_⟩
  ·
    have hΛo : IsOrder Λ := hΛ.isOrder
    have hRo : IsOrder R := hR.isOrder
    constructor
    ·
      rintro ⟨hML, hℓM, hstab, hidx, htr⟩
      let J : Submodule ℤ ℍ[ℚ, a, b] := Λ ⊓ M.comap (qmPeriodMap ι τ)
      have hJΛ : J ≤ Λ := inf_le_left
      have hJmap : ∀ v, v ∈ M ↔ ∃ x ∈ J, qmPeriodMap ι τ x = v := by
        intro v; constructor
        · intro hv
          obtain ⟨x, hx, rfl⟩ := (mem_qmPeriodLattice_iff ι Λ τ v).1 (hML hv)
          exact ⟨x, ⟨hx, hv⟩, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact hx.2
      have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := fun y hy => ⟨Λ.smul_mem _ hy, by
        show qmPeriodMap ι τ ((ℓ : ℤ) • y) ∈ M
        rw [map_zsmul]; exact hℓM _ ((mem_qmPeriodLattice_iff ι Λ τ _).2 ⟨y, hy, rfl⟩)⟩
      have hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := fun m hm x hx => ⟨hΛo.mul_mem hm hx.1, by
        show qmPeriodMap ι τ (m * x) ∈ M
        rw [qmPeriodMap_mul]; exact hstab m hm _ hx.2⟩
      have hidxJ : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
        have h1 : M.toAddSubgroup = J.toAddSubgroup.map
            ((qmPeriodMap ι τ : ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ)) : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)) := by
          ext v
          simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe]
          exact hJmap v
        have h2 : (qmPeriodLattice ι Λ τ).toAddSubgroup =
            Λ.toAddSubgroup.map ((qmPeriodMap ι τ : ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ)) : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)) := rfl
        rw [← AddSubgroup.relIndex_map_map_of_injective
          (f := ((qmPeriodMap ι τ : ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ)) : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)))
          J.toAddSubgroup Λ.toAddSubgroup hinj, ← h1, ← h2]
        exact hidx
      have htransJ : ∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ := by
        intro y hy hℓy
        have h1 : (ℓ : ℂ) • qmPeriodMap ι τ y ∈ M := by
          have : (ℓ : ℂ) • qmPeriodMap ι τ y = qmPeriodMap ι τ ((ℓ : ℤ) • y) := by
            rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast
          rw [this]; exact hℓy.2
        obtain ⟨x, hx, hxy⟩ := (mem_qmPeriodLattice_iff ι Λ τ _).1
          (htr _ ((mem_qmPeriodLattice_iff ι J' τ _).2 ⟨y, hy, rfl⟩) h1)
        rw [← hinj hxy]; exact hx
      obtain ⟨t, htR, hnt, hJt, hlevB⟩ :=
        QuaternionAlgebra.IsEichlerOrder.exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
          hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' ⟨hJ'Λ, hJ'left, hJ'N, hJ'idx, hRchar⟩ ℓ hℓ hℓq hℓq'
          J hJΛ hℓJ hleft hidxJ htransJ
      refine ⟨t, htR, hnt, fun v => ?_, fun v => ?_⟩
      · rw [hJmap]; constructor
        · rintro ⟨x, hx, rfl⟩; obtain ⟨m, hm, rfl⟩ := (hJt x).1 hx; exact ⟨m, hm, rfl⟩
        · rintro ⟨y, hy, rfl⟩; exact ⟨y * t, (hJt _).2 ⟨y, hy, rfl⟩, rfl⟩
      · constructor
        · rintro ⟨w, hw, m, hm, rfl⟩
          obtain ⟨j, hj, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w).1 hw
          obtain ⟨x, hx, rfl⟩ := (hJmap m).1 hm
          obtain ⟨m', hm', rfl⟩ := (hJt x).1 hx
          obtain ⟨j', hj', hj't⟩ := (hlevB _).1 ⟨j, hj, m', hm', rfl⟩
          refine ⟨j', hj', ?_⟩
          rw [hj't, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast
        · rintro ⟨j', hj', rfl⟩
          obtain ⟨j, hj, m', hm', h⟩ := (hlevB (j' * t)).2 ⟨j', hj', rfl⟩
          refine ⟨qmPeriodMap ι τ j, (mem_qmPeriodLattice_iff ι J' τ _).2 ⟨j, hj, rfl⟩, qmPeriodMap ι τ (m' * t),
            (hJmap _).2 ⟨m' * t, (hJt _).2 ⟨m', hm', rfl⟩, rfl⟩, ?_⟩
          rw [← h, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast
    ·
      rintro ⟨t, htR, hnt, hM, hlev⟩
      have htΛ : t ∈ Λ := hRΛ htR
      have ht0 : t ≠ 0 := fun h => by rw [h, nrd_zero] at hnt; exact absurd hnt.symm (ne_of_gt hℓpos)
      have htU : IsUnit t := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t ht0
      have hstΛ : star t ∈ Λ := star_mem hΛo htΛ
      have hstR : star t ∈ R := star_mem hRo htR
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      ·
        intro v hv
        obtain ⟨y, hy, rfl⟩ := (hM v).1 hv
        exact (mem_qmPeriodLattice_iff ι Λ τ _).2 ⟨y * t, hΛo.mul_mem hy htΛ, rfl⟩
      ·
        intro v hv
        obtain ⟨y, hy, rfl⟩ := (mem_qmPeriodLattice_iff ι Λ τ v).1 hv
        refine (hM _).2 ⟨y * star t, hΛo.mul_mem hy hstΛ, ?_⟩
        rw [← natCast_smul_eq_mul_star_mul t y ℓ hnt, map_zsmul]
      ·
        intro y hy v hv
        obtain ⟨m, hm, rfl⟩ := (hM v).1 hv
        exact (hM _).2 ⟨y * m, hΛo.mul_mem hy hm, by rw [mul_assoc, qmPeriodMap_mul]⟩
      ·
        have hA := QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq Λ hΛo.fg hΛo.spanTop t
          (fun y hy => hΛo.mul_mem hy htΛ) ℓ (Or.inl hnt)
        rw [span_image_mul_toAddSubgroup] at hA
        have hMeq : M.toAddSubgroup = (Λ.toAddSubgroup.map (AddMonoidHom.mulRight t)).map
            ((qmPeriodMap ι τ : ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ)) : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)) := by
          ext v
          simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddMonoidHom.mulRight_apply,
            LinearMap.toAddMonoidHom_coe, exists_exists_and_eq_and]
          exact hM v
        have hLeq : (qmPeriodLattice ι Λ τ).toAddSubgroup =
            Λ.toAddSubgroup.map ((qmPeriodMap ι τ : ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ)) : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)) := rfl
        rw [hMeq, hLeq, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
        exact hA
      ·
        intro v hv hℓv
        obtain ⟨j, hj, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ v).1 hv

        have hℓj : (ℓ : ℂ) • qmPeriodMap ι τ j = qmPeriodMap ι τ ((ℓ : ℤ) • j) := by
          rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast
        rw [hℓj] at hℓv
        obtain ⟨y, hy, hyj⟩ := (hM _).1 hℓv
        have hyj' : y * t = (ℓ : ℤ) • j := hinj hyj

        let mr : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight t
        let ms : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight (star t)
        let sℓ : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := DistribSMul.toAddMonoidHom ℍ[ℚ, a, b] (ℓ : ℤ)
        have hmr : Function.Injective mr := fun x y h => htU.mul_right_cancel h
        have hsℓ_eq : ∀ x : ℍ[ℚ, a, b], sℓ x = mr (ms x) := fun x => by
          show (ℓ : ℤ) • x = x * star t * t; exact natCast_smul_eq_mul_star_mul t x ℓ hnt

        have hT3 : (Λ.toAddSubgroup.map mr).relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
          have := QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq Λ hΛo.fg hΛo.spanTop t
            (fun y hy => hΛo.mul_mem hy htΛ) ℓ (Or.inl hnt)
          rwa [span_image_mul_toAddSubgroup] at this

        have hT2 : (Λ.toAddSubgroup.map sℓ).relIndex Λ.toAddSubgroup = ℓ ^ 4 := by
          have := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hΛo ℓ hℓ.pos
          rwa [span_image_smul_toAddSubgroup] at this

        have hℓΛ_le : Λ.toAddSubgroup.map sℓ ≤ Λ.toAddSubgroup.map mr := by
          rintro x ⟨y, hy, rfl⟩; exact ⟨y * star t, hΛo.mul_mem hy hstΛ, (hsℓ_eq y).symm⟩
        have hΛt_le : Λ.toAddSubgroup.map mr ≤ Λ.toAddSubgroup := by
          rintro x ⟨y, hy, rfl⟩; exact hΛo.mul_mem hy htΛ
        have hT4 : (Λ.toAddSubgroup.map sℓ).relIndex (Λ.toAddSubgroup.map mr) = ℓ ^ 2 := by
          have := AddSubgroup.relIndex_mul_relIndex _ _ _ hℓΛ_le hΛt_le
          rw [hT3, hT2, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at this
          exact (mul_eq_mul_right_iff.1 this).resolve_right (pow_ne_zero 2 hℓ.ne_zero)

        have hT5 : J'.toAddSubgroup.map mr = J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr := by
          ext x
          constructor
          · rintro ⟨j₁, hj₁, rfl⟩
            obtain ⟨w, hw, m, hm, hwy⟩ := (hlev (qmPeriodMap ι τ (j₁ * t))).2 ⟨j₁, hj₁, rfl⟩
            obtain ⟨j₂, hj₂, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w).1 hw
            obtain ⟨y₁, hy₁, rfl⟩ := (hM m).1 hm
            have : (ℓ : ℂ) • qmPeriodMap ι τ j₂ + qmPeriodMap ι τ (y₁ * t) = qmPeriodMap ι τ ((ℓ : ℤ) • j₂ + y₁ * t) := by
              rw [map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast
            rw [this] at hwy
            have hx : (ℓ : ℤ) • j₂ + y₁ * t = j₁ * t := hinj hwy
            show j₁ * t ∈ _
            rw [← hx]
            exact AddSubgroup.add_mem_sup ⟨j₂, hj₂, rfl⟩ ⟨y₁, hy₁, rfl⟩
          · intro hx
            obtain ⟨x₁, ⟨j₂, hj₂, rfl⟩, x₂, ⟨y₁, hy₁, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.1 hx
            obtain ⟨j₁, hj₁, h⟩ := (hlev _).1 ⟨qmPeriodMap ι τ j₂, (mem_qmPeriodLattice_iff ι J' τ _).2 ⟨j₂, hj₂, rfl⟩,
              qmPeriodMap ι τ (y₁ * t), (hM _).2 ⟨y₁, hy₁, rfl⟩, rfl⟩
            refine ⟨j₁, hj₁, hinj ?_⟩
            show qmPeriodMap ι τ (j₁ * t) = qmPeriodMap ι τ ((ℓ : ℤ) • j₂ + y₁ * t)
            rw [h, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]; norm_cast

        have hJ'fg : J'.FG := fg_of_smul_le hΛo.fg N (NeZero.ne N) hJ'N
        have hJ'span : Submodule.span ℚ (J' : Set ℍ[ℚ, a, b]) = ⊤ :=
          top_le_iff.1 (hΛo.spanTop ▸ Submodule.span_mono hJ'Λ)
        have hJ'st : ∀ y ∈ J', y * star t ∈ J' := fun y hy => ((hRchar _ hstΛ).1 hstR) y hy
        have hT6a : (J'.toAddSubgroup.map ms).relIndex J'.toAddSubgroup = ℓ ^ 2 := by
          have := QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq J' hJ'fg hJ'span (star t) hJ'st ℓ
            (Or.inl (by rw [nrd_star, hnt]))
          rwa [span_image_mul_toAddSubgroup] at this
        have hsℓ_map : ∀ S : AddSubgroup ℍ[ℚ, a, b], S.map sℓ = (S.map ms).map mr := by
          intro S; ext x; simp only [AddSubgroup.mem_map, exists_exists_and_eq_and, hsℓ_eq]
        have hT6 : (J'.toAddSubgroup.map sℓ).relIndex (J'.toAddSubgroup.map mr) = ℓ ^ 2 := by
          rw [hsℓ_map, AddSubgroup.relIndex_map_map_of_injective _ _ hmr]; exact hT6a

        have hT7 : (J'.toAddSubgroup.map sℓ).relIndex (Λ.toAddSubgroup.map mr) = ℓ ^ 2 := by
          rw [← AddSubgroup.relIndex_sup_left, ← hT5]; exact hT6

        have hℓΛ_le' : Λ.toAddSubgroup.map sℓ ≤ J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr :=
          le_inf (AddSubgroup.map_mono hJ'Λ) hℓΛ_le
        have hT8 : J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr ≤ Λ.toAddSubgroup.map sℓ := by
          have := AddSubgroup.relIndex_mul_relIndex _ _ _ hℓΛ_le' inf_le_right
          rw [AddSubgroup.inf_relIndex_right, hT7, hT4] at this
          have h1 : (Λ.toAddSubgroup.map sℓ).relIndex (J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr) = 1 :=
            (mul_eq_right₀ (pow_ne_zero 2 hℓ.ne_zero)).1 this
          exact AddSubgroup.relIndex_eq_one.1 h1

        have hmem : (ℓ : ℤ) • j ∈ J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr :=
          ⟨⟨j, hj, rfl⟩, ⟨y, hy, hyj'⟩⟩
        obtain ⟨y', hy', hy'j⟩ := hT8 hmem
        have hjy : j = y' := by
          have h' : ((ℓ : ℤ) : ℚ) • y' = ((ℓ : ℤ) : ℚ) • j := by
            rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hy'j
          exact (smul_right_injective ℍ[ℚ, a, b] (by exact_mod_cast hℓ.ne_zero : ((ℓ : ℤ) : ℚ) ≠ 0) h').symm
        rw [hjy]
        exact (mem_qmPeriodLattice_iff ι Λ τ _).2 ⟨y', hy', rfl⟩
  ·
    intro t t' htR ht'R hnt hnt' hlev hsame
    have hΛo : IsOrder Λ := hΛ.isOrder
    have hRo : IsOrder R := hR.isOrder
    have htΛ : t ∈ Λ := hRΛ htR
    have ht'Λ : t' ∈ Λ := hRΛ ht'R
    have ht0 : t ≠ 0 := fun h => by rw [h, nrd_zero] at hnt; exact absurd hnt.symm (ne_of_gt hℓpos)
    have ht'0 : t' ≠ 0 := fun h => by rw [h, nrd_zero] at hnt'; exact absurd hnt'.symm (ne_of_gt hℓpos)
    have htU : IsUnit t := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t ht0
    have ht'U : IsUnit t' := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t' ht'0

    have hLt : ∀ y ∈ Λ, ∃ y' ∈ Λ, y' * t' = y * t := fun y hy => by
      obtain ⟨y', hy', h⟩ := (hsame (qmPeriodMap ι τ (y * t))).1 ⟨y, hy, rfl⟩
      exact ⟨y', hy', hinj h⟩
    have hLt' : ∀ y ∈ Λ, ∃ y' ∈ Λ, y' * t = y * t' := fun y hy => by
      obtain ⟨y', hy', h⟩ := (hsame (qmPeriodMap ι τ (y * t'))).2 ⟨y, hy, rfl⟩
      exact ⟨y', hy', hinj h⟩
    obtain ⟨u, huΛ, hu⟩ : ∃ u ∈ Λ, u * t = t' := by
      obtain ⟨y, hy, h⟩ := hLt' 1 hΛo.one_mem; exact ⟨y, hy, by rw [h, one_mul]⟩
    obtain ⟨u', hu'Λ, hu'⟩ : ∃ u' ∈ Λ, u' * t' = t := by
      obtain ⟨y, hy, h⟩ := hLt 1 hΛo.one_mem; exact ⟨y, hy, by rw [h, one_mul]⟩
    have huu' : u * u' = 1 := ht'U.mul_right_cancel (by rw [mul_assoc, hu', hu, one_mul])
    have hu'u : u' * u = 1 := htU.mul_right_cancel (by rw [mul_assoc, hu, hu', one_mul])
    have hnu : nrd u = 1 := by
      have := congrArg nrd hu
      rw [QuaternionAlgebra.nrd_mul, hnt, hnt'] at this
      exact (mul_eq_right₀ (ne_of_gt hℓpos)).1 this

    have hst' : star t' ∈ R := star_mem hRo ht'R
    have hJ'st' : ∀ j ∈ J', j * star t' ∈ J' := fun j hj => ((hRchar _ (hRΛ hst')).1 hst') j hj
    have hincl : ∀ j ∈ J', ∃ j' ∈ J', j' * t' = j * t := by
      intro j hj
      obtain ⟨w, hw, y, hy, hwy⟩ := (hlev (qmPeriodMap ι τ (j * t))).2 ⟨j, hj, rfl⟩
      obtain ⟨j₁, hj₁, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w).1 hw
      obtain ⟨y₁, hy₁, hy₁t⟩ := hLt y hy
      refine ⟨j₁ * star t' + y₁, J'.add_mem (hJ'st' j₁ hj₁) (hJ'Λ hy₁), hinj ?_⟩
      rw [add_mul, ← natCast_smul_eq_mul_star_mul t' j₁ ℓ hnt', hy₁t, map_add, map_zsmul, ← hwy]
      congr 1
      rw [← Int.cast_smul_eq_zsmul ℂ]
      norm_cast

    let mr : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight t
    let mr' : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight t'
    have hmr : Function.Injective mr := fun x y h => htU.mul_right_cancel h
    have hmr' : Function.Injective mr' := fun x y h => ht'U.mul_right_cancel h
    have hC : Λ.toAddSubgroup.map mr = Λ.toAddSubgroup.map mr' := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; obtain ⟨y', hy', h⟩ := hLt y hy; exact ⟨y', hy', h⟩
      · rintro ⟨y, hy, rfl⟩; obtain ⟨y', hy', h⟩ := hLt' y hy; exact ⟨y', hy', h⟩
    have hA : J'.toAddSubgroup.map mr ≤ J'.toAddSubgroup.map mr' := by
      rintro x ⟨j, hj, rfl⟩; obtain ⟨j', hj', h⟩ := hincl j hj; exact ⟨j', hj', h⟩
    have hCA : Λ.toAddSubgroup.map mr ≤ J'.toAddSubgroup.map mr := AddSubgroup.map_mono hJ'Λ
    have hi1 : (Λ.toAddSubgroup.map mr).relIndex (J'.toAddSubgroup.map mr) = N ^ 2 := by
      rw [AddSubgroup.relIndex_map_map_of_injective _ _ hmr]; exact hJ'idx
    have hi2 : (Λ.toAddSubgroup.map mr).relIndex (J'.toAddSubgroup.map mr') = N ^ 2 := by
      rw [hC, AddSubgroup.relIndex_map_map_of_injective _ _ hmr']; exact hJ'idx
    have hi3 := AddSubgroup.relIndex_mul_relIndex (Λ.toAddSubgroup.map mr) _ _ hCA hA
    rw [hi1, hi2] at hi3
    have hone : (J'.toAddSubgroup.map mr).relIndex (J'.toAddSubgroup.map mr') = 1 := by
      have hN0 : (N ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 (NeZero.ne N)
      exact (mul_eq_left₀ hN0).1 hi3
    have hA' : J'.toAddSubgroup.map mr' ≤ J'.toAddSubgroup.map mr := AddSubgroup.relIndex_eq_one.1 hone

    have huR : u ∈ R := by
      refine (hRchar u huΛ).2 (fun j hj => ?_)
      obtain ⟨j₂, hj₂, h⟩ : ∃ j₂ ∈ J', j₂ * t = j * t' := by
        obtain ⟨j₂, hj₂, h⟩ := hA' ⟨j, hj, rfl⟩; exact ⟨j₂, hj₂, h⟩
      have : j * u = j₂ := htU.mul_right_cancel (by rw [mul_assoc, hu, h])
      rw [this]; exact hj₂
    have hu'R : u' ∈ R := by
      refine (hRchar u' hu'Λ).2 (fun j hj => ?_)
      obtain ⟨j₂, hj₂, h⟩ : ∃ j₂ ∈ J', j₂ * t' = j * t := hincl j hj
      have : j * u' = j₂ := ht'U.mul_right_cancel (by rw [mul_assoc, hu', h])
      rw [this]; exact hj₂
    exact ⟨u, ⟨huR, u', hu'R, huu', hu'u⟩, hnu, hu⟩
  ·
    intro t htR hnrd
    have hdet : (ι t).det = (ℓ : ℝ) := by
      rw [QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι t, hnrd]; push_cast; rfl
    have hdet0 : (ι t).det ≠ 0 := by rw [hdet]; exact_mod_cast hℓ.ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (ι t) hdet0, rfl, ?_, ?_, ?_⟩
    · show 0 < (ι t).det
      rw [hdet]; exact_mod_cast hℓ.pos
    · intro v
      exact ((QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι Λ t
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (ι t) hdet0) rfl (by show 0 < (ι t).det; rw [hdet]; exact_mod_cast hℓ.pos) τ).2.1 v).symm
    · intro v
      exact ((QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι J' t
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (ι t) hdet0) rfl (by show 0 < (ι t).det; rw [hdet]; exact_mod_cast hℓ.pos) τ).2.1 v).symm

end S_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq (solution)
