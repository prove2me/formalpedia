-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_forall_mul_star_mem_imp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/82c1bb4b-3059-59f5-bd41-7c6efbff849c

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace T2bG15

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

end T2bG15

open T2bG15 in

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) := by
  classical
  obtain ⟨hJ'Λ, hJ'left, hJ'N, hJ'idx, hRchar⟩ := hJ'
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hRo : IsOrder R := hR.isOrder
  have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ.pos
  have htΛ : t ∈ Λ := hRΛ ht
  have ht0 : t ≠ 0 := fun h => by rw [h, nrd_zero] at hnt; exact absurd hnt.symm (ne_of_gt hℓpos)
  have htU : IsUnit t := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t ht0
  have hstΛ : star t ∈ Λ := star_mem hΛo htΛ
  have hstR : star t ∈ R := star_mem hRo ht
  have hJ'st : ∀ y ∈ J', y * star t ∈ J' := fun y hy => ((hRchar _ hstΛ).1 hstR) y hy

  let mr : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight t
  let ms : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := AddMonoidHom.mulRight (star t)
  let sℓ : ℍ[ℚ, a, b] →+ ℍ[ℚ, a, b] := DistribSMul.toAddMonoidHom ℍ[ℚ, a, b] (ℓ : ℤ)
  have hmr : Function.Injective mr := fun x y h => htU.mul_right_cancel h
  have hsℓ_eq : ∀ x : ℍ[ℚ, a, b], sℓ x = mr (ms x) := fun x => by
    show (ℓ : ℤ) • x = x * star t * t; exact natCast_smul_eq_mul_star_mul t x ℓ hnt
  have hsℓ_map : ∀ S : AddSubgroup ℍ[ℚ, a, b], S.map sℓ = (S.map ms).map mr := by
    intro S; ext x; simp only [AddSubgroup.mem_map, exists_exists_and_eq_and, hsℓ_eq]

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
  have hJ'fg : J'.FG := fg_of_smul_le hΛo.fg N (NeZero.ne N) hJ'N
  have hJ'span : Submodule.span ℚ (J' : Set ℍ[ℚ, a, b]) = ⊤ :=
    top_le_iff.1 (hΛo.spanTop ▸ Submodule.span_mono hJ'Λ)
  have hT6 : (J'.toAddSubgroup.map sℓ).relIndex (J'.toAddSubgroup.map mr) = ℓ ^ 2 := by
    have h := QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq J' hJ'fg hJ'span (star t) hJ'st ℓ
      (Or.inl (by rw [nrd_star, hnt]))
    rw [span_image_mul_toAddSubgroup] at h
    rw [hsℓ_map, AddSubgroup.relIndex_map_map_of_injective _ _ hmr]; exact h

  have hBA : J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr ≤ J'.toAddSubgroup.map mr := by
    apply sup_le
    · rw [hsℓ_map]; exact AddSubgroup.map_mono (by rintro x ⟨y, hy, rfl⟩; exact hJ'st y hy)
    · exact AddSubgroup.map_mono hJ'Λ
  have hℓΛ_le' : Λ.toAddSubgroup.map sℓ ≤ J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr :=
    le_inf (AddSubgroup.map_mono hJ'Λ) hℓΛ_le

  have hLI : (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      J'.toAddSubgroup.map mr = J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr := by
    constructor
    · intro h; ext x
      rw [AddSubgroup.mem_sup]
      constructor
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨j₁, hj₁, m, hm, e⟩ := (h (j * t)).2 ⟨j, hj, rfl⟩
        exact ⟨_, ⟨j₁, hj₁, rfl⟩, _, ⟨m, hm, rfl⟩, e⟩
      · rintro ⟨_, ⟨j₁, hj₁, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
        obtain ⟨j, hj, e⟩ := (h _).1 ⟨j₁, hj₁, m, hm, rfl⟩
        exact ⟨j, hj, e⟩
    · intro h x
      constructor
      · rintro ⟨j₁, hj₁, m, hm, rfl⟩
        have : sℓ j₁ + mr m ∈ J'.toAddSubgroup.map mr := by
          rw [h]; exact AddSubgroup.add_mem_sup ⟨j₁, hj₁, rfl⟩ ⟨m, hm, rfl⟩
        obtain ⟨j, hj, e⟩ := this
        exact ⟨j, hj, e⟩
      · rintro ⟨j, hj, rfl⟩
        have : mr j ∈ J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr := by rw [← h]; exact ⟨j, hj, rfl⟩
        obtain ⟨_, ⟨j₁, hj₁, rfl⟩, _, ⟨m, hm, rfl⟩, e⟩ := AddSubgroup.mem_sup.1 this
        exact ⟨j₁, hj₁, m, hm, e⟩
  rw [hLI]
  constructor
  ·
    intro h5 j hj hjst
    have hT7 : (J'.toAddSubgroup.map sℓ).relIndex (Λ.toAddSubgroup.map mr) = ℓ ^ 2 := by
      rw [← AddSubgroup.relIndex_sup_left, ← h5]; exact hT6
    have hT8 : J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr ≤ Λ.toAddSubgroup.map sℓ := by
      have := AddSubgroup.relIndex_mul_relIndex _ _ _ hℓΛ_le' inf_le_right
      rw [AddSubgroup.inf_relIndex_right, hT7, hT4] at this
      exact AddSubgroup.relIndex_eq_one.1 ((mul_eq_right₀ (pow_ne_zero 2 hℓ.ne_zero)).1 this)
    have hmem : (ℓ : ℤ) • j ∈ J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr :=
      ⟨⟨j, hj, rfl⟩, ⟨j * star t, hjst, (hsℓ_eq j).symm⟩⟩
    obtain ⟨y', hy', hy'j⟩ := hT8 hmem
    have hjy : j = y' := by
      have h' : ((ℓ : ℤ) : ℚ) • y' = ((ℓ : ℤ) : ℚ) • j := by
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hy'j
      exact (smul_right_injective ℍ[ℚ, a, b] (by exact_mod_cast hℓ.ne_zero : ((ℓ : ℤ) : ℚ) ≠ 0) h').symm
    rw [hjy]; exact hy'
  ·
    intro hT
    have hinf : J'.toAddSubgroup.map sℓ ⊓ Λ.toAddSubgroup.map mr = Λ.toAddSubgroup.map sℓ := by
      refine le_antisymm ?_ hℓΛ_le'
      rintro x ⟨⟨j, hj, rfl⟩, ⟨m, hm, hmx⟩⟩
      have hjst : j * star t = m := hmr (by show mr (ms j) = mr m; rw [← hsℓ_eq]; exact hmx.symm)
      exact ⟨j, hT j hj (hjst ▸ hm), rfl⟩
    have hT7 : (J'.toAddSubgroup.map sℓ).relIndex (J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr) = ℓ ^ 2 := by
      rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right, hinf]; exact hT4
    have := AddSubgroup.relIndex_mul_relIndex (J'.toAddSubgroup.map sℓ) _ _ le_sup_left hBA
    rw [hT7, hT6] at this
    have h1 : (J'.toAddSubgroup.map sℓ ⊔ Λ.toAddSubgroup.map mr).relIndex (J'.toAddSubgroup.map mr) = 1 :=
      (mul_eq_left₀ (pow_ne_zero 2 hℓ.ne_zero)).1 this
    exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hBA

end S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem (solution)
