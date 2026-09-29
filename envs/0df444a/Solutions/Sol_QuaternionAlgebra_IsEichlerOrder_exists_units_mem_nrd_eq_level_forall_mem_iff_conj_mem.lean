-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3bc7f546-eb12-5292-8d09-518960eb67c1

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_levelModule
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CerednikDrinfeld

namespace AlExists

variable {a b : ℚ}

theorem zsmul_eq_ratCast_smul (n : ℤ) (x : ℍ[ℚ, a, b]) : n • x = (n : ℚ) • x :=
  (Int.cast_smul_eq_zsmul ℚ n x).symm

theorem natCast_zsmul_eq_ratCast_smul (n : ℕ) (x : ℍ[ℚ, a, b]) : (n : ℤ) • x = (n : ℚ) • x := by
  rw [zsmul_eq_ratCast_smul]; push_cast; rfl

theorem natCast_zsmul_eq_coe_mul (n : ℕ) (x : ℍ[ℚ, a, b]) : (n : ℤ) • x = ((n : ℚ) : ℍ[ℚ, a, b]) * x := by
  rw [natCast_zsmul_eq_ratCast_smul, coe_mul_eq_smul]

theorem zsmul_right_cancel {n : ℤ} (hn : n ≠ 0) {x y : ℍ[ℚ, a, b]} (h : n • x = n • y) : x = y := by
  rw [zsmul_eq_ratCast_smul, zsmul_eq_ratCast_smul] at h
  exact smul_right_injective ℍ[ℚ, a, b] (Int.cast_ne_zero.mpr hn) h

def nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] :=
  X.map ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))

theorem mem_nsub {n : ℕ} {X : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ[ℚ, a, b]} :
    x ∈ nsub n X ↔ ∃ y ∈ X, (n : ℤ) • y = x := by
  simp [nsub, Submodule.mem_map]

theorem nsub_mono {n : ℕ} {X Y : Submodule ℤ ℍ[ℚ, a, b]} (h : X ≤ Y) : nsub n X ≤ nsub n Y :=
  Submodule.map_mono h

theorem span_image_eq_nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) '' (X : Set ℍ[ℚ, a, b])) = nsub n X := by
  have : (fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) = ⇑((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
    funext y; simp
  rw [this, ← Submodule.map_span, Submodule.span_eq]; rfl

theorem relIndex_nsub_self {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (n : ℕ) (hn : 0 < n) :
    (nsub n X).toAddSubgroup.relIndex X.toAddSubgroup = n ^ 4 := by
  rw [← span_image_eq_nsub]; exact hX.relIndex_span_smul_eq_pow_four n hn

theorem relIndex_nsub_nsub {n : ℕ} (hn : n ≠ 0) (X Y : Submodule ℤ ℍ[ℚ, a, b]) :
    (nsub n X).toAddSubgroup.relIndex (nsub n Y).toAddSubgroup = X.toAddSubgroup.relIndex Y.toAddSubgroup := by
  simp only [nsub, Submodule.map_toAddSubgroup]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ ?_
  intro x y hxy
  have : (n : ℤ) • x = (n : ℤ) • y := by simpa using hxy
  exact zsmul_right_cancel (Int.natCast_ne_zero.mpr hn) this

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_eq_one_or_of_mul_eq_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u v : ℍ[ℚ, a, b]}
    (hu : u ∈ Λ) (hv : v ∈ Λ) (huv : u * v = 1) : nrd u = 1 ∨ nrd u = -1 := by
  obtain ⟨m, hm⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hu).1
  obtain ⟨n, hn⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hv).1
  have h : nrd u * nrd v = 1 := by rw [← nrd_mul', huv, nrd_one]
  rw [← hm, ← hn] at h
  have h' : m * n = 1 := by exact_mod_cast h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h' with h1 | h1
  · left; rw [← hm, h1]; simp
  · right; rw [← hm, h1]; simp

end AlExists

open AlExists in

theorem AlExists.core
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (h1 : Λ ≤ J') (h2 : ∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') (h3 : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ)
    (h4 : Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2) (h5 : ∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')
    (s : ℍ[ℚ, a, b]) (hs : ∀ y : ℍ[ℚ, a, b], y ∈ nsub N J' ↔ ∃ z ∈ Λ, z * s = y) :
    (nrd s = (N : ℚ) ∨ nrd s = -(N : ℚ)) ∧
      ∃ W : (ℍ[ℚ, a, b])ˣ, (W : ℍ[ℚ, a, b]) ∈ R ∧ nrd (W : ℍ[ℚ, a, b]) = nrd s ∧
        ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (W : ℍ[ℚ, a, b]) * x * ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  set n : ℍ[ℚ, a, b] := ((N : ℚ) : ℍ[ℚ, a, b]) with hn
  have hncomm : ∀ x : ℍ[ℚ, a, b], n * x = x * n := fun x => coe_commutes _ _

  have hNJΛ : ∀ y ∈ nsub N J', y ∈ Λ := by
    intro y hy; obtain ⟨y', hy', rfl⟩ := mem_nsub.1 hy; exact h3 y' hy'
  have hsNJ : s ∈ nsub N J' := (hs s).2 ⟨1, hΛo.one_mem, one_mul s⟩
  have hsΛ : s ∈ Λ := hNJΛ s hsNJ
  obtain ⟨y₀, hy₀, hy₀s⟩ := mem_nsub.1 hsNJ
  have hnNJ : n ∈ nsub N J' := mem_nsub.2 ⟨1, h1 hΛo.one_mem, by rw [hn, natCast_zsmul_eq_coe_mul, mul_one]⟩
  obtain ⟨μ, hμ, hμs⟩ := (hs n).1 hnNJ
  have hs0 : s ≠ 0 := by
    intro h; apply hNq
    have : n = 0 := by rw [← hμs, h, mul_zero]
    have := congrArg QuaternionAlgebra.re this
    simpa [hn] using this
  obtain ⟨S, hS⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB s hs0
  have hn0 : n ≠ 0 := by
    intro h; apply hNq; have := congrArg QuaternionAlgebra.re h; simpa [hn] using this
  obtain ⟨Nu, hNu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB n hn0
  have hμ' : μ = n * (S⁻¹ : (ℍ[ℚ, a, b])ˣ) := by
    rw [← hμs, ← hS, Units.mul_inv_cancel_right]

  have hidxNJ : (nsub N J').toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 2 := by
    have hNΛNJ : nsub N Λ ≤ nsub N J' := nsub_mono h1
    have hidx1 : (nsub N Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 4 :=
      relIndex_nsub_self hΛo N (Nat.pos_of_ne_zero hN0)
    have hidx2 : (nsub N Λ).toAddSubgroup.relIndex (nsub N J').toAddSubgroup = N ^ 2 := by
      rw [relIndex_nsub_nsub hN0, h4]
    have h' := AddSubgroup.relIndex_mul_relIndex (nsub N Λ).toAddSubgroup (nsub N J').toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hNΛNJ hx) (fun x hx => hNJΛ x hx)
    rw [hidx1, hidx2, show N ^ 4 = N ^ 2 * N ^ 2 by ring] at h'
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN0) 2) h'

  let fR : ℍ[ℚ, a, b] → ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := fun y => LinearMap.mulRight ℤ y
  have hfR : ∀ y x, fR y x = x * y := fun y x => rfl
  set K : Submodule ℤ ℍ[ℚ, a, b] := Λ.map (fR ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) with hK
  have hmemK : ∀ y, y ∈ K ↔ y * s ∈ Λ := by
    intro y
    rw [hK, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [hfR, ← hS, Units.inv_mul_cancel_right]; exact hx
    · intro hy; exact ⟨y * s, hy, by rw [hfR, ← hS, Units.mul_inv_cancel_right]⟩
  have hK1 : Λ ≤ K := fun x hx => (hmemK x).2 (hΛo.mul_mem hx hsΛ)
  have hK2 : ∀ x ∈ Λ, ∀ y ∈ K, x * y ∈ K := by
    intro x hx y hy; rw [hmemK] at hy ⊢; rw [mul_assoc]; exact hΛo.mul_mem hx hy
  have hsμ : s * μ = n := by
    rw [hμ', ← mul_assoc, ← hncomm, mul_assoc, ← hS, Units.mul_inv, mul_one]
  have hK3 : ∀ y ∈ K, ((N : ℤ) • y) ∈ Λ := by
    intro y hy
    rw [hmemK] at hy
    rw [natCast_zsmul_eq_coe_mul, ← hn, hncomm, ← hsμ, ← mul_assoc]
    exact hΛo.mul_mem hy hμ
  have hfs_inj : Function.Injective (fR s) := by
    intro x y hxy; rw [hfR, hfR, ← hS] at hxy; exact (Units.mul_left_inj S).1 hxy
  have hΛs : Λ.map (fR s) = nsub N J' := by
    ext y; rw [Submodule.mem_map, hs]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, (hfR s z).symm ▸ rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, hfR s z⟩
  have hKs : K.map (fR s) = Λ := by
    ext y; rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [hfR]; exact (hmemK x).1 hx
    · intro hy
      refine ⟨y * ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), (hmemK _).2 ?_, ?_⟩
      · rw [← hS, Units.inv_mul_cancel_right]; exact hy
      · rw [hfR, ← hS, Units.inv_mul_cancel_right]
  have hK4 : Λ.toAddSubgroup.relIndex K.toAddSubgroup = N ^ 2 := by
    have e1 := AddSubgroup.relIndex_map_map_of_injective (f := (fR s).toAddMonoidHom) Λ.toAddSubgroup K.toAddSubgroup hfs_inj
    have e2 : (Λ.map (fR s)).toAddSubgroup.relIndex (K.map (fR s)).toAddSubgroup =
        Λ.toAddSubgroup.relIndex K.toAddSubgroup := e1
    rw [← e2, hΛs, hKs, hidxNJ]

  obtain ⟨u, ⟨huΛ, v, hvΛ, huv, hvu⟩, hunrd, hKu⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
      hqN hq'N hqq' hB Λ hΛ hN J' K ⟨h1, h2, h3, h4⟩ ⟨hK1, hK2, hK3, hK4⟩
  let U : (ℍ[ℚ, a, b])ˣ := ⟨u, v, huv, hvu⟩
  have hU : (U : ℍ[ℚ, a, b]) = u := rfl
  have hUi : ((U⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = v := rfl

  have hy₀us : y₀ * u * s ∈ Λ := by
    have : y₀ * u ∈ K := (hKu _).2 ⟨y₀, hy₀, rfl⟩
    exact (hmemK _).1 this
  set lam : ℍ[ℚ, a, b] := y₀ * u * s with hlam
  have hsus : s * u * s = n * lam := by
    rw [hlam, ← mul_assoc, ← mul_assoc, hn, ← natCast_zsmul_eq_coe_mul, hy₀s]

  have hsinvK : ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ K := (hmemK _).2 (by rw [← hS, Units.inv_mul]; exact hΛo.one_mem)
  obtain ⟨y₁, hy₁, hy₁u⟩ := (hKu _).1 hsinvK
  obtain ⟨ζ, hζ, hζs⟩ := (hs ((N : ℤ) • y₁)).1 (mem_nsub.2 ⟨y₁, hy₁, rfl⟩)
  have hζlam : ζ * lam = 1 := by

    have hζy₀ : ζ * y₀ = y₁ := by
      apply zsmul_right_cancel (Int.natCast_ne_zero.mpr hN0 : ((N : ℕ) : ℤ) ≠ 0)
      rw [← hζs, ← hy₀s, mul_smul_comm]
    rw [hlam, ← mul_assoc, ← mul_assoc, hζy₀, ← hy₁u, ← hS, Units.inv_mul]
  have hlamζ : lam * ζ = 1 := by
    have hlam0 : lam ≠ 0 := by intro h; rw [h, mul_zero] at hζlam; exact zero_ne_one hζlam
    obtain ⟨Lu, hLu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB lam hlam0
    rw [← hLu] at hζlam ⊢
    calc (Lu : ℍ[ℚ, a, b]) * ζ = (Lu : ℍ[ℚ, a, b]) * ζ * ((Lu : ℍ[ℚ, a, b]) * ((Lu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) := by
          rw [Units.mul_inv, mul_one]
      _ = (Lu : ℍ[ℚ, a, b]) * (ζ * (Lu : ℍ[ℚ, a, b])) * ((Lu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hζlam, mul_one, Units.mul_inv]
  let L : (ℍ[ℚ, a, b])ˣ := ⟨lam, ζ, hlamζ, hζlam⟩
  have hL : (L : ℍ[ℚ, a, b]) = lam := rfl
  have hLi : ((L⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = ζ := rfl
  have hlamΛ : lam ∈ Λ := hy₀us

  have hRchar : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ x ∈ Λ ∧ ∃ z ∈ Λ, z * s = s * x := by
    intro x
    constructor
    · intro hx
      have hxΛ := hRΛ hx
      refine ⟨hxΛ, ?_⟩
      have hyx : y₀ * x ∈ J' := (h5 x hxΛ).1 hx y₀ hy₀
      have : s * x ∈ nsub N J' := mem_nsub.2 ⟨y₀ * x, hyx, by rw [← smul_mul_assoc, hy₀s]⟩
      exact (hs _).1 this
    · rintro ⟨hxΛ, z, hz, hzs⟩
      refine (h5 x hxΛ).2 fun y hy => ?_
      obtain ⟨z₂, hz₂, hz₂s⟩ := (hs ((N : ℤ) • y)).1 (mem_nsub.2 ⟨y, hy, rfl⟩)
      have : (N : ℤ) • (y * x) ∈ nsub N J' := by
        refine (hs _).2 ⟨z₂ * z, hΛo.mul_mem hz₂ hz, ?_⟩
        rw [mul_assoc, hzs, ← mul_assoc, hz₂s, smul_mul_assoc]
      obtain ⟨y₃, hy₃, e⟩ := mem_nsub.1 this
      rw [← zsmul_right_cancel (Int.natCast_ne_zero.mpr hN0 : ((N : ℕ) : ℤ) ≠ 0) e]; exact hy₃

  have hnsmul : ∀ x : ℍ[ℚ, a, b], n * x = (N : ℚ) • x := fun x => by rw [hn, coe_mul_eq_smul]
  have hsusS : s * (u * s) = (N : ℚ) • lam := by rw [← mul_assoc, hsus, hnsmul]
  set W : (ℍ[ℚ, a, b])ˣ := U * S with hW
  have hWv : (W : ℍ[ℚ, a, b]) = u * s := by rw [hW, Units.val_mul, hU, hS]
  have hWi : ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v := by
    rw [hW, mul_inv_rev, Units.val_mul, hUi]

  have hfwd : ∀ x ∈ R, (W : ℍ[ℚ, a, b]) * x * ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by
    intro x hx
    obtain ⟨hxΛ, z, hz, hzs⟩ := (hRchar x).1 hx
    have e : (W : ℍ[ℚ, a, b]) * x * ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = u * z * v := by
      rw [hWv, hWi, show u * s * x * (((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v) =
        u * (s * x) * ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v by simp only [mul_assoc], ← hzs,
        show u * (z * s) * ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v =
          u * z * (s * ((S⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * v by simp only [mul_assoc], ← hS, Units.mul_inv, mul_one]
    rw [e]
    refine (hRchar _).2 ⟨hΛo.mul_mem (hΛo.mul_mem huΛ hz) hvΛ, lam * x * ζ,
      hΛo.mul_mem (hΛo.mul_mem hlamΛ hxΛ) hζ, ?_⟩

    apply (Units.mul_left_inj W).1
    rw [hWv]
    have lhs : lam * x * ζ * s * (u * s) = (N : ℚ) • (lam * x) := by
      rw [show lam * x * ζ * s * (u * s) = lam * x * ζ * (s * (u * s)) by simp only [mul_assoc], hsusS,
        mul_smul_comm, show lam * x * ζ * lam = lam * x * (ζ * lam) by simp only [mul_assoc], hζlam, mul_one]
    have rhs : s * (u * z * v) * (u * s) = (N : ℚ) • (lam * x) := by
      rw [show s * (u * z * v) * (u * s) = s * u * z * (v * u) * s by simp only [mul_assoc], hvu, mul_one,
        show s * u * z * s = s * u * (z * s) by simp only [mul_assoc], hzs,
        show s * u * (s * x) = s * (u * s) * x by simp only [mul_assoc], hsusS, smul_mul_assoc]
    rw [lhs, rhs]

  have hbwd : ∀ x ∈ R, ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * x * (W : ℍ[ℚ, a, b]) ∈ R := by
    intro x hx
    obtain ⟨hxΛ, z, hz, hzs⟩ := (hRchar x).1 hx
    have key2 : x * (W : ℍ[ℚ, a, b]) = (W : ℍ[ℚ, a, b]) * (ζ * z * lam) := by
      apply (Units.mul_right_inj S).1
      rw [hS, hWv]
      have lhs : s * (x * (u * s)) = (N : ℚ) • (z * lam) := by
        rw [← mul_assoc, ← hzs, mul_assoc, hsusS, mul_smul_comm]
      have rhs : s * (u * s * (ζ * z * lam)) = (N : ℚ) • (z * lam) := by
        rw [show s * (u * s * (ζ * z * lam)) = s * (u * s) * (ζ * z * lam) by simp only [mul_assoc], hsusS,
          smul_mul_assoc, show lam * (ζ * z * lam) = lam * ζ * (z * lam) by simp only [mul_assoc], hlamζ, one_mul]
      rw [lhs, rhs]
    have e : ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * x * (W : ℍ[ℚ, a, b]) = ζ * z * lam := by
      rw [mul_assoc, key2, Units.inv_mul_cancel_left]
    refine (hRchar _).2 ⟨?_, v * x * u, hΛo.mul_mem (hΛo.mul_mem hvΛ hxΛ) huΛ, ?_⟩
    · rw [e]; exact hΛo.mul_mem (hΛo.mul_mem hζ hz) hlamΛ
    · rw [hWi, hWv, ← hS]; simp only [mul_assoc, Units.mul_inv_cancel_left]
  refine ⟨?_, W, ?_, by rw [hWv, nrd_mul', hunrd, one_mul], fun x => ⟨hfwd x, fun hx => ?_⟩⟩
  ·
    have hnl : nrd s * nrd s = (N : ℚ) ^ 2 * nrd lam := by
      have := congrArg nrd hsus
      rw [nrd_mul', nrd_mul', hunrd, mul_one, nrd_mul', hn, nrd_coe] at this
      exact this
    rcases nrd_eq_one_or_of_mul_eq_one hΛo hlamΛ hζ hlamζ with h | h
    · rw [h, mul_one, ← sq] at hnl
      exact sq_eq_sq_iff_eq_or_eq_neg.1 hnl
    · exfalso
      rw [h] at hnl
      have : (0 : ℚ) ≤ nrd s * nrd s := mul_self_nonneg _
      have : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
      linarith
  ·
    refine (hRchar _).2 ⟨by rw [hWv]; exact hΛo.mul_mem huΛ hsΛ, lam * μ, hΛo.mul_mem hlamΛ hμ, ?_⟩
    rw [hWv, hsusS, mul_assoc, hμs, ← hncomm, hnsmul]
  ·
    have e : x = ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) *
        ((W : ℍ[ℚ, a, b]) * x * ((W⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * (W : ℍ[ℚ, a, b]) := by
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    rw [e]; exact hbwd _ hx

open AlExists in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ) :
    ∃ w : (ℍ[ℚ, a, b])ˣ,
      (w : ℍ[ℚ, a, b]) ∈ R ∧ nrd (w : ℍ[ℚ, a, b]) = (N : ℚ) ∧
      ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N

  obtain ⟨ι, hι⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_algHom_matrix_injective hB
  obtain ⟨J', h1, h2, h3, h4, h5⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_levelModule hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι

  have hNJΛ : nsub N J' ≤ Λ := by
    intro y hy; obtain ⟨y', hy', rfl⟩ := mem_nsub.1 hy; exact h3 y' hy'
  have hfg : (nsub N J').FG := by
    haveI : IsNoetherian ℤ ↥Λ := isNoetherian_of_fg_of_noetherian _ hΛo.fg
    have h' : ((nsub N J').comap Λ.subtype).FG := IsNoetherian.noetherian _
    have e : ((nsub N J').comap Λ.subtype).map Λ.subtype = nsub N J' := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hNJΛ]
    rw [← e]; exact h'.map _
  have hspan : Submodule.span ℚ ((nsub N J' : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = ⊤ := by
    rw [eq_top_iff, ← hΛo.spanTop]
    apply Submodule.span_le.2
    intro x hx
    have hNx : (N : ℤ) • x ∈ nsub N J' := mem_nsub.2 ⟨x, h1 hx, rfl⟩
    have e : x = ((N : ℚ)⁻¹) • ((N : ℤ) • x) := by
      rw [natCast_zsmul_eq_ratCast_smul, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN0 : (N : ℚ) ≠ 0),
        one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hNx)
  have hstab : ∀ x ∈ Λ, ∀ y ∈ nsub N J', x * y ∈ nsub N J' := by
    intro x hx y hy
    obtain ⟨y', hy', rfl⟩ := mem_nsub.1 hy
    exact mem_nsub.2 ⟨x * y', h2 x hx y' hy', by rw [mul_smul_comm]⟩
  obtain ⟨s₀, hs₀0, hs₀⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ
      (nsub N J') hfg hspan hstab

  obtain ⟨hsign, W, hWR, hWnrd, hWconj⟩ := AlExists.core hqN hq'N hqq' hB Λ hΛ hN R hRΛ J' h1 h2 h3 h4 h5 s₀ hs₀
  rcases hsign with hpos | hneg
  · exact ⟨W, hWR, by rw [hWnrd, hpos], hWconj⟩
  · obtain ⟨ε, ⟨hεΛ, ε', hε'Λ, hεε', hε'ε⟩, hεnrd⟩ :=
      QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_neg_one hB Λ hΛ
    have hs₁ : ∀ y : ℍ[ℚ, a, b], y ∈ nsub N J' ↔ ∃ z ∈ Λ, z * (ε * s₀) = y := by
      intro y
      rw [hs₀]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z * ε', hΛo.mul_mem hz hε'Λ, by rw [mul_assoc, ← mul_assoc ε', hε'ε, one_mul]⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z * ε, hΛo.mul_mem hz hεΛ, by rw [mul_assoc]⟩
    obtain ⟨-, W₁, hW₁R, hW₁nrd, hW₁conj⟩ :=
      AlExists.core hqN hq'N hqq' hB Λ hΛ hN R hRΛ J' h1 h2 h3 h4 h5 (ε * s₀) hs₁
    exact ⟨W₁, hW₁R, by rw [hW₁nrd, nrd_mul', hεnrd, hneg]; ring, hW₁conj⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem (solution)
