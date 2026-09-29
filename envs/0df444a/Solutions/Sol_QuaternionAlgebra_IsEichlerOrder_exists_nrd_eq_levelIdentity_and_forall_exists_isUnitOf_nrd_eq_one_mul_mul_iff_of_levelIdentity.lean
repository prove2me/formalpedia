-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6c00726e-4eb7-5cdf-8aed-3295a4dbc605

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace DoubleCoset
p2m_open "DoubleCoset"

variable {a b : ℚ}

theorem zsmul_eq_ratCast_smul (n : ℤ) (x : ℍ[ℚ, a, b]) : n • x = (n : ℚ) • x :=
  (Int.cast_smul_eq_zsmul ℚ n x).symm

theorem natCast_zsmul_eq_ratCast_smul (n : ℕ) (x : ℍ[ℚ, a, b]) : (n : ℤ) • x = (n : ℚ) • x := by
  rw [zsmul_eq_ratCast_smul]; push_cast; rfl

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

theorem not_dvd_of_squarefree {N p m : ℕ} (hN : Squarefree N) (hp : p.Prime) (h : N = p * m) : ¬ p ∣ m := by
  rintro ⟨k, rfl⟩
  have : p * p ∣ N := ⟨k, by rw [h]; ring⟩
  exact hp.not_isUnit (hN p this)

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem intCast_eq_zsmul_one (t : ℤ) : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨t, ht⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht, intCast_eq_zsmul_one]
  exact sub_mem (Λ.smul_mem t hΛ.one_mem) hx

theorem star_mem_of_le {Λ R : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (hRΛ : R ≤ Λ) (h1 : (1 : ℍ[ℚ, a, b]) ∈ R)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ R) : star x ∈ R := by
  obtain ⟨t, ht⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd (hRΛ hx)).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht, intCast_eq_zsmul_one]
  exact sub_mem (R.smul_mem t h1) hx

theorem exists_nrd_add_zsmul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x w : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hw : w ∈ Λ) (m : ℤ) :
    ∃ j : ℤ, nrd (x + m • w) = nrd x + (m : ℚ) * (j : ℚ) := by
  obtain ⟨n₁, hn₁⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).1
  obtain ⟨n₂, hn₂⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hw).1
  obtain ⟨n₃, hn₃⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd (add_mem hx hw)).1
  refine ⟨n₃ - n₁ - n₂ + m * n₂, ?_⟩
  have key : nrd (x + m • w) = nrd x + (m : ℚ) * (nrd (x + w) - nrd x - nrd w) + (m : ℚ) ^ 2 * nrd w := by
    rw [zsmul_eq_ratCast_smul]
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    obtain ⟨w₀, w₁, w₂, w₃⟩ := w
    simp only [nrd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
    ring
  rw [key, ← hn₁, ← hn₂, ← hn₃]; push_cast; ring

theorem smul_mem_line {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {t' : ℍ[ℚ, a, b]} (ht' : t' ∈ Λ)
    {ℓ : ℕ} (hnt' : nrd t' = (ℓ : ℚ)) {m : ℍ[ℚ, a, b]} (hm : m ∈ Λ) :
    ∃ m' ∈ Λ, m' * t' = (ℓ : ℤ) • m := by
  refine ⟨m * star t', hΛ.mul_mem hm (star_mem hΛ ht'), ?_⟩
  rw [mul_assoc, star_mul_eq_coe_nrd, hnt', ← coe_commutes, coe_mul_eq_smul, natCast_zsmul_eq_ratCast_smul]

end DoubleCoset

namespace DoubleCoset
p2m_open "DoubleCoset"

variable {a b : ℚ}

theorem crt_step {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) {c : ℍ[ℚ, a, b]} (hc : c ∈ Λ)
    {ℓ m₀ : ℕ} (hcop : Nat.Coprime ℓ m₀) (k : ℤ) (hk : nrd c = 1 + (ℓ : ℚ) * (k : ℚ))
    (α β : ℤ) (hαβ : α * ℓ + β * m₀ = 1) :
    (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) ∈ Λ ∧
    (∃ k' : ℤ, nrd (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = 1 + ((ℓ * m₀ : ℕ) : ℚ) * (k' : ℚ)) ∧
    (∃ w ∈ Λ, (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = c + (ℓ : ℤ) • w) ∧
    (∃ w' ∈ Λ, (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = 1 + (m₀ : ℤ) • w') := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛo.one_mem
  have hc1 : c - 1 ∈ Λ := sub_mem hc h1
  have e1 : (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = c + (ℓ : ℤ) • ((-α) • (c - 1)) := by
    have : β * (m₀ : ℤ) = 1 - α * ℓ := by linarith
    rw [this]; module
  have e2 : (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = 1 + (m₀ : ℤ) • (β • (c - 1)) := by module
  refine ⟨add_mem h1 (Λ.smul_mem _ hc1), ?_, ⟨(-α) • (c - 1), Λ.smul_mem _ hc1, e1⟩,
    ⟨β • (c - 1), Λ.smul_mem _ hc1, e2⟩⟩
  obtain ⟨j₁, hj₁⟩ := exists_nrd_add_zsmul hΛo hc (Λ.smul_mem (-α) hc1) (ℓ : ℤ)
  obtain ⟨j₂, hj₂⟩ := exists_nrd_add_zsmul hΛo h1 (Λ.smul_mem β hc1) (m₀ : ℤ)
  obtain ⟨ν, hν⟩ := (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
    (add_mem h1 (Λ.smul_mem (β * (m₀ : ℤ)) hc1))).1
  have hνℓ : (ℓ : ℤ) ∣ ν - 1 := by
    refine ⟨k + j₁, ?_⟩
    have h' : (ν : ℚ) = 1 + (ℓ : ℚ) * ((k + j₁ : ℤ) : ℚ) := by
      rw [hν, e1, hj₁, hk]; push_cast; ring
    have h'' : ν = 1 + (ℓ : ℤ) * (k + j₁) := by exact_mod_cast h'
    linarith
  have hνm : (m₀ : ℤ) ∣ ν - 1 := by
    refine ⟨j₂, ?_⟩
    have h' : (ν : ℚ) = 1 + (m₀ : ℚ) * ((j₂ : ℤ) : ℚ) := by
      rw [hν, e2, hj₂, nrd_one]; push_cast; ring
    have h'' : ν = 1 + (m₀ : ℤ) * j₂ := by exact_mod_cast h'
    linarith
  obtain ⟨k', hk'⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd hνℓ hνm
  refine ⟨k', ?_⟩
  rw [← hν]
  have h'' : ν = 1 + (ℓ : ℤ) * (m₀ : ℤ) * k' := by linarith
  push_cast
  exact_mod_cast h''

theorem global_step
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (h1 : Λ ≤ J') (h3 : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) (h5 : ∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M m₀ : ℕ) [NeZero M] (hqM : ¬ q ∣ M) (hq'M : ¬ q' ∣ M) (hM : M = ℓ * m₀) (hNM : N ∣ M)
    (t t' : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (ht' : t' ∈ Λ) (hnt : nrd t = (ℓ : ℚ)) (hnt' : nrd t' = (ℓ : ℚ))
    (c' : ℍ[ℚ, a, b]) (hc'R : c' ∈ R) (k : ℤ) (hk : nrd c' = 1 + (M : ℚ) * (k : ℚ))
    (hmove : ∀ m ∈ Λ, ∃ m' ∈ Λ, m * t * c' = m' * t') :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧
      ∀ x : ℍ[ℚ, a, b], (∃ m ∈ Λ, m * (t * u) = x) ↔ ∃ m ∈ Λ, m * t' = x := by
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hc'Λ : c' ∈ Λ := hRΛ hc'R

  obtain ⟨u, ⟨huΛ, v, hvΛ, huv, hvu⟩, hnrd, z, hzΛ, huz⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
      (N := M) hqM hq'M hqq' hB Λ hΛ c' hc'Λ k hk
  have hu_eq : u = c' + (M : ℤ) • z := by rw [← huz]; abel

  obtain ⟨d, hd⟩ := hNM
  have hMzR : (M : ℤ) • z ∈ R := by
    refine (h5 _ (Λ.smul_mem _ hzΛ)).2 fun y hy => ?_
    rw [hd, Nat.cast_mul, mul_smul, mul_smul_comm, ← smul_mul_assoc]
    exact h1 (hΛo.mul_mem (h3 y hy) (Λ.smul_mem _ hzΛ))
  have huR : u ∈ R := by rw [hu_eq]; exact add_mem hc'R hMzR

  have hstar : star u ∈ R := star_mem_of_le hΛo hRΛ hRo.one_mem huR
  have hus : u * star u = 1 := by rw [mul_star_eq_coe_nrd, hnrd]; rfl
  have hsu : star u * u = 1 := by rw [star_mul_eq_coe_nrd, hnrd]; rfl
  refine ⟨u, ⟨huR, star u, hstar, hus, hsu⟩, hnrd, ?_⟩

  have hsub : ∀ m ∈ Λ, ∃ m' ∈ Λ, m * (t * u) = m' * t' := by
    intro m hm
    obtain ⟨m₁, hm₁, e₁⟩ := hmove m hm
    obtain ⟨m₂, hm₂, e₂⟩ := smul_mem_line hΛo ht' hnt'
      (Λ.smul_mem (m₀ : ℤ) (hΛo.mul_mem (hΛo.mul_mem hm ht) hzΛ))
    refine ⟨m₁ + m₂, add_mem hm₁ hm₂, ?_⟩
    rw [← mul_assoc, hu_eq, mul_add, e₁, add_mul, e₂, mul_smul_comm, hM, Nat.cast_mul, mul_smul]

  have hu0 : IsUnit u := ⟨⟨u, star u, hus, hsu⟩, rfl⟩
  let f : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := LinearMap.mulRight ℤ u
  have hf : ∀ x, f x = x * u := fun x => rfl
  have hfinj : Function.Injective f := fun x y hxy => hu0.mul_left_injective hxy
  let L : ℍ[ℚ, a, b] → Submodule ℤ ℍ[ℚ, a, b] := fun s => Λ.map (LinearMap.mulRight ℤ s)
  have hL : ∀ s x, x ∈ L s ↔ ∃ m ∈ Λ, m * s = x := fun s x => by
    simp only [L, Submodule.mem_map, LinearMap.mulRight_apply]
  have hLt_map : (L t).map f = L (t * u) := by
    ext x; simp only [L, Submodule.mem_map, LinearMap.mulRight_apply]
    constructor
    · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨m, hm, by rw [hf, mul_assoc]⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨m * t, ⟨m, hm, rfl⟩, by rw [hf, mul_assoc]⟩
  have hΛf : Λ.map f = Λ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hΛo.mul_mem hx huΛ
    · intro x hx; exact ⟨x * v, hΛo.mul_mem hx hvΛ, by rw [hf, mul_assoc, hvu, mul_one]⟩
  have hidx : ∀ s, s ∈ Λ → nrd s = (ℓ : ℚ) → (L s).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
    intro s hs hns
    have e1 : Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => y * s) '' (Λ : Set ℍ[ℚ, a, b])) = L s := by
      have : (fun y : ℍ[ℚ, a, b] => y * s) = ⇑(LinearMap.mulRight ℤ s : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]) := by
        funext y; rfl
      rw [this, ← Submodule.map_span, Submodule.span_eq]
    rw [← e1]
    exact QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq Λ hΛo.fg hΛo.spanTop s
      (fun y hy => hΛo.mul_mem hy hs) ℓ (Or.inl hns)
  have hKle : L (t * u) ≤ L t' := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (hL _ _).1 hx
    obtain ⟨m', hm', e'⟩ := hsub m hm
    exact (hL _ _).2 ⟨m', hm', e'.symm⟩
  have hL'le : L t' ≤ Λ := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (hL _ _).1 hx
    exact hΛo.mul_mem hm ht'
  have hidx1 : (L (t * u)).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
    have h' := AddSubgroup.relIndex_map_map_of_injective (f := f.toAddMonoidHom) (L t).toAddSubgroup Λ.toAddSubgroup hfinj
    have h'' : ((L t).map f).toAddSubgroup.relIndex (Λ.map f).toAddSubgroup =
        (L t).toAddSubgroup.relIndex Λ.toAddSubgroup := h'
    rw [hLt_map, hΛf, hidx t ht hnt] at h''
    exact h''
  have hone : (L (t * u)).toAddSubgroup.relIndex (L t').toAddSubgroup = 1 := by
    have h' := AddSubgroup.relIndex_mul_relIndex (L (t * u)).toAddSubgroup (L t').toAddSubgroup Λ.toAddSubgroup
      (fun x hx => hKle hx) (fun x hx => hL'le hx)
    rw [hidx1, hidx t' ht' hnt'] at h'
    have hℓ2 : 0 < ℓ ^ 2 := pow_pos hℓ.pos 2
    have : (L (t * u)).toAddSubgroup.relIndex (L t').toAddSubgroup * ℓ ^ 2 = 1 * ℓ ^ 2 := by rw [one_mul]; exact h'
    exact Nat.eq_of_mul_eq_mul_right hℓ2 this
  have hKge : L t' ≤ L (t * u) := fun x hx => (AddSubgroup.relIndex_eq_one.mp hone) hx
  intro x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨m', hm', e'⟩ := hsub m hm
    exact ⟨m', hm', e'.symm⟩
  · intro hx
    exact (hL _ _).1 (hKge ((hL _ _).2 hx))

end DoubleCoset

namespace DoubleCoset
p2m_open "DoubleCoset"

variable {a b : ℚ}

theorem exists_transversal_line
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (h1 : Λ ≤ J') (h2 : ∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') (h3 : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ)
    (h4 : Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧ (∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ) :=
  QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
    hqN hq'N hqq' hB Λ hΛ hN J' ⟨h1, h2, h3, h4⟩ ℓ hℓ hℓq hℓq'

end DoubleCoset

open _root_.DoubleCoset _root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity.DoubleCoset in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :

    (∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)) ∧

    (∀ t t' : ℍ[ℚ, a, b], t ∈ R → t' ∈ R → nrd t = (ℓ : ℚ) → nrd t' = (ℓ : ℚ) →
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) →
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t' = x) ↔ ∃ j ∈ J', j * t' = x) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧
        ∀ x : ℍ[ℚ, a, b], (∃ m ∈ Λ, m * (t * u) = x) ↔ ∃ m ∈ Λ, m * t' = x) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hRo : IsOrder R := hR.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ'
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨J, hJΛ, hℓJ, hleft, hidx, htrans⟩ :=
      exists_transversal_line hqN hq'N hqq' hB Λ hΛ hN J' h1 h2 h3 h4 ℓ hℓ hℓq hℓq'
    obtain ⟨t, htR, hnt, -, hlev⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
        hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' ⟨h1, h2, h3, h4, h5⟩ ℓ hℓ hℓq hℓq' J hJΛ hℓJ hleft hidx htrans
    exact ⟨t, htR, hnt, hlev⟩
  ·
    intro t t' htR ht'R hnt hnt' hlev hlev'
    have htΛ : t ∈ Λ := hRΛ htR
    have ht'Λ : t' ∈ Λ := hRΛ ht'R
    obtain ⟨c, hcΛ, ⟨k, hk⟩, hJc, hmv⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
        hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' ⟨h1, h2, h3, h4, h5⟩ ℓ hℓ hℓq hℓq' t t' htΛ ht'Λ hnt hnt' hlev hlev'

    have key : ∀ (c' w : ℍ[ℚ, a, b]), w ∈ Λ → c' = c + (ℓ : ℤ) • w →
        ∀ m ∈ Λ, ∃ m' ∈ Λ, m * t * c' = m' * t' := by
      intro c' w hw hc' m hm
      obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := hmv m hm
      obtain ⟨m₂, hm₂, e₂⟩ := smul_mem_line hΛo ht'Λ hnt'
        (add_mem hz₁ (hΛo.mul_mem (hΛo.mul_mem hm htΛ) hw))
      refine ⟨m₁ + m₂, add_mem hm₁ hm₂, ?_⟩
      rw [hc', mul_add, e₁, mul_smul_comm, add_mul, e₂, smul_add, add_assoc]
    by_cases hℓN : ℓ ∣ N
    ·
      obtain ⟨m₀, hm₀⟩ := hℓN
      have hℓm₀ : ¬ ℓ ∣ m₀ := not_dvd_of_squarefree hN hℓ hm₀
      have hcop : Nat.Coprime ℓ m₀ := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓm₀
      obtain ⟨α, β, hαβ⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      obtain ⟨hc'Λ, ⟨k', hk'⟩, ⟨w, hw, e1⟩, -⟩ := crt_step hΛo hcΛ hcop k hk α β hαβ
      have hN' : ((N : ℕ) : ℤ) = (ℓ : ℤ) * (m₀ : ℤ) := by rw [hm₀]; push_cast; rfl
      have hc'R : (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) ∈ R := by
        refine (h5 _ hc'Λ).2 fun y hy => ?_
        obtain ⟨y'', hy'', z, hz, e⟩ := hJc y hy
        have hmid : (m₀ : ℤ) • (y * c - y) = (m₀ : ℤ) • y'' + z - (m₀ : ℤ) • y := by
          apply zsmul_right_cancel (Int.natCast_ne_zero.mpr hℓ.ne_zero)
          calc (ℓ : ℤ) • ((m₀ : ℤ) • (y * c - y)) = ((N : ℤ) • y) * c - (N : ℤ) • y := by
                rw [smul_smul, ← hN', smul_sub, smul_mul_assoc]
            _ = (N : ℤ) • y'' + (ℓ : ℤ) • z - (N : ℤ) • y := by rw [e]
            _ = (ℓ : ℤ) • ((m₀ : ℤ) • y'' + z - (m₀ : ℤ) • y) := by
                rw [smul_sub, smul_add, smul_smul, smul_smul, ← hN']
        have ey : y * (1 + (β * m₀) • (c - 1)) = y + β • ((m₀ : ℤ) • (y * c - y)) := by
          rw [mul_add, mul_one, mul_smul_comm, mul_sub, mul_one, smul_smul]
        rw [ey, hmid]
        exact add_mem hy (J'.smul_mem _ (sub_mem (add_mem (J'.smul_mem _ hy'') (h1 hz)) (J'.smul_mem _ hy)))
      have hkN : nrd (1 + (β * m₀) • (c - 1) : ℍ[ℚ, a, b]) = 1 + (N : ℚ) * (k' : ℚ) := by
        rw [hm₀]; exact hk'
      exact global_step hqq' hB Λ hΛ R hRo hRΛ J' h1 h3 h5 ℓ hℓ N m₀ hqN hq'N hm₀ dvd_rfl
        t t' htΛ ht'Λ hnt hnt' _ hc'R k' hkN (key _ w hw e1)
    ·
      have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓN
      obtain ⟨α, β, hαβ⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      obtain ⟨hc'Λ, ⟨k', hk'⟩, ⟨w, hw, e1⟩, -⟩ := crt_step hΛo hcΛ hcop k hk α β hαβ
      have hc'R : (1 + (β * N) • (c - 1) : ℍ[ℚ, a, b]) ∈ R := by
        refine (h5 _ hc'Λ).2 fun y hy => ?_
        have ey : y * (1 + (β * N) • (c - 1)) = y + β • (((N : ℤ) • y) * c - (N : ℤ) • y) := by
          rw [mul_add, mul_one, mul_smul_comm, mul_sub, mul_one, smul_mul_assoc, ← smul_sub, smul_smul]
        rw [ey]
        exact add_mem hy (J'.smul_mem _ (h1 (sub_mem (hΛo.mul_mem (h3 y hy) hcΛ) (h3 y hy))))
      haveI : NeZero (ℓ * N) := ⟨mul_ne_zero hℓ.ne_zero hN0⟩
      have hqM : ¬ q ∣ ℓ * N := by
        intro h
        rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).1 h with h | h
        · exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hℓ).1 h).symm
        · exact hqN h
      have hq'M : ¬ q' ∣ ℓ * N := by
        intro h
        rcases (Nat.Prime.dvd_mul (Fact.out : q'.Prime)).1 h with h | h
        · exact hℓq' ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hℓ).1 h).symm
        · exact hq'N h
      exact global_step hqq' hB Λ hΛ R hRo hRΛ J' h1 h3 h5 ℓ hℓ (ℓ * N) N hqM hq'M rfl (dvd_mul_left N ℓ)
        t t' htΛ ht'Λ hnt hnt' _ hc'R k' hk' (key _ w hw e1)

end S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity (solution)
