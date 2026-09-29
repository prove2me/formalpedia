-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8d1dd4b4-1db2-53a9-a509-1900612b49ac

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld
namespace NormNegOne28
p2m_open "CerednikDrinfeld"

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem diag_mul (x y : (ℍ[ℚ, a, b])ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (x * y) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] y :=
  MonoidHom.map_mul _ x y

theorem diag_inv (x : (ℍ[ℚ, a, b])ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x⁻¹ = (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x)⁻¹ :=
  MonoidHom.map_inv _ x

theorem nrd_mul {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

def unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) : (ℍ[ℚ, a, b])ˣ where
  val := x
  inv := (QuaternionAlgebra.nrd x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd]
    ext <;> simp [hx]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd]
    ext <;> simp [hx]

@[scoped simp] theorem val_unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) :
    ((unitOfNrd x hx : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = x := rfl

theorem nrd_val_inv (B : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]))⁻¹ := by
  have h : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul, Units.mul_inv, QuaternionAlgebra.nrd_one]
  exact (eq_inv_of_mul_eq_one_right h)

theorem nrd_coords {w : HeightOneSpectrum (𝓞 ℚ)} (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd ((⟨algebraMap ℚ (w.adicCompletion ℚ) z.re, algebraMap ℚ (w.adicCompletion ℚ) z.imI,
        algebraMap ℚ (w.adicCompletion ℚ) z.imJ, algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) =
      algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  rw [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_sub, map_add, map_mul, map_pow]

theorem coord_evalAt_tmul_one {w : HeightOneSpectrum (𝓞 ℚ)}
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (hφ : ∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
        algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]))
    (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)))) =
      algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  rw [Submodule.finiteAdeleEvalAt_tmul, show ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w) = 1 from rfl, hφ, one_smul, nrd_coords]

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    ∃ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u ∧ QuaternionAlgebra.nrd u = -1 := by
  classical
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  have h10 : (-1 : ℚ) ≠ 0 := by norm_num

  obtain ⟨β₀, hβ₀⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_nrd_eq hB (-1 : ℚ) h10
  have hβ₀0 : QuaternionAlgebra.nrd β₀ ≠ 0 := by rw [hβ₀]; exact h10
  set B₀ : (ℍ[ℚ, a, b])ˣ := unitOfNrd β₀ hβ₀0 with hB₀

  have hεv : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (-1 : ℚ)) = 1 := by
    intro w
    rw [map_neg, map_one, Valuation.map_neg, Valuation.map_one]
  obtain ⟨m, hmS, hm⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isIndefiniteRamifiedExactlyAt hB hΛ
      (fun w => algebraMap ℚ (w.adicCompletion ℚ) (-1 : ℚ)) hεv

  set y : (𝔸ℍ)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * m with hy
  have hynorm : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ))) = 1 := by
    intro w φ hφ
    have hev : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((B₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ) := by
      rw [hy, Units.val_mul, ← diag_inv, Submodule.val_finiteIdeleDiagonal_apply, map_mul]
    rw [hev, φ.map_mul, nrd_mul, coord_evalAt_tmul_one φ hφ, hm w φ hφ, nrd_val_inv, val_unitOfNrd, hβ₀,
      ← map_mul, inv_mul_cancel₀ h10, map_one]

  obtain ⟨β, u, hβ1, huS, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
      hB.1 (fun x hx => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx) hΛo y hynorm

  have key : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (B₀ * β) = m * u⁻¹ := by
    have e1 : m = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * u) := by
      rw [← hyeq, hy]; group
    rw [diag_mul]
    have e2 : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β = m * u⁻¹ := by
      rw [e1]; group
    exact e2
  have key' : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (B₀ * β)⁻¹ = u * m⁻¹ := by
    rw [diag_inv, key, mul_inv_rev, inv_inv]
  have hmw' := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      Λ hΛo m).mp hmS
  have huw' := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      Λ hΛo u).mp huS

  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((B₀ * β : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
        Submodule.localBox Λ w := by
    intro w
    have hmw := hmw' w
    have huw := huw' w
    rw [Submodule.mem_localBoxUnits_iff] at hmw huw
    have hval : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((B₀ * β : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ) *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((u⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) := by
      rw [← Submodule.val_finiteIdeleDiagonal_apply, key, Units.val_mul, map_mul]
    rw [hval]
    refine localBox_mul_mem hΛo _ ?_ ?_
    · rw [Units.coe_map] at hmw; exact hmw.1
    · rw [Units.coe_map_inv] at huw; exact huw.2
  have hloc' : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((((B₀ * β)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
        Submodule.localBox Λ w := by
    intro w
    have hmw := hmw' w
    have huw := huw' w
    rw [Submodule.mem_localBoxUnits_iff] at hmw huw
    have hval : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((((B₀ * β)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (u : 𝔸ℍ) *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) := by
      rw [← Submodule.val_finiteIdeleDiagonal_apply, key', Units.val_mul, map_mul]
    rw [hval]
    refine localBox_mul_mem hΛo _ ?_ ?_
    · rw [Units.coe_map] at huw; exact huw.1
    · rw [Units.coe_map_inv] at hmw; exact hmw.2

  have hmem_of : ∀ x : ℍ[ℚ, a, b],
      (∀ w : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.localBox Λ w) →
      x ∈ Λ := by
    intro x hx
    rw [← Submodule.ofFiniteIdele_one Λ hΛo.fg hΛo.spanTop, Submodule.mem_ofFiniteIdele_iff]
    refine AddSubgroup.mem_map.mpr ⟨_, ?_, by rw [Units.val_one, AddMonoidHom.coe_mulLeft, one_mul]⟩
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛo.fg hΛo.spanTop]
    exact hx
  have hmem : ((B₀ * β : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ := hmem_of _ hloc
  have hmem' : (((B₀ * β)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ := hmem_of _ hloc'
  refine ⟨_, ⟨hmem, _, hmem', Units.mul_inv _, Units.inv_mul _⟩, ?_⟩
  rw [Units.val_mul, nrd_mul, hβ1, mul_one, hB₀, val_unitOfNrd, hβ₀]

end CerednikDrinfeld.NormNegOne28
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld.NormNegOne28"
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld.NormNegOne28"

open QuaternionAlgebra _root_.CerednikDrinfeld _root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one.CerednikDrinfeld in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = -1 :=
  CerednikDrinfeld.NormNegOne28.main hB Λ hΛ

end S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one (solution)
