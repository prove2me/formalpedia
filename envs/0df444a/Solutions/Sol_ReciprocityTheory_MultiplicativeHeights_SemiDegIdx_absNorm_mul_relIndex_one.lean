-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:23.232864+00:00
-- url     : https://prove2.me/submissions/d15c16c0-5c0d-4408-9886-d3229f4e5199

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := ⟨C, FractionalIdeal.isFractional_of_fg hC⟩ with hIdef
  have hden := FractionalIdeal.den_mul_self_eq_num I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  set J : Ideal (𝓞 K) := I.num with hJ
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let ι : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  let μ : K →+ K := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)
  have hμ : Function.Injective μ := mul_right_injective₀ hdK
  have hsm : ∀ y : K, (I.den : 𝓞 K) • y = μ y := fun y => by
    rw [Algebra.smul_def]
    rfl
  have hone : AddSubgroup.map μ (1 : Submodule (𝓞 K) K).toAddSubgroup =
      AddSubgroup.map ι (Ideal.span {d}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨r * d, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
  have hCm : AddSubgroup.map μ C.toAddSubgroup = AddSubgroup.map ι J.toAddSubgroup := by
    ext x
    open Pointwise in
    have hx : x ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K)) ↔
        x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      exact Iff.rfl
    rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists] at hx
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx.mp ⟨y, hy, hsm y⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx.mpr ⟨z, hz, rfl⟩
      exact ⟨y, hy, by rw [← hsm]; exact hyx⟩
  have hidx : (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex J.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hμ, hone, hCm,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι]
  have hle : Ideal.span {d} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h1C : (1 : K) ∈ C := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hm : algebraMap (𝓞 K) K d ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      open Pointwise in
      show _ ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K))
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, h1C, by rw [hsm]; simp [μ]⟩
    obtain ⟨z, hz, hzd⟩ := Submodule.mem_map.mp hm
    have hzd' := hι hzd
    rw [hd, ← hzd']
    exact hz
  have htower := AddSubgroup.relIndex_mul_relIndex (Ideal.span {d}).toAddSubgroup
    J.toAddSubgroup ⊤ hle le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htower
  have hiJ : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, AddSubgroup.index_eq_card]
    rfl
  have hid : (Ideal.span {d}).toAddSubgroup.index = (Algebra.norm ℤ d).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      AddSubgroup.index_eq_card]
    rfl
  rw [hiJ, hid] at htower
  have hb : (Algebra.norm ℤ d).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact hd0 h
  have hbq : ((Algebra.norm ℤ d).natAbs : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcast : ((|Algebra.norm ℤ d| : ℤ) : ℚ) = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [hidx, FractionalIdeal.absNorm_eq, hcast, div_mul_eq_mul_div, div_eq_one_iff_eq hbq]
  rw [mul_comm] at htower
  exact_mod_cast htower
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
