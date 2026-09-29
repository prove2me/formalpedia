-- Prove2me | solution 1 for Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8e64f651-d69e-5dcf-9d64-f9f7d250999b

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

section BoxFull

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

theorem q7_algebraMap_apply (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl

theorem q7_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem q7_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, q7_valued_algebraMap_apply]

theorem q7_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem q7_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem q7_hDen (a : 𝔸f) : ∃ m : ℕ, m ≠ 0 ∧
    ∀ v : HOS, (algebraMap ℚ 𝔸f (m : ℚ) * a) v ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers ℚ a
  obtain ⟨m', hm'⟩ := q7_exists_intCast_eq d
  have hd0 : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero] at hm'
    exact hd0 hm'
  have hdm : algebraMap (𝓞 ℚ) ℚ d = (m' : ℚ) := hm'
  refine ⟨m'.natAbs ^ 2, pow_ne_zero _ (Int.natAbs_ne_zero.mpr hm'0), fun v => ?_⟩
  have e : (((m'.natAbs ^ 2 : ℕ)) : ℚ) = (m' : ℚ) * (m' : ℚ) := by
    have hz : ((m'.natAbs : ℤ)) * (m'.natAbs : ℤ) = m' * m' := Int.natAbs_mul_self' m'
    rw [sq, Nat.cast_mul, ← Int.cast_natCast, ← Int.cast_mul, hz, Int.cast_mul]
  have : (algebraMap ℚ 𝔸f (((m'.natAbs ^ 2 : ℕ)) : ℚ) * a) v
      = algebraMap ℚ (v.adicCompletion ℚ) (m' : ℚ) * (algebraMap ℚ (v.adicCompletion ℚ) (m' : ℚ) * a v) := by
    have h1 : (algebraMap ℚ 𝔸f (((m'.natAbs ^ 2 : ℕ)) : ℚ) * a) v
        = (algebraMap ℚ 𝔸f (((m'.natAbs ^ 2 : ℕ)) : ℚ)) v * a v := rfl
    rw [h1, q7_algebraMap_apply, e, map_mul, mul_assoc]
  rw [this]
  refine mul_mem ?_ ?_
  · rw [← q7_algebraMap_apply]
    exact (q7_algebraMap_apply_mem_integers_iff _ v).mpr (q7_valuation_intCast_le_one v m')
  · have h2 := h v
    rwa [hdm] at h2

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem q7_tmul_mem_box (Λ : Submodule ℤ D) {z : D} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem q7_natCast_smul_mem_box (Λ : Submodule ℤ D) {t : D ⊗[ℚ] 𝔸f}
    (ht : t ∈ Submodule.finiteAdeleBox Λ) (n : ℕ) : (n : ℚ) • t ∈ Submodule.finiteAdeleBox Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ ht n

theorem q7_exists_natCast_smul_mem (Λ : Submodule ℤ D) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (z : D) : ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • z ∈ Λ := by
  have hz : z ∈ Submodule.span ℚ (Λ : Set D) := by rw [hspan]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm0, hm⟩ := hx
      obtain ⟨n, hn0, hn⟩ := hy
      refine ⟨m * n, mul_ne_zero hm0 hn0, ?_⟩
      have e1 : ((m * n : ℕ) : ℚ) • x = n • ((m : ℚ) • x) := by
        rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
      have e2 : ((m * n : ℕ) : ℚ) • y = m • ((n : ℚ) • y) := by
        rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
      rw [smul_add, e1, e2]
      exact Λ.add_mem (nsmul_mem hm n) (nsmul_mem hn m)
  | smul q x _ hx =>
      obtain ⟨n, hn0, hn⟩ := hx
      refine ⟨q.den * n, mul_ne_zero q.den_nz hn0, ?_⟩
      have e : ((q.den * n : ℕ) : ℚ) • (q • x) = (q.num : ℤ) • ((n : ℚ) • x) := by
        rw [Nat.cast_mul, smul_smul, mul_assoc, mul_comm (n : ℚ) q, ← mul_assoc, mul_comm (q.den : ℚ) q,
          Rat.mul_den_eq_num, mul_smul, Int.cast_smul_eq_zsmul]
      rw [e]
      exact Λ.smul_mem q.num hn

theorem q7_box_full (Λ : Submodule ℤ D) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (w : D ⊗[ℚ] 𝔸f) : ∃ N : ℕ, N ≠ 0 ∧ (N : ℚ) • w ∈ Submodule.finiteAdeleBox Λ := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | tmul z a =>
      obtain ⟨n, hn0, hn⟩ := q7_exists_natCast_smul_mem Λ hspan z
      obtain ⟨m, hm0, hm⟩ := q7_hDen a
      refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
      have e : ((n * m : ℕ) : ℚ) • (z ⊗ₜ[ℚ] a) = ((n : ℚ) • z) ⊗ₜ[ℚ] ((m : ℚ) • a) := by
        rw [Nat.cast_mul, mul_comm, mul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul]
      rw [e]
      refine q7_tmul_mem_box Λ hn fun v => ?_
      rw [Algebra.smul_def]
      exact hm v
  | add x y hx hy =>
      obtain ⟨M, hM0, hM⟩ := hx
      obtain ⟨N, hN0, hN⟩ := hy
      refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
      have e1 : ((M * N : ℕ) : ℚ) • x = (N : ℚ) • ((M : ℚ) • x) := by
        rw [Nat.cast_mul, mul_comm, mul_smul]
      have e2 : ((M * N : ℕ) : ℚ) • y = (M : ℚ) • ((N : ℚ) • y) := by
        rw [Nat.cast_mul, mul_smul]
      rw [smul_add, e1, e2]
      exact add_mem (q7_natCast_smul_mem_box Λ hM N) (q7_natCast_smul_mem_box Λ hN M)

end Box

end BoxFull

theorem solution {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (w : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℚ) • w ∈ Submodule.finiteAdeleBox Λ :=
  q7_box_full Λ hspan w

end S_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
end P2MW
export P2MW.S_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox (solution)
