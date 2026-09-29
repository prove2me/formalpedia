-- Prove2me | solution 1 for Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/553b8f5c-d6e9-5475-944d-d87b3b466fa8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "Valued P2MW.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt.Valued Filter Topology"

namespace Valued
p2m_export "Valued" "v hasBasis_uniformity mem_nhds"
namespace AdicComplete
p2m_open "Valued"

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]

theorem pow_dvd_iff_v_le (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0) (x : 𝒪[K]) (n : ℕ) :
    ϖ ^ n ∣ x ↔ Valued.v (x : K) ≤ Valued.v (ϖ : K) ^ n := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subring.coe_mul, Subring.coe_pow, Valuation.map_mul, Valuation.map_pow]
    exact mul_le_of_le_one_right' z.2
  · intro h
    have hϖn : (ϖ : K) ^ n ≠ 0 := pow_ne_zero n hϖ0
    refine ⟨⟨(x : K) / (ϖ : K) ^ n, ?_⟩, ?_⟩
    · change Valued.v ((x : K) / (ϖ : K) ^ n) ≤ 1
      rw [map_div₀, Valuation.map_pow]
      exact (div_le_one₀ (pow_pos ((Valuation.pos_iff _).mpr hϖ0) n)).mpr h
    · apply Subtype.ext
      simp only [Subring.coe_mul, Subring.coe_pow]
      rw [mul_div_cancel₀ _ hϖn]

theorem mem_span_pow_iff_v_le (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0) (x : 𝒪[K]) (n : ℕ) :
    x ∈ (Ideal.span {ϖ} ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K]) ↔ Valued.v (x : K) ≤ Valued.v (ϖ : K) ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_dvd_iff_v_le ϖ hϖ0]

end Valued.AdicComplete

open _root_.Valued _root_.P2MW.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt.Valued Filter Topology Valued.AdicComplete in

theorem solution
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]
    [CompleteSpace K] (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0)
    (harch : ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, Valued.v (ϖ : K) ^ n < γ) :
    IsAdicComplete (Ideal.span {ϖ}) 𝒪[K] where
  haus' := by
    intro x hx
    have hle : ∀ n, Valued.v (x : K) ≤ Valued.v (ϖ : K) ^ n := fun n =>
      (mem_span_pow_iff_v_le ϖ hϖ0 x n).mp (SModEq.zero.mp (hx n))
    by_contra hx0
    have hv0 : Valued.v (x : K) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact fun h => hx0 (Subtype.ext h)
    obtain ⟨n, hn⟩ := harch _ hv0
    exact (lt_irrefl _) ((hle n).trans_lt hn)
  prec' := by
    intro f hf
    have hvϖ0 : ∀ k : ℕ, Valued.v ((ϖ : K) ^ k) ≠ 0 := fun k => by
      rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hϖ0

    have hfK : ∀ {m n : ℕ}, m ≤ n → Valued.v ((f n : K) - f m) ≤ Valued.v (ϖ : K) ^ m := by
      intro m n hmn
      have h := (SModEq.sub_mem.mp (hf hmn).symm)
      rw [mem_span_pow_iff_v_le ϖ hϖ0] at h
      simpa only [AddSubgroupClass.coe_sub] using h
    have hϖ1 : Valued.v (ϖ : K) ≤ 1 := ϖ.2
    have hmono : ∀ {m n : ℕ}, m ≤ n → Valued.v (ϖ : K) ^ n ≤ Valued.v (ϖ : K) ^ m := fun h =>
      pow_le_pow_right_of_le_one' hϖ1 h
    have hfK' : ∀ m n k : ℕ, k ≤ m → k ≤ n → Valued.v ((f n : K) - f m) ≤ Valued.v (ϖ : K) ^ k := by
      intro m n k hkm hkn
      rcases le_total m n with hmn | hnm
      · exact (hfK hmn).trans (hmono hkm)
      · rw [Valuation.map_sub_swap]; exact (hfK hnm).trans (hmono hkn)
    have hcau : CauchySeq (fun n => (f n : K)) := by
      rw [(Valued.hasBasis_uniformity K Γ₀).cauchySeq_iff]
      intro γ _
      have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).mpr γ.ne_zero
      obtain ⟨k, hk⟩ := harch _ hγ0
      refine ⟨k, fun m hm n hn => ?_⟩
      simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
      exact (hfK' m n k hm hn).trans_lt hk
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau

    have hLn : ∀ n, Valued.v (L - f n) ≤ Valued.v (ϖ : K) ^ n := by
      intro n
      have hs : {y : K | Valued.v.restrict (y - L) < Units.mk0 (Valued.v.restrict ((ϖ : K) ^ n))
          (mt (Valuation.restrict_eq_zero_iff _).mp (hvϖ0 n))} ∈ 𝓝 L := Valued.mem_nhds.mpr ⟨_, subset_rfl⟩
      have hev := hL hs
      rw [mem_map, mem_atTop_sets] at hev
      obtain ⟨N, hN⟩ := hev
      have hk := hN (max N n) (le_max_left _ _)
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Units.val_mk0] at hk
      rw [Valuation.restrict_lt_iff, Valuation.map_pow] at hk
      have e : L - f n = -(((f (max N n) : K) - L)) + ((f (max N n) : K) - f n) := by ring
      rw [e]
      refine (Valued.v.map_add _ _).trans (max_le ?_ (hfK' n (max N n) n le_rfl (le_max_right _ _)))
      rw [Valuation.map_neg]; exact hk.le
    have hLint : Valued.v L ≤ 1 := by
      have e : L = (L - f 0) + f 0 := by ring
      rw [e]
      refine (Valued.v.map_add _ _).trans (max_le ((hLn 0).trans (by rw [pow_zero])) (f 0).2)
    refine ⟨⟨L, hLint⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_pow_iff_v_le ϖ hϖ0, AddSubgroupClass.coe_sub, Valuation.map_sub_swap]
    exact hLn n

end S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
end P2MW
export P2MW.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt (solution)
