-- Prove2me | solution 1 for Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4b327e72-156f-58b9-a505-ae18502a5fd9

import Mathlib
import Theorems.Thm_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le

set_option autoImplicit false

open Polynomial

theorem solution {K : Type*} [Field K]
    [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X])
    {z : K} (hz : v z ≤ 1) (hlt : v (p.eval z) < p.gaussNorm v 1) :
    ∃ a ∈ p.roots, v a ≤ 1 ∧ p.gaussNorm v 1 * v (z - a) ^ p.natDegree ≤ v (p.eval z) := by
  classical

  have hG : 0 < p.gaussNorm v 1 := lt_of_le_of_lt (v.nonneg _) hlt
  have hp : p ≠ 0 := by
    rintro rfl
    simp [Polynomial.gaussNorm] at hG
  by_cases hpz : p.eval z = 0
  ·
    refine ⟨z, (Polynomial.mem_roots hp).2 hpz, hz, ?_⟩
    have hdeg : p.natDegree ≠ 0 := by
      intro h0
      obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero h0⟩
      simp only [eval_C] at hpz
      exact hp (by simp [hpz])
    simp [hpz, zero_pow hdeg]
  ·
    have hJ := Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum v hv p hp hz hpz
    set S : Multiset K := p.roots.filter fun a => v a ≤ 1 with hS
    have hvz : 0 < v (p.eval z) := v.pos hpz

    have hSne : S ≠ 0 := by
      intro h0
      rw [h0, Multiset.map_zero, Multiset.sum_zero, add_zero] at hJ
      have : v (p.eval z) = p.gaussNorm v 1 := by
        rw [← Real.exp_log hvz, hJ, Real.exp_log hG]
      exact hlt.ne this

    have hSne' : S.toFinset.Nonempty := by
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hSne
      exact ⟨a, Multiset.mem_toFinset.2 ha⟩
    obtain ⟨a, haS, hmin⟩ := S.toFinset.exists_min_image (fun b => v (z - b)) hSne'
    rw [Multiset.mem_toFinset] at haS
    have ha_root : a ∈ p.roots := (Multiset.mem_filter.1 haS).1
    have ha1 : v a ≤ 1 := (Multiset.mem_filter.1 haS).2
    refine ⟨a, ha_root, ha1, ?_⟩

    have hza : z - a ≠ 0 := by
      intro h
      have : z = a := sub_eq_zero.1 h
      apply hpz
      rw [this]
      exact (Polynomial.mem_roots hp).1 ha_root
    have hm0 : 0 < v (z - a) := v.pos hza
    have hm1 : v (z - a) ≤ 1 := by
      calc v (z - a) = v (z + -a) := by rw [sub_eq_add_neg]
        _ ≤ max (v z) (v (-a)) := hv z (-a)
        _ ≤ 1 := max_le hz (by rwa [v.map_neg])
    have hlogm : Real.log (v (z - a)) ≤ 0 := Real.log_nonpos hm0.le hm1

    have hsum : (S.card : ℝ) * Real.log (v (z - a))
        ≤ (S.map fun b => Real.log (v (z - b))).sum := by
      have : (S.map fun _ => Real.log (v (z - a))).sum
          ≤ (S.map fun b => Real.log (v (z - b))).sum := by
        apply Multiset.sum_map_le_sum_map
        intro b hb
        have hb' : b ∈ S.toFinset := Multiset.mem_toFinset.2 hb
        have hzb : 0 < v (z - b) := by
          apply v.pos
          intro h
          have : z = b := sub_eq_zero.1 h
          apply hpz
          rw [this]
          exact (Polynomial.mem_roots hp).1 (Multiset.mem_filter.1 hb).1
        exact Real.log_le_log hm0 (hmin b hb')
      simpa [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul] using this

    have hcard : S.card ≤ p.natDegree :=
      (Multiset.card_le_card (Multiset.filter_le _ _)).trans (Polynomial.card_roots' p)
    have hdeg : (p.natDegree : ℝ) * Real.log (v (z - a)) ≤ (S.card : ℝ) * Real.log (v (z - a)) :=
      mul_le_mul_of_nonpos_right (by exact_mod_cast hcard) hlogm

    have hpow : 0 < v (z - a) ^ p.natDegree := pow_pos hm0 _
    have hlog : Real.log (p.gaussNorm v 1 * v (z - a) ^ p.natDegree)
        ≤ Real.log (v (p.eval z)) := by
      rw [Real.log_mul hG.ne' hpow.ne', Real.log_pow, hJ]
      linarith
    exact (Real.log_le_log_iff (mul_pos hG hpow) hvz).1 hlog

end S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le
end P2MW
export P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le (solution)
