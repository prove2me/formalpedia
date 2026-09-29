-- Prove2me | solution 1 for Submodule.exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6a1d3ad6-68dd-5466-a682-8b6965ec4634

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced

set_option autoImplicit false

namespace Submodule
p2m_export "Submodule" "factor span_singleton_le_iff_mem smul_mem span mem_span_singleton generators one orthogonal module"
namespace IsoCycAux
p2m_open "Submodule"

theorem minor_smul_mem {T : Type*} [CommRing T] {V : Type*} [AddCommGroup V] [Module T V]
    (e : V ≃ₗ[T] (Fin 2 → T)) (N : Submodule T V) {n n' : V} (hn : n ∈ N) (hn' : n' ∈ N) (v : V) :
    (e n 0 * e n' 1 - e n 1 * e n' 0) • v ∈ N := by
  have key : (e n 0 * e n' 1 - e n 1 * e n' 0) • v =
      (e v 0 * e n' 1 - e v 1 * e n' 0) • n + (e v 1 * e n 0 - e v 0 * e n 1) • n' := by
    apply e.injective
    rw [map_smul, map_add, map_smul, map_smul]
    funext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    fin_cases k <;> simp <;> ring
  rw [key]
  exact N.add_mem (N.smul_mem _ hn) (N.smul_mem _ hn')

end Submodule.IsoCycAux

theorem solution
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [FiniteDimensional K T] [IsReduced T]
    {V : Type*} [AddCommGroup V] [Module K V] [Module T V] [IsScalarTower K T V]
    (e : V ≃ₗ[T] (Fin 2 → T))
    (B : V →ₗ[K] V →ₗ[K] K)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBt : ∀ (t : T) (x y : V), B (t • x) y = B x (t • y))
    (N : Submodule T V) (hN : ∀ x ∈ N, ∀ y ∈ N, B x y = 0) :
    ∃ g : V, N = Submodule.span T {g} := by
  classical
  haveI : IsArtinianRing T := IsArtinianRing.of_finite K T

  have hmin : ∀ n ∈ N, ∀ n' ∈ N, e n 0 * e n' 1 - e n 1 * e n' 0 = 0 := by
    intro n hn n' hn'
    set δ := e n 0 * e n' 1 - e n 1 * e n' 0 with hδ
    have h1 : ∀ v : V, δ • v ∈ N := fun v => Submodule.IsoCycAux.minor_smul_mem e N hn hn' v
    have h2 : ∀ v : V, (δ * δ) • v = 0 := by
      intro v
      apply hBl
      intro w
      rw [mul_smul, hBt]
      exact hN _ (h1 v) _ (h1 w)
    have h3 : δ * δ = 0 := by
      have := congrArg (fun f => e f 0) (h2 (e.symm fun _ => 1))
      simpa using this
    exact IsNilpotent.eq_zero ⟨2, by rw [pow_two, h3]⟩

  let ι := MaximalSpectrum T
  haveI : Fintype ι := Fintype.ofFinite ι
  let φ := IsArtinianRing.equivPi T
  let ε : ι → T := fun i => φ.symm (Pi.single i 1)
  have hφε : ∀ i, φ (ε i) = Pi.single i 1 := fun i => φ.apply_symm_apply _
  have hε_sum : ∑ i, ε i = 1 := by
    apply φ.injective
    rw [map_sum, map_one]
    simp_rw [hφε]
    exact Finset.univ_sum_single (1 : ∀ i : ι, T ⧸ i.asIdeal)
  have hε_mul : ∀ i j, ε i * ε j = if i = j then ε i else 0 := by
    intro i j
    apply φ.injective
    rw [map_mul, hφε, hφε]
    split_ifs with h
    · subst h
      rw [hφε, ← Pi.single_mul, one_mul]
    · rw [map_zero]
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_of_ne h, mul_zero]
      · rw [Pi.single_eq_of_ne hk, zero_mul]
  have hε_zero : ∀ (i : ι) (t : T), φ t i = 0 → ε i * t = 0 := by
    intro i t ht
    apply φ.injective
    rw [map_mul, hφε, map_zero]
    funext k
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk
      rw [ht, mul_zero]
    · rw [Pi.single_eq_of_ne hk, zero_mul]
  have hε_unit : ∀ (i : ι) (t : T), φ t i ≠ 0 → ∃ u : T, ε i * t * u = ε i := by
    intro i t ht
    haveI : i.asIdeal.IsMaximal := i.isMaximal
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ht
    refine ⟨φ.symm (Pi.single i b), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, hφε, φ.apply_symm_apply]
    funext k
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul, hb]
    · rw [Pi.single_eq_of_ne hk, zero_mul, zero_mul]

  have hgen : ∀ i : ι, ∃ gi : V, gi ∈ N ∧ ε i • gi = gi ∧ ∀ n ∈ N, ∃ t : T, ε i • n = t • gi := by
    intro i
    by_cases h : ∃ n ∈ N, ε i • n ≠ 0
    · obtain ⟨n, hn, hne⟩ := h
      refine ⟨ε i • n, N.smul_mem _ hn, by rw [← mul_smul, hε_mul, if_pos rfl], fun n' hn' => ?_⟩
      have hcoord : ε i * e n 0 ≠ 0 ∨ ε i * e n 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hne
        apply e.injective
        rw [map_smul, map_zero]
        funext k
        fin_cases k
        · simpa using hc.1
        · simpa using hc.2
      have hm := hmin n hn n' hn'
      rcases hcoord with ha | hb
      · obtain ⟨u, hu⟩ := hε_unit i (e n 0) (fun h0 => ha (hε_zero i _ h0))
        refine ⟨e n' 0 * u, ?_⟩
        apply e.injective
        rw [map_smul, map_smul, map_smul]
        funext k
        simp only [Pi.smul_apply, smul_eq_mul]
        fin_cases k
        · simp
          linear_combination (-(e n' 0)) * hu
        · simp
          linear_combination (u * ε i) * hm - (e n' 1) * hu
      · obtain ⟨u, hu⟩ := hε_unit i (e n 1) (fun h0 => hb (hε_zero i _ h0))
        refine ⟨e n' 1 * u, ?_⟩
        apply e.injective
        rw [map_smul, map_smul, map_smul]
        funext k
        simp only [Pi.smul_apply, smul_eq_mul]
        fin_cases k
        · simp
          linear_combination (-(u * ε i)) * hm - (e n' 0) * hu
        · simp
          linear_combination (-(e n' 1)) * hu
    · push Not at h
      exact ⟨0, N.zero_mem, smul_zero _, fun n hn => ⟨0, by rw [h n hn, zero_smul]⟩⟩
  choose g hgN hgε hgspan using hgen
  have hεg : ∀ i j, ε i • g j = if i = j then g j else 0 := by
    intro i j
    calc ε i • g j = ε i • (ε j • g j) := by rw [hgε]
      _ = (ε i * ε j) • g j := by rw [mul_smul]
      _ = if i = j then g j else 0 := by
          rw [hε_mul]
          split_ifs with h
          · subst h; exact hgε i
          · exact zero_smul _ _

  refine ⟨∑ i, g i, le_antisymm ?_ ?_⟩
  · intro n hn
    rw [Submodule.mem_span_singleton]
    choose t ht using fun i => hgspan i n hn
    refine ⟨∑ i, t i * ε i, ?_⟩
    calc (∑ i, t i * ε i) • ∑ j, g j = ∑ i, (t i * ε i) • ∑ j, g j := Finset.sum_smul
      _ = ∑ i, t i • g i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_smul, Finset.smul_sum]
          simp_rw [hεg i]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      _ = ∑ i, ε i • n := by simp_rw [ht]
      _ = (∑ i, ε i) • n := Finset.sum_smul.symm
      _ = n := by rw [hε_sum, one_smul]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact N.sum_mem fun i _ => hgN i

end S_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced
end P2MW
export P2MW.S_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced (solution)
