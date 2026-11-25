-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyclotomic_irreducible_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:14.140204+00:00
-- url     : https://prove2.me/submissions/e25423bd-0f16-4d54-8bb5-b9cfd3fdaae0

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Theorems.Thm_ReciprocityTheory_Cheb_natCast_notMem_sq_of_isUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField
namespace ReciprocityTheory.Cheb
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime] (hlP : (l : 𝓞 K) ∈ P)
    [Algebra.IsUnramifiedAt ℤ P] : Irreducible (cyclotomic l K) := by
  haveI := Fact.mk hl
  have hl2 := natCast_notMem_sq_of_isUnramifiedAt hl P

  have hE := cyclotomic_comp_X_add_one_isEisensteinAt l
  have hX1 : (X + 1 : ℤ[X]).Monic := by simpa using monic_X_add_C (1 : ℤ)
  have hX1d : (X + 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℤ)
  have hmon : ((cyclotomic l ℤ).comp (X + 1)).Monic :=
    (cyclotomic.monic l ℤ).comp hX1 (by rw [hX1d]; exact one_ne_zero)
  have hg : ((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    simp [Polynomial.map_comp, map_cyclotomic]
  have hdeg : (((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K))).natDegree =
      ((cyclotomic l ℤ).comp (X + 1)).natDegree := hmon.natDegree_map _
  have hc0 : ((cyclotomic l ℤ).comp (X + 1)).coeff 0 = l := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp [eval_one_cyclotomic_prime]
  have hE' : ((cyclotomic l (𝓞 K)).comp (X + 1)).IsEisensteinAt P := by
    rw [← hg]
    refine ⟨?_, ?_, ?_⟩
    · rw [(hmon.map _).leadingCoeff]
      exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_map]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
      rw [← hc, smul_eq_mul, map_mul, map_natCast]
      exact P.mul_mem_left _ hlP
    · rw [coeff_map, hc0, map_natCast]
      exact hl2
  have hpos : 0 < ((cyclotomic l (𝓞 K)).comp (X + 1)).natDegree := by
    rw [← hg, hdeg, natDegree_comp, natDegree_cyclotomic, hX1d, mul_one, Nat.totient_prime hl]
    exact Nat.sub_pos_of_lt hl.one_lt
  have hmon' : ((cyclotomic l (𝓞 K)).comp (X + 1)).Monic := by
    rw [← hg]
    exact hmon.map _
  have hirr1 := hE'.irreducible inferInstance hmon'.isPrimitive hpos
  have hcomp : (algEquivAevalXAddC (1 : 𝓞 K)) (cyclotomic l (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval, map_one]
  have hirr2 : Irreducible (cyclotomic l (𝓞 K)) := by
    rw [← hcomp] at hirr1
    exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : 𝓞 K)).toMulEquiv).mp hirr1
  have := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K)
    (cyclotomic.monic l (𝓞 K))).mp hirr2
  rwa [map_cyclotomic] at this
end ReciprocityTheory.Cheb
