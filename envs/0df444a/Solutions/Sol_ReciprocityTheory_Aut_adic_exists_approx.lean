-- Prove2me | solution 1 for ReciprocityTheory.Aut.adic_exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:00.889783+00:00
-- url     : https://prove2.me/submissions/ede8d8ef-48cb-4faf-838b-6fcc855c4263

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Theorems.Thm_ReciprocityTheory_Aut_adic_valued_algebraMap
import Theorems.Thm_ReciprocityTheory_Aut_adic_algebraMap_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace ReciprocityTheory.Aut
theorem _root_.solution (y : v.adicCompletion K) (hy : Valued.v y ≤ 1) :
    ∃ a : R, Valued.v (y - algebraMap R (v.adicCompletion K) a) < 1 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : K, Valued.v (y - algebraMap K (v.adicCompletion K) k) < 1 := by
    have hn : {w : v.adicCompletion K | Valued.v (w - y) < 1} ∈ nhds y :=
      Valued.mem_nhds.mpr ⟨1, fun w hw => by simpa using hw⟩
    obtain ⟨w, hw, k, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap K v y) _ hn
    refine ⟨k, ?_⟩
    rw [← Valuation.map_neg, neg_sub]
    exact hw
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← adic_valued_algebraMap]
    have e : algebraMap K (v.adicCompletion K) k = y - (y - algebraMap K _ k) := by ring
    rw [e]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hy hk.le)
  obtain ⟨c, hc⟩ : ∃ c : R, v.valuation K (k - algebraMap R K c) < 1 := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    haveI := v.isPrime
    have hex : ∃ N, b ∉ v.asIdeal ^ N := by
      by_contra hall
      push_neg at hall
      have hmem : b ∈ ⨅ i, v.asIdeal ^ i := Submodule.mem_iInf _ |>.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isDomain _ v.isPrime.ne_top, Ideal.mem_bot] at hmem
      exact hb0 (by rw [hmem, map_zero])
    have hspec := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, b ∈ v.asIdeal ^ m := fun m hm => by
      by_contra h'
      exact Nat.find_min hex hm h'
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero (by
      intro h0
      rw [h0, pow_zero] at hspec
      exact hspec (by simp))
    rw [hn] at hspec
    have hbn : b ∈ v.asIdeal ^ n := hmin n (by omega)
    have hvb : 0 < v.valuation K (algebraMap R K b) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb0)
    have hk1' := hk1
    rw [map_div₀, div_le_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap] at hk1'
    have ha : a ∈ v.asIdeal ^ n := by
      rw [← intValuation_le_pow_iff_mem]
      exact hk1'.trans ((intValuation_le_pow_iff_mem v b n).mpr hbn)
    have hI : Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal ^ n := by
      apply Ideal.eq_prime_pow_of_succ_lt_of_le v.ne_bot
      · refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        apply hspec
        rw [heq]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)
      · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hbn)
          (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [← hI] at ha
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy1
    refine ⟨r, ?_⟩
    have hkz : algebraMap R K a / algebraMap R K b - algebraMap R K r =
        algebraMap R K z / algebraMap R K b := by
      rw [← hyz, map_add, map_mul]
      field_simp
      ring
    rw [hkz, map_div₀, div_lt_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap]
    have h1 := (intValuation_le_pow_iff_mem v z (n + 1)).mpr hz
    have h2 : ¬ v.intValuation b ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
      hspec ((intValuation_le_pow_iff_mem v b (n + 1)).mp h)
    exact lt_of_le_of_lt h1 (not_le.mp h2)
  refine ⟨c, ?_⟩
  have e : y - algebraMap R (v.adicCompletion K) c =
      (y - algebraMap K _ k) + algebraMap K _ (k - algebraMap R K c) := by
    rw [adic_algebraMap_R, map_sub]
    ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hk ?_)
  rw [adic_valued_algebraMap]
  exact hc
end ReciprocityTheory.Aut
