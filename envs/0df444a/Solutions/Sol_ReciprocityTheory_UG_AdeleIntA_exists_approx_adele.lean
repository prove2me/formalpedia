-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.exists_approx_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:48.750099+00:00
-- url     : https://prove2.me/submissions/245a44ef-f0e2-4b37-ad76-31bb94e57a7e

import Mathlib
import Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_R
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_le_one_of_mem
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain WithZero
open ReciprocityTheory ReciprocityTheory.UG ReciprocityTheory.UG.AdeleIntA
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace ReciprocityTheory.UG.AdeleIntA
theorem _root_.solution (α : FiniteAdeleRing R K) : ∃ u : K, IsInt (α - algebraMap K (FiniteAdeleRing R K) u) := by
  classical
  have hT : {v : HeightOneSpectrum R | α v ∉ v.adicCompletionIntegers K}.Finite := by
    have := α.2
    rw [Filter.eventually_cofinite] at this
    exact this
  set T := hT.toFinset
  have hden : ∀ v : HeightOneSpectrum R, ∃ d : R, d ≠ 0 ∧ Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v) ≤ 1 := by
    intro v
    by_cases h0 : α v = 0
    · exact ⟨1, one_ne_zero, by simp [h0]⟩
    have hα0 : Valued.v (α v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨n, hn⟩ : ∃ n : ℕ, exp (-(n : ℤ)) * Valued.v (α v) ≤ 1 := by
      obtain ⟨z, hz⟩ : ∃ z : ℤ, Valued.v (α v) = exp z := ⟨log (Valued.v (α v)), (exp_log hα0).symm⟩
      refine ⟨z.toNat, ?_⟩
      rw [hz, ← exp_add, ← exp_zero, exp_le_exp]
      omega
    obtain ⟨d, hd, hd0⟩ : ∃ d ∈ v.asIdeal ^ n, d ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero n v.ne_bot)
    refine ⟨d, hd0, ?_⟩
    rw [Valuation.map_mul, val_R]
    exact (mul_le_mul' ((HeightOneSpectrum.intValuation_le_pow_iff_mem v d n).2 hd) le_rfl).trans hn
  choose dv hdv0 hdv using hden
  set d : R := ∏ v ∈ T, dv v
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hdv0 v
  have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd0
  set y : FiniteAdeleRing R K := algebraMap K (FiniteAdeleRing R K) (algebraMap R K d) * α
  have hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v) ≤ 1
    by_cases hv : v ∈ T
    · have e : d = dv v * ∏ w ∈ T.erase v, dv w := (Finset.mul_prod_erase T dv hv).symm
      have h1 := hdv v
      rw [Valuation.map_mul] at h1
      rw [e]
      simp only [map_mul]
      have h2 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (∏ w ∈ T.erase v, dv w))) ≤ 1 := by
        rw [val_R]; exact v.intValuation_le_one _
      have h3 := mul_le_mul' h2 h1
      rw [one_mul] at h3
      refine le_trans (le_of_eq ?_) h3
      rw [mul_comm (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (dv v)))), mul_assoc]
    · have hαv : α v ∈ v.adicCompletionIntegers K := by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).2 h)
      rw [Valuation.map_mul, val_R]
      exact mul_le_one' (v.intValuation_le_one d) (val_le_one_of_mem hαv)
  obtain ⟨a, ha⟩ := exists_approx y hy d hd0
  refine ⟨algebraMap R K a / algebraMap R K d, fun v => ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hdv' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)) ≠ 0 := by
    rw [val_R]; exact v.intValuation_ne_zero d hd0
  have e : (α - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K d)) v =
      (algebraMap K (v.adicCompletion K) (algebraMap R K d))⁻¹ *
        (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    have hne : algebraMap K (v.adicCompletion K) (algebraMap R K d) ≠ 0 := (map_ne_zero _).2 hdK
    show α v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K d) = _
    show _ = _ * (algebraMap K (v.adicCompletion K) (algebraMap R K d) * α v - _)
    rw [map_div₀]
    field_simp
  rw [e, Valuation.map_mul, map_inv₀]
  have := ha v
  rw [← val_R (K := K)] at this
  calc (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)))⁻¹ *
        Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a))
      ≤ (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)))⁻¹ *
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := mul_le_mul' le_rfl this
    _ = 1 := inv_mul_cancel₀ hdv'
end ReciprocityTheory.UG.AdeleIntA
