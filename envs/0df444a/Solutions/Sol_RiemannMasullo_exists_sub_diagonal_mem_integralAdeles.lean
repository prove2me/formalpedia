-- Prove2me | solution 1 for RiemannMasullo.exists_sub_diagonal_mem_integralAdeles
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:37:58.755861+00:00
-- url     : https://prove2.me/submissions/669983d7-b9b0-41b1-88f8-b26cdd1b9ea3

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L343-L407
import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

local notation "Integral(" F ")" => integralAdelesOutside F ∅

private theorem mem_integralAdeles_iff (a : 𝔸[F]) :
    a ∈ Integral(F) ↔ ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F := by
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true, true_implies]
  rfl
theorem solution (a : 𝔸[F]) :
    ∃ x : F, a - algebraMap F 𝔸[F] x ∈ Integral(F) := by
  classical
  have hfinite : {v : Primes(F) | 1 < Valued.v (a.2 v)}.Finite := by
    have h := a.2.property
    simp only [Filter.eventually_cofinite, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h
    exact h
  let bad := hfinite.toFinset
  have hlocal (v : Primes(F)) : ∃ x : F,
      Valued.v (a.2 v - (x : v.adicCompletion F)) ≤ 1 := by
    let U := (fun y : v.adicCompletion F ↦ a.2 v - y) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hU : IsOpen U :=
      (Valued.isOpen_integer _).preimage (continuous_const.sub continuous_id)
    have ha : a.2 v ∈ U := by
      change Valued.v (a.2 v - a.2 v) ≤ 1
      simp
    exact (v.denseRange_algebraMap F).mem_nhds (hU.mem_nhds ha)
  choose y hy using hlocal
  let x : Primes(F) → F := fun v ↦ if v ∈ bad then y v else 0
  have hx (v : Primes(F)) : Valued.v (a.2 v - (x v : v.adicCompletion F)) ≤ 1 := by
    by_cases hv : v ∈ bad
    · simpa only [x, if_pos hv] using hy v
    · have hnv : ¬ 1 < Valued.v (a.2 v) := by simpa [bad] using hv
      simpa only [x, if_neg hv, HeightOneSpectrum.adicCompletion.coe_zero, sub_zero] using
        le_of_not_gt hnv
  -- Clear the denominators of the local representatives at the finitely many bad places.
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) bad x
  have hd₀ : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hnum (v : Primes(F)) : ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x v := by
    by_cases hv : v ∈ bad
    · simpa only [IsLocalization.IsInteger, RingHom.mem_rangeS, Algebra.smul_def] using hd v hv
    · exact ⟨0, by simp [x, hv]⟩
  choose r hr using hnum
  let I : Ideal (𝓞 F) := Ideal.span {(d : 𝓞 F)}
  have hI : I ≠ ⊥ := by simp [I, hd₀]
  have hS : {v : Primes(F) | v.asIdeal ∣ I}.Finite := Ideal.finite_factors hI
  let S := hS.toFinset
  let m := fun v : Primes(F) ↦ multiplicity v.asIdeal I
  -- Match the resulting numerators modulo the prime powers dividing the common denominator.
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    HeightOneSpectrum.asIdeal m (fun v _ ↦ v.prime)
    (fun _ _ _ _ h ↦ fun he ↦ h (HeightOneSpectrum.ext he)) (fun v ↦ r v)
  have hb' (v : Primes(F)) : v.intValuation (b - r v) ≤ v.intValuation d := by
    by_cases hv : v ∈ S
    · rw [v.intValuation_eq_exp_neg_multiplicity hd₀, v.intValuation_le_pow_iff_mem]
      exact hb v hv
    · have hn : ¬ v.asIdeal ∣ I := by simpa [S] using hv
      have hd' : v.intValuation (d : 𝓞 F) = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr (mt Ideal.dvd_span_singleton.mpr hn)
      rw [hd']
      exact v.intValuation_le_one _
  let D := algebraMap (𝓞 F) F d
  let z := algebraMap (𝓞 F) F b / D
  refine ⟨z, (mem_integralAdeles_iff F _).mpr fun v ↦ ?_⟩
  have hD : D ≠ 0 := (RingOfIntegers.coe_ne_zero_iff (K := F)).mpr hd₀
  have hz : v.valuation F (x v - z) ≤ 1 := by
    rw [(v.valuation F).map_sub_swap, div_sub', ← hr v, ← map_sub, Valuation.map_div,
      v.valuation_of_algebraMap, v.valuation_of_algebraMap]
    · exact div_le_one_of_le₀ (hb' v) zero_le
    · exact hD
  change Valued.v (a.2 v - (z : v.adicCompletion F)) ≤ 1
  rw [← sub_add_sub_cancel (a.2 v) (x v : v.adicCompletion F) (z : v.adicCompletion F)]
  apply (Valued.v : Valuation (v.adicCompletion F) _).map_add_le (hx v)
  change Valued.v (algebraMap F (v.adicCompletion F) (x v) -
    algebraMap F (v.adicCompletion F) z) ≤ 1
  rw [← map_sub]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _).trans_le hz
