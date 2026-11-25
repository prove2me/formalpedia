-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.wa_exists_int_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:25.054424+00:00
-- url     : https://prove2.me/submissions/02d1adcf-c4b7-41e7-994e-f4c2cbb5558b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → F) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - b v) ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image b)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdF : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hint : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F (d : 𝓞 F) * b v := by
    intro v hv
    obtain ⟨n, hn⟩ := hd (b v) (Finset.mem_image_of_mem b hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hint
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation (d : 𝓞 F) ≠ 0 := by
    intro v
    first
      | exact v.intValuation_ne_zero _ hd0
      | exact (v.intValuation).ne_zero_iff.mpr hd0
      | (intro h0
         have h1 := v.valuation_of_algebraMap (K := F) (d : 𝓞 F)
         rw [h0] at h1
         exact hdF ((Valuation.zero_iff _).mp h1))
  have hexp : ∀ v : HeightOneSpectrum (𝓞 F), ∃ e : ℕ,
      WithZero.exp (-(e : ℤ)) ≤ v.intValuation (d : 𝓞 F) := by
    intro v
    obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (d : 𝓞 F) = WithZero.exp k := by
      first
        | exact ⟨_, (WithZero.exp_log (hne v)).symm⟩
        | (obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp (hne v)
           exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩)
    refine ⟨k.natAbs, ?_⟩
    rw [hk, WithZero.exp_le_exp]
    first
      | omega
      | (rw [Int.natCast_natAbs]; exact neg_abs_le k)
  choose e he using hexp
  obtain ⟨m, hm⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => n v.1)
  refine ⟨algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F), fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ (e v)).mpr (hm v hv)
  have hkey : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F) - b v =
      algebraMap (𝓞 F) F (m - n v) / algebraMap (𝓞 F) F (d : 𝓞 F) := by
    rw [eq_div_iff hdF, sub_mul, div_mul_cancel₀ _ hdF, map_sub, hn v hv]
    ring
  rw [hkey, map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have hlt : (0 : WithZero (Multiplicative ℤ)) < v.intValuation (d : 𝓞 F) := zero_lt_iff.mpr (hne v)
  first
    | exact (div_le_one₀ hlt).mpr (h1.trans (he v))
    | exact div_le_one_of_le₀ (h1.trans (he v)) hlt.le
end PI.UnitaryApproxFinWork
