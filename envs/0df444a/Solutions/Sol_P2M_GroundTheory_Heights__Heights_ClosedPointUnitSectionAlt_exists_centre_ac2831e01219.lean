-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:50.095888+00:00
-- url     : https://prove2.me/submissions/283d2674-d6c4-4fc3-86d9-9c75a4a74007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (W : ValuationSubring K') {q : ℕ} (hq : q.Prime) (hWq : W.valuation (q : K') < 1) :
    ∃ P : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ P.asIdeal ∧
      ∀ x : K', P.valuation K' x ≤ 1 → x ∈ W := by
  have hO : ∀ a : 𝓞 K', (a : K') ∈ W := fun a => mem_of_isIntegral W (RingOfIntegers.isIntegral_coe a)
  let φ : 𝓞 K' →+* W :=
    { toFun := fun a => ⟨a, hO a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hmem : ∀ a : 𝓞 K', a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal W) ↔ W.valuation (a : K') < 1 :=
    fun a => by rw [Ideal.mem_comap]; exact W.valuation_lt_one_iff (φ a)
  have hqmem : (q : 𝓞 K') ∈ Ideal.comap φ (IsLocalRing.maximalIdeal W) := (hmem _).mpr (by simpa using hWq)
  have hne : Ideal.comap φ (IsLocalRing.maximalIdeal W) ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hqmem
    exact hq.ne_zero (by exact_mod_cast hqmem)
  refine ⟨⟨Ideal.comap φ (IsLocalRing.maximalIdeal W), inferInstance, hne⟩, hqmem, fun x hx => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ x hx
  have hd : W.valuation (algebraMap (𝓞 K') K' d) = 1 :=
    le_antisymm ((W.valuation_le_one_iff _).mpr (hO d)) (not_lt.mp fun h => d.2 ((hmem d).mpr h))
  rw [← W.valuation_le_one_iff]
  have : W.valuation (algebraMap (𝓞 K') K' n) ≤ 1 := (W.valuation_le_one_iff _).mpr (hO n)
  rwa [← hnd, map_mul, hd, mul_one] at this
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
