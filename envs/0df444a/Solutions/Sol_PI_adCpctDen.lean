-- Prove2me | solution 1 for PI.adCpctDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:48.367796+00:00
-- url     : https://prove2.me/submissions/57f0b85d-6b05-4fd0-b817-c5a286a18277

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Theorems.Thm_PI_AdCpctDenWork_mem_intAd
import Theorems.Thm_PI_AdCpctDenWork_isOpen_intAd
import Theorems.Thm_PI_AdCpctDenWork_natCast_mul_apply
import Theorems.Thm_PI_AdCpctDenWork_natCast_mem_int
import Theorems.Thm_PI_AdCpctDenWork_exists_nat_adele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum PI.AdCpctDenWork
namespace PI
theorem _root_.solution : PI.AdCpctDen := by
  intro F _ _ C hC
  classical
  choose m hm0 hm using fun a : FiniteAdeleRing (𝓞 F) F => exists_nat_adele a
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun a => (fun x => (m a : FiniteAdeleRing (𝓞 F) F) * x) ⁻¹' intAd F)
    (fun a => isOpen_intAd.preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈
      intAd F := hfa
  have hA : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∏ a ∈ t, m a : ℕ) : F) * f) =
      (k : FiniteAdeleRing (𝓞 F) F) *
        ((m a : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) f) := by
    rw [map_mul, map_natCast, hk, Nat.cast_mul]
    ring
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (((∏ a ∈ t, m a : ℕ) : F) * f) ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h2 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∏ a ∈ t, m a : ℕ) : F) * f)) v ∈
        v.adicCompletionIntegers F := by
      rw [hA, natCast_mul_apply]
      exact mul_mem (natCast_mem_int v k) ((mem_intAd _).mp hfa' v)
    rw [FiniteAdeleRing.algebraMap_apply] at h2
    exact h2
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r
end PI
