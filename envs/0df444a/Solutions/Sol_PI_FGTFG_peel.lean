-- Prove2me | solution 1 for PI.FGTFG.peel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:30.931248+00:00
-- url     : https://prove2.me/submissions/6c0b1105-33b5-40fd-85e8-452be4b82014

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module
namespace PI.FGTFG
theorem _root_.solution {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M] (φ : M →ₗ[R] R) (b : R) (hb : b ≠ 0)
    (hφ : LinearMap.range φ = Ideal.span {b}) :
    finrank R (LinearMap.ker φ) + 1 = finrank R M ∧
    ∃ e : M, LinearMap.ker φ ⊔ Submodule.span R {e} = ⊤ := by
  constructor
  · have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    have h2 : finrank R (M ⧸ LinearMap.ker φ) = 1 := by
      rw [(φ.quotKerEquivRange).finrank_eq, hφ]
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R b hb).finrank_eq]
      exact Module.finrank_self R
    omega
  · have hbm : b ∈ LinearMap.range φ := hφ ▸ Ideal.mem_span_singleton_self b
    obtain ⟨e, he⟩ := hbm
    refine ⟨e, eq_top_iff.mpr fun m _ => ?_⟩
    have hm' : φ m ∈ LinearMap.range φ := LinearMap.mem_range_self φ m
    rw [hφ, Ideal.mem_span_singleton'] at hm'
    obtain ⟨t, ht⟩ := hm'
    have hm : m = (m - t • e) + t • e := by abel
    rw [hm]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    rw [LinearMap.mem_ker, map_sub, map_smul, he, smul_eq_mul, ht, sub_self]
end PI.FGTFG
