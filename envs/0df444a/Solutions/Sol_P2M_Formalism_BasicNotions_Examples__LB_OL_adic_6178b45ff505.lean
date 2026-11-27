-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_OL_adic_6178b45ff505
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:42.165513+00:00
-- url     : https://prove2.me/submissions/238a3bea-9a99-47f0-bc6c-fd99b675106a

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution : IsAdic (maximalIdeal ↥(OL LL)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have h1 : nrm LL ϖ < 1 := (mem_max LL ϖ).mp hϖ.not_isUnit
  have h0 : 0 < nrm LL ϖ := lt_of_le_of_ne (norm_nonneg _) fun e => hϖ.ne_zero ((nrm_eq_zero LL ϖ).mp e.symm)
  have key : ∀ n : ℕ, ((maximalIdeal ↥(OL LL) ^ n : Ideal ↥(OL LL)) : Set ↥(OL LL)) =
      toOm LL ⁻¹' Metric.closedBall 0 (nrm LL ϖ ^ n) := fun n => by
    ext a
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff,
      nrm_pow, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rfl
  refine isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [key]
    exact (IsUltrametricDist.isOpen_closedBall _ (pow_pos h0 n).ne').preimage (inducing_toOm LL).continuous
  · rw [(inducing_toOm LL).nhds_eq_comap, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [map_zero] at ht
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by
      rw [key]
      exact (Set.preimage_mono ((Metric.closedBall_subset_ball hn).trans h)).trans hts⟩
end Formalism.BasicNotions.Examples₂.LB
