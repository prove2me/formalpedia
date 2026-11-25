-- Prove2me | solution 1 for PI.CompDegEF.liesOver_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:03.102427+00:00
-- url     : https://prove2.me/submissions/5f1125bc-1dc5-4b51-8906-c59b2195b982

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_SpanLIsMaximal
import Theorems.Thm_PI_CompDegEF_span_l_isMaximal
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  constructor
  refine (span_l_isMaximal l).eq_of_le ?_ ?_
  · intro h
    rw [Ideal.comap_eq_top_iff] at h
    exact v.isPrime.ne_top h
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change algebraMap ℤ (𝓞 E) ((l : ℕ) : ℤ) ∈ v.asIdeal
    simpa using (show ((l : ℕ) : 𝓞 E) ∈ v.asIdeal from hv)
end PI.CompDegEF
