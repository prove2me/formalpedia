-- Prove2me | solution 1 for PI.SqPairLocal.mem_hcompl_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:55.338389+00:00
-- url     : https://prove2.me/submissions/ccc1ac1e-fea9-4bb3-9209-430cb79128a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) (s : 𝓞 E) :
    s ∈ hcompl (K := E) Q ↔ s ∉ Q := by
  haveI := hQ
  constructor
  · intro h
    have hle : hcompl (K := E) Q ≤ Q.primeCompl := Submonoid.closure_le.mpr fun s hs => hs.1
    exact hle h
  · intro hs
    apply Submonoid.subset_closure
    refine ⟨hs, fun t ht => ?_⟩
    have htc : t = cj E s := by
      apply RingOfIntegers.ext
      exact ht
    subst htc
    intro hcs
    apply hs
    have h2 : s ∈ Q.comap (cj E) := Ideal.mem_comap.mpr hcs
    rwa [hc] at h2
end PI.SqPairLocal
