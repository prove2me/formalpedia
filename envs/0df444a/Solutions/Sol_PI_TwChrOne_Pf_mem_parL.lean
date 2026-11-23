-- Prove2me | solution 1 for PI.TwChrOne.Pf.mem_parL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:42.942164+00:00
-- url     : https://prove2.me/submissions/aa3019f4-ffe3-40e9-90d2-1601e227cf45

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution {q : ℕ} {x : Sp E (N + c)} :
    x ∈ LocE.parL P q kj N c ↔
      (fun l : Fin (N + c) => ((q : E) ^ (if kj ≤ l.1 ∧ l.1 < N then (1 : ℤ) else 0))⁻¹ * x l) ∈
        stdAt E (N + c) P := Iff.rfl
end PI.TwChrOne.Pf
