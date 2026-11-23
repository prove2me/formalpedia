-- Prove2me | solution 1 for PI.TwChrOne.Pf.mem_stdAt_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:42.878971+00:00
-- url     : https://prove2.me/submissions/9ce35758-4763-4fd5-8bc2-7cfd2e14e7cc

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
namespace PI.TwChrOne.Pf
theorem _root_.solution {x : Sp E n} (hx : ∀ i, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = x i) :
    x ∈ stdAt E n P := by
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  exact Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 (hx i)
end PI.TwChrOne.Pf
