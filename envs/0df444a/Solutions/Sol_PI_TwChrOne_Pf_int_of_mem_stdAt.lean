-- Prove2me | solution 1 for PI.TwChrOne.Pf.int_of_mem_stdAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:42.648423+00:00
-- url     : https://prove2.me/submissions/eb8fe952-66df-4978-8cc9-daa37926e531

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
theorem _root_.solution {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hsx) i (Set.mem_univ _))
  exact ⟨y, s, hs, by rw [hy, Pi.smul_apply, Algebra.smul_def]⟩
end PI.TwChrOne.Pf
