-- Prove2me | solution 1 for PI.TwNormLat.W.mem_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:06.034893+00:00
-- url     : https://prove2.me/submissions/207f6366-ba14-4f38-82db-6c8b7ccc8989

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_PI_TwNormLat_W_mem_stdAt

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
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution (N c : ℕ) (v : Sp E (N + c)) :
    v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ ∀ l, IntAt P (v l) := by
  show v ∈ Submodule.comap _ (stdAt E (N + c) P) ↔ _
  rw [Submodule.mem_comap, ← mem_stdAt P]
  refine Iff.of_eq (congrArg (· ∈ stdAt E (N + c) P) ?_)
  funext l
  simp [LocE.scE]
end PI.TwNormLat.W
