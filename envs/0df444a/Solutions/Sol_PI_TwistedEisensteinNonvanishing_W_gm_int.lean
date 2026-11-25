-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:11.261794+00:00
-- url     : https://prove2.me/submissions/73d5fd79-49fb-4c7f-927a-ddbbc8eb8646

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_jq_int
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (p p'' : ℕ) (hp : p < n + c) :
    IntAt P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p)) := by
  unfold atN
  split_ifs with hlt
  · exact jq_int hg _ _
  · exact ia_zero (P := P)
end PI.TwistedEisensteinNonvanishing.W
