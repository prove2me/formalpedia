-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.jq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:59.891691+00:00
-- url     : https://prove2.me/submissions/3381bf43-a216-41d3-8757-7054ea469ff8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09

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
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (l : Fin (n + c)) : IntAt P (g (eN E (n + c) j) l) := by
  have h1 : ∀ x, g x ∈ stdAt E (n + c) P ↔ x ∈ stdAt E (n + c) P := (Subgroup.mem_inf.mp hg).1
  exact (mem_stdAt' _).mp ((h1 _).mpr (eN_mem' _ _)) l
end PI.TwistedEisensteinNonvanishing.W
