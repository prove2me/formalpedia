-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:42.946018+00:00
-- url     : https://prove2.me/submissions/bc9a0fd0-175a-4077-961c-2640c04d9d5f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def

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
theorem _root_.solution {q kj n c : ℕ} (x : Sp E (n + c)) :
    x ∈ parL P q kj n c ↔ ∀ l : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold parL sclLat
  rw [Submodule.mem_comap, mem_stdAt']
  simp only [LinearMap.coe_restrictScalars, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj,
    Function.eval, smul_eq_mul]
end PI.TwistedEisensteinNonvanishing.W
