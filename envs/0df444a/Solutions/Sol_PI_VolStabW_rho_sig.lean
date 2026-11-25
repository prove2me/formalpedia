-- Prove2me | solution 1 for PI.VolStabW.rho_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:06.398778+00:00
-- url     : https://prove2.me/submissions/b1a4e6ab-9ec9-4412-9096-e6a893c26e4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Theorems.Thm_PI_VolStabW_coe_sigC
import Theorems.Thm_PI_VolStabW_rho_apply
import Theorems.Thm_PI_VolStabW_red_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)
variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
namespace PI.VolStabW
theorem _root_.solution (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
    (z : lamC v A hD) : rho v A hD r hr (sigC v A hD z) = σ' (rho v A hD r hr z) := by
  have hz := z.2
  rw [mem_lamC] at hz
  rw [rho_apply, rho_apply, coe_sigC, Xc_sig, Yc_sig, red_neg v hz.2, map_add, map_mul,
    AlgEquiv.commutes, AlgEquiv.commutes, hσr, map_neg]
  ring
end PI.VolStabW
