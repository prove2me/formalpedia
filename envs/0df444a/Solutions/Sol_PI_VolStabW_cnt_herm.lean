-- Prove2me | solution 1 for PI.VolStabW.cnt_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:24:26.584153+00:00
-- url     : https://prove2.me/submissions/58c30e52-81d4-4baf-9bc3-9177789fabbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148
import Theorems.Thm_PI_VolStabW_coe_sigC
import Theorems.Thm_PI_VolStabW_rho_sig


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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
include hσr
namespace PI.VolStabW
theorem _root_.solution {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hGs : ∀ i j, σ (G j i) = G i j)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (i j : Fin n) :
    σ' (((entL v A hD G hG).map (rho v A hD r hr)) j i) = ((entL v A hD G hG).map (rho v A hD r hr)) i j := by
  simp only [Matrix.map_apply]
  rw [← rho_sig v A hD r hr σ' hσr]
  congr 1
  apply Subtype.ext
  rw [coe_sigC]
  show sigR (Fv F v) σ (inclR (Fv F v) (G j i)) = inclR (Fv F v) (G i j)
  rw [sigR_incl, hGs]
end PI.VolStabW
