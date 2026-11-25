-- Prove2me | solution 1 for PI.VolStabW.cnt_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:25.115741+00:00
-- url     : https://prove2.me/submissions/bf291c41-b5e2-4e34-b3f4-c0dd090cba55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_PI_VolStabW_incl_mem


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
namespace PI.VolStabW
theorem _root_.solution {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (u : E) (hu : G.det * u = 1)
    (hui : ∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) :
    IsUnit ((entL v A hD G hG).map (rho v A hD r hr)).det := by
  have hdet : ((entL v A hD G hG).det : Fv F v ⊗[F] E) = inclR (Fv F v) G.det := by
    have e1 := RingHom.map_det (lamC v A hD).subtype (entL v A hD G hG)
    rw [RingHom.mapMatrix_apply] at e1
    have e2 := RingHom.map_det (inclR (Fv F v) (F := F) (E := E)) G
    rw [RingHom.mapMatrix_apply] at e2
    rw [show ((entL v A hD G hG).det : Fv F v ⊗[F] E) = (lamC v A hD).subtype (entL v A hD G hG).det
      from rfl, e1, e2]
    rfl
  have hu' : (entL v A hD G hG).det * ⟨inclR (Fv F v) u, incl_mem v A hD u hui⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdet, Subring.coe_one]
    show inclR (Fv F v) G.det * inclR (Fv F v) u = 1
    rw [← map_mul, hu, map_one]
  have e3 := RingHom.map_det (rho v A hD r hr) (entL v A hD G hG)
  rw [RingHom.mapMatrix_apply] at e3
  rw [← e3]
  exact (isUnit_iff_exists_inv.2 ⟨_, hu'⟩).map _
end PI.VolStabW
