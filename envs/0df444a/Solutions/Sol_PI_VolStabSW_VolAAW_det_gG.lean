-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.det_gG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:47.713998+00:00
-- url     : https://prove2.me/submissions/2f99457e-e2b5-4b56-8463-4add38f1d7b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Theorems.Thm_PI_VolStabSW_VolAAW_BR_eq_sum
import Theorems.Thm_PI_VolStabSW_VolAAW_cT_surj
import Theorems.Thm_PI_VolStabSW_SdDualW_nondeg_BR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
include v
namespace PI.VolStabSW.VolAAW
theorem _root_.solution [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) : (gG b σ J a).det ≠ 0 := by
  classical
  intro h0
  set G := (gG b σ J a).map (algebraMap F (Fv F v)) with hG
  have hdet : G.det = 0 := by
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨Y, hY⟩ := cT_surj b v (a := a) (M := M) w
  have hY0 : Y = 0 := by
    apply nondeg_BR v σ hσ J hJ Y
    intro X
    rw [BR_eq_sum, hY, hw]
    simp
  apply hw0
  rw [← hY, hY0]
  funext q
  simp [cT, crd]
end PI.VolStabSW.VolAAW
