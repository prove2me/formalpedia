-- Prove2me | solution 1 for PI.VolStabW.rho_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:24:48.93988+00:00
-- url     : https://prove2.me/submissions/69fea36f-5ebd-46ae-b92d-13fff2ae217b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Theorems.Thm_PI_VolStabW_rho_apply
import Theorems.Thm_PI_VolStabW_red_eq_zero_iff


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
variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))
include hbij
namespace PI.VolStabW
theorem _root_.solution (z : lamC v A hD) : rho v A hD r hr z = 0 ↔
    Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1 := by
  have hz := z.2
  rw [mem_lamC] at hz
  rw [← red_eq_zero_iff v hz.1, ← red_eq_zero_iff v hz.2, rho_apply]
  constructor
  · intro h
    have := hbij.1 (a₁ := (red v (Xc v A z), red v (Yc v A z))) (a₂ := (0, 0)) (by simpa using h)
    simp only [Prod.mk.injEq] at this
    exact this
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; simp
end PI.VolStabW
