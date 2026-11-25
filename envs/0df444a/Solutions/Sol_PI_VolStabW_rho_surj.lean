-- Prove2me | solution 1 for PI.VolStabW.rho_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:24:56.854053+00:00
-- url     : https://prove2.me/submissions/4fc1c792-942e-4e8f-8f25-acea695d2763

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Theorems.Thm_PI_VolStabW_rho_apply
import Theorems.Thm_PI_VolStabW_red_surj


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
theorem _root_.solution (w : K) : ∃ z : lamC v A hD, rho v A hD r hr z = w := by
  obtain ⟨⟨s, t⟩, hst⟩ := hbij.2 w
  obtain ⟨x, hx, rfl⟩ := red_surj v s
  obtain ⟨y, hy, rfl⟩ := red_surj v t
  refine ⟨⟨Pt v A x y, ?_⟩, ?_⟩
  · rw [mem_lamC, Xc_Pt, Yc_Pt]; exact ⟨hx, hy⟩
  · rw [rho_apply]
    simp only [Xc_Pt, Yc_Pt]
    exact hst
end PI.VolStabW
