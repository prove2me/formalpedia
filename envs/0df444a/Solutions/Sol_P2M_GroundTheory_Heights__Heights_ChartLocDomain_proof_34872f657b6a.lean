-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:48.747947+00:00
-- url     : https://prove2.me/submissions/dbd7fbbe-b15d-4d88-9aa5-b57fbf0565b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartLocDomain
theorem _root_.solution (h₁ : IncIdealBelow.Statement) (h₂ : ChartIncDomain.Statement)
    (h₃ : ChartKernel.Statement) : ChartLocDomain.Statement := by
  intro F _ n e I f t p _ hI hf ht
  obtain ⟨hdom, hker⟩ := h₂ F n e I t hI ht
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [h₃ F n e I t hI ht, h₁ F n e I f hI hf])
  have hle : Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl ≤ nonZeroDivisors (ChartInc I t e) := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    rw [hinj (h0.trans (map_zero _).symm)]
    exact p.zero_mem
  have : IsDomain (ChartLoc I t e p) := IsLocalization.isDomain_localization hle
  refine ⟨inferInstance, localizationAlgebra_injective (M := p.primeCompl) (S := ChartInc I t e)
    (Rₘ := Localization.AtPrime p) (Sₘ := ChartLoc I t e p) (hRS := hinj), fun u hu h0 => ?_⟩
  have hz : chartLin I t e u = 0 := IsLocalization.injective (ChartLoc I t e p) hle (h0.trans (map_zero _).symm)
  have hmem : linForm u ∈ RingHom.ker (chartX I t e) := hz
  rw [hker] at hmem
  exact ChartLocDomain.linForm_not_mem_sup hI ht hu hmem
end ChartLocDomain
end GroundTheory.Heights₂.Heights
