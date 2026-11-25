-- Prove2me | solution 1 for PI.VolStabSW.densFibInf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:55.961086+00:00
-- url     : https://prove2.me/submissions/f12b134d-f72a-4683-ada0-b0d4b9e18848

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibInf
import Theorems.Thm_PI_VolStabSW_DensGen_densGen
import Theorems.Thm_PI_VolStabSW_continuous_gramH
import Theorems.Thm_PI_VolStabSW_isOpen_unitHerm
import Theorems.Thm_PI_VolStabSW_isOpen_units_Ainf
import Theorems.Thm_PI_VolStabSW_isUnit_det_hermOf
import Theorems.Thm_PI_VolStabSW_linIndep_of_isUnit_det
import Theorems.Thm_PI_VolStabSW_sigma_invol


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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation
namespace PI.VolStabSW
theorem _root_.solution : DensFibInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ μinf hμ νinf hν fibInf hfib Φ g
    hΦc hΦs hg
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have hD : {S : HermR (Ainf F) σ a | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} ∈
      𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT) :=
    (isOpen_unitHerm (Ainf F) (isOpen_units_Ainf F) σ a).mem_nhds
      (isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  exact DensGen.densGen (f' := gramH (Ainf F) σ hσ J hJ.1) hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) Subtype.val_injective
    (fun v hv => linIndep_of_isUnit_det (Ainf F) σ J v hv) hΦc hΦs hg Filter.univ_mem hD hD
end PI.VolStabSW
