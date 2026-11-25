-- Prove2me | solution 1 for PI.VolStabW.densFibV_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:51.068935+00:00
-- url     : https://prove2.me/submissions/58fcafb8-c06a-462a-a8f1-8a31f9e99cb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Theorems.Thm_PI_VolStabW_secondCountable_Fv
import Theorems.Thm_PI_VolStabW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabW_isOpen_units_Fv
import Theorems.Thm_PI_VolStabW_DensGen_densGen
import Theorems.Thm_PI_VolStabW_continuous_gramH
import Theorems.Thm_PI_VolStabW_isOpen_unitHerm
import Theorems.Thm_PI_VolStabW_isUnit_det_hermOf
import Theorems.Thm_PI_VolStabW_linIndep_of_isUnit_det
import Theorems.Thm_PI_VolStabW_sigma_invol


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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
namespace PI.VolStabW
theorem _root_.solution : DensFibV := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv
    hSB hdens
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  exact DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1)
    (fun X => rfl) Subtype.val_injective
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX)
    hSB.1.continuous hSB.2 hdens Filter.univ_mem
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
end PI.VolStabW
