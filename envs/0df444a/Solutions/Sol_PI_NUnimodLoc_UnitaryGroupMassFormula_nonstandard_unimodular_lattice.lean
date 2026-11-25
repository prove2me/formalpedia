-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.nonstandard_unimodular_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:33.139802+00:00
-- url     : https://prove2.me/submissions/3a1c765d-3abf-4180-bf13-a2b8b4a09121

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_nset_isMatGroup
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_dS_conj_N_iff
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_exists_conj_box
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isCompact_inter_unit_box
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_le_one_of_pow_le
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modEqOne
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modPow
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_pow_mem
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_exists_modular_function


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
theorem _root_.solution : NStdUnimod := by
  intro k r μ hμ
  have hG := nset_isMatGroup k r
  obtain ⟨D, hD, hR⟩ := exists_modular_function _ (Nset k r) hG
  have hle : ∀ n ∈ Nset k r, D n ≤ 1 := by
    intro n hn
    obtain ⟨M, hM⟩ := hD.2.2.2 (Nset k r ∩ box1 _) Set.inter_subset_left (isCompact_inter_unit_box hG.1)
    apply le_one_of_pow_le (M := M)
    intro p
    have hnp : n ^ p ∈ Nset k r := pow_mem hG hn p
    obtain ⟨s, hs0, hbox⟩ := exists_conj_box hnp
    have hc : IsUnit (dS k r s) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (dS_mul_dS_inv hs0.ne'))
    have hcG : ∀ g, dS k r s * g * (dS k r s)⁻¹ ∈ Nset k r ↔ g ∈ Nset k r :=
      fun g => dS_conj_N_iff hs0.ne' g
    rw [← modPow hG hD hn p, ← hD.2.2.1 _ hc hcG _ hnp]
    exact hM _ ⟨(hcG _).2 hnp, hbox⟩
  exact hR (fun n hn => modEqOne hG hD hn (hle n hn) (hle _ ((nilpotent_subgroup k r).2.2 _ hn))) μ hμ
end PI.NUnimodLoc.UnitaryGroupMassFormula
