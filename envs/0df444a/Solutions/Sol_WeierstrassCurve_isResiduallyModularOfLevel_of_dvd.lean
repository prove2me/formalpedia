-- Prove2me | solution 1 for WeierstrassCurve.isResiduallyModularOfLevel_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/67ddf0c9-5c77-5e4e-b078-97e564b38a6e

import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

theorem solution (W : WeierstrassCurve ℤ) (p : ℕ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsResiduallyModularOfLevel p M) : W.IsResiduallyModularOfLevel p N := by
  obtain ⟨f, 𝔪, hf, hmax, hpm, hcong⟩ := h
  obtain ⟨g, hg, hcoeff⟩ := CuspForm.exists_isNormalizedEigenform_of_dvd hMN f hf
  refine ⟨g, 𝔪, hg, hmax, hpm, fun ℓ hℓ hgood hℓN hℓp ↦ ?_⟩
  obtain ⟨a, ha, ham⟩ := hcong ℓ hℓ hgood (fun hℓM ↦ hℓN (hℓM.trans hMN)) hℓp
  exact ⟨a, ha.trans (hcoeff ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)).symm, ham⟩

end

end S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd
end P2MW
export P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd (solution)
