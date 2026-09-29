-- Prove2me | solution 1 for WeierstrassCurve.isModularModelOfLevel_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8ae90011-0732-5f64-9b5e-31bbf1410036

import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

theorem solution (W : WeierstrassCurve ℤ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsModularModelOfLevel M) : W.IsModularModelOfLevel N := by
  obtain ⟨f, hf, hap⟩ := h
  obtain ⟨g, hg, hcoeff⟩ := CuspForm.exists_isNormalizedEigenform_of_dvd hMN f hf
  exact ⟨g, hg, fun p hp hgood hpN ↦
    (hcoeff p (hp.coprime_iff_not_dvd.mpr hpN)).trans (hap p hp hgood fun hpM ↦ hpN (hpM.trans hMN))⟩

end

end S_WeierstrassCurve_isModularModelOfLevel_of_dvd
end P2MW
export P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_dvd (solution)
