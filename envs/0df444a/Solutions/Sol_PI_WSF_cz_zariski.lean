-- Prove2me | solution 1 for PI.WSF.cz_zariski
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:26.903411+00:00
-- url     : https://prove2.me/submissions/bb79dd2f-8f06-4c0a-87fb-a46b474cad52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
import Theorems.Thm_PI_WSF_cz_torus_zero
import Theorems.Thm_PI_WSF_czFam_eval
import Theorems.Thm_PI_WSF_cz_diag_unitary
import Theorems.Thm_PI_WSF_cz_svd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
namespace PI.WSF
theorem _root_.solution {N : ℕ} (P : MvPolynomial (Fin N × Fin N) ℂ)
    (h : ∀ u ∈ unitaryGroup (Fin N) ℂ, evalM u P = 0) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : IsUnit g.det) : evalM g P = 0 := by
  obtain ⟨u, hu, v, hv, z, rfl⟩ := cz_svd g hg
  have hQ : czFam u v P = 0 := by
    apply cz_torus_zero
    intro w hw
    rw [czFam_eval]
    exact h _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hu (cz_diag_unitary w hw)) hv)
  have h1 := czFam_eval u v P z
  rw [hQ, map_zero] at h1
  exact h1.symm
end PI.WSF
