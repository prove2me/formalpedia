-- Prove2me | solution 1 for PI.MkQ.phi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:21.725904+00:00
-- url     : https://prove2.me/submissions/7a79bc7c-06a7-44c3-913c-c038fa083b41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
import Theorems.Thm_PI_MkQ_rho_apply_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MkQ
open Matrix
variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))
variable [Finite G]
namespace PI.MkQ
theorem _root_.solution : Function.Injective (phi G) := by
  intro g g' h
  have h1 : rho G g = rho G g' := by
    have h0 := congrArg (fun u : GeneralLinearGroup (Fin N) ℤ => (u : Matrix (Fin N) (Fin N) ℤ)) h
    change (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g) =
      (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g') at h0
    exact (LinearMap.toMatrixAlgEquiv (basisFin G)).injective h0
  have h2 : ∀ i, ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) =
      ((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) := by
    intro i
    have h0 := congrArg
      (fun f : Module.End ℤ (lat G) => ((f ⟨Pi.single i 1, single_mem G i⟩ : lat G) : Fin N → ℚ)) h1
    simpa [rho_apply_coe] using h0
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h0 := congrFun (h2 b) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0
end PI.MkQ
