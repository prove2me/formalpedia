-- Prove2me | solution 1 for PI.PolynomialProperness.unipotent_fixes_frame_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:31.060222+00:00
-- url     : https://prove2.me/submissions/ed70ab38-6b44-4238-8e69-c20681c0eb29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector
import Theorems.Thm_PI_PolynomialProperness_one_mem_UW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (hU : UMapFrame) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z)
    {n0 : B.Mat k r} (hn : n0 ∈ N0set k r z) (b : Fin (r + 1)) :
    n0 *ᵥ fvec k r z b = fvec k r z b := by
  have hS : n0 ∈ Sset k r z := ⟨1, one_mem_UW k r z, n0, hn.1, (Matrix.one_mul _).symm⟩
  rw [((hU k r z hz).1 n0 hS).1 b, hn.2]
  simp [Matrix.one_apply]
end PI.PolynomialProperness
