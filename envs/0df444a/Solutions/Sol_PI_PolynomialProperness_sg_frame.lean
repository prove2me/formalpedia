-- Prove2me | solution 1 for PI.PolynomialProperness.sg_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:10.485213+00:00
-- url     : https://prove2.me/submissions/55af033b-d82f-4edb-aafb-11142d1f818d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector
import Theorems.Thm_PI_PolynomialProperness_UW_fix
import Theorems.Thm_PI_PolynomialProperness_unipotent_fixes_frame_vector

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
theorem _root_.solution (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) {n0 h : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hn : n0 ∈ N0set k r z) (hv : v ∈ UTset (r + 1)) (hh : h ∈ UWset k r z) :
    n0 * tauM k r z v * h ∈ B.GV k r ∧
      ∀ b, (n0 * tauM k r z v * h) *ᵥ fvec k r z b = fmul k r z v b := by
  obtain ⟨hτN, hτf, -⟩ := hT k r z hz v hv
  have hmul := (hG k r).1
  refine ⟨hmul _ (hmul _ hn.1.1 _ hτN.1) _ hh.1, fun b => ?_⟩
  rw [← Matrix.mulVec_mulVec, UW_fix hh, ← Matrix.mulVec_mulVec, hτf b]
  simp only [fmul, Matrix.mulVec_sum, Matrix.mulVec_smul, unipotent_fixes_frame_vector hU hz hn]
end PI.PolynomialProperness
