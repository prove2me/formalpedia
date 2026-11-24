-- Prove2me | solution 1 for PI.GreenLabelMapW.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:34.113372+00:00
-- url     : https://prove2.me/submissions/b9cb5c24-c7b1-4acf-a6b1-4e94e2823f63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]
namespace PI.GreenLabelMapW
theorem _root_.solution {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) : w ≠ 0 := by
  rintro rfl
  apply hX
  have h0 : P.coeff 0 = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at hw
    exact (algebraMap K (AlgebraicClosure K)).injective (by rw [hw, map_zero])
  have hXP : X ∣ P := Polynomial.X_dvd_iff.2 h0
  have hPX : P ∣ X := Polynomial.irreducible_X.dvd_symm hi hXP
  exact Polynomial.eq_of_monic_of_associated hm Polynomial.monic_X (associated_of_dvd_dvd hPX hXP)
end PI.GreenLabelMapW
