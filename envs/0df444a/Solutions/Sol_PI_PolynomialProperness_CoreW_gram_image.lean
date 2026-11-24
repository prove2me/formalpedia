-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.gram_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:16.448969+00:00
-- url     : https://prove2.me/submissions/b6bd001d-6df0-492b-9d20-1f228a27089d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (H s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (m : ι → Fin n → ℂ) :
    gramOf H (fun i => s *ᵥ m i) = gramOf H m := by
  ext i j
  simp only [gramOf, Matrix.of_apply]
  exact herm_iso H s hs (m j) (m i)
end PI.PolynomialProperness.CoreW
