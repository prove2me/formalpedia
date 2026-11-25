-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:34.165133+00:00
-- url     : https://prove2.me/submissions/fffc6cba-4e46-4320-996f-29db056ee505

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv

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
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (a b : Fin n → ℂ) :
    herm H ((c : ℂ) • a - b) ((c : ℂ) • a - b) =
      (c : ℂ) * ((c : ℂ) * herm H a a) - (c : ℂ) * herm H a b - ((c : ℂ) * herm H b a - herm H b b) := by
  simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  ring
end PI.PolynomialProperness.CoreW
