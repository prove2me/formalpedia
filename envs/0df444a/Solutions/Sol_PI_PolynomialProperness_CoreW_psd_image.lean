-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.psd_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:16.263126+00:00
-- url     : https://prove2.me/submissions/499b71e1-66b4-4498-9d64-1fb2238078cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
import Theorems.Thm_PI_PolynomialProperness_CoreW_iso_right_inv
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
theorem _root_.solution (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H)
    (m : ι → Fin n → ℂ) (hpsd : ∀ x, (∀ i, herm H x (m i) = 0) → 0 ≤ (herm H x x).re)
    (w : Fin n → ℂ) (hw : ∀ i, herm H w (s *ᵥ m i) = 0) : 0 ≤ (herm H w w).re := by
  have hsx : s *ᵥ ((H * sᴴ * H) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, iso_right_inv H s hHH hs, Matrix.one_mulVec]
  have h1 : ∀ i, herm H ((H * sᴴ * H) *ᵥ w) (m i) = 0 := fun i => by
    rw [← herm_iso H s hs, hsx]
    exact hw i
  have h2 := hpsd _ h1
  rwa [← herm_iso H s hs, hsx] at h2
end PI.PolynomialProperness.CoreW
