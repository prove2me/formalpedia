-- Prove2me | solution 1 for PI.WickFormula.Gen.pow_apply_eq_zero_of_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:13.544954+00:00
-- url     : https://prove2.me/submissions/9627e11e-6e0f-434c-8c17-9a1056e3e29e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
import Theorems.Thm_PI_WickFormula_Gen_eq_zero_of_mem_lowDeg_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.WickFormula.Gen
theorem _root_.solution (D : Module.End K (MvPolynomial σ K)) (f : ι → σ)
    (hD : ∀ t R, R ∈ lowDeg f (t + 1) → D R ∈ lowDeg f t) :
    ∀ n R, R ∈ lowDeg f n → (D ^ n) R = 0 := by
  intro n
  induction n with
  | zero =>
    intro R hR
    rw [pow_zero]
    exact eq_zero_of_mem_lowDeg_zero hR
  | succ n ih =>
    intro R hR
    rw [pow_succ]
    exact ih _ (hD n R hR)
end PI.WickFormula.Gen
