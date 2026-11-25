-- Prove2me | solution 1 for PositivityTheory.CW.CasimirRealScalar.cas_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:07.571721+00:00
-- url     : https://prove2.me/submissions/a18eb9f0-6c93-463b-8460-330d4ce42645

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealOfCentral
import Theorems.Thm_PositivityTheory_CW_CasimirRealScalar_term_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CasimirRealScalar
variable {n : ℕ}
namespace PositivityTheory.CW.CasimirRealScalar
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (v : V) :
    (inner ℂ v (casimir E v)).im = 0 := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, inner_sum, Complex.im_sum]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => term_im ε E hu a b v
end PositivityTheory.CW.CasimirRealScalar
