-- Prove2me | solution 1 for PositivityTheory.CW.CasimirRealScalar.term_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:13.072892+00:00
-- url     : https://prove2.me/submissions/424ef478-63fa-44f1-9451-28db513e5c32

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealOfCentral

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
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (a b : Fin n) (v : V) :
    (inner ℂ v (E a b (E b a v))).im = 0 := by
  rw [← inner_conj_symm, hu a b, Complex.conj_im, neg_eq_zero]
  have h1 : (adjSign ε a b).im = 0 := by
    unfold adjSign
    split_ifs <;> simp
  have h2 : (inner ℂ (E b a v) (E b a v)).im = 0 := inner_self_im (𝕜 := ℂ) _
  rw [Complex.mul_im, h1, h2]
  ring
end PositivityTheory.CW.CasimirRealScalar
