-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.prod_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:18.449777+00:00
-- url     : https://prove2.me/submissions/50f07631-dd32-4775-99f6-a96ab89527e5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_renInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α : R) {r s : ℕ} (I J : Fin r ↪ Fin s) (σ : Equiv.Perm (Fin r)) (l : List (Fin r)) (f : Pm R r) :
    (l.map (fun k => opE α (I k) (J (σ k)))).prod (ren I J f) = ren I J ((l.map (fun k => opE α k (σ k))).prod f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    exact renInt R r s I J α a (σ a) _
end PositivityTheory.Rg.Sw.SP.Mi
