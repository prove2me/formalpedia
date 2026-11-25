-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.box_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:04.652054+00:00
-- url     : https://prove2.me/submissions/5f7946c0-0440-4802-82c4-bc14536177cc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_gen_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, KopL ε i j f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => KopL ε i j x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    exact gen_stable ε i j R s hs hR
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx
end PositivityTheory.Rg.Sw.LC.CoreC
