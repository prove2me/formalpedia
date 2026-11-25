-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.altPair_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:39.106988+00:00
-- url     : https://prove2.me/submissions/9ccc6394-a4ad-4ccc-b422-2ba4f0885aa2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (tl : Fin N → ι) (f : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (I : Q ⊕ (Fin N ⊕ Fin N) → Fin n) :
    altPair tl f I = ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ dbl σ) := by
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, pm_apply]
end PositivityTheory.Rg.Cz.YoungTableau
