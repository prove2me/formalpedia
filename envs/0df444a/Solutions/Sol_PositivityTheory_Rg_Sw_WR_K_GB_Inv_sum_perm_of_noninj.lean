-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.sum_perm_of_noninj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:19.629417+00:00
-- url     : https://prove2.me/submissions/b77b7616-076b-4441-b70b-21d6541ba4ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution {α : Type*} [AddCommMonoid α] (h : (Fin n → Fin n) → α)
    (h0 : ∀ c, ¬ Function.Injective c → h c = 0) :
    ∑ c : Fin n → Fin n, h c = ∑ π : Equiv.Perm (Fin n), h π := by
  classical
  rw [← Finset.sum_filter_of_ne (f := h) (p := Function.Injective) (fun c _ hc => by_contra fun hn => hc (h0 c hn))]
  refine Finset.sum_bij' (fun c hc => Equiv.ofBijective c
      ((Finite.injective_iff_bijective).1 (Finset.mem_filter.1 hc).2)) (fun π _ => ⇑π) ?_ ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro π _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, π.injective⟩
  · intro c _; rfl
  · intro π _; ext; rfl
  · intro c _; rfl
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
