-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.iteratedFDeriv_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:15.143818+00:00
-- url     : https://prove2.me/submissions/60471469-0323-402d-b18d-f6866d915aaa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (L : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) (n : ℕ) (v : Fin n → Matrix ι ι ℂ) :
    iteratedFDeriv ℂ n (F ∘ L) 0 v = iteratedFDeriv ℂ n F 0 (fun i => L (v i)) := by
  obtain ⟨s, hs0, hAs⟩ := hF.exists_mem_nhds_analyticOnNhd
  have ht : IsOpen (interior s) := isOpen_interior
  have h0t : (0 : Matrix κ κ ℂ) ∈ interior s := mem_interior_iff_mem_nhds.mpr hs0
  have hcd : ContDiffOn ℂ ω F (interior s) := (hAs.mono interior_subset).contDiffOn ht.uniqueDiffOn
  have hpre : IsOpen (L ⁻¹' interior s) := ht.preimage L.continuous
  have hL0 : L 0 ∈ interior s := by simpa using h0t
  have h0pre : (0 : Matrix ι ι ℂ) ∈ L ⁻¹' interior s := hL0
  have key := L.iteratedFDerivWithin_comp_right hcd ht.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := n) le_top
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F ∘ L) n hpre h0pre
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F) n ht h0t
  have hz : L 0 = 0 := L.map_zero
  rw [← e1, ← e2]
  erw [key]
  exact congrArg (fun y => iteratedFDerivWithin ℂ n F (interior s) y (fun i => L (v i))) hz
end PositivityTheory.Rg.Sw.LVs.CEq
