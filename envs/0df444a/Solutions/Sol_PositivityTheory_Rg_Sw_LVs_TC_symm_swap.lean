-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.symm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:28.30595+00:00
-- url     : https://prove2.me/submissions/558c4d1a-6283-4e5b-a275-4f471c3c4b56

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_smooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped ContDiff
open Set Filter Topology
namespace PositivityTheory.Rg.Sw.LVs.TC
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
private theorem iteratedFDeriv_add_two_apply {F : V → ℂ} (k : ℕ) (c : V) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c v =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k F)) c (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
  simp [LinearIsometryEquiv.comp_fderiv, Fin.tail]
end
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
end PositivityTheory.Rg.Sw.LVs.TC
end
end

set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    {c : V} (hc : c ∈ Ω) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℂ (k + 2) F c v := by
  have hG : ContDiffAt ℂ ∞ (iteratedFDeriv ℂ k F) c :=
    (iter_smooth hΩ hF k).contDiffAt (hΩ.mem_nhds hc)
  have hmin : minSmoothness ℂ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hs := hG.isSymmSndFDerivAt hmin
  have htt : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
  rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, htt]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hs (v 1) (v 0)]
end PositivityTheory.Rg.Sw.LVs.TC
