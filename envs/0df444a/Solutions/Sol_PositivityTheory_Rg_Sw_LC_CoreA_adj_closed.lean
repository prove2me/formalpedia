-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.adj_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:05.348175+00:00
-- url     : https://prove2.me/submissions/a58b45a0-7207-4147-8dd1-74699d9db2b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_add_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
namespace PositivityTheory.Rg.Sw.LC.CoreA
theorem _root_.solution (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) :
    ∀ s ∈ Algebra.adjoin ℂ (Set.range T), ∃ s' ∈ Algebra.adjoin ℂ (Set.range T), ∀ v w, φ (s v) w = φ v (s' w) := by
  intro s hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hT i
    exact ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩, hj⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (star r), Subalgebra.algebraMap_mem _ _, fun v w => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [h.smul_left, h.smul]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨x' + y', add_mem hx' hy', fun v w => ?_⟩
    simp only [LinearMap.add_apply]
    rw [h.add_left, hx'', hy'', h.add]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨y' * x', mul_mem hy' hx', fun v w => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hx'', hy'']
end PositivityTheory.Rg.Sw.LC.CoreA
