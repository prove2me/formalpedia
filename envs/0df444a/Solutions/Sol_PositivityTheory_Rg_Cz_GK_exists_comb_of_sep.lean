-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.GK.exists_comb_of_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:33:59.574356+00:00
-- url     : https://prove2.me/submissions/3250fe65-4174-4e44-87e7-b8d6a7ca75ff

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_UnitaryCurves_ExistsUnitaryCurve

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.GK
namespace PositivityTheory.Rg.Cz.GK
theorem _root_.solution {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ev : ι → Module.Dual ℂ V) (hsep : ∀ v, (∀ i, ev i v = 0) → v = 0) (lam : Module.Dual ℂ V) :
    ∃ (s : Finset ι) (c : ι → ℂ), ∀ v, lam v = ∑ i ∈ s, c i * ev i v := by
  classical
  set W := Submodule.span ℂ (Set.range ev)
  have hW : W = ⊤ := by
    have h1 : W.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (hsep v fun i => hv _ (Submodule.subset_span ⟨i, rfl⟩))
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hl : lam ∈ W := hW ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hl
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  simp [smul_eq_mul]
end PositivityTheory.Rg.Cz.GK
