-- Prove2me | solution 1 for UpperHalfPlane.qExpansion_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b6ad8b51-5d7d-5710-a482-b68825033819

import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_qExpansion_prod

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

open scoped Real MatrixGroups Topology Manifold

theorem solution {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by
  suffices H : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) ∧
      AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, F i)) 0 from H.1
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : cuspFunction h (1 : ℍ → ℂ) = 1 := by
      ext q
      rcases eq_or_ne q 0 with rfl | hq
      · simp [cuspFunction, Periodic.cuspFunction]
        exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
      · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
    refine ⟨by simpa using qExpansion_one h, ?_⟩
    rw [Finset.prod_empty, h1]
    exact analyticAt_const
  | cons a s ha ih =>
    have hFa : AnalyticAt ℂ (cuspFunction h (F a)) 0 := hF a (Finset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons, qExpansion_mul hFa ih2, ih1]
    refine ⟨rfl, ?_⟩
    rw [cuspFunction_mul hFa.continuousAt ih2.continuousAt]
    exact hFa.mul ih2

end

end S_UpperHalfPlane_qExpansion_prod
end P2MW
export P2MW.S_UpperHalfPlane_qExpansion_prod (solution)
