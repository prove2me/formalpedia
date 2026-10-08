-- Prove2me | solution 1 for StochApproxDyn.Lyapunov.inter_nonempty_and_isGLB_inter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:21:21.931513+00:00
-- url     : https://prove2.me/submissions/0edb5164-2ec3-426e-be76-60102451ccb8

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

open scoped NNReal

set_option autoImplicit false

open NNReal StochApproxDyn.Lyapunov in
theorem solution {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (L : Set M) (hL : StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L)
    (vstar : ℝ) (hvstar : IsGLB (V '' L) vstar) :
    (L ∩ Λ).Nonempty ∧ IsGLB (V '' (L ∩ Λ)) vstar := by
  obtain ⟨_, _, hVc, _, hdec⟩ := hV
  obtain ⟨hLne, hLc, hLinv, _⟩ := hL
  obtain ⟨x0, hx0L, hmin⟩ := hLc.exists_isMinOn hLne hVc.continuousOn
  -- x0 ∈ Λ, else V decreases strictly along the orbit, which stays in L
  have hx0Λ : x0 ∈ Λ := by
    by_contra hx
    have h1 : Φ 1 x0 ∈ L := by
      rw [← hLinv 1]; exact Set.mem_image_of_mem _ hx0L
    have hlt : V (Φ 1 x0) < V (Φ 0 x0) := hdec x0 hx (by norm_num : (0 : ℝ≥0) < 1)
    rw [Flow.map_zero_apply] at hlt
    have : V x0 ≤ V (Φ 1 x0) := hmin h1
    linarith
  -- vstar = V x0
  have hv : vstar = V x0 := by
    have hglb2 : IsGLB (V '' L) (V x0) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact hmin hy
      · intro b hb
        exact hb ⟨x0, hx0L, rfl⟩
    exact hvstar.unique hglb2
  refine ⟨⟨x0, hx0L, hx0Λ⟩, ?_⟩
  subst hv
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmin hy.1
  · intro b hb
    exact hb ⟨x0, ⟨hx0L, hx0Λ⟩, rfl⟩
