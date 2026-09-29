-- Prove2me | solution 1 for OnlineConvexOpt.ConvexBasics.kkt_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T22:09:40.928475+00:00
-- url     : https://prove2.me/submissions/8c7f9a54-b598-42b7-a4b0-d656d142839e

import Mathlib

/-! f573edf5 OnlineConvexOpt.ConvexBasics.kkt_optimality (Hazan, OCO, Thm 2.2).
`x⋆` minimises `f` on the convex set `K`, so it is a local minimum of `f` on `K`; `y - x⋆` lies in
the positive tangent cone of `K` at `x⋆` (the segment `[x⋆, y]` is in `K`), and Fermat's theorem
on a set gives `0 ≤ f'(x⋆)(y - x⋆) = ⟪∇f(x⋆), y - x⋆⟫`. -/

set_option autoImplicit false

open scoped InnerProductSpace in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : Set E) (hK : Convex ℝ K) (f : E → ℝ)
    (xstar : E) (hxstarK : xstar ∈ K) (hxstar : IsMinOn f K xstar)
    (gstar : E) (hgstar : HasGradientAt f gstar xstar) :
    ∀ y ∈ K, ⟪gstar, y - xstar⟫_ℝ ≥ 0 := by
  intro y hy
  have h1 : HasFDerivAt f (InnerProductSpace.toDual ℝ E gstar) xstar := hgstar.hasFDerivAt
  have h2 : IsLocalMinOn f K xstar := hxstar.localize
  have h3 : y - xstar ∈ posTangentConeAt K xstar :=
    sub_mem_posTangentConeAt_of_segment_subset (hK.segment_subset hxstarK hy)
  have h4 := h2.hasFDerivWithinAt_nonneg h1.hasFDerivWithinAt h3
  simpa [InnerProductSpace.toDual_apply_apply] using h4
