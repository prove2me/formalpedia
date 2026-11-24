-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.reach_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.557839+00:00
-- url     : https://prove2.me/submissions/b0a32fb7-68d4-49c0-a245-e5e4cd189078

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (b : ι → K) : Reach σ J e f a b b := by
  have h1 : (1 : Matrix ι ι K) ∈ Good σ J e f :=
    ⟨1, Submonoid.one_mem _, 1, 1, by simp, by simp [tor]⟩
  exact ⟨1, h1, fun j => Matrix.one_mulVec _, Matrix.one_mulVec _⟩
end ReciprocityTheory.ChartRestriction.G.SA
