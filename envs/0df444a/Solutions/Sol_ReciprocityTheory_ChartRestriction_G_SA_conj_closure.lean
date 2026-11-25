-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.conj_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:57.038084+00:00
-- url     : https://prove2.me/submissions/195b29b6-6c29-4eda-8248-40eb0ef2c231

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_conj_mem_eichSet

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
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {l m : K} (hml : m * σ l = 1) {n : Matrix ι ι K}
    (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ n' ∈ Submonoid.closure (eichSet σ J e f), tor σ J e f l m * n = n' * tor σ J e f l m := by
  induction hn using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨M', h1, h2⟩ := conj_mem_eichSet hσ hJ he hff hef hml hx
    exact ⟨M', Submonoid.subset_closure h1, h2⟩
  | one => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx2⟩ := hx
    obtain ⟨y', hy', hy2⟩ := hy
    refine ⟨x' * y', Submonoid.mul_mem _ hx' hy', ?_⟩
    rw [← Matrix.mul_assoc, hx2, Matrix.mul_assoc, hy2, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.SA
