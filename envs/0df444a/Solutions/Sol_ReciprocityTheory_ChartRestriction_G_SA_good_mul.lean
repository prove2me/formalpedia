-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:20.076264+00:00
-- url     : https://prove2.me/submissions/34d4d02e-6de1-4807-82c2-490c781fef2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_conj_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mul

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
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {g g' : Matrix ι ι K} (hg : g ∈ Good σ J e f) (hg' : g' ∈ Good σ J e f) :
    g * g' ∈ Good σ J e f := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨n', hn', l', m', hml', rfl⟩ := hg'
  obtain ⟨n'', hn'', h⟩ := conj_closure hσ hJ he hff hef hml hn'
  refine ⟨n * n'', Submonoid.mul_mem _ hn hn'', l * l', m * m', ?_, ?_⟩
  · rw [map_mul]; linear_combination (m' * σ l') * hml + hml'
  · rw [← tor_mul hσ hJ he hff hef, Matrix.mul_assoc n, ← Matrix.mul_assoc (tor σ J e f l m), h]
    simp only [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.SA
