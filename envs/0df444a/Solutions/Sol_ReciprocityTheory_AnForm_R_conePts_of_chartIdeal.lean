-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.conePts_of_chartIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:12.727+00:00
-- url     : https://prove2.me/submissions/34e810bc-ccbf-429d-b614-4f6b77c5d3b8

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) (hy : ∀ h ∈ chartIdeal P p, eval y h = 0) :
    y ∈ conePts P ∧ (∀ k, y ⟨k, p k⟩ = 1) ∧ affCoord p y = y := by
  have hle : Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) ≤
      chartIdeal P p := le_sup_right
  have hleP : P ≤ chartIdeal P p := le_sup_left
  have h1 : ∀ k, y ⟨k, p k⟩ = 1 := by
    intro k
    have hmem : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      hle (Ideal.subset_span (Set.mem_range_self k))
    have := hy _ hmem
    rw [map_sub, eval_X, map_one, sub_eq_zero] at this
    exact this
  refine ⟨?_, h1, ?_⟩
  · unfold conePts
    rw [Set.mem_setOf_eq]
    exact ⟨fun k => ⟨p k, by rw [h1 k]; exact one_ne_zero⟩, fun f hf => hy f (hleP hf)⟩
  · funext q
    show y q / y ⟨q.1, p q.1⟩ = y q
    rw [h1 q.1, div_one]
end ReciprocityTheory.AnForm.R
