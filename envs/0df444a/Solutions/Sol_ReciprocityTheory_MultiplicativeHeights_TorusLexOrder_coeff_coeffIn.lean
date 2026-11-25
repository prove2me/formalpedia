-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.coeff_coeffIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:19.69347+00:00
-- url     : https://prove2.me/submissions/2ea0b072-1f72-429d-bdba-b8d9ff7f003d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
private theorem erase_eq_and_apply_eq_iff_eq_add_single {ι : Type} (i : ι) (k : ℕ) (s u : ι →₀ ℕ) (hu : u i = 0) :
    (s.erase i = u ∧ s i = k) ↔ s = u + Finsupp.single i k := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu, h2]
    · have h3 : (s.erase i) j = u j := by rw [h1]
      rw [Finsupp.erase_ne hj] at h3
      simp [Ne.symm hj, h3]
  · rintro rfl
    refine ⟨?_, by simp [hu]⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu]
    · simp [Finsupp.erase_ne hj]
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) (u : ι →₀ ℕ) :
    (coeffIn i k f).coeff u = if u i = 0 then f.coeff (u + Finsupp.single i k) else 0 := by
  classical
  unfold coeffIn
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with hu
  · have hsp := (erase_eq_and_apply_eq_iff_eq_add_single i k (u + Finsupp.single i k) u hu).mpr rfl
    rw [Finset.sum_eq_single (u + Finsupp.single i k)]
    · rw [if_pos hsp.1]
    · intro t ht hne
      rw [if_neg]
      intro hte
      exact hne ((erase_eq_and_apply_eq_iff_eq_add_single i k t u hu).mp ⟨hte, (Finset.mem_filter.mp ht).2⟩)
    · intro hnot
      rw [if_pos hsp.1]
      by_contra hc
      exact hnot (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hc, hsp.2⟩)
  · apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    rintro rfl
    exact hu (by simp)
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
