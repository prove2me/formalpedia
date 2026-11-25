-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.map_ptIdeal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:29.920841+00:00
-- url     : https://prove2.me/submissions/ee6859c2-7c29-4dc3-a3db-05a05184fa8d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    (χ : locRing K p →+* DualNumber ℂ)
    (hχ : ∀ i, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) = 0) :
    ∀ x ∈ ptIdeal p, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = 0 := by
  intro x hx
  have h1 : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x ∈
      Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) := by
    rw [hr]
    exact Ideal.mem_map_of_mem _ hx
  have h2 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) ≤
      RingHom.ker χ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hχ i
  exact h2 h1
end ReciprocityTheory.AnForm.R
