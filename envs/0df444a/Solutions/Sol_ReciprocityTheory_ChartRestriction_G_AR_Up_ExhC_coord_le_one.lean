-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.coord_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:31.276242+00:00
-- url     : https://prove2.me/submissions/30d1f899-9b47-47f5-ab9e-b1c515c138b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution {w : V (nD f p q)} (hw : w ∈ Dset f p q) (j : Fin (nD f p q)) :
    ‖w j‖ ≤ 1 := by
  obtain ⟨⟨k, ab⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective ab
  have h := (hw k).diag_pos (i := a)
  rw [Complex.lt_def] at h
  have h1 := h.1
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq,
    Complex.sub_re, Complex.one_re, Complex.re_sum, Complex.zero_re, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re] at h1
  have h2 : Complex.normSq (Zof w k a b) ≤ ∑ c, Complex.normSq (Zof w k a c) :=
    Finset.single_le_sum (f := fun c => Complex.normSq (Zof w k a c))
      (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  have h3 : ‖Zof w k a b‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]; linarith
  have h4 : ‖Zof w k a b‖ ≤ 1 := by nlinarith [norm_nonneg (Zof w k a b)]
  exact h4
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
