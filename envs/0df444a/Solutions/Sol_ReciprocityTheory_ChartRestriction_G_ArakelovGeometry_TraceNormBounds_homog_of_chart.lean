-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.homog_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:06.177016+00:00
-- url     : https://prove2.me/submissions/9bf7f7f0-ec9a-4dd3-ac8d-38d439f0d2dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_chart_elem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) (hl : x (e l) ≠ 0) :
    ∃ N0, ∀ N, N0 ≤ N → ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H.IsHomogeneous N ∧
      x (e l) ^ N * (a : Ω) = MvPolynomial.aeval (x ∘ e) H := by
  obtain ⟨g, hg⟩ := chart_elem x e l a ha
  rw [hg]
  clear hg
  induction g using MvPolynomial.induction_on
  · rename_i c
    refine ⟨0, fun N _ => ⟨MvPolynomial.C c * MvPolynomial.X l ^ N, ?_, ?_⟩⟩
    · simpa using (MvPolynomial.isHomogeneous_C (Fin (D + 1)) c).mul (MvPolynomial.isHomogeneous_X_pow l N)
    · simp [mul_comm]
  · rename_i p q hp hq
    obtain ⟨N1, h1⟩ := hp
    obtain ⟨N2, h2⟩ := hq
    refine ⟨max N1 N2, fun N hN => ?_⟩
    obtain ⟨H1, hH1, e1⟩ := h1 N (le_of_max_le_left hN)
    obtain ⟨H2, hH2, e2⟩ := h2 N (le_of_max_le_right hN)
    exact ⟨H1 + H2, hH1.add hH2, by rw [map_add, mul_add, e1, e2, map_add]⟩
  · rename_i p k hp
    obtain ⟨N1, h1⟩ := hp
    refine ⟨N1 + 1, fun N hN => ?_⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨H, hH, e1⟩ := h1 N' (by omega)
    refine ⟨H * MvPolynomial.X k.1, hH.mul (MvPolynomial.isHomogeneous_X ℤ k.1), ?_⟩
    rw [map_mul, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_X, ← e1]
    simp only [Function.comp]
    field_simp
    ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
