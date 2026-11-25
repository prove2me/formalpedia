-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:11.148681+00:00
-- url     : https://prove2.me/submissions/c0c89ef1-242e-4b18-9aeb-25b316ad7dc5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paIso_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (hP : Ext.PackingCount) (Y : GT ι) {q : ℕ} {R0 : ℝ} (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) (R : ℝ) (hR : R0 ≤ R)
    (S : Finset ({γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} : Set (lat Y.b)))
    (hS : ∀ i ∈ S, Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖ ≤ R) :
    (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * Fintype.card ι) := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨i₀, hi₀⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    have : 0 < R := lt_of_lt_of_le hR0 hR
    positivity
  set c := Real.sqrt (q * Real.pi) with hc
  have hcpos : 0 < c := by
    have h1 := hlat _ (i₀ : lat Y.b).2 i₀.2
    by_contra hle
    rw [not_lt] at hle
    have : c * ‖((i₀ : lat Y.b) : EuclideanSpace ℂ ι)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (norm_nonneg _)
    linarith
  obtain ⟨e⟩ := (paIso_ex : Nonempty (EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * Fintype.card ι))))
  let g : ({γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} : Set (lat Y.b)) →
      EuclideanSpace ℝ (Fin (2 * Fintype.card ι)) := fun i => c • e ((i : lat Y.b) : EuclideanSpace ℂ ι)
  have hg : Function.Injective g := by
    intro i j hij
    have h1 : e ((i : lat Y.b) : EuclideanSpace ℂ ι) = e ((j : lat Y.b) : EuclideanSpace ℂ ι) :=
      smul_right_injective _ hcpos.ne' hij
    exact Subtype.ext (Subtype.ext (e.injective h1))
  have hcard : ((S.image g).card : ℝ) ≤ (3 * R / R0) ^ (2 * Fintype.card ι) := by
    refine hP (2 * Fintype.card ι) (S.image g) R0 R hR0 hR ?_ ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hcpos]
      exact hS i hi
    · intro x hx y hy hxy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      have hij : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ≠ 0 := by
        intro h0
        apply hxy
        rw [sub_eq_zero] at h0
        simp only [g, h0]
      have hmem : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ∈ lat Y.b :=
        Submodule.sub_mem _ (i : lat Y.b).2 (j : lat Y.b).2
      have hd : dist (g i) (g j) =
          c * ‖((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι)‖ := by
        simp only [g, dist_eq_norm, ← smul_sub, ← map_sub, norm_smul, LinearIsometryEquiv.norm_map,
          Real.norm_eq_abs, abs_of_pos hcpos]
      rw [hd]
      exact hlat _ hmem hij
  rwa [Finset.card_image_of_injective S hg] at hcard
end ReciprocityTheory.ChartRestriction.G.I2.FPw
