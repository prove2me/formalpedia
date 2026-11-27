-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.norm_th_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:20.366369+00:00
-- url     : https://prove2.me/submissions/933f7690-2e9f-4583-88d9-940fdf2631f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
theorem _root_.solution {y : ι → Fin 2 → Fin 2 → ℝ} (hy : ‖y‖ < 1) (τ : ι) (i k : Fin 2) :
    ‖th y τ i k‖ < 2 := by
  have h1 : ∀ a b : Fin 2, |y τ a b| < 1 := fun a b => by
    have h := (norm_le_pi_norm (y τ a) b).trans ((norm_le_pi_norm (y τ) a).trans (norm_le_pi_norm y τ))
    rw [Real.norm_eq_abs] at h
    linarith
  have hadd : ∀ a b : ℝ, |a| < 1 → |b| < 1 → ‖(a : ℂ) + I * b‖ < 2 := fun a b ha hb => by
    have e1 : ‖(a : ℂ)‖ = |a| := by simp
    have e2 : ‖I * (b : ℂ)‖ = |b| := by simp
    have := norm_add_le (a : ℂ) (I * b)
    linarith
  have hsub : ∀ a b : ℝ, |a| < 1 → |b| < 1 → ‖(a : ℂ) - I * b‖ < 2 := fun a b ha hb => by
    have e1 : ‖(a : ℂ)‖ = |a| := by simp
    have e2 : ‖I * (b : ℂ)‖ = |b| := by simp
    have := norm_sub_le (a : ℂ) (I * b)
    linarith
  simp only [th]
  split_ifs
  · have e1 : ‖(y τ i k : ℂ)‖ = |y τ i k| := by simp
    have := h1 i k
    linarith
  · exact hadd _ _ (h1 i k) (h1 k i)
  · exact hsub _ _ (h1 k i) (h1 i k)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
