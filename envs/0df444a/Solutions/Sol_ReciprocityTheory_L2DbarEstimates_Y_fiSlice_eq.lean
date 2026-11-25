-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiSlice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:42.876804+00:00
-- url     : https://prove2.me/submissions/cafcad3d-8a84-4873-be94-7f401a70d70d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiG_differentiableOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiG_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (b : Fin (n + 1) → ℝ) (β : ℝ)
    (hseg : ∀ t ∈ Set.uIcc (b i) β, Function.update b i t ∈ Ω) (y : Fin n → ℝ) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I) =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
          (Function.update b i β k : ℂ) * Complex.I) := by
  set base : Fin (n + 1) → ℂ :=
    fun k => ((i.insertNth (0 : ℝ) y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I
  set P : ℂ → Fin (n + 1) → ℂ := fun z k => if k = i then z else base k with hPdef
  have hP : ∀ t c : ℝ, (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (Function.update b i c k : ℂ) * Complex.I) = P (t + c * Complex.I) := by
    intro t c
    funext k
    by_cases hk : k = i
    · subst hk
      simp [P]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [P, base, hk]
  have hb : Function.update b i (b i) = b := Function.update_eq_self i b
  have hPim : ∀ z : ℂ, (fun k => (P z k).im) = Function.update b i z.im := by
    intro z
    funext k
    by_cases hk : k = i
    · subst hk
      simp [P]
    · simp [P, base, hk]
  have hPdiff : Differentiable ℂ P := by
    refine differentiable_pi.2 fun k => ?_
    by_cases hk : k = i
    · simp only [P, hk, if_true]
      exact differentiable_id
    · simp only [P, hk, if_false]
      exact differentiable_const _
  set g : ℂ → ℂ := fun z => fiG h ν (P z) with hgdef
  have hgd : DifferentiableOn ℂ g ([[(0 : ℝ), 1]] ×ℂ [[b i, β]]) := by
    refine (fiG_differentiableOn hh ν).comp hPdiff.differentiableOn ?_
    intro z hz
    show (fun k => (P z k).im) ∈ Ω
    rw [hPim]
    exact hseg _ hz.2
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨0, b i⟩ ⟨1, β⟩ hgd
  dsimp only at hC
  have hv : ∫ y in (b i)..β, g (((1 : ℝ) : ℂ) + y * Complex.I) =
      ∫ y in (b i)..β, g (((0 : ℝ) : ℂ) + y * Complex.I) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    show fiG h ν (P (((1 : ℝ) : ℂ) + t * Complex.I)) = fiG h ν (P (((0 : ℝ) : ℂ) + t * Complex.I))
    have hm : P (((1 : ℝ) : ℂ) + t * Complex.I) = P (((0 : ℝ) : ℂ) + t * Complex.I) +
        fun k => ((Pi.single i (1 : ℤ) : Fin (n + 1) → ℤ) k : ℂ) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [P]
        ring
      · simp [P, hk]
    rw [hm]
    apply fiG_periodic hper
    show (fun k => (P _ k).im) ∈ Ω
    rw [hPim]
    have him : ((((0 : ℝ) : ℂ) + t * Complex.I) : ℂ).im = t := by simp
    rw [him]
    exact hseg t ht
  have hh1 : ∫ x in (0 : ℝ)..1, g (x + (b i) * Complex.I) =
      ∫ x in (0 : ℝ)..1, g (x + β * Complex.I) := by
    rw [hv, add_sub_cancel_right, sub_eq_zero] at hC
    exact hC
  have e1 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (b k : ℂ) * Complex.I) = g (t + (b i) * Complex.I) := by
    intro t
    have := hP t (b i)
    rw [hb] at this
    simp only [g]
    rw [this]
  have e2 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (Function.update b i β k : ℂ) * Complex.I) = g (t + β * Complex.I) := by
    intro t
    simp only [g]
    rw [hP]
  simp only [e1, e2]
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  exact hh1
end ReciprocityTheory.L2DbarEstimates.Y
