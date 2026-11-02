-- Prove2me | solution 1 for RotationContagion.Rotation.relaxed_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:59:46.873321+00:00
-- url     : https://prove2.me/submissions/bdf634bc-b1b7-4e12-bde9-adadee2332fc

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model
import Theorems.Thm_RotationContagion_Rotation_lemma_3

open MeasureTheory Set Filter

namespace RotContRelaxed

open RotationContagion.Rotation

lemma loss_bdd (P : Params) (x : ℝ) : |loss P x| ≤ 1 := by
  unfold loss
  have h := Real.exp_pos (P.γ * (x - b P))
  rw [abs_le]
  constructor
  · have : 0 ≤ Real.exp (P.γ * (x - b P)) / (1 + Real.exp (P.γ * (x - b P))) := by positivity
    linarith
  · rw [div_le_one (by linarith)]; linarith

lemma loss_cont (P : Params) : Continuous (loss P) := by
  unfold loss
  have : ∀ x, 1 + Real.exp (P.γ * (x - b P)) ≠ 0 := fun x => by positivity
  fun_prop (disch := exact this _)

lemma int_rel (P : Params) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (relaxedObj P) ν := by
  have hc : Continuous (relaxedObj P) := by
    unfold relaxedObj
    exact (loss_cont P).add ((loss_cont P).comp (continuous_const.sub continuous_id))
  refine Integrable.of_bound hc.aestronglyMeasurable 2 (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs]
  unfold relaxedObj
  calc |loss P τ + loss P (P.R - τ)| ≤ |loss P τ| + |loss P (P.R - τ)| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add (loss_bdd P _) (loss_bdd P _)
    _ = 2 := by norm_num

lemma int_mix (f : ℝ → ℝ) (a c : ℝ) :
    ∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac a + (1 / 2 : ENNReal) • Measure.dirac c) =
      (1 / 2) * f a + (1 / 2) * f c := by
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp

end RotContRelaxed

open RotationContagion.Rotation RotContRelaxed in
theorem solution (P : Params) (hP : P.Standing) :
    (P.R / 2 < b P →
      ∫ x, x ∂(Measure.dirac (P.R / 2)) = P.R / 2 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc 0 P.R)ᶜ = 0 →
        ∫ x, x ∂ν = P.R / 2 →
          ∫ τ, relaxedObj P τ ∂(Measure.dirac (P.R / 2)) ≤ ∫ τ, relaxedObj P τ ∂ν) ∧
    (b P < P.R / 2 →
      ∫ x, x ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac P.R) =
          P.R / 2 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc 0 P.R)ᶜ = 0 →
        ∫ x, x ∂ν = P.R / 2 →
          ∫ τ, relaxedObj P τ
              ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac P.R) ≤
            ∫ τ, relaxedObj P τ ∂ν) := by
  have hR := hP.2.2
  obtain ⟨h3a, h3b⟩ := lemma_3 P hP
  constructor
  · intro hlt
    obtain ⟨hanti, hmono⟩ := h3a hlt
    refine ⟨by simp [integral_dirac], fun ν hν _ _ => ?_⟩
    rw [integral_dirac]
    calc relaxedObj P (P.R / 2) = ∫ _τ, relaxedObj P (P.R / 2) ∂ν := by simp
      _ ≤ ∫ τ, relaxedObj P τ ∂ν := by
        refine integral_mono (integrable_const _) (int_rel P ν) (fun τ => ?_)
        rcases le_total τ (P.R / 2) with h | h
        · exact hanti.antitoneOn (show τ ∈ Iic (P.R / 2) from h) (Set.mem_Iic.2 le_rfl) h
        · exact hmono.monotoneOn (Set.mem_Ici.2 le_rfl) (show τ ∈ Ici (P.R / 2) from h) h
  · intro hlt
    obtain ⟨hmono, hanti⟩ := h3b hlt
    have hsym : relaxedObj P P.R = relaxedObj P 0 := by
      unfold relaxedObj; simp only [sub_self, sub_zero]; ring
    have hmin : ∀ τ ∈ Icc 0 P.R, relaxedObj P 0 ≤ relaxedObj P τ := by
      intro τ hτ
      rcases le_total τ (P.R / 2) with h | h
      · exact hmono.monotoneOn (show (0:ℝ) ∈ Iic (P.R / 2) by simp only [mem_Iic]; linarith)
          (show τ ∈ Iic (P.R / 2) from h) hτ.1
      · rw [← hsym]
        exact hanti.antitoneOn (show τ ∈ Ici (P.R / 2) from h)
          (show P.R ∈ Ici (P.R / 2) by simp only [mem_Ici]; linarith) hτ.2
    refine ⟨by rw [int_mix (fun x => x)]; ring, fun ν hν hsupp _ => ?_⟩
    rw [int_mix (relaxedObj P), hsym]
    have hae : ∀ᵐ τ ∂ν, τ ∈ Icc 0 P.R := by
      rw [ae_iff]
      simpa [Set.compl_def] using hsupp
    calc (1 / 2) * relaxedObj P 0 + (1 / 2) * relaxedObj P 0
        = ∫ _τ, relaxedObj P 0 ∂ν := by simp; ring
      _ ≤ ∫ τ, relaxedObj P τ ∂ν := by
        refine integral_mono_ae (integrable_const _) (int_rel P ν) ?_
        filter_upwards [hae] with τ hτ using hmin τ hτ
