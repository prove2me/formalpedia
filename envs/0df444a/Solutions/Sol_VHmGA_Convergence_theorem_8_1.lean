-- Prove2me | solution 1 for VHmGA.Convergence.theorem_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:11:58.571485+00:00
-- url     : https://prove2.me/submissions/3e93abea-a852-4101-9300-d7c4d7de0c02

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_VHmGA_Convergence_Defs
import Theorems.Thm_VHmGA_Convergence_eq_25

set_option autoImplicit false
open MeasureTheory

namespace VHmGA.Convergence

theorem _root_.solution {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {L η : ℝ}
    {σ σDP σa α : ℝ} {w1 : EuclideanSpace ℝ (Fin d)}
    {w gt : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hη : 0 < η) (hηL : η ≤ 1 / L) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : IsVerifiedSGDRun μ g (fun _ => η) w1 w gt m (sigmaTotalSq σ σDP σa α))
    {Fstar : ℝ} (hFstar : ∀ x, Fstar ≤ F x) (T : ℕ) (hT : 1 ≤ T) :
    (∀ t ∈ Finset.Icc 1 T, Integrable (fun ω => ‖g (w t ω)‖ ^ 2) μ) ∧
    1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, ∫ ω, ‖g (w t ω)‖ ^ 2 ∂μ ≤
      2 * (F w1 - Fstar) / (η * T) + L * η * sigmaTotalSq σ σDP σa α := by
  letI : IsProbabilityMeasure μ := hrun.isProbabilityMeasure
  let E : ℕ → ℝ := fun t => ∫ ω, F (w t ω) ∂μ
  let G : ℕ → ℝ := fun t => ∫ ω, ‖g (w t ω)‖ ^ 2 ∂μ
  let c : ℝ := L * η ^ 2 / 2 * sigmaTotalSq σ σDP σa α

  have hstep (t : ℕ) (ht : 1 ≤ t) :
      Integrable (fun ω => F (w t ω)) μ ∧
      Integrable (fun ω => F (w (t + 1) ω)) μ ∧
      Integrable (fun ω => ‖g (w t ω)‖ ^ 2) μ ∧
      η / 2 * G t ≤ E t - E (t + 1) + c := by
    exact (VHmGA.Convergence.eq_25 hF hL hη hηL hα0 hα1 hrun t ht)

  have hsum : ∀ T : ℕ,
      η / 2 * (∑ t ∈ Finset.Icc 1 T, G t) ≤
        E 1 - E (T + 1) + (T : ℝ) * c := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        have hsplit : Finset.Icc 1 (T + 1) =
            insert (T + 1) (Finset.Icc 1 T) := by
          ext u
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : T + 1 ∉ Finset.Icc 1 T := by
          simp only [Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert hnot]
        have hs := (hstep (T + 1) (by omega)).2.2.2
        push_cast
        nlinarith [ih, hs]

  have hE1 : E 1 = F w1 := by
    simp only [E]
    rw [show w 1 = fun _ => w1 from hrun.init]
    simp

  have hnext : Integrable (fun ω => F (w (T + 1) ω)) μ :=
    (hstep T hT).2.1

  have hElower : Fstar ≤ E (T + 1) := by
    have hconst : Integrable (fun _ : Ω => Fstar) μ := integrable_const _
    calc
      Fstar = ∫ _ : Ω, Fstar ∂μ := by rw [integral_const]; simp
      _ ≤ ∫ ω, F (w (T + 1) ω) ∂μ := by
        exact integral_mono_ae hconst hnext
          (Filter.Eventually.of_forall (fun ω => hFstar (w (T + 1) ω)))
      _ = E (T + 1) := rfl

  have hbound : η / 2 * (∑ t ∈ Finset.Icc 1 T, G t) ≤
      (F w1 - Fstar) + (T : ℝ) * c := by
    have hs := hsum T
    rw [hE1] at hs
    linarith

  have hTpos : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast (show 0 < T by omega)
  have hfactor : 0 ≤ 2 / (η * (T : ℝ)) := by
    exact (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hη hTpos)).le

  have hfinal :
      1 / (T : ℝ) * (∑ t ∈ Finset.Icc 1 T, G t) ≤
        2 * (F w1 - Fstar) / (η * (T : ℝ)) +
          L * η * sigmaTotalSq σ σDP σa α := by
    calc
      1 / (T : ℝ) * (∑ t ∈ Finset.Icc 1 T, G t) =
          (2 / (η * (T : ℝ))) *
            (η / 2 * (∑ t ∈ Finset.Icc 1 T, G t)) := by
        field_simp [hη.ne', hTpos.ne'] <;> ring
      _ ≤ (2 / (η * (T : ℝ))) * ((F w1 - Fstar) + (T : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hbound hfactor
      _ = 2 * (F w1 - Fstar) / (η * (T : ℝ)) +
          L * η * sigmaTotalSq σ σDP σa α := by
        dsimp only [c]
        field_simp [hη.ne', hTpos.ne'] <;> ring

  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hstep t (Finset.mem_Icc.mp ht).1).2.2.1
  · simpa only [G] using hfinal

end VHmGA.Convergence
