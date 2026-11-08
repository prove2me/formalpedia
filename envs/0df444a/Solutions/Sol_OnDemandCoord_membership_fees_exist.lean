-- Prove2me | solution 1 for OnDemandCoord.membership_fees_exist
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:35:19.930428+00:00
-- url     : https://prove2.me/submissions/b889febd-fe3a-421c-8aa3-ac6bf6e38c6a

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

open MeasureTheory ProbabilityTheory

open OnDemandCoord in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp : Fin n → ℝ) (hQp : M.IsPermanentBenchmark Qp)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar) :
    ∃ r : Fin n → ℝ, M.FeeLower Qstar ηstar (M.mParam Qstar) r ∧
      ∀ i, M.FeeUpper Qp Qstar (M.mParam Qstar) r i := by
  haveI := M.isProb
  -- Qp is nonnegative
  have hQp0 : 0 ≤ Qp := by
    intro i
    by_contra hneg
    push_neg at hneg
    have hneg' : Qp i < 0 := hneg
    have hs : MeasurableSet {ω | Qp i < M.X i ω} :=
      measurableSet_lt measurable_const (M.measurable_X i)
    have hae : ∀ᵐ ω ∂P, ω ∈ {ω | Qp i < M.X i ω} :=
      (M.nonneg_X i).mono (fun ω h => by show Qp i < M.X i ω; linarith [hneg'])
    have h0 : P {ω | Qp i < M.X i ω}ᶜ = 0 := ae_iff.mp hae
    have h1 : P {ω | Qp i < M.X i ω} = 1 := (prob_compl_eq_zero_iff hs).mp h0
    have hF : M.Fbar i (Qp i) = 1 := by
      unfold Model.Fbar; rw [measureReal_def, h1]; simp
    have := hQp i
    rw [hF, mul_one] at this
    linarith [M.c_lt_p]
  have hS : M.S M.τl = 0 := by
    unfold Model.S; rw [M.G_of_le _ le_rfl, mul_zero]
  have hvac0 : ∀ Q i ω, 0 ≤ M.vac Q i ω := fun _ _ _ => le_max_right _ _
  have hint : ∀ i, Integrable (fun ω => M.vac Qp i ω) P := fun i =>
    ((M.integrable_X i).sub (integrable_const (Qp i))).pos_part
  have hCp : M.C Qp M.τl = ∑ i, M.hp Qp i := by
    unfold Model.C Model.hp Model.mean
    rw [hS]
    have e : (fun ω => max (∑ i, M.vac Qp i ω - 0) 0) = fun ω => ∑ i, M.vac Qp i ω := by
      funext ω
      rw [sub_zero, max_eq_left (Finset.sum_nonneg (fun i _ => hvac0 _ _ _))]
    rw [e, integral_finsetSum _ (fun i _ => hint i), Finset.sum_add_distrib, Finset.mul_sum,
      Finset.mul_sum]
    ring
  have hC := hopt.2 Qp M.τl hQp0
  rw [hCp] at hC
  refine ⟨fun i => M.hp Qp i - (M.p * (1 - M.mParam Qstar i) * M.mean Qstar i + M.c * Qstar i),
    ?_, fun i => le_refl _⟩
  unfold Model.FeeLower
  calc M.C Qstar ηstar - M.c * ∑ i, Qstar i -
        M.p * ∑ i, (1 - M.mParam Qstar i) * M.mean Qstar i
      ≤ ∑ i, M.hp Qp i - M.p * ∑ i, (1 - M.mParam Qstar i) * M.mean Qstar i -
          M.c * ∑ i, Qstar i := by linarith
    _ = ∑ i, (M.hp Qp i -
          (M.p * (1 - M.mParam Qstar i) * M.mean Qstar i + M.c * Qstar i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
