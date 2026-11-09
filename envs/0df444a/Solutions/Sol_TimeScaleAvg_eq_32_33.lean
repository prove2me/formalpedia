-- Prove2me | solution 1 for TimeScaleAvg.eq_32_33
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:12:28.143266+00:00
-- url     : https://prove2.me/submissions/6483ee4b-c045-48e1-b620-f2c3b4038831

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
import Definitions.Def_TimeScaleAvg_IsRescaledSDSolution
import Definitions.Def_TimeScaleAvg_yTraj
import Definitions.Def_TimeScaleAvg_yTrajDeriv

open Filter Topology MeasureTheory

open TimeScaleAvg in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    IsRescaledSDSolution f α s₀ (yTraj α x xdot) (yTrajDeriv f α x xdot) ∧
      yTraj α x xdot s₀ = x s₀ + (s₀ / (α - 1)) • xdot s₀ ∧
      ∀ s ∈ Set.Ici s₀, xdot s + ((α - 1) / s) • (x s - yTraj α x xdot s) = 0 := by
  have hα1 : α - 1 ≠ 0 := by linarith
  refine ⟨fun s hs => ?_, rfl, fun s hs => ?_⟩
  · have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    obtain ⟨h1, h2, h3⟩ := hx s hs
    have hd := h1.add (((hasDerivWithinAt_id s (Set.Ici s₀)).div_const (α - 1)).smul h2)
    have hdd : xddot s = -((α / s) • xdot s) - gradient f (yTraj α x xdot s) := by
      unfold yTraj
      rw [eq_sub_iff_add_eq, ← sub_eq_zero]
      rw [← h3]; abel
    have hderiv : xdot s + ((id s / (α - 1)) • xddot s + (1 / (α - 1)) • xdot s) =
        yTrajDeriv f α x xdot s := by
      rw [hdd]
      unfold yTrajDeriv
      have hc : (s / (α - 1)) * (α / s) = 1 + 1 / (α - 1) := by
        field_simp; ring
      simp only [id]
      rw [smul_sub, smul_neg, smul_smul, hc, add_smul, one_smul]
      abel
    refine ⟨hd.congr_deriv hderiv, ?_⟩
    unfold yTrajDeriv
    abel
  · have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    unfold yTraj
    have hc : (α - 1) / s * (s / (α - 1)) = 1 := by field_simp
    rw [sub_add_cancel_left, smul_neg, smul_smul, hc, one_smul]
    abel
