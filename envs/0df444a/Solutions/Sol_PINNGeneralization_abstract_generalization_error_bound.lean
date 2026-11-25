-- Prove2me | solution 1 for PINNGeneralization.abstract_generalization_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T10:05:20.706751+00:00
-- url     : https://prove2.me/submissions/7b869d61-d976-4441-aa83-ad9c160d8be1

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory
open PINNGeneralization

theorem solution {n m : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (P : AbstractPDE n m X) (hP : P.Hyp)
    (Z : Submodule ℝ X) (zNorm : X → ℝ) (Cpde : ℝ → ℝ → ℝ) (hstab : P.IsStable Z zNorm Cpde)
    (u : X) (hu : P.IsSolution u) (huZ : u ∈ Z) (ustar : X) (hustar : ustar ∈ Z)
    (Zs : Submodule ℝ (Pt n → ℝ)) (zsNorm : (Pt n → ℝ) → ℝ) (hZs : IsNormOn Zs zsNorm)
    (Cquad : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (Q : QuadRule (Pt n)) (hQ : Q.IsOn P.dom) (hN : 0 < Q.N)
    (hquad : QuadErrorBound volume P.dom (Zs : Set (Pt n → ℝ)) zsNorm Cquad α Q)
    (hR : (fun y => ‖P.residual ustar y‖ ^ P.p) ∈ Zs) :
    ‖u - ustar‖ ≤ Cpde (zNorm u) (zNorm ustar) * trainingError Q P.p (P.residual ustar) +
      Cpde (zNorm u) (zNorm ustar) *
        Cquad (zsNorm fun y => ‖P.residual ustar y‖ ^ P.p) ^ (1 / P.p) *
          (Q.N : ℝ) ^ (-α / P.p) := by
  obtain ⟨_, hp1, _, hYsLp, _, hDmap, hf, _⟩ := hP
  obtain ⟨_, hZX, _, hCpos, hstab'⟩ := hstab
  have hp0 : 0 < P.p := by linarith
  set R := P.residual ustar with hRdef
  have h1 := hstab' u huZ ustar hustar
  have hRY : R ∈ P.Ys := by
    have hD : P.D ustar ∈ P.Ys := hDmap _ (hZX hustar)
    have : R = P.D ustar - P.f := rfl
    rw [this]
    exact P.Ys.sub_mem hD hf
  have hae : P.D u - P.D ustar =ᵐ[volume.restrict P.dom] -R := by
    filter_upwards [hu.2] with y hy
    simp [hRdef, AbstractPDE.residual, hy]
  have hL : PINNGeneralization.lpNorm P.dom P.p (P.D u - P.D ustar) = PINNGeneralization.lpNorm P.dom P.p R := by
    unfold PINNGeneralization.lpNorm; rw [eLpNorm_congr_ae hae, eLpNorm_neg]
  have hRmem : MemLp R (ENNReal.ofReal P.p) (volume.restrict P.dom) := hYsLp R hRY
  have hLeq : PINNGeneralization.lpNorm P.dom P.p R = (∫ y in P.dom, ‖R y‖ ^ P.p) ^ (1 / P.p) := by
    unfold PINNGeneralization.lpNorm
    rw [hRmem.eLpNorm_eq_integral_rpow_norm (by simp; linarith) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by
        apply Real.rpow_nonneg
        exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    simp [ENNReal.toReal_ofReal hp0.le, one_div]
  obtain ⟨_, hq⟩ := hquad _ hR
  set I := ∫ y in P.dom, ‖R y‖ ^ P.p with hIdef
  set Sq := Q.sum fun y => ‖R y‖ ^ P.p with hSqdef
  set c := Cquad (zsNorm fun y => ‖R y‖ ^ P.p) with hcdef
  have hNpos : (0 : ℝ) < (Q.N : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hc0 : 0 ≤ c := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hNpos
    linarith [abs_nonneg (I - Sq)]
  have hSq : 0 ≤ Sq := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hQ.2 i) (Real.rpow_nonneg (norm_nonneg _) _)
  have hI0 : 0 ≤ I := integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _
  have hI : I ≤ Sq + c * (Q.N : ℝ) ^ (-α) := by
    have := le_abs_self (I - Sq); linarith
  have hcN : 0 ≤ c * (Q.N : ℝ) ^ (-α) := mul_nonneg hc0 hNpos.le
  have hq1 : 0 ≤ 1 / P.p := by positivity
  have hq2 : 1 / P.p ≤ 1 := by rw [div_le_one hp0]; exact hp1
  have hsub : (Sq + c * (Q.N : ℝ) ^ (-α)) ^ (1 / P.p) ≤
      Sq ^ (1 / P.p) + (c * (Q.N : ℝ) ^ (-α)) ^ (1 / P.p) := by
    have := NNReal.rpow_add_le_add_rpow ⟨Sq, hSq⟩ ⟨_, hcN⟩ hq1 hq2
    exact_mod_cast this
  have hsplit : (c * (Q.N : ℝ) ^ (-α)) ^ (1 / P.p) = c ^ (1 / P.p) * (Q.N : ℝ) ^ (-α / P.p) := by
    rw [Real.mul_rpow hc0 hNpos.le, ← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div]
  have hlp : PINNGeneralization.lpNorm P.dom P.p R ≤ trainingError Q P.p R + c ^ (1 / P.p) * (Q.N : ℝ) ^ (-α / P.p) := by
    rw [hLeq]
    calc I ^ (1 / P.p) ≤ (Sq + c * (Q.N : ℝ) ^ (-α)) ^ (1 / P.p) :=
          Real.rpow_le_rpow hI0 hI hq1
      _ ≤ _ := hsub
      _ = _ := by rw [hsplit]; rfl
  have hC := hCpos (zNorm u) (zNorm ustar)
  calc ‖u - ustar‖ ≤ Cpde (zNorm u) (zNorm ustar) * PINNGeneralization.lpNorm P.dom P.p (P.D u - P.D ustar) := h1
    _ = Cpde (zNorm u) (zNorm ustar) * PINNGeneralization.lpNorm P.dom P.p R := by rw [hL]
    _ ≤ Cpde (zNorm u) (zNorm ustar) *
        (trainingError Q P.p R + c ^ (1 / P.p) * (Q.N : ℝ) ^ (-α / P.p)) :=
          mul_le_mul_of_nonneg_left hlp hC.le
    _ = _ := by ring
