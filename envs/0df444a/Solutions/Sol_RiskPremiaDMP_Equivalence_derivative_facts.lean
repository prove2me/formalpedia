-- Prove2me | solution 1 for RiskPremiaDMP.Equivalence.derivative_facts
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:16:37.020192+00:00
-- url     : https://prove2.me/submissions/c2583244-d202-4b49-866e-d5d706a7958b

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

open RiskPremiaDMP.Equivalence

namespace Aux_RiskPremia_DF
open RiskPremiaDMP.Equivalence

theorem dshift (F : ℝ → ℝ) (a x : ℝ) : deriv (fun x => F (x + a)) x = deriv F (x + a) :=
  deriv_comp_add_const F a x

theorem drefl (F : ℝ → ℝ) (c b x : ℝ) :
    deriv (fun x => F (c * (b - x))) x = -c * deriv F (c * (b - x)) := by
  have h3 := deriv_comp_const_sub (fun u => F (c * u)) b x
  rw [h3]
  have h2 : deriv (fun u => F (c * u)) (b - x) = c • deriv F (c * (b - x)) := deriv_comp_mul_left c F (b - x)
  rw [h2, smul_eq_mul]
  ring

theorem d1_eq (G : ℝ → ℝ → ℝ) (K sh c b y η : ℝ) :
    d1 (fun y η => K * G (y + sh) (c * (b - η))) y η = K * d1 G (y + sh) (c * (b - η)) := by
  unfold d1
  rw [deriv_const_mul_field']
  simp only
  rw [dshift (fun y' => G y' (c * (b - η)))]

theorem d11_eq (G : ℝ → ℝ → ℝ) (K sh c b y η : ℝ) :
    d11 (fun y η => K * G (y + sh) (c * (b - η))) y η = K * d11 G (y + sh) (c * (b - η)) := by
  have h := fun y' => d1_eq G K sh c b y' η
  unfold d1 at h
  unfold d11
  simp only [h]
  rw [deriv_const_mul_field']
  simp only
  rw [dshift (fun y' => deriv (fun y'' => G y'' (c * (b - η))) y')]

theorem d2_eq (G : ℝ → ℝ → ℝ) (K sh c b y η : ℝ) :
    d2 (fun y η => K * G (y + sh) (c * (b - η))) y η = -c * K * d2 G (y + sh) (c * (b - η)) := by
  unfold d2
  rw [deriv_const_mul_field']
  simp only
  rw [drefl (fun m => G (y + sh) m)]
  ring

theorem d22_eq (G : ℝ → ℝ → ℝ) (K sh c b y η : ℝ) :
    d22 (fun y η => K * G (y + sh) (c * (b - η))) y η = c ^ 2 * K * d22 G (y + sh) (c * (b - η)) := by
  have h := fun η' => d2_eq G K sh c b y η'
  unfold d2 at h
  unfold d22
  simp only [h]
  rw [deriv_const_mul_field']
  simp only
  rw [drefl (fun m => deriv (fun m'' => G (y + sh) m'') m)]
  ring

end Aux_RiskPremia_DF

theorem solution (P : RPParams) (hP : P.Standing) (S SQ : ℝ → ℝ → ℝ)
    (hSQ : ContDiff ℝ 2 (Function.uncurry SQ))
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η) (y η : ℝ) :
    d1 S y η = Real.exp (-shift P) * d1 SQ (toYQ P y) (toMuQ P η) ∧
      d11 S y η = Real.exp (-shift P) * d11 SQ (toYQ P y) (toMuQ P η) ∧
      d2 S y η = -(P.σy / P.κy) * Real.exp (-shift P) * d2 SQ (toYQ P y) (toMuQ P η) ∧
      d22 S y η
        = P.σy ^ 2 / P.κy ^ 2 * Real.exp (-shift P) * d22 SQ (toYQ P y) (toMuQ P η) := by
  open Aux_RiskPremia_DF in
  have hS : S = fun y η => Real.exp (-shift P) * SQ (y + shift P) (P.σy / P.κy * (P.ηbar - η)) := by
    funext y η
    have h := h24a y η
    have e : toMuQ P η = P.σy / P.κy * (P.ηbar - η) := by unfold toMuQ; ring
    rw [e] at h
    unfold toYQ at h
    rw [h, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have e : toMuQ P η = P.σy / P.κy * (P.ηbar - η) := by unfold toMuQ; ring
  have e2 : toYQ P y = y + shift P := rfl
  rw [e, e2, hS, d1_eq, d11_eq, d2_eq, d22_eq]
  refine ⟨rfl, rfl, by ring, by ring⟩
