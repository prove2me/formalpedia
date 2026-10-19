-- Prove2me | solution 1 for STVFriedmann.corollary1_order2_SM_eigenpairs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:15:54.998732+00:00
-- url     : https://prove2.me/submissions/ac169026-1219-4f17-851c-5287d38d06ad

import Mathlib
import Definitions.Def_STVFriedmann_basic
open Filter Topology Real STVFriedmann

namespace STAux

lemma comp_fderiv {m : ℕ} (F : (Fin m → ℝ) → Fin m → ℝ) (x v : Fin m → ℝ)
    (hF : ∀ i, DifferentiableAt ℝ (fun u => F u i) x) (i : Fin m) :
    fderiv ℝ F x v i = fderiv ℝ (fun u => F u i) x v := by
  have h := fderiv_pi (φ := fun i u => F u i) hF
  change fderiv ℝ (fun u i => F u i) x v i = _
  rw [h]; rfl

lemma pdiff {m : ℕ} (i : Fin m) (x v : Fin m → ℝ) :
    HasFDerivAt (fun u : Fin m → ℝ => u i) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) x :=
  hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) i x

lemma J1 (x v : Fin 2 → ℝ) :
    fderiv ℝ stvField1 x v = ![2 * v 0 - 3 * (v 0 * x 1 + x 0 * v 1),
      -(1 / 6) * v 0 + v 1 - 2 * x 1 * v 1] := by
  have hd : ∀ i, DifferentiableAt ℝ (fun u => stvField1 u i) x := by
    intro i; fin_cases i <;> simp [stvField1] <;> fun_prop
  ext i
  rw [comp_fderiv _ _ _ hd]
  fin_cases i
  · have e : (fun u : Fin 2 → ℝ => stvField1 u 0) = fun u => 2 * u 0 - 3 * u 0 * u 1 := by
      funext u; simp [stvField1]
    have h : HasFDerivAt (fun u : Fin 2 → ℝ => 2 * u 0 - 3 * u 0 * u 1) _ x := ((pdiff 0 x v).const_mul 2).sub (((pdiff 0 x v).const_mul 3).mul (pdiff 1 x v))
    simp only [Fin.zero_eta, Fin.isValue]
    rw [e, h.fderiv]
    simp; ring
  · have e : (fun u : Fin 2 → ℝ => stvField1 u 1) = fun u => -(1 / 6) * u 0 + u 1 - u 1 ^ 2 := by
      funext u; simp [stvField1]
    have h : HasFDerivAt (fun u : Fin 2 → ℝ => -(1 / 6) * u 0 + u 1 - u 1 ^ 2) _ x := (((pdiff 0 x v).const_mul (-(1/6))).add (pdiff 1 x v)).sub ((pdiff 1 x v).pow 2)
    simp only [Fin.mk_one, Fin.isValue]
    rw [e, h.fderiv]
    simp

lemma J2 (x v : Fin 4 → ℝ) :
    fderiv ℝ stvField2 x v = ![2 * v 0 - 3 * (v 0 * x 1 + x 0 * v 1),
      -(1 / 6) * v 0 + v 1 - 2 * x 1 * v 1,
      (5 / 12) * (2 * x 0 * v 0 * x 1 + x 0 ^ 2 * v 1) + 4 * v 2 - 5 * (v 1 * x 2 + x 1 * v 2)
        - 5 * (v 0 * x 3 + x 0 * v 3),
      -(1 / 12) * x 0 * v 0 + (1 / 4) * (v 0 * x 1 ^ 2 + 2 * x 0 * x 1 * v 1) - (1 / 10) * v 2 + 3 * v 3
        - 4 * (v 1 * x 3 + x 1 * v 3)] := by
  have hd : ∀ i, DifferentiableAt ℝ (fun u => stvField2 u i) x := by
    intro i; fin_cases i <;> simp [stvField2] <;> fun_prop
  ext i
  rw [comp_fderiv _ _ _ hd]
  fin_cases i
  · have e : (fun u : Fin 4 → ℝ => stvField2 u 0) = fun u => 2 * u 0 - 3 * u 0 * u 1 := by
      funext u; simp [stvField2]
    have h : HasFDerivAt (fun u : Fin 4 → ℝ => 2 * u 0 - 3 * u 0 * u 1) _ x :=
      ((pdiff 0 x v).const_mul 2).sub (((pdiff 0 x v).const_mul 3).mul (pdiff 1 x v))
    simp only [Fin.zero_eta, Fin.isValue]
    rw [e, h.fderiv]
    simp <;> ring
  · have e : (fun u : Fin 4 → ℝ => stvField2 u 1) = fun u => -(1 / 6) * u 0 + u 1 - u 1 ^ 2 := by
      funext u; simp [stvField2]
    have h : HasFDerivAt (fun u : Fin 4 → ℝ => -(1 / 6) * u 0 + u 1 - u 1 ^ 2) _ x :=
      (((pdiff 0 x v).const_mul (-(1/6))).add (pdiff 1 x v)).sub ((pdiff 1 x v).pow 2)
    simp only [Fin.mk_one, Fin.isValue]
    rw [e, h.fderiv]
    simp <;> ring
  · have e : (fun u : Fin 4 → ℝ => stvField2 u 2)
        = fun u => (5 / 12) * u 0 ^ 2 * u 1 + 4 * u 2 - 5 * u 1 * u 2 - 5 * u 0 * u 3 := by
      funext u; simp [stvField2]
    have h : HasFDerivAt (fun u : Fin 4 → ℝ => (5 / 12) * u 0 ^ 2 * u 1 + 4 * u 2 - 5 * u 1 * u 2 - 5 * u 0 * u 3) _ x :=
      (((((pdiff 0 x v).pow 2).const_mul (5/12)).mul (pdiff 1 x v)).add ((pdiff 2 x v).const_mul 4)).sub
        (((pdiff 1 x v).const_mul 5).mul (pdiff 2 x v)) |>.sub (((pdiff 0 x v).const_mul 5).mul (pdiff 3 x v))
    rw [show (⟨2, by norm_num⟩ : Fin 4) = 2 from rfl, e, h.fderiv]
    simp <;> ring
  · have e : (fun u : Fin 4 → ℝ => stvField2 u 3)
        = fun u => -(1 / 24) * u 0 ^ 2 + (1 / 4) * u 0 * u 1 ^ 2 - (1 / 10) * u 2 + 3 * u 3 - 4 * u 1 * u 3 := by
      funext u; simp [stvField2]
    have h : HasFDerivAt (fun u : Fin 4 → ℝ =>
        -(1 / 24) * u 0 ^ 2 + (1 / 4) * u 0 * u 1 ^ 2 - (1 / 10) * u 2 + 3 * u 3 - 4 * u 1 * u 3) _ x :=
      (((((pdiff 0 x v).pow 2).const_mul (-(1/24))).add (((pdiff 0 x v).const_mul (1/4)).mul ((pdiff 1 x v).pow 2))).sub
        ((pdiff 2 x v).const_mul (1/10))).add ((pdiff 3 x v).const_mul 3) |>.sub (((pdiff 1 x v).const_mul 4).mul (pdiff 3 x v))
    rw [show (⟨3, by norm_num⟩ : Fin 4) = 3 from rfl, e, h.fderiv]
    simp <;> ring

end STAux

open STAux in
theorem solution :
    fderiv ℝ stvField2 restSM2 ![-9, 3 / 2, -10 / 3, -1] =
        (2 / 3 : ℝ) • ![-9, 3 / 2, -10 / 3, -1] ∧
    fderiv ℝ stvField2 restSM2 ![4, 1, 80 / 9, 1] = (-1 : ℝ) • ![4, 1, 80 / 9, 1] ∧
    fderiv ℝ stvField2 restSM2 ![0, 0, -10, 1] = (4 / 3 : ℝ) • ![0, 0, -10, 1] ∧
    fderiv ℝ stvField2 restSM2 ![0, 0, 20 / 3, 1] = (-1 / 3 : ℝ) • ![0, 0, 20 / 3, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [J2]; ext i; fin_cases i <;> simp [restSM2] <;> norm_num
