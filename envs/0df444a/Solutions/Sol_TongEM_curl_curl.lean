-- Prove2me | solution 1 for TongEM.curl_curl
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T03:15:48.380929+00:00
-- url     : https://prove2.me/submissions/84797132-5c9b-487a-a7cb-9ae7a3385871

import Definitions.Def_TongEM_wave_ops

open TongEM Larmor

namespace CCAux

/-- Smooth scalar fields are closed under `pd`. -/
lemma smooth_pd (f : Vec → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (pd j f) := by
  unfold pd
  have : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact this.clm_apply contDiff_const

lemma pd_sub (f g : Vec → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (x : Vec) : pd j (fun y => f y - g y) x = pd j f x - pd j g x := by
  unfold pd; rw [fderiv_fun_sub (hf x) (hg x)]; rfl

lemma pd_add (f g : Vec → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (x : Vec) : pd j (fun y => f y + g y) x = pd j f x + pd j g x := by
  unfold pd; rw [fderiv_fun_add (hf x) (hg x)]; rfl

lemma pd_comm (f : Vec → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) (x : Vec) :
    pd i (pd j f) x = pd j (pd i f) x := by
  unfold pd
  have hf2 : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ f) := hC1.differentiable (by norm_num)
  rw [fderiv_clm_apply (hD x) (differentiableAt_const _),
    fderiv_clm_apply (hD x) (differentiableAt_const _)]
  simp
  exact (hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness])) _ _

/-- The components of a vector field and their partial derivatives. -/
lemma partialDeriv_eq (F : Vec → Vec) (hF : Differentiable ℝ F) (j i : Fin 3) (x : Vec) :
    partialDeriv F j i x = pd j (fun y => F y i) x := by
  unfold partialDeriv pd
  have h : HasFDerivAt (fun y => F y i)
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ F x)) x :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x (hF x).hasFDerivAt
  rw [h.fderiv]
  simp

end CCAux

open CCAux in
theorem solution (F : Vec → Vec) (hF : SmoothV F) (x : Vec) :
    curl (curl F) x = grad (divg F) x - lapVec F x := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hFi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := (contDiff_piLp _).mp hF
  have hP : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (pd j (fun y => F y i)) := fun j i => smooth_pd _ (hFi i) j
  have hPd : ∀ j i, Differentiable ℝ (pd j (fun y => F y i)) :=
    fun j i => (hP j i).differentiable (by simp)
  -- the components of `curl F`
  have hc : ∀ i, (fun y => curl F y i) =
      fun y => ![pd 1 (fun y => F y 2) y - pd 2 (fun y => F y 1) y,
                 pd 2 (fun y => F y 0) y - pd 0 (fun y => F y 2) y,
                 pd 0 (fun y => F y 1) y - pd 1 (fun y => F y 0) y] i := by
    intro i; funext y; fin_cases i <;> simp [curl, partialDeriv_eq F hFd]
  have hcs : ContDiff ℝ (⊤ : ℕ∞) (curl F) := by
    refine (contDiff_piLp _).mpr fun i => ?_
    rw [hc i]
    fin_cases i
    · exact ((hP 1 2).sub (hP 2 1))
    · exact ((hP 2 0).sub (hP 0 2))
    · exact ((hP 0 1).sub (hP 1 0))
  have hcd : Differentiable ℝ (curl F) := hcs.differentiable (by simp)
  have hdiv : divg F = fun y => pd 0 (fun y => F y 0) y + pd 1 (fun y => F y 1) y +
      pd 2 (fun y => F y 2) y := by
    funext y; simp [divg, Fin.sum_univ_three, partialDeriv_eq F hFd]
  have hcomm := fun i j k => pd_comm (fun y => F y k) (hFi k) i j x
  have houter : curl (curl F) x =
      !₂[pd 1 (fun y => curl F y 2) x - pd 2 (fun y => curl F y 1) x,
         pd 2 (fun y => curl F y 0) x - pd 0 (fun y => curl F y 2) x,
         pd 0 (fun y => curl F y 1) x - pd 1 (fun y => curl F y 0) x] := by
    rw [curl]
    simp only [partialDeriv_eq _ hcd]
  rw [houter, hc 0, hc 1, hc 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [pd_sub _ _ (hPd 0 1) (hPd 1 0), pd_sub _ _ (hPd 2 0) (hPd 0 2),
    pd_sub _ _ (hPd 1 2) (hPd 2 1)]
  rw [pd_sub _ _ (hPd 0 1) (hPd 1 0), pd_sub _ _ (hPd 2 0) (hPd 0 2),
    pd_sub _ _ (hPd 1 2) (hPd 2 1)]
  have hgd : ∀ j, pd j (divg F) x = pd j (pd 0 (fun y => F y 0)) x + pd j (pd 1 (fun y => F y 1)) x +
      pd j (pd 2 (fun y => F y 2)) x := by
    intro j
    have h01 : Differentiable ℝ (fun y => pd 0 (fun y => F y 0) y + pd 1 (fun y => F y 1) y) :=
      (hPd 0 0).add (hPd 1 1)
    rw [hdiv, pd_add (fun y => pd 0 (fun y => F y 0) y + pd 1 (fun y => F y 1) y) _ h01 (hPd 2 2),
      pd_add _ _ (hPd 0 0) (hPd 1 1)]
  ext i
  fin_cases i
  · simp [grad, lapVec, lap, Fin.sum_univ_three, hgd]
    rw [hcomm 1 0 1, hcomm 2 0 2]
    ring
  · simp [grad, lapVec, lap, Fin.sum_univ_three, hgd]
    rw [hcomm 2 1 2, hcomm 0 1 0]
    ring
  · simp [grad, lapVec, lap, Fin.sum_univ_three, hgd]
    rw [hcomm 0 2 0, hcomm 1 2 1]
    ring
