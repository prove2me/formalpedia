-- Prove2me | solution 1 for TongEM.wave_equation_E
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T03:43:47.75259+00:00
-- url     : https://prove2.me/submissions/be8592df-bb10-403f-8000-488bca521d84

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

namespace WaveAux
open CCAux
theorem curl_curl (F : Vec → Vec) (hF : SmoothV F) (x : Vec) :
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

end WaveAux

namespace DTAux

variable (F : ℝ → Vec → Vec)

/-- The joint map. -/
def G : ℝ × Vec → Vec := fun p => F p.1 p.2

lemma pd_F (hG : Differentiable ℝ (G F)) (s : ℝ) (y : Vec) (j i : Fin 3) :
    partialDeriv (F s) j i y = fderiv ℝ (G F) (s, y) (0, EuclideanSpace.single j 1) i := by
  unfold partialDeriv
  have h : HasFDerivAt (F s) ((fderiv ℝ (G F) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Vec)) y :=
    (hG (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [h.fderiv]
  simp

lemma hasDerivAt_F (hG : Differentiable ℝ (G F)) (s : ℝ) (y : Vec) :
    HasDerivAt (fun r => F r y) (fderiv ℝ (G F) (s, y) (1, 0)) s := by
  have hp : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Vec)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact (hG (s, y)).hasFDerivAt.comp_hasDerivAt s hp

lemma hasDerivAt_DG (hDG : Differentiable ℝ (fderiv ℝ (G F))) (t : ℝ) (x : Vec)
    (v : ℝ × Vec) (i : Fin 3) :
    HasDerivAt (fun s => fderiv ℝ (G F) (s, x) v i)
      (fderiv ℝ (fderiv ℝ (G F)) (t, x) (1, 0) v i) t := by
  have hp : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : Vec)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h1 := (hDG (t, x)).hasFDerivAt.comp_hasDerivAt t hp
  -- evaluate at `v`, then take the `i`-th coordinate
  have h2 : HasDerivAt (fun s => fderiv ℝ (G F) (s, x) v)
      (fderiv ℝ (fderiv ℝ (G F)) (t, x) (1, 0) v) t := by
    exact (ContinuousLinearMap.apply ℝ Vec v).hasFDerivAt.comp_hasDerivAt t h1
  exact (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h2

lemma pd_H (hDG : Differentiable ℝ (fderiv ℝ (G F))) (t : ℝ) (x : Vec) (j i : Fin 3) :
    partialDeriv (fun y => fderiv ℝ (G F) (t, y) (1, 0)) j i x =
      fderiv ℝ (fderiv ℝ (G F)) (t, x) (0, EuclideanSpace.single j 1) (1, 0) i := by
  unfold partialDeriv
  have h1 : HasFDerivAt (fun y => fderiv ℝ (G F) (t, y))
      ((fderiv ℝ (fderiv ℝ (G F)) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec)) x :=
    (hDG (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have h2 : HasFDerivAt (fun y => fderiv ℝ (G F) (t, y) (1, 0))
      ((ContinuousLinearMap.apply ℝ Vec ((1 : ℝ), (0 : Vec))).comp
        ((fderiv ℝ (fderiv ℝ (G F)) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec))) x :=
    (ContinuousLinearMap.apply ℝ Vec ((1 : ℝ), (0 : Vec))).hasFDerivAt.comp x h1
  rw [h2.fderiv]
  simp

end DTAux

namespace WaveAux
open DTAux
theorem curl_dt_comm (F : ℝ → Vec → Vec) (hF : SmoothTV F) (t : ℝ) (x : Vec) :
    deriv (fun s => curl (F s) x) t = curl (fun y => deriv (fun s => F s y) t) x := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (G F) := hF
  have hG2 : ContDiff ℝ 2 (G F) := contDiff_infty.mp hG 2
  have hGd : Differentiable ℝ (G F) := hG2.differentiable (by norm_num)
  have hDG : Differentiable ℝ (fderiv ℝ (G F)) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsymm := hG2.contDiffAt (x := (t, x)) |>.isSymmSndFDerivAt (by simp [minSmoothness])
  set D2 := fderiv ℝ (fderiv ℝ (G F)) (t, x)
  -- rewrite the right-hand field
  have hH : (fun y => deriv (fun s => F s y) t) = fun y => fderiv ℝ (G F) (t, y) (1, 0) := by
    funext y; exact (hasDerivAt_F F hGd t y).deriv
  rw [hH]
  -- the left-hand curve, componentwise
  set e : Fin 3 → Vec := fun j => EuclideanSpace.single j 1
  have hcurve : (fun s => curl (F s) x) = fun s =>
      !₂[fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0] := by
    funext s; simp only [curl, pd_F F hGd, e]
  rw [hcurve]
  have hd := fun v i => hasDerivAt_DG F hDG t x v i
  have hvec : HasDerivAt (fun s =>
      (!₂[fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0] : Vec))
      (!₂[D2 (1, 0) (0, e 1) 2 - D2 (1, 0) (0, e 2) 1,
          D2 (1, 0) (0, e 2) 0 - D2 (1, 0) (0, e 0) 2,
          D2 (1, 0) (0, e 0) 1 - D2 (1, 0) (0, e 1) 0]) t := by
    have hpi : HasDerivAt (fun s => ![fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0])
        ![D2 (1, 0) (0, e 1) 2 - D2 (1, 0) (0, e 2) 1,
          D2 (1, 0) (0, e 2) 0 - D2 (1, 0) (0, e 0) 2,
          D2 (1, 0) (0, e 0) 1 - D2 (1, 0) (0, e 1) 0] t := by
      rw [hasDerivAt_pi]
      intro k
      fin_cases k
      · exact (hd _ 2).sub (hd _ 1)
      · exact (hd _ 0).sub (hd _ 2)
      · exact (hd _ 1).sub (hd _ 0)
    exact (PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) _).comp_hasDerivAt t hpi
  rw [hvec.deriv]
  simp only [curl, pd_H F hDG t x, e]
  rw [hsymm (1, 0) (0, EuclideanSpace.single 1 1), hsymm (1, 0) (0, EuclideanSpace.single 2 1),
    hsymm (1, 0) (0, EuclideanSpace.single 0 1)]


lemma curl_neg (H : Vec → Vec) (x : Vec) : curl (fun y => -H y) x = -curl H x := by
  ext i; fin_cases i <;> simp [curl, partialDeriv, fderiv_neg] <;> ring

lemma curl_smul (a : ℝ) (H : Vec → Vec) (hH : Differentiable ℝ H) (x : Vec) :
    curl (fun y => a • H y) x = a • curl H x := by
  have h : fderiv ℝ (fun y => a • H y) x = a • fderiv ℝ H x :=
    ((hH x).hasFDerivAt.const_smul a).fderiv
  ext i; fin_cases i <;> simp [curl, partialDeriv, h] <;> ring

lemma grad_zero (x : Vec) : grad (fun _ => (0 : ℝ)) x = 0 := by
  ext i; fin_cases i <;> simp [grad, pd]

/-- Space slices of a smooth time-dependent field are smooth. -/
lemma smooth_slice (F : ℝ → Vec → Vec) (hF : SmoothTV F) (t : ℝ) : SmoothV (F t) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec => (fun p : ℝ × Vec => F p.1 p.2) (t, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  exact this

/-- `s ↦ ∂ₜF(s, x)` is differentiable. -/
lemma dt_diff (F : ℝ → Vec → Vec) (hF : SmoothTV F) (x : Vec) :
    Differentiable ℝ (fun s => deriv (fun r => F r x) s) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (G F) := hF
  have hG2 : ContDiff ℝ 2 (G F) := contDiff_infty.mp hG 2
  have hGd : Differentiable ℝ (G F) := hG2.differentiable (by norm_num)
  have hDG : Differentiable ℝ (fderiv ℝ (G F)) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : (fun s => deriv (fun r => F r x) s) = fun s => fderiv ℝ (G F) (s, x) (1, 0) := by
    funext s; exact (hasDerivAt_F F hGd s x).deriv
  rw [e]
  intro s
  have hp : DifferentiableAt ℝ (fun r : ℝ => (r, x)) s :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  exact ((hDG _).comp s hp).clm_apply (differentiableAt_const _)

/-- `y ↦ ∂ₜF(t, y)` is differentiable. -/
lemma dt_diff_space (F : ℝ → Vec → Vec) (hF : SmoothTV F) (t : ℝ) :
    Differentiable ℝ (fun y => deriv (fun s => F s y) t) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (G F) := hF
  have hG2 : ContDiff ℝ 2 (G F) := contDiff_infty.mp hG 2
  have hGd : Differentiable ℝ (G F) := hG2.differentiable (by norm_num)
  have hDG : Differentiable ℝ (fderiv ℝ (G F)) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : (fun y => deriv (fun s => F s y) t) = fun y => fderiv ℝ (G F) (t, y) (1, 0) := by
    funext y; exact (hasDerivAt_F F hGd t y).deriv
  rw [e]
  intro y
  have hp : DifferentiableAt ℝ (fun r : Vec => (t, r)) y :=
    (differentiableAt_const t).prodMk differentiableAt_id
  exact ((hDG _).comp y hp).clm_apply (differentiableAt_const _)

/-- The vacuum wave equation for `E`. -/
theorem waveE (eps0 c : ℝ) (hc : c ≠ 0) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    (1 / c ^ 2) • dtt E t x - lapVec (E t) x = 0 := by
  have hcc := curl_curl (E t) (smooth_slice E hE t) x
  have hdiv : divg (E t) = fun _ => (0 : ℝ) := by
    funext y; rw [hEB.gauss t y]; simp
  rw [hdiv, grad_zero, zero_sub] at hcc
  -- ∇×E = -∂ₜB
  have hcE : curl (E t) = fun y => -deriv (fun s => B s y) t := by
    funext y; exact hEB.faraday t y
  rw [hcE, curl_neg, ← curl_dt_comm B hB t x] at hcc
  -- ∇×B = (1/c²) ∂ₜE
  have hcB : (fun s => curl (B s) x) = fun s => (1 / c ^ 2) • deriv (fun r => E r x) s := by
    funext s; rw [hEB.ampere s x]; simp
  have hd : deriv (fun s => (1 / c ^ 2) • deriv (fun r => E r x) s) t =
      (1 / c ^ 2) • deriv (fun s => deriv (fun r => E r x) s) t :=
    (((dt_diff E hE x) t).hasDerivAt.const_smul (1 / c ^ 2)).deriv
  rw [hcB, hd] at hcc
  unfold dtt
  rw [← neg_neg (lapVec (E t) x), ← hcc]
  simp

/-- The vacuum wave equation for `B`. -/
theorem waveB (eps0 c : ℝ) (hc : c ≠ 0) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    (1 / c ^ 2) • dtt B t x - lapVec (B t) x = 0 := by
  have hcc := curl_curl (B t) (smooth_slice B hB t) x
  have hdiv : divg (B t) = fun _ => (0 : ℝ) := by
    funext y; exact hEB.noMonopole t y
  rw [hdiv, grad_zero, zero_sub] at hcc
  -- ∇×B = (1/c²) ∂ₜE
  have hcB : curl (B t) = fun y => (1 / c ^ 2) • deriv (fun s => E s y) t := by
    funext y; rw [hEB.ampere t y]; simp
  rw [hcB, curl_smul _ _ (dt_diff_space E hE t), ← curl_dt_comm E hE t x] at hcc
  -- ∇×E = -∂ₜB
  have hcE : (fun s => curl (E s) x) = fun s => -deriv (fun r => B r x) s := by
    funext s; exact hEB.faraday s x
  have hd : deriv (fun s => -deriv (fun r => B r x) s) t =
      -deriv (fun s => deriv (fun r => B r x) s) t :=
    (((dt_diff B hB x) t).hasDerivAt.neg).deriv
  rw [hcE, hd] at hcc
  unfold dtt
  rw [← neg_neg (lapVec (B t) x), ← hcc]
  simp
end WaveAux

open WaveAux
theorem solution (mu0 eps0 c : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    (1 / c ^ 2) • dtt E t x - lapVec (E t) x = 0 := by
  have hc0 : c ≠ 0 := by rw [hc]; exact (Real.sqrt_pos.mpr (by positivity)).ne'
  exact waveE eps0 c hc0 E B hE hB hEB t x
