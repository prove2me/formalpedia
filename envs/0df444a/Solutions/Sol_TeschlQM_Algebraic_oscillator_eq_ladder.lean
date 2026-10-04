-- Prove2me | solution 1 for TeschlQM.Algebraic.oscillator_eq_ladder
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:43:10.392057+00:00
-- url     : https://prove2.me/submissions/b885aa7d-807e-4584-ba90-6fd4cf6f5a61

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_ladder

set_option autoImplicit false

namespace TeschlQM.Algebraic.Pb753eb34

open TeschlQM.Algebraic

lemma core1_contDiff (ω : ℝ) (f : ℝ → ℂ) (hf : f ∈ core1 ω) : ContDiff ℝ (⊤ : ℕ∞) f := by
  unfold core1 at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ k * Real.exp (-(ω * x ^ 2) / 2)) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  | zero => exact contDiff_const
  | add g h _ _ hg hh => exact hg.add hh
  | smul a g _ hg => exact contDiff_const.smul hg

lemma core1_diff (ω : ℝ) (f : ℝ → ℂ) (hf : f ∈ core1 ω) : Differentiable ℝ f :=
  (core1_contDiff ω f hf).differentiable (by simp)

lemma phi_mem (ω : ℝ) (k : ℕ) :
    (fun x : ℝ => ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) ∈ core1 ω :=
  Submodule.subset_span ⟨k, rfl⟩

lemma mulX_mem (ω : ℝ) (f : ℝ → ℂ) (hf : f ∈ core1 ω) :
    (fun x : ℝ => (x : ℂ) * f x) ∈ core1 ω := by
  have key : ∀ g ∈ core1 ω, (fun x : ℝ => (x : ℂ) * g x) ∈ core1 ω := by
    intro g hg
    unfold core1 at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      have : (fun x : ℝ => (x : ℂ) * ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) =
          (fun x : ℝ => ((x ^ (k + 1) * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) := by
        funext x; push_cast; ring
      rw [this]; exact phi_mem ω (k + 1)
    | zero =>
      have : (fun x : ℝ => (x : ℂ) * (0 : ℝ → ℂ) x) = 0 := by funext x; simp
      rw [this]; exact Submodule.zero_mem _
    | add g h _ _ hg hh =>
      have : (fun x : ℝ => (x : ℂ) * (g + h) x) =
          (fun x : ℝ => (x : ℂ) * g x) + (fun x : ℝ => (x : ℂ) * h x) := by
        funext x; simp only [Pi.add_apply]; ring
      rw [this]; exact Submodule.add_mem _ hg hh
    | smul a g _ hg =>
      have : (fun x : ℝ => (x : ℂ) * (a • g) x) = a • (fun x : ℝ => (x : ℂ) * g x) := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact Submodule.smul_mem _ a hg
  exact key f hf

lemma phi_hasDerivAt (ω : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ))
      (((k * x ^ (k - 1) * Real.exp (-(ω * x ^ 2) / 2)
        + x ^ k * (Real.exp (-(ω * x ^ 2) / 2) * (-(ω * (2 * x)) / 2)) : ℝ) : ℂ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ k) ((k : ℝ) * x ^ (k - 1)) x := hasDerivAt_pow k x
  have h2 : HasDerivAt (fun y : ℝ => -(ω * y ^ 2) / 2) (-(ω * (2 * x)) / 2) x := by
    have e : (fun y : ℝ => -(ω * y ^ 2) / 2) = fun y : ℝ => (-ω / 2) * y ^ 2 := by
      funext y; ring
    rw [e]
    refine ((hasDerivAt_pow 2 x).const_mul (-ω / 2)).congr_deriv ?_
    norm_num
    try ring
  have h3 := h1.mul (h2.exp)
  exact h3.ofReal_comp

lemma deriv_mem (ω : ℝ) (f : ℝ → ℂ) (hf : f ∈ core1 ω) : deriv f ∈ core1 ω := by
  unfold core1 at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    have : deriv (fun x : ℝ => ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) =
        (k : ℂ) • (fun x : ℝ => ((x ^ (k - 1) * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) +
        (-(ω : ℂ)) • (fun x : ℝ => ((x ^ (k + 1) * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)) := by
      funext x
      rw [(phi_hasDerivAt ω k x).deriv]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast; ring
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (phi_mem ω _))
      (Submodule.smul_mem _ _ (phi_mem ω _))
  | zero =>
    have : deriv (0 : ℝ → ℂ) = 0 := by funext x; simp
    rw [this]; exact Submodule.zero_mem _
  | add g h hg0 hh0 hg hh =>
    have hgd := core1_diff ω g hg0
    have hhd := core1_diff ω h hh0
    have : deriv (g + h) = deriv g + deriv h := by
      funext x; exact deriv_add (hgd x) (hhd x)
    rw [this]; exact Submodule.add_mem _ hg hh
  | smul a g hg0 hg =>
    have hgd := core1_diff ω g hg0
    have : deriv (a • g) = a • deriv g := by
      funext x; exact deriv_const_smul a (hgd x)
    rw [this]; exact Submodule.smul_mem _ a hg

lemma hasDerivAt_lin (s : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((s * y : ℝ) : ℂ)) ((s : ℝ) : ℂ) x := by
  have := ((hasDerivAt_id x).const_mul s).ofReal_comp
  simpa using this

lemma hasDerivAt_minus (ω : ℝ) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    HasDerivAt (ladderMinus ω f)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((((Real.sqrt ω : ℝ) : ℂ) * f x
        + ((Real.sqrt ω * x : ℝ) : ℂ) * deriv f x)
        + ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (deriv f) x)) x := by
  unfold ladderMinus
  have h := (((hasDerivAt_lin (Real.sqrt ω) x).mul (hf x).hasDerivAt).add
    ((hf' x).hasDerivAt.const_mul (((1 / Real.sqrt ω : ℝ) : ℂ)))).const_mul
    (((1 / Real.sqrt 2 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  ring

lemma ladderPlus_eq (ω : ℝ) (f : ℝ → ℂ) :
    ladderPlus ω f = (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt ω : ℝ) : ℂ)) •
        (fun x : ℝ => (x : ℂ) * f x) +
      (-(((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt ω : ℝ) : ℂ))) • deriv f := by
  funext x
  simp only [ladderPlus, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

lemma ladderMinus_eq (ω : ℝ) (f : ℝ → ℂ) :
    ladderMinus ω f = (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt ω : ℝ) : ℂ)) •
        (fun x : ℝ => (x : ℂ) * f x) +
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt ω : ℝ) : ℂ)) • deriv f := by
  funext x
  simp only [ladderMinus, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

end TeschlQM.Algebraic.Pb753eb34

open TeschlQM.Algebraic in
theorem solution (ω : ℝ) (hω : 0 < ω) :
    (∀ f ∈ core1 ω,
      (fun x : ℝ => -deriv (deriv f) x + ((ω ^ 2 * x ^ 2 : ℝ) : ℂ) * f x) =
        fun x : ℝ => (ω : ℂ) * (2 * ladderPlus ω (ladderMinus ω f) x + f x)) ∧
      (∀ f ∈ core1 ω, ladderPlus ω f ∈ core1 ω ∧ ladderMinus ω f ∈ core1 ω) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    have hc := TeschlQM.Algebraic.Pb753eb34.core1_contDiff ω f hf
    have hd : Differentiable ℝ f := hc.differentiable (by simp)
    have hd' : Differentiable ℝ (deriv f) := by
      have := (hc.iterate_deriv 1).differentiable (by simp)
      simpa using this
    funext x
    have hM := (TeschlQM.Algebraic.Pb753eb34.hasDerivAt_minus ω f hd hd' x).deriv
    rw [show ladderPlus ω (ladderMinus ω f) x =
        ((1 / Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt ω * x : ℝ) : ℂ) * ladderMinus ω f x
          - ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (ladderMinus ω f) x) from rfl, hM]
    simp only [ladderMinus]
    have hs : Real.sqrt ω ≠ 0 := (Real.sqrt_pos.mpr hω).ne'
    have ht : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
      rw [← Complex.ofReal_mul]
      have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
      rw [this]; push_cast; ring
    have hu : ((Real.sqrt ω : ℝ) : ℂ) * ((1 / Real.sqrt ω : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_one_div_cancel hs]; simp
    have hw : (ω : ℂ) = ((Real.sqrt ω : ℝ) : ℂ) * ((Real.sqrt ω : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hω.le]
    set s : ℂ := ((Real.sqrt ω : ℝ) : ℂ) with hs_def
    set u : ℂ := ((1 / Real.sqrt ω : ℝ) : ℂ) with hu_def
    set t : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) with ht_def
    have hx1 : ((Real.sqrt ω * x : ℝ) : ℂ) = s * (x : ℂ) := by rw [hs_def]; push_cast; ring
    have hx2 : ((ω ^ 2 * x ^ 2 : ℝ) : ℂ) = (ω : ℂ) ^ 2 * (x : ℂ) ^ 2 := by push_cast; ring
    rw [hx1, hx2, hw]
    linear_combination
      (-2 * s ^ 2 * (s ^ 2 * (x : ℂ) ^ 2 * f x - s * u * f x - u ^ 2 * deriv (deriv f) x)) * ht
        + (s ^ 2 * f x + deriv (deriv f) x * (s * u + 1)) * hu
  · intro f hf
    have hX := TeschlQM.Algebraic.Pb753eb34.mulX_mem ω f hf
    have hD := TeschlQM.Algebraic.Pb753eb34.deriv_mem ω f hf
    refine ⟨?_, ?_⟩
    · rw [TeschlQM.Algebraic.Pb753eb34.ladderPlus_eq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hX) (Submodule.smul_mem _ _ hD)
    · rw [TeschlQM.Algebraic.Pb753eb34.ladderMinus_eq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hX) (Submodule.smul_mem _ _ hD)
