-- Prove2me | solution 1 for SchwartzSpaceWiki.monomial_mul_gaussian_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:27:01.623749+00:00
-- url     : https://prove2.me/submissions/78df33e4-b596-49cc-b362-bd77948c3996

import Definitions.Def_SchwartzSpaceWiki_Defs

open SchwartzSpaceWiki
open scoped ENNReal

private inductive PolyFn (n : ℕ) : (Rn n → ℂ) → Prop
  | const (c : ℂ) : PolyFn n (fun _ => c)
  | coord (i : Fin n) : PolyFn n (fun x => (x i : ℂ))
  | add {f g} : PolyFn n f → PolyFn n g → PolyFn n (f + g)
  | mul {f g} : PolyFn n f → PolyFn n g → PolyFn n (f * g)

private lemma poly_smooth {n : ℕ} {f : Rn n → ℂ} (hf : PolyFn n f) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  induction hf with
  | const => exact contDiff_const
  | coord i => exact (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).contDiff
  | add _ _ ih ih' => exact ih.add ih'
  | mul _ _ ih ih' => exact ih.mul ih'

private lemma partial_add {n : ℕ} (i : Fin n) {f g : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext x
  simp [partialDeriv, fderiv_add ((hf.differentiable (by simp)) x)
    ((hg.differentiable (by simp)) x)]

private lemma partial_mul {n : ℕ} (i : Fin n) {f g : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    partialDeriv i (f * g) = partialDeriv i f * g + f * partialDeriv i g := by
  ext x
  simp [partialDeriv, fderiv_mul ((hf.differentiable (by simp)) x)
    ((hg.differentiable (by simp)) x), mul_comm, add_comm]

private lemma poly_partial {n : ℕ} (i : Fin n) {f : Rn n → ℂ}
    (hf : PolyFn n f) : PolyFn n (partialDeriv i f) := by
  classical
  induction hf with
  | const c =>
    have h : partialDeriv i (fun _ : Rn n => c) = fun _ => 0 := by
      ext x
      simp only [partialDeriv, fderiv_const_apply, zero_apply]
    rw [h]
    exact PolyFn.const 0
  | coord j =>
    have h : partialDeriv i (fun x : Rn n => (x j : ℂ)) =
        fun _ => ((EuclideanSpace.single i (1 : ℝ)) j : ℂ) := by
      ext x
      change fderiv ℝ (Complex.ofRealCLM ∘ (EuclideanSpace.proj j)) x _ = _
      rw [((Complex.ofRealCLM.hasFDerivAt).comp x (EuclideanSpace.proj j).hasFDerivAt).fderiv]
      rfl
    rw [h]
    exact PolyFn.const _
  | add hf hg ih ih' => rw [partial_add i (poly_smooth hf) (poly_smooth hg)]; exact ih.add ih'
  | mul hf hg ih ih' =>
    rw [partial_mul i (poly_smooth hf) (poly_smooth hg)]
    exact (ih.mul hg).add (hf.mul ih')

private lemma poly_pow {n : ℕ} {f : Rn n → ℂ} (hf : PolyFn n f) (k : ℕ) :
    PolyFn n (f ^ k) := by
  induction k with
  | zero => exact PolyFn.const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

private lemma poly_monomial {n : ℕ} (α : MultiIndex n) :
    PolyFn n (fun x => (monomial α x : ℂ)) := by
  classical
  have h : ∀ s : Finset (Fin n), PolyFn n (fun x : Rn n => ∏ i ∈ s, (x i : ℂ) ^ α i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using PolyFn.const (n := n) 1
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi, Pi.mul_def, Pi.pow_apply] using (poly_pow (PolyFn.coord i) (α i)).mul ih
  simpa [monomial] using h Finset.univ

private noncomputable def G {n : ℕ} (a : ℝ) (x : Rn n) : ℂ := Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))

private lemma G_smooth {n : ℕ} (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (@G n a) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn n =>
      Complex.exp (((-(a * ‖x‖ ^ 2) : ℝ) : ℂ))) :=
    (Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_norm_sq ℝ (E := Rn n))).neg)).cexp
  convert h using 1
  funext x
  simp only [G]
  push_cast
  rfl

private lemma G_norm {n : ℕ} (a : ℝ) (x : Rn n) :
    ‖G a x‖ = Real.exp (-(a * ‖x‖ ^ 2)) := by simp [G, Complex.norm_exp, -Complex.ofReal_pow]

private lemma G_partial {n : ℕ} (a : ℝ) (i : Fin n) :
    partialDeriv i (@G n a) = (fun x => (-2 * a : ℂ) * (x i : ℂ)) * G a := by
  ext x
  have h := ((Complex.ofRealCLM.hasFDerivAt).comp x
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul a).neg)).cexp
  change fderiv ℝ (G a) x _ = _
  have hfun : G a = (fun y : Rn n =>
      Complex.exp ((Complex.ofRealCLM ∘ (-fun y : Rn n => a * ‖y‖ ^ 2)) y)) := by
    funext y
    simp only [G, Function.comp_apply, Complex.ofRealCLM_apply, Pi.neg_apply]
    push_cast
    rfl
  rw [← hfun] at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, EuclideanSpace.inner_single_right,
    G, -Complex.ofReal_pow]
  push_cast
  ring

private lemma derivative_form {n : ℕ} (a : ℝ) {p : Rn n → ℂ} (hp : PolyFn n p)
    (i : Fin n) : ∃ q, PolyFn n q ∧ partialDeriv i (p * G a) = q * G a := by
  have hc : PolyFn n (fun x => (-2 * a : ℂ) * (x i : ℂ)) :=
    (PolyFn.const _).mul (PolyFn.coord i)
  refine ⟨partialDeriv i p + p * (fun x => (-2 * a : ℂ) * (x i : ℂ)),
    (poly_partial i hp).add (hp.mul hc), ?_⟩
  rw [partial_mul i (poly_smooth hp) (G_smooth a), G_partial]
  ext x
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

private lemma multi_form {n : ℕ} (a : ℝ) (β : MultiIndex n) {p : Rn n → ℂ}
    (hp : PolyFn n p) :
    ∃ q, PolyFn n q ∧ iteratedPartialDeriv β (p * G a) = q * G a := by
  have step (i : Fin n) (k : ℕ) : ∀ p, PolyFn n p →
      ∃ q, PolyFn n q ∧ (partialDeriv i)^[k] (p * G a) = q * G a := by
    induction k with
    | zero => intro p hp; exact ⟨p, hp, rfl⟩
    | succ k ih =>
      intro p hp
      obtain ⟨q, hq, he⟩ := ih p hp
      obtain ⟨r, hr, he'⟩ := derivative_form a hq i
      exact ⟨r, hr, by rw [Function.iterate_succ_apply', he, he']⟩
  have fold : ∀ l : List (Fin n), ∃ q, PolyFn n q ∧
      l.foldr (fun i f => (partialDeriv i)^[β i] f) (p * G a) = q * G a := by
    intro l
    induction l with
    | nil => exact ⟨p, hp, rfl⟩
    | cons i l ih =>
      obtain ⟨q, hq, he⟩ := ih
      obtain ⟨r, hr, he'⟩ := step i (β i) q hq
      exact ⟨r, hr, by rw [List.foldr_cons, he, he']⟩
  exact fold (List.finRange n)

private lemma G_le_one {n : ℕ} {a : ℝ} (ha : 0 < a) (x : Rn n) : ‖G a x‖ ≤ 1 := by
  rw [G_norm, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))

private lemma coord_bound {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin n) (x : Rn n) :
    ‖(x i : ℂ) * G a x‖ ≤ 1 + 1 / a := by
  have hx : ‖x i‖ ≤ 1 + ‖x‖ ^ 2 :=
    (PiLp.norm_apply_le x i).trans (by nlinarith [sq_nonneg (‖x‖ - 1)])
  have he : Real.exp (-(a * ‖x‖ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))
  have hy : a * ‖x‖ ^ 2 * Real.exp (-(a * ‖x‖ ^ 2)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hy' : ‖x‖ ^ 2 * Real.exp (-(a * ‖x‖ ^ 2)) ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  rw [norm_mul, Complex.norm_real, G_norm]
  calc
    ‖x i‖ * Real.exp (-(a * ‖x‖ ^ 2)) ≤
        (1 + ‖x‖ ^ 2) * Real.exp (-(a * ‖x‖ ^ 2)) := by gcongr
    _ ≤ 1 + 1 / a := by nlinarith

private lemma poly_bound {n : ℕ} {p : Rn n → ℂ} (hp : PolyFn n p) :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖p x * G a x‖ ≤ C := by
  induction hp with
  | const c =>
    intro a ha
    refine ⟨‖c‖, norm_nonneg _, ?_⟩
    intro x
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (G_le_one ha x) (norm_nonneg c)
  | coord i =>
    intro a ha
    exact ⟨1 + 1 / a, by positivity, coord_bound ha i⟩
  | @add f g hf hg ih ih' =>
    intro a ha
    obtain ⟨C, hC, hCf⟩ := ih a ha
    obtain ⟨D, hD, hDg⟩ := ih' a ha
    exact ⟨C + D, by positivity, fun x => by
      simpa [add_mul] using (norm_add_le (f x * G a x) (g x * G a x)).trans
        (add_le_add (hCf x) (hDg x))⟩
  | @mul f g hf hg ih ih' =>
    intro a ha
    obtain ⟨C, hC, hCf⟩ := ih (a / 2) (by positivity)
    obtain ⟨D, hD, hDg⟩ := ih' (a / 2) (by positivity)
    refine ⟨C * D, by positivity, fun x => ?_⟩
    have hsplit : G a x = G (a / 2) x * G (a / 2) x := by
      rw [G, G, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simpa only [Pi.mul_apply, hsplit, mul_mul_mul_comm, norm_mul] using
      mul_le_mul (hCf x) (hDg x) (norm_nonneg _) hC

theorem solution (n : ℕ) (α : MultiIndex n) (a : ℝ) (ha : 0 < a) :
    (fun x : Rn n => (monomial α x : ℂ) * Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) ∈
      schwartzSpace n := by
  let p : Rn n → ℂ := fun x => (monomial α x : ℂ)
  have hp : PolyFn n p := poly_monomial α
  change p * G a ∈ schwartzSpace n
  refine ⟨(poly_smooth hp).mul (G_smooth a), ?_⟩
  intro γ β
  obtain ⟨q, hq, he⟩ := multi_form a β hp
  obtain ⟨C, hC, hCb⟩ := poly_bound ((poly_monomial γ).mul hq) a ha
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ (ENNReal.ofReal_lt_top)
  apply iSup_le
  intro x
  rw [he]
  have hb := hCb x
  simp only [Pi.mul_apply, mul_assoc] at hb
  simpa only [ofReal_norm, Pi.mul_apply] using ENNReal.ofReal_le_ofReal hb
