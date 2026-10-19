-- Prove2me | solution 1 for SchwartzSpaceWiki.fourierTransform_linearIsomorphism
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:44:54.216519+00:00
-- url     : https://prove2.me/submissions/f6f5182d-f797-4f4f-b99a-dce1a6d687ef

import Definitions.Def_SchwartzSpaceWiki_Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.LinearAlgebra.Multilinear.Basis

open SchwartzSpaceWiki MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform

set_option backward.isDefEq.respectTransparency false

private lemma partial_smooth {n : ℕ} (i : Fin n) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private lemma partial_comm {n : ℕ} (i j : Fin n) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  ext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f)).differentiable (by simp)
  simpa +unfoldPartialApp [partialDeriv, fderiv_clm_apply (hd x) (differentiableAt_const _)] using
    ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

private noncomputable def W {n : ℕ} (l : List (Fin n)) (f : Rn n → ℂ) : Rn n → ℂ :=
  l.foldr partialDeriv f

private lemma W_smooth {n : ℕ} (l : List (Fin n)) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (W l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact partial_smooth i ih

private lemma W_perm {n : ℕ} {l r : List (Fin n)} (h : l.Perm r) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : W l f = W r f := by
  induction h with
  | nil => rfl
  | cons i h ih => exact congrArg (partialDeriv i) ih
  | swap i j l => exact partial_comm j i (W_smooth l hf)
  | trans h h' ih ih' => exact ih.trans ih'

private def word {n : ℕ} (β : MultiIndex n) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (β i) i)

private lemma W_word {n : ℕ} (β : MultiIndex n) (f : Rn n → ℂ) :
    W (word β) f = iteratedPartialDeriv β f := by
  have hr (i : Fin n) (k : ℕ) (g : Rn n → ℂ) :
      W (List.replicate k i) g = (partialDeriv i)^[k] g := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simpa only [W, List.replicate_succ, List.foldr_cons,
          Function.iterate_succ_apply'] using congrArg (partialDeriv i) ih
  unfold word iteratedPartialDeriv
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.flatMap_cons, W, List.foldr_append, List.foldr_cons]
      change W (List.replicate (β i) i) (W (l.flatMap (fun j => List.replicate (β j) j)) f) = _
      rw [hr, ih]

private lemma count_word {n : ℕ} (β : MultiIndex n) (i : Fin n) :
    (word β).count i = β i := by
  classical
  simp only [word, List.count_flatMap, Function.comp_def, List.count_replicate]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

private lemma W_canonical {n : ℕ} (l : List (Fin n)) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    W l f = iteratedPartialDeriv (fun i => l.count i) f := by
  rw [← W_word]
  apply W_perm _ hf
  exact List.perm_iff_count.mpr (fun i => (count_word (fun j => l.count j) i).symm)

private lemma W_ofFn {n k : ℕ} (v : Fin k → Fin n) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    W (List.ofFn v) f = fun x =>
      iteratedFDeriv ℝ k f x (fun i => EuclideanSpace.single (v i) 1) := by
  induction k with
  | zero => ext x; simp [W]
  | succ k ih =>
    rw [List.ofFn_succ]
    change partialDeriv (v 0) (W (List.ofFn (fun i => v i.succ)) f) = _
    rw [ih]
    ext x
    simpa only [partialDeriv, Fin.tail_def] using
      ((hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k) x).iteratedFDeriv_succ_apply_left'
        (m := fun i => EuclideanSpace.single (v i) 1)).symm

private lemma multilinear_bound (n k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Rn n) ℂ,
      ‖A‖ ≤ K * ∑ v : Fin k → Fin n, ‖A (fun i => EuclideanSpace.single (v i) 1)‖ := by
  classical
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Rn n) ℂ →ₗ[ℝ]
      ((Fin k → Fin n) → ℂ) :=
    { toFun := fun A v => A (fun i => EuclideanSpace.single (v i) 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective T := by
    intro A B h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    intro v
    simpa [T, EuclideanSpace.basisFun_apply] using congrFun h v
  have := FiniteDimensional.of_injective T hinj
  obtain ⟨K, hK, hb⟩ := T.injective_iff_antilipschitz.mp hinj
  refine ⟨K, by exact_mod_cast hK.le, fun A => ?_⟩
  apply (ZeroHomClass.bound_of_antilipschitz T hb A).trans
  gcongr
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro v
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ v)

private lemma polynomial_bound {n : ℕ} (f : Rn n → ℂ) (hf : ∀ α : MultiIndex n, ∃ C : ℝ, ∀ x, ‖(monomial α x : ℂ) * f x‖ ≤ C)
    (P : MvPolynomial (Fin n) ℂ) :
    ∃ C : ℝ, ∀ x, ‖MvPolynomial.eval (fun i => (x i : ℂ)) P * f x‖ ≤ C := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    obtain ⟨C, hC⟩ := hf (fun i => d i)
    refine ⟨‖c‖ * C, fun x => ?_⟩
    have he : MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.monomial d c) =
        c * (monomial (fun i => d i) x : ℂ) := by
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp [monomial]
    rw [he, mul_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  | add P Q hP hQ =>
    obtain ⟨CP, hCP⟩ := hP
    obtain ⟨CQ, hCQ⟩ := hQ
    refine ⟨CP + CQ, fun x => ?_⟩
    simpa only [map_add, add_mul] using
      (norm_add_le (MvPolynomial.eval (fun i => (x i : ℂ)) P * f x)
        (MvPolynomial.eval (fun i => (x i : ℂ)) Q * f x)).trans
        (add_le_add (hCP x) (hCQ x))

private lemma power_bound {n : ℕ} (f : Rn n → ℂ) (hf : ∀ α : MultiIndex n, ∃ C : ℝ, ∀ x, ‖(monomial α x : ℂ) * f x‖ ≤ C)
    (k : ℕ) : ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
  classical
  let P : MvPolynomial (Fin n) ℂ := (1 + ∑ i : Fin n, MvPolynomial.X i ^ 2) ^ k
  obtain ⟨C, hC⟩ := polynomial_bound f hf P
  refine ⟨C, fun x => ?_⟩
  have he : MvPolynomial.eval (fun i => (x i : ℂ)) P =
      ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ k := by
    simp only [P, map_pow, map_add, map_one, map_sum, MvPolynomial.eval_X]
    congr 2
    exact_mod_cast congrArg (fun t : ℝ => 1 + t) (EuclideanSpace.real_norm_sq_eq x).symm
  have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  calc
    ‖x‖ ^ k * ‖f x‖ ≤ (1 + ‖x‖ ^ 2) ^ k * ‖f x‖ := by
      gcongr
    _ = ‖MvPolynomial.eval (fun i => (x i : ℂ)) P * f x‖ := by
      rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ C := hC x

private lemma canonical_power_bound {n : ℕ} {f : Rn n → ℂ} (hf : f ∈ schwartzSpace n)
    (β : MultiIndex n) (k : ℕ) : ∃ C : ℝ, ∀ x,
      ‖x‖ ^ k * ‖iteratedPartialDeriv β f x‖ ≤ C := by
  apply power_bound
  intro α
  refine ⟨(schwartzSeminorm α β f).toReal, fun x => ?_⟩
  have h : ‖(monomial α x : ℂ) * iteratedPartialDeriv β f x‖ₑ ≤
      schwartzSeminorm α β f := by
    unfold schwartzSeminorm
    exact le_iSup (fun y : Rn n =>
      (‖(monomial α y : ℂ) * iteratedPartialDeriv β f y‖ₑ : ℝ≥0∞)) x
  exact_mod_cast ENNReal.toReal_mono (hf.2 α β).ne h

private noncomputable def toSchwartz {n : ℕ} (f : Rn n → ℂ)
    (hf : f ∈ schwartzSpace n) : 𝓢(Rn n, ℂ) where
  toFun := f
  smooth' := hf.1
  decay' k r := by
    classical
    have hb (v : Fin r → Fin n) : ∃ C : ℝ, ∀ x,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ r f x (fun i => EuclideanSpace.single (v i) 1)‖ ≤ C := by
      obtain ⟨C, hC⟩ := canonical_power_bound hf (fun i => (List.ofFn v).count i) k
      refine ⟨C, fun x => ?_⟩
      have he := congrFun ((W_ofFn v hf.1).symm.trans (W_canonical (List.ofFn v) hf.1)) x
      rw [he]
      exact hC x
    choose C hC using hb
    obtain ⟨K, hK, hbound⟩ := multilinear_bound n r
    refine ⟨K * ∑ v, C v, fun x => ?_⟩
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ r f x‖ ≤
          ‖x‖ ^ k * (K * ∑ v : Fin r → Fin n,
            ‖iteratedFDeriv ℝ r f x (fun i => EuclideanSpace.single (v i) 1)‖) := by
        gcongr
        exact hbound _
      _ = K * ∑ v : Fin r → Fin n,
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ r f x (fun i => EuclideanSpace.single (v i) 1)‖) := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ ≤ K * ∑ v, C v := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hC v x)) hK

private lemma W_schwartz {n : ℕ} (l : List (Fin n)) (f : 𝓢(Rn n, ℂ)) :
    ∃ g : 𝓢(Rn n, ℂ), (g : Rn n → ℂ) = W l f := by
  induction l with
  | nil => exact ⟨f, rfl⟩
  | cons i l ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨SchwartzMap.evalCLM ℝ (Rn n) ℂ (EuclideanSpace.single i 1)
      (SchwartzMap.fderivCLM ℝ (Rn n) ℂ g), ?_⟩
    change (fun x => fderiv ℝ (g : Rn n → ℂ) x (EuclideanSpace.single i 1)) = _
    rw [hg]
    rfl

private lemma ofSchwartz_mem {n : ℕ} (f : 𝓢(Rn n, ℂ)) :
    (f : Rn n → ℂ) ∈ schwartzSpace n := by
  classical
  refine ⟨f.smooth ⊤, fun α β => ?_⟩
  obtain ⟨g, hg⟩ := W_schwartz (word β) f
  rw [W_word] at hg
  obtain ⟨C, hC, hb⟩ := g.decay (∑ i, α i) 0
  have hnorm (x : Rn n) : ‖(monomial α x : ℂ) * iteratedPartialDeriv β f x‖ ≤ C := by
    rw [← hg, norm_mul, Complex.norm_real, monomial, norm_prod]
    calc
      (∏ i, ‖(x i) ^ α i‖) * ‖g x‖ ≤ (∏ i, ‖x‖ ^ α i) * ‖g x‖ := by
        gcongr with i
        rw [norm_pow]
        gcongr
        exact PiLp.norm_apply_le x i
      _ = ‖x‖ ^ (∑ i, α i) * ‖g x‖ := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ C := by simpa only [norm_iteratedFDeriv_zero] using hb x
  have hsup : schwartzSeminorm α β f ≤ ENNReal.ofReal C := by
    unfold schwartzSeminorm
    apply iSup_le
    intro x
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hnorm x)
  exact hsup.trans_lt ENNReal.ofReal_lt_top

private lemma fourier_eq (n : ℕ) (f : Rn n → ℂ) :
    fourierTransform f = 𝓕 f := by
  ext ξ
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem solution (n : ℕ) :
    Set.BijOn fourierTransform (schwartzSpace n) (schwartzSpace n) ∧
    ∀ f ∈ schwartzSpace n, ∀ g ∈ schwartzSpace n, ∀ c : ℂ,
      fourierTransform (f + c • g) = fourierTransform f + c • fourierTransform g := by
  have hcoe (f : 𝓢(Rn n, ℂ)) :
      fourierTransform (f : Rn n → ℂ) = (𝓕 f : 𝓢(Rn n, ℂ)) := by
    rw [fourier_eq, SchwartzMap.fourier_coe]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    rw [show f = (toSchwartz f hf : Rn n → ℂ) from rfl, hcoe]
    exact ofSchwartz_mem _
  · intro f hf g hg h
    change fourierTransform (toSchwartz f hf : Rn n → ℂ) =
      fourierTransform (toSchwartz g hg : Rn n → ℂ) at h
    have he : 𝓕 (toSchwartz f hf) = 𝓕 (toSchwartz g hg) := by
      apply SchwartzMap.ext
      exact congrFun ((hcoe _).symm.trans (h.trans (hcoe _)))
    have := (FourierTransform.fourierCLE ℂ 𝓢(Rn n, ℂ)).injective he
    exact congrArg (fun s : 𝓢(Rn n, ℂ) => (s : Rn n → ℂ)) this
  · intro g hg
    let s := (FourierTransform.fourierCLE ℂ 𝓢(Rn n, ℂ)).symm (toSchwartz g hg)
    refine ⟨s, ofSchwartz_mem s, ?_⟩
    rw [hcoe]
    exact congrArg (fun s : 𝓢(Rn n, ℂ) => (s : Rn n → ℂ))
      ((FourierTransform.fourierCLE ℂ 𝓢(Rn n, ℂ)).apply_symm_apply (toSchwartz g hg))
  · intro f hf g hg c
    have he : f + c • g = ((toSchwartz f hf + c • toSchwartz g hg : 𝓢(Rn n, ℂ)) : Rn n → ℂ) := rfl
    rw [he, hcoe, FourierTransform.fourier_add, FourierTransform.fourier_smul]
    change _ = fourierTransform (toSchwartz f hf : Rn n → ℂ) +
      c • fourierTransform (toSchwartz g hg : Rn n → ℂ)
    rw [hcoe, hcoe]
    rfl
