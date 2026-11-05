-- Prove2me | solution 1 for StrongConv.isLinearMap_nu_and_abs_expTr_sub_sum_nu_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:06:42.385582+00:00
-- url     : https://prove2.me/submissions/3641b5a3-74d1-48df-8658-ec3895f63b9e

import Theorems.Thm_StrongConv_abs_nu_le
import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_uniformExp_trN_wordEval_eq_div
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_div_le
import Theorems.Thm_StrongConv_cNorm_le_two_mul_sSup_of_subset_add

open Polynomial Filter Topology

namespace StrongConv

/-- `F` has the asymptotic expansion with coefficients `c`. -/
def HasExp (F : ℕ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    |F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i| ≤ C / (N : ℝ) ^ m


end StrongConv
section

open Polynomial Filter Topology

namespace StrongConv.PartA1
open StrongConv

lemma permOp_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp σ x j = x (σ.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) :
    permOp (σ * τ) x = permOp σ (permOp τ x) := by
  ext j
  simp only [permOp_apply]
  have : (σ * τ).symm j = τ.symm (σ.symm j) := by
    rw [← Equiv.Perm.inv_def, mul_inv_rev]; rfl
  rw [this]

lemma permOp_one {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : permOp (1 : Equiv.Perm (Fin N)) x = x := by
  ext j
  simp only [permOp_apply]
  rfl

lemma inner_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (permOp σ x) y = inner ℂ x (permOp σ⁻¹ y) := by
  have h : permOp σ x = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ x := rfl
  have h2 : permOp σ⁻¹ y = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ⁻¹ y := rfl
  rw [h, h2, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

lemma star_permOpPerp_apply {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    ((star (permOpPerp τ) x : OnesPerp N) : EuclideanSpace ℂ (Fin N)) = permOp τ⁻¹ x := by
  have : star (permOpPerp τ) = permOpPerp τ⁻¹ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro a b
    show inner ℂ (permOp τ⁻¹ (a : EuclideanSpace ℂ (Fin N))) (b : EuclideanSpace ℂ (Fin N)) =
      inner ℂ (a : EuclideanSpace ℂ (Fin N)) (permOp τ (b : EuclideanSpace ℂ (Fin N)))
    rw [inner_permOp]; simp
  rw [this]; rfl

lemma key {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    ∃ π : Equiv.Perm (Fin N), ∀ x : OnesPerp N,
      ((wordEval (sModel σ) w x : OnesPerp N) : EuclideanSpace ℂ (Fin N)) = permOp π x := by
  induction w with
  | nil => exact ⟨1, fun x => by simp [wordEval, permOp_one]⟩
  | cons a w ih =>
    obtain ⟨π, hπ⟩ := ih
    have hc : ∀ x, wordEval (sModel σ) (a :: w) x = (match a with
        | none => (1 : OnesPerp N →L[ℂ] OnesPerp N)
        | some l => letterOp (sModel σ) l) (wordEval (sModel σ) w x) := by
      intro x; cases a <;> simp [wordEval]
    rcases a with _ | (i | i)
    · exact ⟨π, fun x => by rw [hc]; exact hπ x⟩
    · refine ⟨σ i * π, fun x => ?_⟩
      rw [hc, permOp_mul, ← hπ x]; rfl
    · refine ⟨(σ i)⁻¹ * π, fun x => ?_⟩
      rw [hc, permOp_mul, ← hπ x]
      exact star_permOpPerp_apply (σ i) _

lemma trace_perm_im {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (permOp π).toLinearMap).im = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin N) ℂ).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [permOp_apply, EuclideanSpace.basisFun_apply]
  split_ifs <;> simp

lemma permOp_ones {N : ℕ} (π : Equiv.Perm (Fin N)) : permOp π (onesVec N) = onesVec N := by
  ext j; simp [permOp_apply, onesVec]

lemma permOp_mem_perp {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (hx : x ∈ OnesPerp N) : permOp π x ∈ OnesPerp N := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  have := inner_permOp π⁻¹ (onesVec N) x
  rw [inv_inv, permOp_ones] at this
  rw [← this]
  exact hx

lemma trace_perp_im {N : ℕ} (π : Equiv.Perm (Fin N))
    (h : ∀ x ∈ OnesPerp N, permOp π x ∈ OnesPerp N) :
    (LinearMap.trace ℂ (OnesPerp N)
      (((permOp π).toLinearMap.restrict (p := OnesPerp N) (q := OnesPerp N) h))).im = 0 := by
  let Nb : Bool → Submodule ℂ (EuclideanSpace ℂ (Fin N)) := fun b => cond b (OnesPerp N) (ℂ ∙ onesVec N)
  have hint : DirectSum.IsInternal Nb := by
    rw [DirectSum.isInternal_submodule_iff_isCompl Nb (i := false) (j := true) (by simp) (by ext b; cases b <;> simp)]
    exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have hf : ∀ b, Set.MapsTo (permOp π).toLinearMap (Nb b) (Nb b) := by
    intro b x hx
    cases b
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      show permOp π (c • onesVec N) ∈ ℂ ∙ onesVec N
      rw [map_smul, permOp_ones]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · exact h x hx
  have := LinearMap.trace_eq_sum_trace_restrict hint hf
  have hF : (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (permOp π).toLinearMap).im = 0 := trace_perm_im π
  rw [Fintype.sum_bool] at this
  have hspan : LinearMap.trace ℂ (Nb false) ((permOp π).toLinearMap.restrict (hf false)) =
      (Module.finrank ℂ (Nb false) : ℂ) := by
    have : (permOp π).toLinearMap.restrict (hf false) = LinearMap.id := by
      refine LinearMap.ext fun ⟨x, hx⟩ => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      apply Subtype.ext
      show permOp π (c • onesVec N) = c • onesVec N
      rw [map_smul, permOp_ones]
    rw [this, LinearMap.trace_id]
  have e1 : LinearMap.trace ℂ (Nb true) ((permOp π).toLinearMap.restrict (hf true)) =
      LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (permOp π).toLinearMap -
        (Module.finrank ℂ (Nb false) : ℂ) := by
    rw [this, hspan]; ring
  have e2 : (LinearMap.trace ℂ (Nb true) ((permOp π).toLinearMap.restrict (hf true))).im = 0 := by
    rw [e1, Complex.sub_im, hF]; simp
  exact e2

lemma im_trace_wordEval {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    (LinearMap.trace ℂ (OnesPerp N)
      ((wordEval (sModel σ) w : OnesPerp N →L[ℂ] OnesPerp N) : OnesPerp N →ₗ[ℂ] OnesPerp N)).im = 0 := by
  obtain ⟨π, hπ⟩ := key σ w
  have h : ∀ x ∈ OnesPerp N, permOp π x ∈ OnesPerp N := fun x hx => permOp_mem_perp π x hx
  have : ((wordEval (sModel σ) w : OnesPerp N →L[ℂ] OnesPerp N) : OnesPerp N →ₗ[ℂ] OnesPerp N) =
      (permOp π).toLinearMap.restrict h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hπ x
  rw [this]
  exact trace_perp_im π h

abbrev PN (D N : ℕ) := PiLp 2 (fun _ : Fin D => OnesPerp N)

noncomputable def blk {D N : ℕ} (a b : Fin D) (X : OnesPerp N →L[ℂ] OnesPerp N) : PN D N →L[ℂ] PN D N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => OnesPerp N)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.single ℂ (fun _ : Fin D => OnesPerp N) a).comp
      (X.comp (PiLp.proj 2 (fun _ : Fin D => OnesPerp N) b)))

lemma trace_blk {D N : ℕ} (a b : Fin D) (X : OnesPerp N →L[ℂ] OnesPerp N) :
    LinearMap.trace ℂ (PN D N) (blk a b X : PN D N →ₗ[ℂ] PN D N)
      = if a = b then LinearMap.trace ℂ (OnesPerp N) (X : OnesPerp N →ₗ[ℂ] OnesPerp N) else 0 := by
  have : (blk a b X : PN D N →ₗ[ℂ] PN D N) =
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => OnesPerp N)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin D => OnesPerp N) a)).toLinearMap ∘ₗ
      ((X.comp (PiLp.proj 2 (fun _ : Fin D => OnesPerp N) b)).toLinearMap) := rfl
  rw [this, LinearMap.trace_comp_comm']
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp
  · simp only [hab, if_false]
    have : ((X.comp (PiLp.proj 2 (fun _ : Fin D => OnesPerp N) b)).toLinearMap) ∘ₗ
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => OnesPerp N)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin D => OnesPerp N) a)).toLinearMap = 0 := by
      refine LinearMap.ext fun x => ?_
      simp [Pi.single_apply, Ne.symm hab]
    rw [this]; simp

lemma trace_tensorOp {D N : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (X : OnesPerp N →L[ℂ] OnesPerp N) :
    LinearMap.trace ℂ (PN D N) ((tensorOp A X : PN D N →L[ℂ] PN D N) : PN D N →ₗ[ℂ] PN D N) =
      (∑ a, A a a) * LinearMap.trace ℂ (OnesPerp N) (X : OnesPerp N →ₗ[ℂ] OnesPerp N) := by
  have : tensorOp A X = ∑ a : Fin D, ∑ b : Fin D, A a b • blk a b X := rfl
  rw [this]
  simp only [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul, map_sum, map_smul,
    trace_blk, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_mul]

lemma wordOp_eq {d N : ℕ} (u : Fin d → OnesPerp N →L[ℂ] OnesPerp N) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u w = wordEval u (w.toList.map some) := by
  simp only [wordOp, wordEval, List.map_map]
  rfl

lemma trDN_eval_eq {D d N : ℕ} (B : NCPoly D d) (σ : Fin d → Equiv.Perm (Fin N)) :
    trDN D N (B.eval (sModel σ)) =
      ∑ w ∈ B.support, ((∑ a, B w a a) / (D : ℂ)).re *
        trN N (wordEval (sModel σ) (w.toList.map some)) := by
  have h1 : LinearMap.trace ℂ (PN D N) ((B.eval (sModel σ) : PN D N →L[ℂ] PN D N) : PN D N →ₗ[ℂ] PN D N) =
      ∑ w ∈ B.support, (∑ a, B w a a) *
        LinearMap.trace ℂ (OnesPerp N) ((wordEval (sModel σ) (w.toList.map some) : OnesPerp N →L[ℂ] OnesPerp N) : OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    have : B.eval (sModel σ) = ∑ w ∈ B.support, tensorOp (B w) (wordOp (sModel σ) w) := rfl
    rw [this]
    simp only [ContinuousLinearMap.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [trace_tensorOp, wordOp_eq]
  unfold trDN
  rw [h1, Complex.re_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  have him := im_trace_wordEval σ (w.toList.map some)
  unfold trN
  set t := LinearMap.trace ℂ (OnesPerp N) ((wordEval (sModel σ) (w.toList.map some) : OnesPerp N →L[ℂ] OnesPerp N) : OnesPerp N →ₗ[ℂ] OnesPerp N)
  set c := ∑ a, B w a a
  have hre : (c / (D : ℂ)).re = c.re / D := by
    rw [show (D : ℂ) = ((D : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
  rw [hre, Complex.mul_re, him, mul_zero, sub_zero, div_mul_div_comm]

end StrongConv.PartA1

end

namespace StrongConv
alias im_trace_wordEval := StrongConv.PartA1.im_trace_wordEval
alias trDN_eval_eq := StrongConv.PartA1.trDN_eval_eq
end StrongConv

section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.PartA2

open StrongConv Matrix

section Tensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (v : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T v a = ∑ b, A a b • T (v b) := by
  simp [tensorOp, Finset.sum_apply, Pi.single_apply, smul_ite, Finset.sum_ite_eq]

lemma tensorOp_ext {m n : ℕ} {S S' : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H)}
    (h : ∀ v a, S v a = S' v a) : S = S' :=
  ContinuousLinearMap.ext fun v => PiLp.ext fun a => h v a

lemma tensorOp_add_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

lemma tensorOp_zero_left {m n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply]

lemma tensorOp_smul_left {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (c • A) T = c • tensorOp A T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Finset.smul_sum, smul_smul]

lemma tensorOp_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ)
    (X X' : H →L[ℂ] H) :
    tensorOp A X * tensorOp A' X' = tensorOp (A * A') (X * X') := by
  apply tensorOp_ext; intro v a
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma tensorOp_one {n : ℕ} : tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Matrix.one_apply]

lemma tensorOp_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (X : H →L[ℂ] H) :
    star (tensorOp A X) = tensorOp Aᴴ (star X) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [PiLp.inner_apply, tensorOp_apply, ContinuousLinearMap.star_eq_adjoint]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    Matrix.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]



/-! ## words -/

lemma wordOp_mul {d : ℕ} (u : Fin d → H →L[ℂ] H) (w₁ w₂ : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u (w₁ * w₂) = wordOp u w₁ * wordOp u w₂ := by
  simp [wordOp, FreeMonoid.toList_mul, List.map_append, List.prod_append]

lemma wordOp_one {d : ℕ} (u : Fin d → H →L[ℂ] H) : wordOp u 1 = 1 := by
  simp [wordOp]

lemma letterOp_swap {d : ℕ} (u : Fin d → H →L[ℂ] H) (a : Fin d ⊕ Fin d) :
    letterOp u a.swap = star (letterOp u a) := by
  cases a <;> simp [letterOp]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  generalize w.toList = l
  simp only [FreeMonoid.toList_ofList]
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_nil, List.prod_nil, mul_one, star_mul, ← ih, List.map_singleton, List.prod_singleton,
      letterOp_swap]


lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  simp [NCPoly.wordStar, List.map_reverse, Function.comp_def]

lemma length_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    (NCPoly.wordStar w).length = w.length := by
  simp [NCPoly.wordStar, FreeMonoid.length]

/-! ## eval as an additive map -/

variable {D d : ℕ}

def evalAdd (u : Fin d → H →L[ℂ] H) :
    NCPoly D d →+ (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :=
  Finsupp.liftAddHom fun w =>
    { toFun := fun A => tensorOp A (wordOp u w)
      map_zero' := tensorOp_zero_left _
      map_add' := fun A B => tensorOp_add_left A B _ }

lemma eval_eq_evalAdd (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) : P.eval u = evalAdd u P := by
  simp [NCPoly.eval, evalAdd, Finsupp.liftAddHom_apply, Finsupp.sum]

lemma eval_single (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ)
    (u : Fin d → H →L[ℂ] H) : NCPoly.eval (Finsupp.single w A : NCPoly D d) u = tensorOp A (wordOp u w) := by
  rw [eval_eq_evalAdd]; unfold evalAdd; rw [Finsupp.liftAddHom_apply_single]; rfl

lemma eval_add (P Q : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (P + Q).eval u = P.eval u + Q.eval u := by
  simp only [eval_eq_evalAdd, map_add]

lemma eval_sum {ι : Type*} (s : Finset ι) (f : ι → NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (∑ i ∈ s, f i).eval u = ∑ i ∈ s, (f i).eval u := by
  simp only [eval_eq_evalAdd, map_sum]

lemma eval_smul (c : ℂ) (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (c • P).eval u = c • P.eval u := by
  induction P using Finsupp.induction_linear with
  | zero => simp only [smul_zero, eval_eq_evalAdd, map_zero]; ext x i; simp
  | add P Q hP hQ => rw [smul_add, eval_add, eval_add, hP, hQ, smul_add]
  | single w A =>
    rw [Finsupp.smul_single, eval_single, eval_single, tensorOp_smul_left]

/-! ## degree -/

lemma degree_le_iff (P : NCPoly D d) (n : ℕ) :
    P.degree ≤ n ↔ ∀ w, P w ≠ 0 → w.length ≤ n := by
  unfold NCPoly.degree
  rw [Finset.sup_le_iff]
  simp

lemma degree_sum_le {ι : Type*} (s : Finset ι) (f : ι → NCPoly D d) (n : ℕ)
    (h : ∀ i ∈ s, (f i).degree ≤ n) : (∑ i ∈ s, f i).degree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NCPoly.degree]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, degree_le_iff]
    intro w hw
    have h1 := (degree_le_iff _ _).1 (h a (Finset.mem_insert_self _ _))
    have h2 := (degree_le_iff _ _).1 (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finsupp.add_apply] at hw
    by_cases ha' : f a w = 0
    · rw [ha', zero_add] at hw; exact h2 w hw
    · exact h1 w ha'

lemma degree_smul_le (c : ℂ) (P : NCPoly D d) (n : ℕ) (h : P.degree ≤ n) :
    (c • P).degree ≤ n := by
  rw [degree_le_iff] at h ⊢
  intro w hw
  apply h
  intro h0
  apply hw
  simp [h0]

lemma degree_single_le (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (h : w.length ≤ n) : NCPoly.degree (Finsupp.single w A : NCPoly D d) ≤ n := by
  rw [degree_le_iff]
  intro v hv
  by_cases hvw : v = w
  · subst hvw; exact h
  · simp [Finsupp.single_apply, Ne.symm hvw] at hv

/-- product -/
def mulNC (B P : NCPoly D d) : NCPoly D d :=
  ∑ w ∈ B.support, ∑ w' ∈ P.support, Finsupp.single (w * w') (B w * P w')

lemma eval_mulNC (B P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (mulNC B P).eval u = B.eval u * P.eval u := by
  unfold mulNC
  have hB : B.eval u = ∑ w ∈ B.support, tensorOp (B w) (wordOp u w) := rfl
  have hP : P.eval u = ∑ w ∈ P.support, tensorOp (P w) (wordOp u w) := rfl
  rw [eval_sum, hB, hP, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [eval_single, wordOp_mul, tensorOp_mul]

lemma degree_mulNC (B P : NCPoly D d) : (mulNC B P).degree ≤ B.degree + P.degree := by
  unfold mulNC
  refine degree_sum_le _ _ _ fun w hw => degree_sum_le _ _ _ fun w' hw' => ?_
  refine degree_single_le _ _ _ ?_
  rw [FreeMonoid.length_mul]
  exact add_le_add (Finset.le_sup (f := FreeMonoid.length) hw) (Finset.le_sup (f := FreeMonoid.length) hw')

lemma pow_expansion (P : NCPoly D d) (q₀ : ℕ) (hq₀ : P.degree ≤ q₀) (k : ℕ) :
    ∃ B : NCPoly D d, B.degree ≤ k * q₀ ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (u : Fin d → H →L[ℂ] H), (P.eval u) ^ k = B.eval u := by
  induction k with
  | zero =>
    refine ⟨(Finsupp.single 1 1 : NCPoly D d), degree_single_le _ _ _ (by simp [FreeMonoid.length_one]), ?_⟩
    intro H _ _ _ u
    rw [eval_single, wordOp_one, tensorOp_one, pow_zero]
  | succ k ih =>
    obtain ⟨B, hB, hBe⟩ := ih
    refine ⟨mulNC B P, ?_, ?_⟩
    · refine (degree_mulNC B P).trans ?_
      rw [add_mul, one_mul]
      exact add_le_add hB hq₀
    · intro H _ _ _ u
      rw [pow_succ, hBe, eval_mulNC]


lemma star_eval {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    star (P.eval u) = ∑ w ∈ P.support, tensorOp (P w)ᴴ (wordOp u (NCPoly.wordStar w)) := by
  unfold NCPoly.eval
  erw [star_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tensorOp_star, star_wordOp]

end Tensor

lemma exists_poly_expansion {D d q₀ : ℕ} (P : NCPoly D d) (hq₀ : P.degree ≤ q₀) (h : ℝ[X]) :
    ∃ B : NCPoly D d, B.degree ≤ h.natDegree * q₀ ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (u : Fin d → H →L[ℂ] H),
        ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • (P.eval u) ^ k = B.eval u := by
  choose Bk hBk hBke using pow_expansion P q₀ hq₀
  refine ⟨∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • Bk k, ?_, ?_⟩
  · refine degree_sum_le _ _ _ fun k hk => degree_smul_le _ _ _ ((hBk k).trans ?_)
    exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  · intro H _ _ _ u
    rw [eval_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_smul, hBke k H u]

lemma fnCalc_poly {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) (h : ℝ[X]) :
    fnCalc (fun x => h.eval x) T = ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • T ^ k := by
  have := hT.isStarNormal
  unfold fnCalc
  have : cfc (fun z : ℂ => ((h.eval z.re : ℝ) : ℂ)) T =
      cfc (fun z : ℂ => (h.map (algebraMap ℝ ℂ)).eval z) T := by
    apply cfc_congr
    intro z hz
    have := hT.mem_spectrum_eq_re hz
    simp only
    conv_rhs => rw [this]
    simp [Polynomial.eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply]
  rw [this, cfc_polynomial (h.map (algebraMap ℝ ℂ)) T, aeval_eq_sum_range, natDegree_map]
  simp [coeff_map]

lemma isSelfAdjoint_eval {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  unfold IsSelfAdjoint
  rw [star_eval]
  have hmem : ∀ w, w ∈ P.support → NCPoly.wordStar w ∈ P.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    rw [hP]
    simpa using hw
  calc _ = ∑ w ∈ P.support, tensorOp (P (NCPoly.wordStar w)) (wordOp u (NCPoly.wordStar w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hP]
    _ = P.eval u := by
        unfold NCPoly.eval
        exact Finset.sum_nbij' NCPoly.wordStar NCPoly.wordStar hmem hmem
          (fun _ _ => wordStar_wordStar _) (fun _ _ => wordStar_wordStar _) (fun _ _ => rfl)

end StrongConv.PartA2

end

end

namespace StrongConv
alias exists_poly_expansion := StrongConv.PartA2.exists_poly_expansion
alias fnCalc_poly := StrongConv.PartA2.fnCalc_poly
alias isSelfAdjoint_eval := StrongConv.PartA2.isSelfAdjoint_eval
end StrongConv

section

open Polynomial Filter Topology

namespace StrongConv.PartA3

open StrongConv






lemma uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (F : ι → X → ℝ) :
    uniformExp (fun x => ∑ i ∈ s, c i * F i x) = ∑ i ∈ s, c i * uniformExp (F i) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, mul_div_assoc]

lemma uniformExp_add_smul {X : Type*} [Fintype X] (F G : X → ℝ) (c : ℝ) :
    uniformExp (fun x => F x + c * G x) = uniformExp F + c * uniformExp G := by
  unfold uniformExp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Rationality of `E tr_{DN} h(P)` (the use of Lemma 5.1 in the proof of Theorem 6.1). -/
lemma rational_expTr {D d q₀ : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀)
    (hq₀' : 1 ≤ q₀) (q : ℕ) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) :
    ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ ((q * q₀ : ℕ) : ℝ) * (1 + Real.log d) ∧
      ∀ N : ℕ, q * q₀ ≤ N → expTr P N (fun x => h.eval x) =
        f.eval (1 / (N : ℝ)) / (gPoly d (q * q₀)).eval (1 / (N : ℝ)) := by
  obtain ⟨B, hBdeg, hB⟩ := exists_poly_expansion P hq₀ h
  have hQ : 1 ≤ q * q₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hBQ : B.degree ≤ q * q₀ := hBdeg.trans (Nat.mul_le_mul hh le_rfl)
  have key : ∀ w : FreeMonoid (Fin d ⊕ Fin d), ∃ fw : ℝ[X], w ∈ B.support →
      ((fw.natDegree : ℝ) ≤ ((q * q₀ : ℕ) : ℝ) * (1 + Real.log d) ∧
        ∀ N : ℕ, q * q₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            trN N (wordEval (sModel σ) (w.toList.map some))) =
          fw.eval (1 / (N : ℝ)) / (gPoly d (q * q₀)).eval (1 / (N : ℝ))) := by
    intro w
    by_cases hw : w ∈ B.support
    · have hlen : (w.toList.map some).length ≤ q * q₀ := by
        simp only [List.length_map]
        exact (Finset.le_sup (f := FreeMonoid.length) hw).trans hBQ
      obtain ⟨-, fw, h1, h2⟩ := exists_uniformExp_trN_wordEval_eq_div d (q * q₀) hQ _ hlen
      exact ⟨fw, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hw⟩
  choose fw hfw using key
  let c : FreeMonoid (Fin d ⊕ Fin d) → ℝ := fun w => ((∑ a, B w a a) / (D : ℂ)).re
  refine ⟨∑ w ∈ B.support, Polynomial.C (c w) * fw w, ?_, ?_⟩
  · have hnn : 0 ≤ ((q * q₀ : ℕ) : ℝ) * (1 + Real.log d) := by
      have : 0 ≤ Real.log d := Real.log_natCast_nonneg d
      positivity
    refine (Nat.cast_le.2 (Polynomial.natDegree_sum_le_of_forall_le (n := ⌊((q * q₀ : ℕ) : ℝ) *
      (1 + Real.log d)⌋₊) _ _ ?_)).trans (Nat.floor_le hnn)
    intro w hw
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Nat.le_floor (hfw w hw).1)
  · intro N hN
    have hexp : expTr P N (fun x => h.eval x) =
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => ∑ w ∈ B.support, c w *
          trN N (wordEval (sModel σ) (w.toList.map some))) := by
      unfold expTr
      congr 1
      funext σ
      rw [fnCalc_poly _ (isSelfAdjoint_eval P hP _), hB (OnesPerp N) (sModel σ),
        trDN_eval_eq]
    rw [hexp, uniformExp_sum, Polynomial.eval_finsetSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [(hfw w hw).2 N hN]
    simp [Polynomial.eval_mul, c, mul_div_assoc]

lemma sum_range_coeff_eq {A : Type*} [Ring A] [Module ℂ A] (h : ℝ[X]) (n : ℕ)
    (hn : h.natDegree ≤ n) (T : A) :
    ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • T ^ k =
      ∑ k ∈ Finset.range (n + 1), (h.coeff k : ℂ) • T ^ k := by
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

lemma trDN_add_smul (D N : ℕ)
    (Y Z : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ] PiLp 2 (fun _ : Fin D => OnesPerp N))
    (c : ℝ) : trDN D N (Y + (c : ℂ) • Z) = trDN D N Y + c * trDN D N Z := by
  unfold trDN
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul]
  simp only [Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  ring

lemma poly_comb_aux {A : Type*} [Ring A] [Module ℂ A] (h₁ h₂ : ℝ[X]) (c : ℝ) (n : ℕ) (T : A) :
    ∑ k ∈ Finset.range (n + 1), ((h₁ + Polynomial.C c * h₂).coeff k : ℂ) • T ^ k =
      ∑ k ∈ Finset.range (n + 1), (h₁.coeff k : ℂ) • T ^ k +
        (c : ℂ) • ∑ k ∈ Finset.range (n + 1), (h₂.coeff k : ℂ) • T ^ k := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  push_cast
  rw [add_smul, smul_smul]

set_option synthInstance.maxHeartbeats 200000 in
lemma expTr_add_smul {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (N : ℕ) (h₁ h₂ : ℝ[X])
    (c : ℝ) : expTr P N (fun x => (h₁ + Polynomial.C c * h₂).eval x) =
      expTr P N (fun x => h₁.eval x) + c * expTr P N (fun x => h₂.eval x) := by
  unfold expTr
  rw [← uniformExp_add_smul]
  congr 1
  funext σ
  set T := P.eval (sModel σ) with hT
  have hTs : IsSelfAdjoint T := isSelfAdjoint_eval P hP _
  set n := max (h₁ + Polynomial.C c * h₂).natDegree (max h₁.natDegree h₂.natDegree)
  have e0 := fnCalc_poly T hTs (h₁ + Polynomial.C c * h₂)
  have e1 := fnCalc_poly T hTs h₁
  have e2 := fnCalc_poly T hTs h₂
  rw [sum_range_coeff_eq _ n (le_max_left _ _)] at e0
  rw [sum_range_coeff_eq _ n ((le_max_left _ _).trans (le_max_right _ _))] at e1
  rw [sum_range_coeff_eq _ n ((le_max_right _ _).trans (le_max_right _ _))] at e2
  have hf : fnCalc (fun x => (h₁ + Polynomial.C c * h₂).eval x) T =
      fnCalc (fun x => h₁.eval x) T + (c : ℂ) • fnCalc (fun x => h₂.eval x) T := by
    rw [e0, e1, e2]
    exact poly_comb_aux h₁ h₂ c n T
  rw [hf, trDN_add_smul]

end StrongConv.PartA3

end

namespace StrongConv
alias rational_expTr := StrongConv.PartA3.rational_expTr
alias expTr_add_smul := StrongConv.PartA3.expTr_add_smul
end StrongConv

section

open Polynomial Filter Topology

namespace StrongConv.PartB
open StrongConv


section tensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [Pi.single_apply, hc.symm]
  · simp

lemma norm_pi_le_sum {n : ℕ} (y : PiLp 2 (fun _ : Fin n => H)) : ‖y‖ ≤ ∑ a, ‖y a‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

lemma tensorOp_norm_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    ‖tensorOp A T‖ ≤ (∑ a, ∑ b, ‖A a b‖) * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine (norm_pi_le_sum _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [tensorOp_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_smul]
  have h1 : ‖T (x b)‖ ≤ ‖T‖ * ‖x‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x b) (norm_nonneg _))
  calc ‖A a b‖ * ‖T (x b)‖ ≤ ‖A a b‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖A a b‖ * ‖T‖ * ‖x‖ := by ring

end tensor
section conj
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma wordOp_conj {d : ℕ} (e : H ≃ₗᵢ[ℂ] K) (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp (fun i => e.conjStarAlgEquiv (u i)) w = e.conjStarAlgEquiv (wordOp u w) := by
  unfold wordOp
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  rcases l with i | i <;> simp [letterOp, map_star]

lemma tensorOp_conj_apply {m n : ℕ} (e : H ≃ₗᵢ[ℂ] K) (A : Matrix (Fin m) (Fin n) ℂ)
    (T : H →L[ℂ] H) (y : PiLp 2 (fun _ : Fin n => K)) :
    tensorOp A (e.conjStarAlgEquiv T) y =
      LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin m => e)
        (tensorOp A T ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin n => e)).symm y)) := by
  ext a
  rw [tensorOp_apply]
  simp only [LinearIsometryEquiv.piLpCongrRight_apply, tensorOp_apply, map_sum, map_smul]
  simp [LinearIsometryEquiv.piLpCongrRight_symm]

lemma eval_conj {D d : ℕ} (P : NCPoly D d) (e : H ≃ₗᵢ[ℂ] K) (u : Fin d → H →L[ℂ] H) :
    P.eval (fun i => e.conjStarAlgEquiv (u i)) =
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin D => e)).conjStarAlgEquiv (P.eval u) := by
  ext1 y
  simp only [NCPoly.eval, wordOp_conj, sum_apply, tensorOp_conj_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, map_sum]

end conj

/-! ### Norm bounds -/

lemma norm_le_one_of_unitary {A : Type*} [CStarAlgebra A] (U : A) (hU : U ∈ unitary A) :
    ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial A with h | h
  · rw [Subsingleton.elim U 0]; simp
  · exact (CStarRing.norm_of_mem_unitary hU).le

lemma wordOp_norm_le_one {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1)
    (w : FreeMonoid (Fin d ⊕ Fin d)) : ‖wordOp u w‖ ≤ 1 := by
  unfold wordOp
  generalize w.toList = l
  induction l with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    have : ‖letterOp u a‖ ≤ 1 := by
      rcases a with i | i
      · exact hu i
      · simpa [letterOp] using hu i
    nlinarith [norm_nonneg (letterOp u a), norm_nonneg ((l.map (letterOp u)).prod)]

lemma norm_eval_le {D d : ℕ} (P : NCPoly D d) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖P.eval u‖ ≤ ∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖ := by
  unfold NCPoly.eval
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  refine (tensorOp_norm_le _ _).trans ?_
  have := wordOp_norm_le_one u hu w
  have h0 : 0 ≤ ∑ a, ∑ b, ‖P w a b‖ := by positivity
  nlinarith

lemma norm_toEuclideanCLM_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
  refine norm_le_one_of_unitary _ ?_
  have h := U.2
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · rw [← map_star, ← map_mul, h.1, map_one]
  · rw [← map_star, ← map_mul, h.2, map_one]

lemma bddAbove_fullNorm {D d : ℕ} (P : NCPoly D d) :
    BddAbove {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
      x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖} := by
  refine ⟨∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖, ?_⟩
  rintro x ⟨n, U, rfl⟩
  exact norm_eval_le P _ fun i => norm_toEuclideanCLM_le (U i)

/-! ### The permutation model is unitarily equivalent to a unitary-matrix tuple -/

section perm
variable {N : ℕ}

lemma permOpPerp_apply (σ : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    ((permOpPerp σ x : OnesPerp N) : EuclideanSpace ℂ (Fin N)) = permOp σ x := rfl

lemma inner_permOpPerp (σ : Equiv.Perm (Fin N)) (x y : OnesPerp N) :
    inner ℂ (permOpPerp σ x) (permOpPerp σ y) = inner ℂ x y := by
  show inner ℂ (permOp σ x : EuclideanSpace ℂ (Fin N)) (permOp σ y) = inner ℂ (x : EuclideanSpace ℂ (Fin N)) y
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).inner_map_map _ _

lemma permOpPerp_mul_inv (σ : Equiv.Perm (Fin N)) : permOpPerp σ * permOpPerp σ⁻¹ = 1 := by
  ext1 x
  apply Subtype.ext
  ext j
  simp [permOpPerp_apply, permOp, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.Perm.inv_def]

lemma star_permOpPerp_mul (σ : Equiv.Perm (Fin N)) : star (permOpPerp σ) * permOpPerp σ = 1 := by
  ext1 x
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_left, inner_permOpPerp]
  rfl

lemma permOpPerp_unitary (σ : Equiv.Perm (Fin N)) : permOpPerp σ ∈ unitary (OnesPerp N →L[ℂ] OnesPerp N) := by
  have h1 := star_permOpPerp_mul σ
  have h2 : star (permOpPerp σ) = permOpPerp σ⁻¹ := by
    calc star (permOpPerp σ) = star (permOpPerp σ) * (permOpPerp σ * permOpPerp σ⁻¹) := by
          rw [permOpPerp_mul_inv, mul_one]
      _ = permOpPerp σ⁻¹ := by rw [← mul_assoc, h1, one_mul]
  rw [Unitary.mem_iff]
  refine ⟨h1, ?_⟩
  rw [h2, permOpPerp_mul_inv]

end perm


section starequiv
variable {A B : Type*}

lemma unitary_map_equiv [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (φ : A ≃⋆ₐ[ℂ] B) {x : A} (hx : x ∈ unitary A) : φ x ∈ unitary B := by
  rw [Unitary.mem_iff] at hx ⊢
  constructor
  · rw [← map_star, ← map_mul, hx.1, map_one]
  · rw [← map_star, ← map_mul, hx.2, map_one]

lemma norm_equiv [CStarAlgebra A] [CStarAlgebra B] (φ : A ≃⋆ₐ[ℂ] B) (x : A) : ‖φ x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map φ (EquivLike.injective φ) x

lemma unitary_symm_equiv [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (φ : A ≃⋆ₐ[ℂ] B) {y : B} (hy : y ∈ unitary B) : φ.symm y ∈ unitary A :=
  unitary_map_equiv φ.symm hy

end starequiv

lemma exists_unitary_tuple {d N n : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
    (e : OnesPerp N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ U : Fin d → Matrix.unitaryGroup (Fin n) ℂ,
      (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ)) =
        fun i => e.conjStarAlgEquiv (sModel σ i) := by
  have hu : ∀ i, e.conjStarAlgEquiv (sModel σ i) ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    fun i => unitary_map_equiv e.conjStarAlgEquiv (permOpPerp_unitary (σ i))
  have hv : ∀ i, (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (e.conjStarAlgEquiv (sModel σ i)) ∈
      Matrix.unitaryGroup (Fin n) ℂ :=
    fun i => unitary_map_equiv (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (B := Matrix (Fin n) (Fin n) ℂ) (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (hu i)
  refine ⟨fun i => ⟨_, hv i⟩, ?_⟩
  funext i
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _

lemma norm_eval_conj_sModel {D d N n : ℕ} (P : NCPoly D d) (σ : Fin d → Equiv.Perm (Fin N))
    (e : OnesPerp N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ‖P.eval (fun i => e.conjStarAlgEquiv (sModel σ i))‖ = ‖P.eval (sModel σ)‖ := by
  rw [eval_conj P e (sModel σ)]
  exact norm_equiv _ _

lemma norm_eval_sModel_le {D d N : ℕ} (P : NCPoly D d) (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖P.eval (sModel σ)‖ ≤ P.fullNorm := by
  obtain ⟨U, hU⟩ := exists_unitary_tuple σ (stdOrthonormalBasis ℂ (OnesPerp N)).repr
  rw [← norm_eval_conj_sModel P σ (stdOrthonormalBasis ℂ (OnesPerp N)).repr, ← hU]
  exact le_csSup (bddAbove_fullNorm P) ⟨_, U, rfl⟩


/-! ### Trace bound -/

lemma norm_trace_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (Y : V →L[ℂ] V) :
    ‖LinearMap.trace ℂ V (Y : V →ₗ[ℂ] V)‖ ≤ (Module.finrank ℂ V : ℝ) * ‖Y‖ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i, ‖inner ℂ ((stdOrthonormalBasis ℂ V) i) (Y ((stdOrthonormalBasis ℂ V) i))‖ ≤ ‖Y‖ := by
    intro i
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 := (stdOrthonormalBasis ℂ V).orthonormal.1 i
    have h2 := Y.le_opNorm ((stdOrthonormalBasis ℂ V) i)
    rw [h1] at h2
    simpa [h1] using h2
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  simp

lemma finrank_pi_onesPerp (D N : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => OnesPerp N)) = D * Module.finrank ℂ (OnesPerp N) := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → OnesPerp N)).finrank_eq, Module.finrank_pi_fintype]
  simp

lemma finrank_onesPerp_le (N : ℕ) : Module.finrank ℂ (OnesPerp N) ≤ N := by
  have := Submodule.finrank_le (OnesPerp N)
  simpa using this

lemma abs_trDN_le {D N : ℕ}
    (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ] PiLp 2 (fun _ : Fin D => OnesPerp N)) :
    |trDN D N Y| ≤ ‖Y‖ := by
  unfold trDN
  by_cases hDN : (D : ℝ) * N = 0
  · rw [hDN]; simp
  have hD : (0 : ℝ) < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · simp [h] at hDN
    · exact_mod_cast h
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at hDN
    · exact_mod_cast h
  rw [abs_div, abs_of_pos (mul_pos hD hN), div_le_iff₀ (mul_pos hD hN)]
  have h1 := norm_trace_le Y
  rw [finrank_pi_onesPerp] at h1
  have h2 : (Module.finrank ℂ (OnesPerp N) : ℝ) ≤ N := by exact_mod_cast finrank_onesPerp_le N
  have h3 : |(LinearMap.trace ℂ _ (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin D => OnesPerp N))).re| ≤ ‖LinearMap.trace ℂ _ (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin D => OnesPerp N))‖ := Complex.abs_re_le_norm _
  refine h3.trans (h1.trans ?_)
  push_cast
  have := norm_nonneg Y
  nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]


/-! ### Functional calculus bound and the main lemma -/

lemma le_supOn (h : ℝ[X]) {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    |h.eval x| ≤ supOn (fun x => h.eval x) a b := by
  unfold supOn
  refine le_csSup ?_ ⟨x, hx, rfl⟩
  exact (isCompact_Icc.image (by fun_prop : Continuous fun x => |h.eval x|)).bddAbove

lemma norm_fnCalc_le {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) {K : ℝ}
    (hK : ‖T‖ ≤ K) (h : ℝ[X]) :
    ‖fnCalc (fun x => h.eval x) T‖ ≤ supOn (fun x => h.eval x) (-K) K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hS : 0 ≤ supOn (fun x => h.eval x) (-K) K :=
    (abs_nonneg _).trans (le_supOn h (x := 0) ⟨by linarith, hK0⟩)
  unfold fnCalc
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (cfc _ T) 0]; simpa using hS
  have : IsStarNormal T := hT.isStarNormal
  refine norm_cfc_le hS ?_
  intro z hz
  have hre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  have hzn : ‖z‖ ≤ K := (spectrum.norm_le_norm_of_mem hz).trans hK
  have : |z.re| ≤ K := by
    have := Complex.abs_re_le_norm z
    linarith
  have hmem : z.re ∈ Set.Icc (-K) K := abs_le.mp this |> fun h => ⟨h.1, h.2⟩
  simpa using le_supOn h hmem

lemma abs_expTr_le {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (N : ℕ) (hN : 1 ≤ N)
    (h : ℝ[X]) :
    |expTr P N (fun x => h.eval x)| ≤ cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  have hc : cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm =
      supOn (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
    simp [cNorm, iteratedDeriv_zero]
  rw [hc]
  have hterm : ∀ σ : Fin d → Equiv.Perm (Fin N),
      |trDN D N (fnCalc (fun x => h.eval x) (P.eval (sModel σ)))| ≤
        supOn (fun x => h.eval x) (-P.fullNorm) P.fullNorm := fun σ =>
    (abs_trDN_le _).trans (norm_fnCalc_le _ (isSelfAdjoint_eval P hP _) (norm_eval_sModel_le P σ) h)
  unfold expTr uniformExp
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ : Fin d → Equiv.Perm (Fin N), |trDN D N (fnCalc (fun x => h.eval x) (P.eval (sModel σ)))|
      ≤ ∑ σ : Fin d → Equiv.Perm (Fin N), supOn (fun x => h.eval x) (-P.fullNorm) P.fullNorm :=
        Finset.sum_le_sum fun σ _ => hterm σ
    _ = _ := by simp [mul_comm]

end StrongConv.PartB

end

namespace StrongConv
alias abs_expTr_le := StrongConv.PartB.abs_expTr_le
end StrongConv

section

open Polynomial Filter Topology
open scoped Pointwise

namespace StrongConv.PartC

lemma HasExp.tendsto {F c : ℕ → ℝ} (hF : HasExp F c) (m : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i))
      atTop (𝓝 (c m)) := by
  obtain ⟨C, hC⟩ := hF (m + 1)
  have h0 : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h0
  filter_upwards [hC, eventually_gt_atTop 0] with N hN hpos
  have hNp : (0 : ℝ) < N := by exact_mod_cast hpos
  have e : (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) - c m =
      (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range (m + 1), c i / (N : ℝ) ^ i) := by
    rw [Finset.sum_range_succ]; field_simp; ring
  rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos (pow_pos hNp m)]
  calc (N : ℝ) ^ m * |F N - ∑ i ∈ Finset.range (m + 1), c i / (N : ℝ) ^ i|
      ≤ (N : ℝ) ^ m * (C / (N : ℝ) ^ (m + 1)) := mul_le_mul_of_nonneg_left hN (pow_pos hNp m).le
    _ = C / N := by field_simp; ring

lemma HasExp.asympCoeff_eq {F c : ℕ → ℝ} (hF : HasExp F c) (m : ℕ) : asympCoeff F m = c m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [asympCoeff]
    have h : ∀ N : ℕ, ∑ i : Fin m, asympCoeff F i / (N : ℝ) ^ (i : ℕ) =
        ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i := by
      intro N
      rw [Finset.sum_range (fun i => c i / (N : ℝ) ^ i)]
      exact Finset.sum_congr rfl fun i _ => by rw [ih i i.isLt]
    simp only [h]
    exact (PartC.HasExp.tendsto hF m).limUnder_eq

lemma small_N_arith (a : ℝ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN1 : 1 ≤ N)
    (hN : (N : ℝ) < 2 * a ^ 2) :
    1 + ∑ i ∈ Finset.range m, (4 * a) ^ (4 * i) / (N : ℝ) ^ i ≤ (4 * a) ^ (4 * m) / (N : ℝ) ^ m := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  set t : ℝ := (4 * a) ^ 4 / N with ht
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hNp]
    have : (4 * a) ^ 4 = 256 * a ^ 2 * a ^ 2 := by ring
    nlinarith [sq_nonneg a, one_le_pow₀ (n := 2) ha]
  have key : ∀ k : ℕ, 1 + ∑ i ∈ Finset.range k, t ^ i ≤ t ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← add_assoc, pow_succ]
      have : 1 ≤ t ^ k := one_le_pow₀ (by linarith)
      nlinarith
  have e : ∀ k : ℕ, (4 * a) ^ (4 * k) / (N : ℝ) ^ k = t ^ k := by
    intro k; rw [ht, div_pow, ← pow_mul]
  simp only [e]
  exact key m


lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (u : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, (1 - u i) ≤ ∏ i ∈ s, u i ∧ ∏ i ∈ s, u i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hj0 := h0 j (Finset.mem_insert_self _ _)
    have hj1 := h1 j (Finset.mem_insert_self _ _)
    have hp0 : 0 ≤ ∏ i ∈ s, u i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    constructor
    · nlinarith
    · nlinarith

lemma g_bounds {d Q : ℕ} (a : ℝ) (hQa : (Q : ℝ) ≤ a) (ha1 : 1 ≤ a)
    (hdeg : ((gPoly d Q).natDegree : ℝ) ≤ a) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / (2 * a ^ 2)) :
    1 / 2 ≤ (gPoly d Q).eval x ∧ (gPoly d Q).eval x ≤ 1 := by
  have hlin : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X) = C (-(j : ℝ)) * X + C 1 := by
    intro j _; simp [map_natCast]; ring
  have hnd1 : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X).natDegree = 1 := by
    intro j hj
    rw [hlin j hj]
    apply natDegree_linear
    have : 1 ≤ j := (Finset.mem_Ico.1 hj).1
    have : (1 : ℝ) ≤ j := by exact_mod_cast this
    linarith
  have hne : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X) ≠ 0 := by
    intro j hj h
    have := hnd1 j hj
    rw [h] at this; simp at this
  have hnd : (gPoly d Q).natDegree = ∑ j ∈ Finset.Ico 1 Q, min d (Q / (j + 1)) := by
    rw [gPoly, natDegree_prod _ _ (fun j hj => pow_ne_zero _ (hne j hj))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [natDegree_pow, hnd1 j hj, mul_one]
  have hx1 : x * a ≤ 1 / (2 * a) := by
    calc x * a ≤ 1 / (2 * a ^ 2) * a := mul_le_mul_of_nonneg_right hx (by linarith)
      _ = 1 / (2 * a) := by field_simp
  have hxa : x * a ≤ 1 / 2 := by
    refine hx1.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hj : ∀ j ∈ Finset.Ico 1 Q, 0 ≤ 1 - (j : ℝ) * x ∧ (j : ℝ) * x ≤ a * x := by
    intro j hj'
    have hjQ : (j : ℝ) ≤ a := by
      have : j < Q := (Finset.mem_Ico.1 hj').2
      have : (j : ℝ) ≤ Q := by exact_mod_cast this.le
      linarith
    have : (j : ℝ) * x ≤ a * x := mul_le_mul_of_nonneg_right hjQ hx0
    constructor <;> nlinarith
  have hev : (gPoly d Q).eval x = ∏ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ) * x) ^ min d (Q / (j + 1)) := by
    simp [gPoly, eval_prod]
  rw [hev]
  set u : ℕ → ℝ := fun j => (1 - (j : ℝ) * x) ^ min d (Q / (j + 1)) with hu
  have hu0 : ∀ j ∈ Finset.Ico 1 Q, 0 ≤ u j := fun j h => pow_nonneg (hj j h).1 _
  have hu1 : ∀ j ∈ Finset.Ico 1 Q, u j ≤ 1 := fun j h =>
    pow_le_one₀ (hj j h).1 (by have := (hj j h).2; nlinarith [mul_nonneg (Nat.cast_nonneg j) hx0])
  obtain ⟨hA, hB⟩ := prod_one_sub_ge _ u hu0 hu1
  refine ⟨?_, hB⟩
  have hb : ∀ j ∈ Finset.Ico 1 Q, 1 - u j ≤ (min d (Q / (j + 1)) : ℕ) * (a * x) := by
    intro j h
    have hb1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ -((j : ℝ) * x) by
      have := (hj j h).1; nlinarith [mul_nonneg (Nat.cast_nonneg j) hx0]) (min d (Q / (j + 1)))
    rw [← sub_eq_add_neg] at hb1
    have := (hj j h).2
    have h2 : (0 : ℝ) ≤ (min d (Q / (j + 1)) : ℕ) := Nat.cast_nonneg _
    simp only [hu]
    nlinarith [mul_le_mul_of_nonneg_left this h2]
  have hsum : ∑ j ∈ Finset.Ico 1 Q, (1 - u j) ≤ 1 / 2 := by
    calc ∑ j ∈ Finset.Ico 1 Q, (1 - u j)
        ≤ ∑ j ∈ Finset.Ico 1 Q, (min d (Q / (j + 1)) : ℕ) * (a * x) := Finset.sum_le_sum hb
      _ = ((gPoly d Q).natDegree : ℝ) * (a * x) := by
          rw [hnd, ← Finset.sum_mul]; push_cast; rfl
      _ ≤ a * (a * x) := mul_le_mul_of_nonneg_right hdeg (by positivity)
      _ = a * (x * a) := by ring
      _ ≤ a * (1 / (2 * a)) := mul_le_mul_of_nonneg_left hx1 (by linarith)
      _ = 1 / 2 := by field_simp
  linarith


lemma density_lemma (M : ℕ) (hM : 0 < M) (q : ℝ) (hq0 : 0 < q) (hq : 4 * q ^ 2 ≤ 2 * M) :
    Set.Icc (0 : ℝ) (1 / M) ⊆ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} +
      Set.Icc (-((1 / (M : ℝ)) / (4 * q ^ 2))) ((1 / (M : ℝ)) / (4 * q ^ 2)) := by
  intro y hy
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := (1 / (M : ℝ)) / (4 * q ^ 2) with hδ
  have hq2 : 0 < 4 * q ^ 2 := by positivity
  have hδD : 1 / (2 * (M : ℝ) ^ 2) ≤ δ := by
    rw [hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have key : ∃ x ∈ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)}, |y - x| ≤ δ := by
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / δ)
      refine ⟨1 / ((max n M + 1 : ℕ) : ℝ), ⟨_, by omega, rfl⟩, ?_⟩
      have hn' : (1 / δ) ≤ ((max n M + 1 : ℕ) : ℝ) := by
        refine hn.trans ?_
        have : n ≤ max n M + 1 := by omega
        exact_mod_cast this
      have hpos : (0 : ℝ) < ((max n M + 1 : ℕ) : ℝ) := by positivity
      rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hδpos] at hn'
      linarith
    · have hyM : (M : ℝ) ≤ 1 / y := by
        rw [le_div_iff₀ hpos]
        have := hy.2
        rw [le_div_iff₀ hMp] at this
        linarith
      set n := ⌊1 / y⌋₊ with hn
      have hnM : M ≤ n := Nat.le_floor hyM
      have hn1 : (n : ℝ) ≤ 1 / y := Nat.floor_le (by positivity)
      have hn2 : 1 / y < n + 1 := Nat.lt_floor_add_one _
      have hnp : (0 : ℝ) < n := by
        have : (M : ℝ) ≤ n := by exact_mod_cast hnM
        linarith
      have hy1 : y ≤ 1 / (n : ℝ) := by
        rw [le_div_iff₀ hnp]; rw [le_div_iff₀ hpos] at hn1; linarith
      have hy2 : 1 / ((n : ℝ) + 1) < y := by
        rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hpos] at hn2; linarith
      have hgap : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) ≤ 1 / (M : ℝ) ^ 2 := by
        have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
          field_simp; ring
        rw [this]
        have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have hD : 1 / (M : ℝ) ^ 2 = 2 * (1 / (2 * (M : ℝ) ^ 2)) := by field_simp
      by_cases hc : 1 / (n : ℝ) - y ≤ 1 / (2 * (M : ℝ) ^ 2)
      · refine ⟨1 / (n : ℝ), ⟨n, hnM, rfl⟩, ?_⟩
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · push Not at hc
        refine ⟨1 / ((n + 1 : ℕ) : ℝ), ⟨n + 1, by omega, rfl⟩, ?_⟩
        push_cast
        rw [abs_of_nonneg (by linarith)]
        linarith
  obtain ⟨x, hx, hxy⟩ := key
  refine Set.mem_add.2 ⟨x, hx, y - x, ?_, by ring⟩
  rw [Set.mem_Icc]
  exact abs_le.1 hxy


lemma cNorm_zero_eq (h : ℝ → ℝ) (a b : ℝ) :
    cNorm 0 h a b = sSup ((fun x => |iteratedDeriv 0 h x|) '' Set.Icc a b) := by
  simp [cNorm, supOn]

lemma abs_le_cNorm_zero (h : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn (iteratedDeriv 0 h) (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) : |iteratedDeriv 0 h x| ≤ cNorm 0 h a b := by
  rw [cNorm_zero_eq]
  exact le_csSup (isCompact_Icc.bddAbove_image hc.abs) ⟨x, hx, rfl⟩

lemma polyc {n : ℕ} (p : ℝ[X]) : ContDiff ℝ n (fun x => p.eval x) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (n : WithTop ℕ∞)
  simpa only [Polynomial.coe_aeval_eq_eval] using this

lemma poly_div_contDiffAt (f g : ℝ[X]) (n : ℕ) (y : ℝ) (hy : g.eval y ≠ 0) :
    ContDiffAt ℝ n (fun x => f.eval x / g.eval x) y :=
  (polyc f).contDiffAt.div (polyc g).contDiffAt hy

lemma poly_div_continuousOn_iteratedDeriv (f g : ℝ[X]) (b : ℝ) (hb : 0 < b)
    (hg0 : ∀ x ∈ Set.Icc 0 b, g.eval x ≠ 0) (m : ℕ) :
    ContinuousOn (iteratedDeriv m (fun x => f.eval x / g.eval x)) (Set.Icc 0 b) := by
  have hcd : ContDiffOn ℝ m (fun x => f.eval x / g.eval x) (Set.Icc 0 b) :=
    fun y hy => (poly_div_contDiffAt f g m y (hg0 y hy)).contDiffWithinAt
  have := hcd.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hb)
  refine this.congr fun y hy => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
    (poly_div_contDiffAt f g m y (hg0 y hy)) hy).symm


lemma taylor_step (Ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ)
    (hcd : ∀ y ∈ Set.Icc 0 x, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ y) (C : ℝ)
    (hC : ∀ y ∈ Set.Icc 0 x, |iteratedDeriv (n + 1) Ψ y| ≤ C) :
    |Ψ x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k| ≤
      C * x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hu : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx.le
  have hcdOn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ (Set.uIcc 0 x) := by
    rw [hu]; exact fun y hy => (hcd y hy).contDiffWithinAt
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx.ne hcdOn
  have hx'I : x' ∈ Set.Icc 0 x := by
    rw [Set.uIoo_of_le hx.le] at hx'
    exact ⟨hx'.1.le, hx'.2.le⟩
  have htay : taylorWithinEval Ψ n (Set.uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [hu, smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      ((hcd 0 ⟨le_rfl, hx.le⟩).of_le (by exact_mod_cast (by omega : k ≤ n + 1))) ⟨le_rfl, hx.le⟩]
    rw [sub_zero]; field_simp
  rw [htay] at hrem
  rw [hrem, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hx,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' hx'I) (by positivity)


lemma four_mul_pow_le (m : ℕ) (hm : 1 ≤ m) : (4 : ℝ) * 40 ^ m ≤ 256 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : (40 : ℝ) ^ k ≤ 256 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h0 : (0 : ℝ) ≤ 40 ^ k := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

lemma core_estimate {d Q : ℕ} (hQ : 1 ≤ Q) (f : ℝ[X])
    (hf : (f.natDegree : ℝ) ≤ Q * (1 + Real.log d)) (F : ℕ → ℝ) (s : ℝ)
    (hF : ∀ N : ℕ, Q ≤ N → F N = f.eval (1 / (N : ℝ)) / (gPoly d Q).eval (1 / (N : ℝ)))
    (hs : ∀ N : ℕ, Q ≤ N → |F N| ≤ s) (m : ℕ) (hm : 1 ≤ m) (N : ℕ)
    (hN : 2 * (Q * (1 + Real.log d)) ^ 2 ≤ (N : ℝ)) :
    |F N - ∑ i ∈ Finset.range m,
        (iteratedDeriv i (fun x => f.eval x / (gPoly d Q).eval x) 0 / (i.factorial : ℝ)) /
          (N : ℝ) ^ i| ≤ (4 * Q * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s := by
  have hL : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  set a : ℝ := Q * (1 + Real.log d) with ha
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  have hQa : (Q : ℝ) ≤ a := by rw [ha]; nlinarith
  set g := gPoly d Q with hgdef
  obtain ⟨hgdeg, -⟩ := exists_uniformExp_trN_wordEval_eq_div d Q hQ [] (by simp)
  rw [← ha] at hgdeg
  set M : ℕ := ⌈2 * a ^ 2⌉₊ with hMdef
  have hMge : 2 * a ^ 2 ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ 4 * a ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * a ^ 2 by positivity)
    nlinarith
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha1
  have hMp : (0 : ℝ) < M := by linarith
  have hMpos : 0 < M := by exact_mod_cast hMp
  have h1M : 1 / (M : ℝ) ≤ 1 / (2 * a ^ 2) := one_div_le_one_div_of_le (by positivity) hMge
  have hg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / (M : ℝ) → 1 / 2 ≤ g.eval x ∧ g.eval x ≤ 1 :=
    fun x h0 h1 => g_bounds a hQa ha1 hgdeg x h0 (h1.trans h1M)
  set Ψ : ℝ → ℝ := fun x => f.eval x / g.eval x with hΨ
  set q : ℕ := ⌊a⌋₊ with hqdef
  have hqa : (q : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hq1 : 1 ≤ q := Nat.le_floor (by simpa using ha1)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hfq : f.natDegree ≤ q := Nat.le_floor hf
  have hgq : g.natDegree ≤ q := Nat.le_floor hgdeg
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs Q le_rfl)
  have hb : (0 : ℝ) < 1 / M := by positivity
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / M), g.eval x ≠ 0 := fun x hx =>
    by have := (hg x hx.1 hx.2).1; intro h; rw [h] at this; norm_num at this
  -- Step 2: bound on f over the interval
  have hnQ : ∀ n : ℕ, M ≤ n → Q ≤ n := by
    intro n hn
    have : (M : ℝ) ≤ n := by exact_mod_cast hn
    have : (Q : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hfI : ∀ n : ℕ, M ≤ n → |f.eval (1 / (n : ℝ))| ≤ s := by
    intro n hn
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    have hx1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) :=
      one_div_le_one_div_of_le hMp (by exact_mod_cast hn)
    obtain ⟨hg1, hg2⟩ := hg _ (by positivity) hx1
    have hFn := hF n (hnQ n hn)
    have : f.eval (1 / (n : ℝ)) = F n * g.eval (1 / (n : ℝ)) := by
      rw [hFn]; field_simp
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < g.eval (1 / (n : ℝ)))]
    calc |F n| * g.eval (1 / (n : ℝ)) ≤ s * 1 :=
          mul_le_mul (hs n (hnQ n hn)) hg2 (by linarith) hs0
      _ = s := mul_one s
  set I : Set ℝ := {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} with hI
  have hIsub : I ⊆ Set.Icc 0 (1 / (M : ℝ)) := by
    rintro x ⟨n, hn, rfl⟩
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    exact ⟨by positivity, one_div_le_one_div_of_le hMp (by exact_mod_cast hn)⟩
  have hdens := density_lemma M hMpos q (by linarith) (by nlinarith)
  have h42 := cNorm_le_two_mul_sSup_of_subset_add q f hfq (1 / (M : ℝ)) hb I hIsub hdens
  have hsup : sSup ((fun x => |f.eval x|) '' I) ≤ s := by
    refine csSup_le ⟨_, 1 / (M : ℝ), ⟨M, le_rfl, rfl⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    exact hfI n hn
  have hcf : cNorm 0 (fun x => f.eval x) 0 (1 / (M : ℝ)) ≤ 2 * s := by linarith
  have hfcont : ContinuousOn (iteratedDeriv 0 (fun x => f.eval x)) (Set.Icc 0 (1 / (M : ℝ))) := by
    rw [iteratedDeriv_zero]; exact (polyc (n := 0) f).continuous.continuousOn
  have hΨ4 : cNorm 0 Ψ 0 (1 / (M : ℝ)) ≤ 4 * s := by
    rw [cNorm_zero_eq]
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hg1, hg2⟩ := hg x hx.1 hx.2
    have h1 := abs_le_cNorm_zero (fun x => f.eval x) 0 (1 / (M : ℝ)) hfcont x hx
    rw [iteratedDeriv_zero] at h1 ⊢
    simp only [hΨ]
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (f.eval x)]
  -- Step 3
  have hmain := cNorm_iteratedDeriv_div_le q m f g hfq hgq (1 / (M : ℝ)) hb hg0
  set S := sSup {t | ∃ x ∈ Set.Icc (0 : ℝ) (1 / M), ∃ y ∈ Set.Icc (0 : ℝ) (1 / M),
    t = |g.eval x / g.eval y|} with hS
  have hS0 : 0 ≤ S := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact abs_nonneg _
  have hS2 : S ≤ 2 := by
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨hx1, hx2⟩ := hg x hx.1 hx.2
    obtain ⟨hy1, hy2⟩ := hg y hy.1 hy.2
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), abs_of_pos (by linarith : 0 < g.eval y),
      div_le_iff₀ (by linarith)]
    linarith
  have hbase : 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) ≤ 40 * a ^ 4 := by
    have e : 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) = 5 * S * (q : ℝ) ^ 2 * M := by
      field_simp
    rw [e]
    have hq2 : (q : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) hqa 2
    calc 5 * S * (q : ℝ) ^ 2 * M ≤ 5 * 2 * a ^ 2 * (4 * a ^ 2) := by
          have h1 : 5 * S * (q : ℝ) ^ 2 ≤ 5 * 2 * a ^ 2 :=
            mul_le_mul (by linarith) hq2 (by positivity) (by norm_num)
          exact mul_le_mul h1 hMle hMp.le (by positivity)
      _ = 40 * a ^ 4 := by ring
  have hbase0 : 0 ≤ 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) := by positivity
  have hC : cNorm 0 (iteratedDeriv m Ψ) 0 (1 / (M : ℝ)) ≤
      m.factorial * (40 * a ^ 4) ^ m * (4 * s) := by
    refine hmain.trans ?_
    have hp := pow_le_pow_left₀ hbase0 hbase m
    have h4 : 0 ≤ cNorm 0 Ψ 0 (1 / (M : ℝ)) := by
      rw [cNorm_zero_eq]; exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hΨ4 h4 (by positivity)
  -- Step 4: Taylor
  have hMN : M ≤ N := Nat.ceil_le.2 hN
  have hNQ : Q ≤ N := hnQ N hMN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le hMp (by exact_mod_cast hMN)
  have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hxM : 1 / (N : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hMp (by exact_mod_cast hMN)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hT := taylor_step Ψ (1 / (N : ℝ)) hx n
    (fun y hy => poly_div_contDiffAt f g _ y (hg0 y ⟨hy.1, hy.2.trans hxM⟩))
    (cNorm 0 (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ)))
    (fun y hy => by
      have hyM : y ∈ Set.Icc (0 : ℝ) (1 / M) := ⟨hy.1, hy.2.trans hxM⟩
      have := abs_le_cNorm_zero (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ))
        (by rw [iteratedDeriv_zero]; exact poly_div_continuousOn_iteratedDeriv f g _ hb hg0 _) y hyM
      rwa [iteratedDeriv_zero] at this)
  have hFN : F N = Ψ (1 / (N : ℝ)) := hF N hNQ
  have hsum : ∑ i ∈ Finset.range (n + 1), iteratedDeriv i Ψ 0 / (i.factorial : ℝ) / (N : ℝ) ^ i =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * (1 / (N : ℝ)) ^ k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [hFN, hsum]
  refine hT.trans ?_
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hxp : (1 / (N : ℝ)) ^ (n + 1) = 1 / (N : ℝ) ^ (n + 1) := by rw [one_div, one_div, inv_pow]
  calc cNorm 0 (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ)) * (1 / (N : ℝ)) ^ (n + 1) /
        ((n + 1).factorial : ℝ)
      ≤ ((n + 1).factorial * (40 * a ^ 4) ^ (n + 1) * (4 * s)) * (1 / (N : ℝ)) ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hfac.le
        exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = 4 * 40 ^ (n + 1) * (a ^ 4) ^ (n + 1) / (N : ℝ) ^ (n + 1) * s := by
        rw [hxp, mul_pow]; field_simp
    _ ≤ (4 * Q * (1 + Real.log d)) ^ (4 * (n + 1)) / (N : ℝ) ^ (n + 1) * s := by
        have e : (4 * (Q : ℝ) * (1 + Real.log d)) ^ (4 * (n + 1)) = 256 ^ (n + 1) * (a ^ 4) ^ (n + 1) := by
          rw [show 4 * (Q : ℝ) * (1 + Real.log d) = 4 * a by rw [ha]; ring, pow_mul,
            show (4 * a) ^ 4 = 256 * a ^ 4 by ring, mul_pow]
        rw [e]
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (pow_pos hNp _).le) hs0
        exact mul_le_mul_of_nonneg_right (four_mul_pow_le (n + 1) hm) (by positivity)

end StrongConv.PartC

end

namespace StrongConv
alias core_estimate := StrongConv.PartC.core_estimate
alias HasExp.asympCoeff_eq := StrongConv.PartC.HasExp.asympCoeff_eq
alias HasExp.tendsto := StrongConv.PartC.HasExp.tendsto
alias small_N_arith := StrongConv.PartC.small_N_arith
end StrongConv

namespace StrongConv
/-! ## Assembly: Theorem 6.1 and Corollary 6.2 -/

lemma HasExp.add {F G c e : ℕ → ℝ} (hF : HasExp F c) (hG : HasExp G e) :
    HasExp (fun N => F N + G N) (fun i => c i + e i) := by
  intro m
  obtain ⟨C₁, h₁⟩ := hF m
  obtain ⟨C₂, h₂⟩ := hG m
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with N hN₁ hN₂
  have : F N + G N - ∑ i ∈ Finset.range m, (c i + e i) / (N : ℝ) ^ i =
      (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) +
        (G N - ∑ i ∈ Finset.range m, e i / (N : ℝ) ^ i) := by
    simp only [add_div, Finset.sum_add_distrib]; ring
  rw [this, add_div]
  exact (abs_add_le _ _).trans (add_le_add hN₁ hN₂)

lemma HasExp.const_mul {F c : ℕ → ℝ} (hF : HasExp F c) (r : ℝ) :
    HasExp (fun N => r * F N) (fun i => r * c i) := by
  intro m
  obtain ⟨C, h⟩ := hF m
  refine ⟨|r| * C, ?_⟩
  filter_upwards [h] with N hN
  have : r * F N - ∑ i ∈ Finset.range m, r * c i / (N : ℝ) ^ i =
      r * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) := by
    rw [mul_sub, Finset.mul_sum]; simp only [mul_div_assoc]
  rw [this, abs_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hN (abs_nonneg r)

/-- The data of one test polynomial: the expansion coefficients and the bound for large `N`. -/
lemma exp_data {D d q₀ : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀)
    (hq₀' : 1 ≤ q₀) (q : ℕ) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) :
    HasExp (fun N => expTr P N (fun x => h.eval x)) (fun i => nu P i h) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 2 * ((q : ℝ) * q₀ * (1 + Real.log d)) ^ 2 ≤ (N : ℝ) →
      |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nu P i h / (N : ℝ) ^ i| ≤
        (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
          cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  obtain ⟨f, hf, hF⟩ := rational_expTr P hP hq₀ hq₀' q hq h hh
  set s := cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm with hs
  have hQ : 1 ≤ q * q₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hL : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
  have hcore := core_estimate hQ f hf (fun N => expTr P N (fun x => h.eval x)) s hF
    (fun N hN => abs_expTr_le P hP N (le_trans hQ hN) h)
  set c : ℕ → ℝ := fun i =>
    iteratedDeriv i (fun x => f.eval x / (gPoly d (q * q₀)).eval x) 0 / (i.factorial : ℝ) with hc
  have hMN : ∀ N : ℕ, 2 * ((q : ℝ) * q₀ * (1 + Real.log d)) ^ 2 ≤ (N : ℝ) →
      2 * (((q * q₀ : ℕ) : ℝ) * (1 + Real.log d)) ^ 2 ≤ (N : ℝ) := by
    intro N hN; push_cast; exact hN
  have hbound : ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 2 * ((q : ℝ) * q₀ * (1 + Real.log d)) ^ 2 ≤ (N : ℝ) →
      |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i| ≤
        (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s := by
    intro m hm N hN
    have := hcore m hm N (hMN N hN)
    simpa [hc, mul_assoc] using this
  have hexp : HasExp (fun N => expTr P N (fun x => h.eval x)) c := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨s, ?_⟩
      filter_upwards [eventually_ge_atTop (q * q₀)] with N hN
      simpa using abs_expTr_le P hP N (le_trans hQ hN) h
    · refine ⟨(4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) * s, ?_⟩
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * ((q : ℝ) * q₀ * (1 + Real.log d)) ^ 2)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have := hbound m hm N (hN₀.trans (by exact_mod_cast hN))
      rwa [div_mul_eq_mul_div] at this
  have hnu : ∀ i, nu P i h = c i := fun i => hexp.asympCoeff_eq i
  refine ⟨?_, ?_⟩
  · have : (fun i => nu P i h) = c := funext hnu
    rw [this]; exact hexp
  · intro m hm N hN
    simpa [hnu] using hbound m hm N hN

theorem master_dev {D d q₀ : ℕ} (P : NCPoly D d)
    (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀) (hq₀' : 1 ≤ q₀) :
    (∀ i, IsLinearMap ℝ (nu P i)) ∧
      ∀ N m q : ℕ, 1 ≤ N → 1 ≤ m → 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nu P i h / (N : ℝ) ^ i| ≤
          (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
            cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  refine ⟨?_, ?_⟩
  · intro i
    have hE0' : ∀ N, expTr P N (fun x => (0 : ℝ[X]).eval x) = 0 := by
      intro N
      have := expTr_add_smul P hP N 0 0 1
      rw [show (0 : ℝ[X]) + Polynomial.C 1 * 0 = 0 by simp] at this
      linarith
    have key : ∀ (h₁ h₂ : ℝ[X]) (r : ℝ), nu P i (h₁ + Polynomial.C r * h₂) =
        nu P i h₁ + r * nu P i h₂ := by
      intro h₁ h₂ r
      set q := max (max h₁.natDegree h₂.natDegree) 1 with hq
      have hq1 : 1 ≤ q := le_max_right _ _
      have hh₁ : h₁.natDegree ≤ q := (le_max_left _ _).trans (le_max_left _ _)
      have hh₂ : h₂.natDegree ≤ q := (le_max_right _ _).trans (le_max_left _ _)
      have hh₃ : (h₁ + Polynomial.C r * h₂).natDegree ≤ q :=
        (natDegree_add_le _ _).trans (max_le hh₁ ((natDegree_C_mul_le _ _).trans hh₂))
      have e₁ := (exp_data P hP hq₀ hq₀' q hq1 h₁ hh₁).1
      have e₂ := (exp_data P hP hq₀ hq₀' q hq1 h₂ hh₂).1
      have e₃ := (exp_data P hP hq₀ hq₀' q hq1 _ hh₃).1
      have e₄ := e₁.add (e₂.const_mul r)
      have hF : (fun N => expTr P N (fun x => (h₁ + Polynomial.C r * h₂).eval x)) =
          fun N => expTr P N (fun x => h₁.eval x) + r * expTr P N (fun x => h₂.eval x) :=
        funext fun N => expTr_add_smul P hP N h₁ h₂ r
      rw [hF] at e₃
      have a₃ := e₃.asympCoeff_eq i
      have a₄ := e₄.asympCoeff_eq i
      have : nu P i (h₁ + Polynomial.C r * h₂) = asympCoeff
          (fun N => expTr P N (fun x => h₁.eval x) + r * expTr P N (fun x => h₂.eval x)) i := by
        unfold nu; rw [hF]
      rw [this, a₄]
    refine ⟨fun h₁ h₂ => ?_, fun r h => ?_⟩
    · simpa using key h₁ h₂ 1
    · have := key 0 h r
      simp only [zero_add] at this
      have hz : nu P i 0 = 0 := by
        have e0 : HasExp (fun N => expTr P N (fun x => (0 : ℝ[X]).eval x)) (fun _ => 0) := by
          intro m
          refine ⟨0, Filter.Eventually.of_forall fun N => ?_⟩
          show |expTr P N (fun x => (0 : ℝ[X]).eval x) - _| ≤ _
          rw [hE0' N]; simp
        have := e0.asympCoeff_eq i
        simpa [nu] using this
      rw [Polynomial.smul_eq_C_mul, this, hz]; simp
  · intro N m q hN hm hq h hh
    obtain ⟨hexp, hbound⟩ := exp_data P hP hq₀ hq₀' q hq h hh
    set s := cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm with hs
    by_cases hM : 2 * ((q : ℝ) * q₀ * (1 + Real.log d)) ^ 2 ≤ (N : ℝ)
    · exact hbound m hm N hM
    · push Not at hM
      have hL : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
      have ha : (1 : ℝ) ≤ (q : ℝ) * q₀ * (1 + Real.log d) := by
        have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have h2 : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀'
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q - 1) (by linarith : (0:ℝ) ≤ q₀ - 1)]
      have hs0 : |expTr P N (fun x => h.eval x)| ≤ s := abs_expTr_le P hP N hN h
      have harith := small_N_arith ((q : ℝ) * q₀ * (1 + Real.log d)) ha m hm N hN hM
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hs_nn : 0 ≤ s := (abs_nonneg _).trans hs0
      calc |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nu P i h / (N : ℝ) ^ i|
          ≤ |expTr P N (fun x => h.eval x)| + ∑ i ∈ Finset.range m, |nu P i h| / (N : ℝ) ^ i := by
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [abs_div, abs_of_pos (pow_pos hNpos i)]
        _ ≤ s + ∑ i ∈ Finset.range m,
              (4 * q * q₀ * (1 + Real.log d)) ^ (4 * i) * s / (N : ℝ) ^ i := by
            refine add_le_add hs0 (Finset.sum_le_sum fun i _ => ?_)
            exact div_le_div_of_nonneg_right
              (StrongConv.abs_nu_le P hP hq₀ hq₀' i q hq h hh) (pow_pos hNpos i).le
        _ = s * (1 + ∑ i ∈ Finset.range m, (4 * ((q : ℝ) * q₀ * (1 + Real.log d))) ^ (4 * i) /
              (N : ℝ) ^ i) := by
            rw [mul_add s 1, mul_one, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (4 * (q : ℝ) * q₀ * (1 + Real.log d)) = 4 * ((q : ℝ) * q₀ * (1 + Real.log d))
              by ring]
            ring
        _ ≤ s * ((4 * ((q : ℝ) * q₀ * (1 + Real.log d))) ^ (4 * m) / (N : ℝ) ^ m) :=
            mul_le_mul_of_nonneg_left harith hs_nn
        _ = _ := by
            rw [show (4 * (q : ℝ) * q₀ * (1 + Real.log d)) = 4 * ((q : ℝ) * q₀ * (1 + Real.log d))
              by ring]
            ring

end StrongConv

theorem solution : type_of% @StrongConv.master_dev := @StrongConv.master_dev
