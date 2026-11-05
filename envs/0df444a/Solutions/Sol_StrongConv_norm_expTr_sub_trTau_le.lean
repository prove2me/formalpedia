-- Prove2me | solution 1 for StrongConv.norm_expTr_sub_trTau_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:46:28.285723+00:00
-- url     : https://prove2.me/submissions/e30955c5-e52c-41ee-8469-5778ee14633f

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_isLinearMap_nu_and_abs_expTr_sub_sum_nu_le
import Theorems.Thm_StrongConv_abs_nu_le
import Theorems.Thm_StrongConv_abs_coeff_zero_le_and_sum_le_lpNormCircle
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
section
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

end StrongConv.PartB

end

namespace StrongConv
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

end StrongConv.PartC

end

namespace StrongConv
alias HasExp.asympCoeff_eq := StrongConv.PartC.HasExp.asympCoeff_eq
end StrongConv

namespace StrongConv
/-! ## Assembly: Theorem 6.1 and Corollary 6.2 -/

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv
/-!
# Blueprint for Theorem 7.1 and Corollary 7.2 (CGTvH pp. 22–23)

Route.  For a real polynomial `p`, expand `p = ∑ aⱼ Tⱼ(x/K)` (`K = ‖P‖`), apply Theorem 6.1 to each
`Tⱼ(x/K)`, the constant term being exact, and bound `∑ jᵐ |aⱼ|` by Lemma 4.4.  A smooth `h` is
approximated, with its derivatives, by polynomials on a large interval; the trace side, the
distributions `νᵢ` (the unique extensions given by Lemma 4.7) and the `L^β` side all pass to
the limit.  For Corollary 7.2 the limit `(tr ⊗ τ)(h(P(s)))` is controlled through
`|ν₀(p)| ≤ sup_{[-K,K]} |p|` (Corollary 6.2 with `m = 0`), so no bound on `‖P(s)‖` is needed.
-/
/-- `Tⱼ(x/K)` as a polynomial. -/
noncomputable def chebK (K : ℝ) (j : ℕ) : ℝ[X] := (Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
lemma sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range (q + 1), f j = f 0 + ∑ j ∈ Finset.Icc 1 q, f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rfl

lemma natDegree_chebK_le (K : ℝ) (j : ℕ) : (chebK K j).natDegree ≤ j := by
  unfold chebK
  refine (natDegree_comp_le).trans ?_
  have h1 : (C K⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simp
  simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
  nlinarith [h1]

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv
alias natDegree_chebK_le := StrongConv.Part7B.natDegree_chebK_le

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
lemma supOn_le_of_forall {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ c) : supOn f a b ≤ c := by
  unfold supOn
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma cNorm_chebK_le (K : ℝ) (hK : 0 < K) (j : ℕ) :
    cNorm 0 (fun x => (chebK K j).eval x) (-K) K ≤ 1 := by
  unfold cNorm
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero]
  apply supOn_le_of_forall (by linarith)
  intro x hx
  simp only [chebK, eval_comp, eval_mul, eval_C, eval_X]
  apply Chebyshev.abs_eval_T_real_le_one
  rw [abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv

alias cNorm_chebK_le := StrongConv.Part7B.cNorm_chebK_le

alias sum_range_succ_eq_add_Icc := StrongConv.Part7B.sum_range_succ_eq_add_Icc

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
set_option linter.unusedVariables false in
lemma cNorm_zero_le_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (K : ℝ)
    (hK : 0 ≤ K) (ε : ℝ) (hfg : ∀ x ∈ Set.Icc (-K) K, |f x - g x| ≤ ε) :
    cNorm 0 f (-K) K ≤ cNorm 0 g (-K) K + ε := by
  unfold cNorm
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero]
  have hbdd : BddAbove ((fun x => |g x|) '' Set.Icc (-K) K) :=
    (isCompact_Icc.image (hg.abs)).bddAbove
  apply supOn_le_of_forall (by linarith)
  intro x hx
  have h1 : |g x| ≤ supOn g (-K) K := le_csSup hbdd ⟨x, hx, rfl⟩
  have h2 := hfg x hx
  have := abs_sub_abs_le_abs_sub (f x) (g x)
  linarith

lemma iteratedDeriv_sub_of_contDiff (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℕ) :
    iteratedDeriv r (fun x => f x - g x) = fun x => iteratedDeriv r f x - iteratedDeriv r g x := by
  funext x
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  exact iteratedDeriv_fun_sub (hf.contDiffAt.of_le hr) (hg.contDiffAt.of_le hr)

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv
alias iteratedDeriv_sub_of_contDiff := StrongConv.Part7B.iteratedDeriv_sub_of_contDiff

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
lemma abs_iteratedDeriv_cos_le (i : ℕ) (θ : ℝ) : |iteratedDeriv i Real.cos θ| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_cos_le_one θ
  · rw [Real.iteratedDeriv_odd_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_sin_le_one θ

lemma abs_iteratedDeriv_comp_cos_le (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ)
    (hK : 0 ≤ K) (r : ℕ) (ε : ℝ)
    (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K, |iteratedDeriv i g x| ≤ ε) (θ : ℝ) :
    |iteratedDeriv r (fun θ => g (K * Real.cos θ)) θ| ≤ (r.factorial : ℝ) * ε * (max K 1) ^ r := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun θ => K * Real.cos θ) := contDiff_const.mul Real.contDiff_cos
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hmem : K * Real.cos θ ∈ Set.Icc (-K) K := by
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    constructor <;> nlinarith
  have key := norm_iteratedFDeriv_comp_le (g := g) (f := fun θ => K * Real.cos θ) (n := r)
    hg hf hr θ (C := ε) (D := max K 1) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at key
    exact key
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hε i hi _ hmem
  · intro i hi1 _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg hK]
    calc K * |iteratedDeriv i Real.cos θ| ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le i θ) hK
      _ ≤ max K 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max K 1 ^ i := le_self_pow₀ (le_max_right _ _) (by omega)

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv
alias abs_iteratedDeriv_comp_cos_le := StrongConv.Part7B.abs_iteratedDeriv_comp_cos_le

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
lemma lpNormCircle_le_add (β : ℝ) (hβ : 1 < β) (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (δ : ℝ) (hδ : ∀ θ, |F θ - G θ| ≤ δ) :
    lpNormCircle β F ≤ lpNormCircle β G + (2 * Real.pi + 1) * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set μ := MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))
  set p := ENNReal.ofReal β
  have hp1 : 1 ≤ p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hβ.le
  have hptr : p.toReal = β := ENNReal.toReal_ofReal (by linarith)
  have hμ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp [μ, Real.volume_Icc]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hbound : ∀ (H : ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ x ∈ Set.Icc 0 (2 * Real.pi), ‖H x‖ ≤ C) →
      MeasureTheory.eLpNorm H p μ ≤ ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * C) := by
    intro H C hC hH
    refine (MeasureTheory.eLpNorm_le_of_ae_bound
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hH)).trans (le_of_eq ?_)
    rw [hμ, hptr, ENNReal.ofReal_rpow_of_nonneg hpi (by positivity), ← ENNReal.ofReal_mul
      (by positivity)]
  have hFG : MeasureTheory.eLpNorm (fun x => F x - G x) p μ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    hbound _ δ hδ0 (fun x _ => by rw [Real.norm_eq_abs]; exact hδ x)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G)
    (s := Set.Icc 0 (2 * Real.pi)) hG.continuousOn
  have hGfin : MeasureTheory.eLpNorm G p μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hbound G (max M 0) (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)))
  have htri : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + MeasureTheory.eLpNorm (fun x => F x - G x) p μ := by
    have := MeasureTheory.eLpNorm_add_le (μ := μ) (p := p) (f := G) (g := fun x => F x - G x)
      hG.aestronglyMeasurable (hF.sub hG).aestronglyMeasurable hp1
    convert this using 2
    funext x; simp
  have hsum : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    htri.trans (add_le_add_right hFG _)
  unfold lpNormCircle
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, ENNReal.ofReal_ne_top⟩) hsum
  rw [ENNReal.toReal_add hGfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h1
  refine h1.trans (add_le_add_right ?_ _)
  apply mul_le_mul_of_nonneg_right _ hδ0
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc (2 * Real.pi) ^ β⁻¹ ≤ (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpi1 (inv_le_one_of_one_le₀ hβ.le)
    _ ≤ 2 * Real.pi + 1 := by rw [Real.rpow_one]; linarith

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv
alias lpNormCircle_le_add := StrongConv.Part7B.lpNormCircle_le_add

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7B
open StrongConv
lemma natDegree_chebK (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).natDegree = j := by
  unfold chebK
  rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hK.ne')]
  simp

lemma chebK_coeff_ne_zero (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).coeff j ≠ 0 := by
  have h := natDegree_chebK K hK j
  have hne : chebK K j ≠ 0 := by
    intro h0
    have h1 : (chebK K j).leadingCoeff ≠ 0 := by
      unfold chebK
      rw [leadingCoeff_comp (by rw [natDegree_C_mul_X _ (inv_ne_zero hK.ne')]; norm_num)]
      simp [hK.ne']
    rw [h0] at h1
    simp at h1
  have := leadingCoeff_ne_zero.mpr hne
  rwa [leadingCoeff, h] at this

lemma exists_chebyshev_expansion_aux (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∀ p : ℝ[X], p.natDegree ≤ m →
      ∃ a : ℕ → ℝ, p = ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
  induction m with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0, ?_⟩
    rw [eq_C_of_natDegree_le_zero hp]
    simp [chebK]
  | succ m ih =>
    intro p hp
    set c := p.coeff (m + 1) / (chebK K (m + 1)).coeff (m + 1)
    have hc : c * (chebK K (m + 1)).coeff (m + 1) = p.coeff (m + 1) :=
      div_mul_cancel₀ _ (chebK_coeff_ne_zero K hK (m + 1))
    have hdeg : (p - Polynomial.C c * chebK K (m + 1)).natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_chebK_le K (m + 1)) h)]
        simp
      · obtain rfl : N = m + 1 := by omega
        rw [hc]; simp
    obtain ⟨a, ha⟩ := ih _ hdeg
    refine ⟨fun j => if j = m + 1 then c else a j, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [if_true]
    have : ∑ j ∈ Finset.range (m + 1),
        Polynomial.C (if j = m + 1 then c else a j) * chebK K j =
        ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp at hj
      rw [if_neg (by omega)]
    rw [this, ← ha]
    ring

lemma exists_chebyshev_expansion (p : ℝ[X]) (K : ℝ) (hK : 0 < K) :
    ∃ a : ℕ → ℝ,
      (∀ x : ℝ, p.eval x = ∑ j ∈ Finset.range (p.natDegree + 1),
        a j * (Chebyshev.T ℝ j).eval (x / K)) ∧
      p = ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.C (a j) * chebK K j := by
  obtain ⟨a, ha⟩ := exists_chebyshev_expansion_aux K hK p.natDegree p le_rfl
  refine ⟨a, ?_, ha⟩
  intro x
  conv_lhs => rw [ha]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [chebK, eval_comp, div_eq_inv_mul]

lemma exists_antiderivative (q : ℝ[X]) : ∃ Q : ℝ[X], derivative Q = q := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * X ^ (i + 1), ?_⟩
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range_C_mul_X_pow q]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_C_mul_X_pow]
  congr 2
  · push_cast
    field_simp

lemma exists_poly_approx (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R,
      |iteratedDeriv r h x - iteratedDeriv r (fun x => p.eval x) x| ≤ ε := by
  induction k generalizing h ε with
  | zero =>
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R h
      hh.continuous.continuousOn ε hε
    refine ⟨p, fun r hr x hx => ?_⟩
    obtain rfl : r = 0 := by omega
    simp only [iteratedDeriv_zero]
    rw [abs_sub_comm]
    exact (hp x hx).le
  | succ k ih =>
    rcases lt_or_ge R 0 with hR | hR
    · refine ⟨0, fun r _ x hx => ?_⟩
      exfalso
      have := hx.1.trans hx.2
      linarith
    have hR1 : 0 < 2 * R + 1 := by linarith
    set ε' := ε / (2 * R + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε hR1
    have hε'mul : ε' * (2 * R + 1) = ε := div_mul_cancel₀ _ hR1.ne'
    have hε'le : ε' ≤ ε := by nlinarith
    obtain ⟨hdiff, hd⟩ := contDiff_infty_iff_deriv.mp hh
    obtain ⟨q, hq⟩ := ih (deriv h) hd ε' hε'pos
    obtain ⟨Q, hQ⟩ := exists_antiderivative q
    set p := Q + Polynomial.C (h (-R) - Q.eval (-R)) with hpdef
    have hpd : derivative p = q := by
      rw [hpdef, derivative_add, derivative_C, add_zero, hQ]
    have hderiv : deriv (fun x => p.eval x) = fun x => q.eval x := by
      funext x
      rw [Polynomial.deriv, hpd]
    refine ⟨p, fun r hr x hx => ?_⟩
    rcases r with _ | s
    · simp only [iteratedDeriv_zero]
      have hg0 : h (-R) - p.eval (-R) = 0 := by
        rw [hpdef]; simp
      have hmem : (-R) ∈ Set.Icc (-R) R := ⟨le_rfl, by linarith⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun y => h y - p.eval y) (s := Set.Icc (-R) R) (C := ε')
        (fun y _ => (hdiff y).sub p.differentiableAt) ?_ (convex_Icc _ _) hmem hx
      · simp only [hg0, sub_zero, Real.norm_eq_abs] at hmvt
        have hxR : |x - -R| ≤ 2 * R := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc |h x - eval x p| ≤ ε' * |x - -R| := hmvt
          _ ≤ ε' * (2 * R) := mul_le_mul_of_nonneg_left hxR hε'pos.le
          _ ≤ ε := by nlinarith
      · intro y hy
        rw [deriv_fun_sub (hdiff y) p.differentiableAt, Polynomial.deriv, hpd, Real.norm_eq_abs]
        have := hq 0 (Nat.zero_le _) y hy
        simpa only [iteratedDeriv_zero] using this
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', hderiv]
      exact (hq s (by omega) x hx).trans hε'le

end StrongConv.Part7B
end

section
open Polynomial Filter Topology
namespace StrongConv
/-! ## Part B: real analysis -/
alias exists_poly_approx := StrongConv.Part7B.exists_poly_approx

alias exists_chebyshev_expansion := StrongConv.Part7B.exists_chebyshev_expansion

alias cNorm_zero_le_add := StrongConv.Part7B.cNorm_zero_le_add

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7A
open StrongConv
/-! ## Helpers -/
lemma fullNorm_nonneg {D d : ℕ} (P : NCPoly D d) : 0 ≤ P.fullNorm := by
  unfold NCPoly.fullNorm
  apply Real.sSup_nonneg
  rintro x ⟨n, U, rfl⟩
  exact norm_nonneg _

lemma isLinearMap_sum (φ : ℝ[X] → ℝ) (hφ : IsLinearMap ℝ φ) (s : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℝ[X]) :
    φ (∑ j ∈ s, Polynomial.C (a j) * g j) = ∑ j ∈ s, a j * φ (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hφ.map_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hφ.map_add, ih, Polynomial.C_mul',
      hφ.map_smul, smul_eq_mul]

lemma expTr_zero_poly {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (N : ℕ) :
    expTr P N (fun x => (0 : ℝ[X]).eval x) = 0 := by
  have h := expTr_add_smul P hP N 0 0 1
  have e : ((0 : ℝ[X]) + Polynomial.C 1 * 0) = 0 := by simp
  rw [e] at h
  linarith

lemma expTr_sum {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (N : ℕ) (s : Finset ℕ)
    (a : ℕ → ℝ) (g : ℕ → ℝ[X]) :
    expTr P N (fun x => (∑ j ∈ s, Polynomial.C (a j) * g j).eval x) =
      ∑ j ∈ s, a j * expTr P N (fun x => (g j).eval x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expTr_zero_poly P hP N
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, add_comm, expTr_add_smul P hP, ih, add_comm]

lemma affine_expansion (F : ℕ → ℝ) (κ : ℝ) (hF : ∀ N : ℕ, 1 ≤ N → F N = κ * (1 - 1 / (N : ℝ))) :
    asympCoeff F 0 = κ ∧
      ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, 1 ≤ N →
        F N - ∑ i ∈ Finset.range m, asympCoeff F i / (N : ℝ) ^ i = 0 := by
  set c : ℕ → ℝ := fun i => if i = 0 then κ else if i = 1 then -κ else 0 with hc
  have hsum : ∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i = κ - κ / N := by
    intro m hm N
    induction m, hm using Nat.le_induction with
    | base => simp [Finset.sum_range_succ, hc]; ring
    | succ m hm ih =>
      rw [Finset.sum_range_succ, ih]
      have : m ≠ 0 := by omega
      have : m ≠ 1 := by omega
      simp [*]
  have hexp : HasExp F c := by
    intro m
    refine ⟨|κ|, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hF N hN]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
        rw [abs_mul]
        have h1 : |1 - 1 / (N : ℝ)| ≤ 1 := by
          rw [abs_le]
          have : 0 < 1 / (N : ℝ) := by positivity
          have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNp]; exact hN1
          constructor <;> linarith
        nlinarith [abs_nonneg κ]
      · simp [hc]
        rw [show κ * (1 - (N : ℝ)⁻¹) - κ = -(κ / N) by ring, abs_neg, abs_div,
          abs_of_pos hNp]
    · rw [hsum m hm N]
      have : κ * (1 - 1 / (N : ℝ)) - (κ - κ / N) = 0 := by ring
      rw [this, abs_zero]
      positivity
  have hcoef := HasExp.asympCoeff_eq hexp
  refine ⟨by rw [hcoef]; simp [hc], ?_⟩
  intro m hm N hN
  simp only [hcoef]
  rw [hsum m hm N, hF N hN]
  ring

end StrongConv.Part7A
end

section
open Polynomial Filter Topology
namespace StrongConv
alias affine_expansion := StrongConv.Part7A.affine_expansion

alias expTr_sum := StrongConv.Part7A.expTr_sum

alias isLinearMap_sum := StrongConv.Part7A.isLinearMap_sum

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7A
open StrongConv
/-! ## Functional calculus and traces -/
lemma fnCalc_sub {A : Type*} [CStarAlgebra A] (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (T : A) :
    fnCalc (fun x => f x - g x) T = fnCalc f T - fnCalc g T := by
  unfold fnCalc
  rw [← cfc_sub (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T
    (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn
    (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn]
  congr 1
  funext z
  push_cast
  rfl

lemma norm_fnCalc_le_of {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) {R δ : ℝ}
    (hR : ‖T‖ ≤ R) (hδ : 0 ≤ δ) (φ : ℝ → ℝ) (hφ : ∀ x ∈ Set.Icc (-R) R, |φ x| ≤ δ) :
    ‖fnCalc φ T‖ ≤ δ := by
  unfold fnCalc
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (cfc _ T) 0]; simpa using hδ
  have : IsStarNormal T := hT.isStarNormal
  refine norm_cfc_le hδ ?_
  intro z hz
  have hzn : ‖z‖ ≤ R := (spectrum.norm_le_norm_of_mem hz).trans hR
  have : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hzn
  have hmem : z.re ∈ Set.Icc (-R) R := abs_le.mp this |> fun h => ⟨h.1, h.2⟩
  simpa using hφ _ hmem

lemma trDN_sub (D N : ℕ)
    (Y Z : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ] PiLp 2 (fun _ : Fin D => OnesPerp N)) :
    trDN D N (Y - Z) = trDN D N Y - trDN D N Z := by
  unfold trDN
  rw [ContinuousLinearMap.toLinearMap_sub, map_sub, Complex.sub_re, sub_div]

lemma abs_expTr_sub_le {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (N : ℕ)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (ε : ℝ)
    (hfg : ∀ x ∈ Set.Icc (-P.fullNorm) P.fullNorm, |f x - g x| ≤ ε) :
    |expTr P N f - expTr P N g| ≤ ε := by
  have hK := StrongConv.Part7A.fullNorm_nonneg P
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hfg 0 ⟨by linarith, hK⟩)
  have hterm : ∀ σ : Fin d → Equiv.Perm (Fin N),
      |trDN D N (fnCalc f (P.eval (sModel σ))) - trDN D N (fnCalc g (P.eval (sModel σ)))| ≤ ε := by
    intro σ
    rw [← trDN_sub, ← fnCalc_sub f g hf hg]
    exact (PartB.abs_trDN_le _).trans (norm_fnCalc_le_of _ (isSelfAdjoint_eval P hP _)
      (PartB.norm_eval_sModel_le P σ) hε _ hfg)
  unfold expTr uniformExp
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ : Fin d → Equiv.Perm (Fin N), |trDN D N (fnCalc f (P.eval (sModel σ))) -
        trDN D N (fnCalc g (P.eval (sModel σ)))|
      ≤ ∑ σ : Fin d → Equiv.Perm (Fin N), ε := Finset.sum_le_sum fun σ _ => hterm σ
    _ = _ := by simp [mul_comm]

/-! ## The degenerate (affine) case -/
lemma trN_one (N : ℕ) (hN : 1 ≤ N) : trN N 1 = 1 - 1 / (N : ℝ) := by
  have hne : onesVec N ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h
    simp [onesVec] at this
  have : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = (N - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hfr : Module.finrank ℂ (OnesPerp N) = N - 1 :=
    Submodule.finrank_orthogonal_span_singleton hne
  unfold trN
  rw [ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one, hfr]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Nat.cast_sub hN]
  simp only [Nat.cast_one]
  rw [Complex.sub_re, Complex.natCast_re, Complex.one_re]
  field_simp

lemma uniformExp_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    uniformExp (fun _ : X => c) = c := by
  unfold uniformExp
  have : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma affine_of_mul_eq_zero {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (p : ℝ[X])
    (hmul : p.natDegree * P.degree = 0) :
    ∃ κ : ℝ, ∀ N : ℕ, 1 ≤ N → expTr P N (fun x => p.eval x) = κ * (1 - 1 / (N : ℝ)) := by
  obtain ⟨B, hBdeg, hB⟩ := exists_poly_expansion P (le_refl P.degree) p
  rw [hmul] at hBdeg
  have hsub : B.support ⊆ {1} := by
    intro w hw
    have := (Finset.le_sup (f := FreeMonoid.length) hw).trans hBdeg
    rw [Finset.mem_singleton]
    exact FreeMonoid.length_eq_zero.mp (Nat.le_zero.mp this)
  refine ⟨((∑ a, B 1 a a) / (D : ℂ)).re, fun N hN => ?_⟩
  have hσ : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trDN D N (fnCalc (fun x => p.eval x) (P.eval (sModel σ))) =
        ((∑ a, B 1 a a) / (D : ℂ)).re * (1 - 1 / (N : ℝ)) := by
    intro σ
    rw [fnCalc_poly _ (isSelfAdjoint_eval P hP _), hB (OnesPerp N) (sModel σ), trDN_eval_eq]
    rw [Finset.sum_subset hsub, Finset.sum_singleton]
    · simp [wordEval, trN_one N hN]
    · intro w hw hw'
      rw [Finsupp.notMem_support_iff] at hw'
      simp [hw']
  unfold expTr
  simp only [hσ]
  exact uniformExp_const _

lemma expTr_affine_of_degenerate {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (p : ℝ[X])
    (hdeg : P.degree = 0 ∨ P.fullNorm = 0 ∨ p.natDegree = 0) :
    ∃ κ : ℝ, ∀ N : ℕ, 1 ≤ N → expTr P N (fun x => p.eval x) = κ * (1 - 1 / (N : ℝ)) := by
  rcases hdeg with h | h | h
  · exact affine_of_mul_eq_zero P hP p (by rw [h, mul_zero])
  · obtain ⟨κ, hκ⟩ := affine_of_mul_eq_zero P hP (Polynomial.C (p.coeff 0)) (by simp)
    refine ⟨κ, fun N hN => ?_⟩
    rw [← hκ N hN]
    unfold expTr
    congr 1
    funext σ
    have h0 : P.eval (sModel σ) = 0 := by
      have := PartB.norm_eval_sModel_le P σ
      rw [h] at this
      exact norm_le_zero_iff.mp this
    rw [fnCalc_poly _ (isSelfAdjoint_eval P hP _), fnCalc_poly _ (isSelfAdjoint_eval P hP _), h0]
    simp [Finset.sum_range_succ']
  · exact affine_of_mul_eq_zero P hP p (by rw [h, zero_mul])

end StrongConv.Part7A
end

section
open Polynomial Filter Topology
namespace StrongConv
/-! ## Part A: operators, traces, expansions -/
alias expTr_affine_of_degenerate := StrongConv.Part7A.expTr_affine_of_degenerate

alias abs_expTr_sub_le := StrongConv.Part7A.abs_expTr_sub_le

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7A
open StrongConv
/-! ## `tr ⊗ τ` -/
lemma wordOp_eq_wordEval {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u w = wordEval u (w.toList.map some) := by
  simp only [wordOp, wordEval, List.map_map]
  rfl

lemma trTau_tensorOp {D d : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (T : L2Free d →L[ℂ] L2Free d) :
    trTau (tensorOp A T) = (∑ a, A a a) / (D : ℂ) * tau T := by
  unfold trTau tau
  have h : ∀ a : Fin D, inner ℂ (PiLp.single 2 a (delta 1) : PiLp 2 (fun _ : Fin D => L2Free d))
      (tensorOp A T (PiLp.single 2 a (delta 1))) = A a a * inner ℂ (delta 1) (T (delta 1)) := by
    intro a
    rw [PiLp.inner_apply, Finset.sum_eq_single a]
    · rw [PiLp.single_eq_same, PartB.tensorOp_apply, Finset.sum_eq_single a]
      · rw [PiLp.single_eq_same, inner_smul_right]
      · intro b _ hb
        rw [PiLp.single_eq_of_ne (p := 2) hb, map_zero, smul_zero]
      · simp
    · intro b _ hb
      rw [PiLp.single_eq_of_ne (p := 2) hb, inner_zero_left]
    · simp
  simp_rw [h, ← Finset.sum_mul]
  ring

lemma trTau_sum {D d : ℕ} {ι : Type*} (s : Finset ι)
    (Y : ι → PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d)) :
    trTau (∑ i ∈ s, Y i) = ∑ i ∈ s, trTau (Y i) := by
  unfold trTau
  simp only [sum_apply, inner_sum]
  rw [Finset.sum_comm, Finset.mul_sum]

lemma trTau_sub {D d : ℕ}
    (Y Z : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d)) :
    trTau (Y - Z) = trTau Y - trTau Z := by
  unfold trTau
  simp only [sub_apply, inner_sub_right, Finset.sum_sub_distrib, mul_sub]

lemma trTau_eval {D d : ℕ} (B : NCPoly D d) :
    trTau (B.eval (sLimit d)) =
      ∑ w ∈ B.support, (∑ a, B w a a) / (D : ℂ) * tau (wordOp (sLimit d) w) := by
  unfold NCPoly.eval
  rw [trTau_sum]
  simp only [trTau_tensorOp]

lemma norm_single_delta {D d : ℕ} (a : Fin D) :
    ‖(PiLp.single 2 a (delta 1) : PiLp 2 (fun _ : Fin D => L2Free d))‖ = 1 := by
  rw [PiLp.norm_single]
  unfold delta
  rw [lp.norm_single (by norm_num)]
  simp

lemma norm_trTau_le {D d : ℕ}
    (Z : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d)) :
    ‖trTau Z‖ ≤ ‖Z‖ := by
  unfold trTau
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hDp]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ a : Fin D, ‖inner ℂ (PiLp.single 2 a (delta 1) : PiLp 2 (fun _ : Fin D => L2Free d))
      (Z (PiLp.single 2 a (delta 1)))‖ ≤ ‖Z‖ := by
    intro a
    refine (norm_inner_le_norm _ _).trans ?_
    have := Z.le_opNorm (PiLp.single 2 a (delta 1) : PiLp 2 (fun _ : Fin D => L2Free d))
    rw [norm_single_delta] at this ⊢
    simpa using this
  refine (Finset.sum_le_sum fun a _ => h a).trans ?_
  simp

lemma im_trTau_of_isSelfAdjoint {D d : ℕ}
    (Z : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d))
    (hZ : IsSelfAdjoint Z) : (trTau Z).im = 0 := by
  have h : ∀ v, (inner ℂ v (Z v)).im = 0 := by
    intro v
    rw [← Complex.conj_eq_iff_im]
    have e : (starRingEnd ℂ) (inner ℂ v (Z v)) = inner ℂ (Z v) v := inner_conj_symm _ _
    rw [e, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hZ.star_eq]
  unfold trTau
  rw [Complex.mul_im, Complex.im_sum, Complex.re_sum]
  simp only [h, Finset.sum_const_zero, mul_zero, zero_add]
  have : ((D : ℂ)⁻¹).im = 0 := by
    rw [Complex.inv_im]; simp
  rw [this, zero_mul]

lemma isSelfAdjoint_fnCalc {A : Type*} [CStarAlgebra A] (f : ℝ → ℝ) (T : A) :
    IsSelfAdjoint (fnCalc f T) := by
  unfold fnCalc
  show star (cfc _ T) = _
  rw [← cfc_star]
  congr 1
  funext z
  simp [Complex.conj_ofReal]

lemma trTau_fnCalc_poly {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (p : ℝ[X]) :
    trTau (fnCalc (fun x => p.eval x) (P.eval (sLimit d))) = ((nu P 0 p : ℝ) : ℂ) := by
  obtain ⟨B, -, hB⟩ := exists_poly_expansion P (le_refl P.degree) p
  have h1 : fnCalc (fun x => p.eval x) (P.eval (sLimit d)) = B.eval (sLimit d) := by
    rw [fnCalc_poly _ (isSelfAdjoint_eval P hP _), hB (L2Free d) (sLimit d)]
  set c : FreeMonoid (Fin d ⊕ Fin d) → ℂ := fun w => (∑ a, B w a a) / (D : ℂ) with hc
  set t : FreeMonoid (Fin d ⊕ Fin d) → ℂ := fun w => tau (wordOp (sLimit d) w) with ht
  set E : FreeMonoid (Fin d ⊕ Fin d) → ℕ → ℝ := fun w N =>
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) (w.toList.map some)))
    with hE
  have hF : ∀ N, expTr P N (fun x => p.eval x) = ∑ w ∈ B.support, (c w).re * E w N := by
    intro N
    unfold expTr
    rw [← PartA3.uniformExp_sum]
    congr 1
    funext σ
    rw [fnCalc_poly _ (isSelfAdjoint_eval P hP _), hB (OnesPerp N) (sModel σ), trDN_eval_eq]
  have hw : ∀ w, Tendsto (fun N => ((E w N : ℝ) : ℂ)) atTop (𝓝 (t w)) := by
    intro w
    have := tendsto_uniformExp_trN_wordEval d (w.toList.map some)
    rw [← wordOp_eq_wordEval] at this
    exact this
  have ht_real : ∀ w, (t w).im = 0 := by
    intro w
    have h2 := (Complex.continuous_im.tendsto _).comp (hw w)
    have h3 : (Complex.im ∘ fun N => ((E w N : ℝ) : ℂ)) = fun _ => (0 : ℝ) := by
      funext N; simp
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  have hlim : Tendsto (fun N => expTr P N (fun x => p.eval x)) atTop
      (𝓝 (∑ w ∈ B.support, (c w).re * (t w).re)) := by
    simp only [hF]
    refine tendsto_finsetSum _ fun w _ => tendsto_const_nhds.mul ?_
    have := (Complex.continuous_re.tendsto _).comp (hw w)
    simpa [Function.comp_def] using this
  have hnu : nu P 0 p = ∑ w ∈ B.support, (c w).re * (t w).re := by
    unfold nu
    rw [asympCoeff]
    simp only [pow_zero, one_mul, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact hlim.limUnder_eq
  have hreal : (trTau (fnCalc (fun x => p.eval x) (P.eval (sLimit d)))).im = 0 :=
    im_trTau_of_isSelfAdjoint _ (isSelfAdjoint_fnCalc _ _)
  apply Complex.ext
  · rw [Complex.ofReal_re, hnu, h1, trTau_eval, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Complex.mul_re]
    have := ht_real w
    simp only [ht] at this
    rw [this, mul_zero, sub_zero]
  · rw [hreal, Complex.ofReal_im]

end StrongConv.Part7A
end

section
open Polynomial Filter Topology
namespace StrongConv
alias trTau_fnCalc_poly := StrongConv.Part7A.trTau_fnCalc_poly

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7A
open StrongConv
/-! ## Corollary 7.2 side and the distributions -/
lemma abs_nu_zero_le {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (q : ℝ[X]) (B : ℝ)
    (hq : ∀ x ∈ Set.Icc (-P.fullNorm) P.fullNorm, |q.eval x| ≤ B) : |nu P 0 q| ≤ B := by
  have hK := StrongConv.Part7A.fullNorm_nonneg P
  have h := abs_nu_le P hP (q₀ := max P.degree 1) (le_max_left _ _) (le_max_right _ _) 0
    (max q.natDegree 1) (le_max_right _ _) q (le_max_left _ _)
  have hc : cNorm 0 (fun x => q.eval x) (-P.fullNorm) P.fullNorm =
      supOn (fun x => q.eval x) (-P.fullNorm) P.fullNorm := by
    simp [cNorm, iteratedDeriv_zero]
  rw [pow_zero, one_mul, hc] at h
  refine h.trans ?_
  unfold supOn
  refine csSup_le ⟨_, 0, ⟨by linarith, hK⟩, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hq x hx

lemma norm_trTau_fnCalc_sub_le {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (ε : ℝ)
    (hfg : ∀ x ∈ Set.Icc (-P.fullNorm) P.fullNorm, |f x - g x| ≤ ε) :
    ‖trTau (fnCalc f (P.eval (sLimit d))) - trTau (fnCalc g (P.eval (sLimit d)))‖ ≤ ε := by
  set Y := P.eval (sLimit d) with hYdef
  have hY : IsSelfAdjoint Y := isSelfAdjoint_eval P hP _
  set K := P.fullNorm with hKdef
  have hK : 0 ≤ K := StrongConv.Part7A.fullNorm_nonneg P
  set R := ‖Y‖ + K + 1 with hR
  have hYR : ‖Y‖ ≤ R := by linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hδ : 0 < η / 2 := by linarith
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-R) R (fun x => f x - g x)
    (hf.sub hg).continuousOn (η / 2) hδ
  have hqc : Continuous fun x => q.eval x := q.continuous
  have e1 := fnCalc_sub (fun x => f x - g x) (fun x => q.eval x) (hf.sub hg) hqc Y
  have e2 := fnCalc_sub f g hf hg Y
  have key : trTau (fnCalc f Y) - trTau (fnCalc g Y) =
      trTau (fnCalc (fun x => f x - g x - q.eval x) Y) + trTau (fnCalc (fun x => q.eval x) Y) := by
    rw [e1, trTau_sub, sub_add_cancel, e2, trTau_sub]
  rw [key]
  refine (norm_add_le _ _).trans ?_
  have b1 : ‖trTau (fnCalc (fun x => f x - g x - q.eval x) Y)‖ ≤ η / 2 := by
    refine (norm_trTau_le _).trans (norm_fnCalc_le_of Y hY hYR hδ.le _ ?_)
    intro x hx
    have := hq x hx
    rw [abs_sub_comm]
    exact this.le
  have b2 : ‖trTau (fnCalc (fun x => q.eval x) Y)‖ ≤ ε + η / 2 := by
    rw [hYdef, trTau_fnCalc_poly P hP q, Complex.norm_real, Real.norm_eq_abs]
    refine abs_nu_zero_le P hP q _ fun x hx => ?_
    have hxR : x ∈ Set.Icc (-R) R := ⟨by linarith [hx.1, norm_nonneg Y], by linarith [hx.2, norm_nonneg Y]⟩
    have h1 := (hq x hxR).le
    have h2 := hfg x hx
    calc |q.eval x| = |(f x - g x) + (q.eval x - (f x - g x))| := by congr 1; ring
      _ ≤ |f x - g x| + |q.eval x - (f x - g x)| := abs_add_le _ _
      _ ≤ ε + η / 2 := add_le_add h2 h1
  linarith

end StrongConv.Part7A
end

section
open Polynomial Filter Topology
namespace StrongConv
alias norm_trTau_fnCalc_sub_le := StrongConv.Part7A.norm_trTau_fnCalc_sub_le

end StrongConv
end

section
open Polynomial Filter Topology
namespace StrongConv.Part7A
open StrongConv

end StrongConv.Part7A
end

section
open Polynomial Filter Topology
namespace StrongConv

alias fullNorm_nonneg := StrongConv.Part7A.fullNorm_nonneg

lemma lpNormCircle_nonneg (β : ℝ) (F : ℝ → ℝ) : 0 ≤ lpNormCircle β F :=
  ENNReal.toReal_nonneg

lemma conjExp_pos (β : ℝ) (hβ : 1 < β) : 0 < conjExp β := by
  unfold conjExp
  have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
  exact inv_pos.mpr (by linarith)

/-! ## Assembly -/
/-- The constant of Lemma 4.4. -/
noncomputable def Czyg : ℝ := Classical.choose abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma Czyg_spec : ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          Czyg * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) :=
  Classical.choose_spec abs_coeff_zero_le_and_sum_le_lpNormCircle

/-- The master inequality for polynomial test functions (pp. 22–23), with the constant term made
explicit for `m = 1`. -/
theorem poly_master {D d q₀ : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀)
    (p : ℝ[X]) (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) (β : ℝ) (hβ : 1 < β) :
    |expTr P N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nu P i p / (N : ℝ) ^ i| ≤
      max Czyg 0 * (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β *
        lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => p.eval (P.fullNorm * Real.cos θ))) +
      (if m = 1 then cNorm 0 (fun x => p.eval x) (-P.fullNorm) P.fullNorm / N else 0) := by
  set K := P.fullNorm with hKdef
  have hK0 : 0 ≤ K := fullNorm_nonneg P
  have hL : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβs := conjExp_pos β hβ
  set lp := lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => p.eval (K * Real.cos θ)))
  have hlp : 0 ≤ lp := lpNormCircle_nonneg _ _
  have hRHS0 : 0 ≤ max Czyg 0 * (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
      conjExp β * lp := by
    have : (0 : ℝ) ≤ 4 * q₀ * (1 + Real.log d) := by positivity
    have := le_max_right Czyg 0
    positivity
  have hextra : 0 ≤ (if m = 1 then cNorm 0 (fun x => p.eval x) (-K) K / N else 0) := by
    split_ifs
    · have := (abs_nonneg _).trans (abs_nu_le P hP (le_max_left P.degree 1) (le_max_right _ _) 0
        (max p.natDegree 1) (le_max_right _ _) p (le_max_left _ _))
      simp only [mul_zero, pow_zero, one_mul] at this
      positivity
    · exact le_rfl
  -- the degenerate case: the expansion is exact
  by_cases hdeg : q₀ = 0 ∨ K = 0
  · obtain ⟨κ, hκ⟩ := expTr_affine_of_degenerate P hP p (by
      rcases hdeg with h | h
      · exact Or.inl (Nat.le_zero.mp (h ▸ hq₀))
      · exact Or.inr (Or.inl h))
    obtain ⟨h0, h2⟩ := affine_expansion _ κ hκ
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      simp only [if_true, Finset.sum_range_one, pow_zero, div_one]
      have hnu0 : nu P 0 p = κ := h0
      rw [hκ N hN, hnu0]
      have hb := abs_nu_le P hP (le_max_left P.degree 1) (le_max_right _ _) 0
        (max p.natDegree 1) (le_max_right _ _) p (le_max_left _ _)
      simp only [mul_zero, pow_zero, one_mul] at hb
      rw [hnu0] at hb
      have : κ * (1 - 1 / (N : ℝ)) - κ = -(κ / N) := by ring
      rw [this, abs_neg, abs_div, abs_of_pos hNpos]
      have : |κ| / N ≤ cNorm 0 (fun x => p.eval x) (-K) K / N :=
        div_le_div_of_nonneg_right hb hNpos.le
      linarith
    · have := h2 m hm2 N hN
      have hnu : ∀ i, nu P i p = asympCoeff (fun N => expTr P N (fun x => p.eval x)) i :=
        fun i => rfl
      simp only [hnu]
      rw [this, abs_zero]
      linarith
  -- the general case
  push Not at hdeg
  obtain ⟨hq0, hKne⟩ := hdeg
  have hq₀' : 1 ≤ q₀ := Nat.one_le_iff_ne_zero.mpr hq0
  have hK : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKne)
  obtain ⟨a, ha_eval, ha_poly⟩ := exists_chebyshev_expansion p K hK
  set q := p.natDegree
  have hthm := isLinearMap_nu_and_abs_expTr_sub_sum_nu_le P hP hq₀ hq₀'
  set E : ℕ → ℝ := fun j => expTr P N (fun x => (chebK K j).eval x) -
    ∑ i ∈ Finset.range m, nu P i (chebK K j) / (N : ℝ) ^ i with hE
  have hexp : expTr P N (fun x => p.eval x) =
      ∑ j ∈ Finset.range (q + 1), a j * expTr P N (fun x => (chebK K j).eval x) := by
    rw [← expTr_sum P hP N _ a (chebK K), ← ha_poly]
  have hnu : ∀ i, nu P i p = ∑ j ∈ Finset.range (q + 1), a j * nu P i (chebK K j) := by
    intro i
    conv_lhs => rw [ha_poly]
    exact isLinearMap_sum _ (hthm.1 i) _ a (chebK K)
  have key : expTr P N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nu P i p / (N : ℝ) ^ i =
      ∑ j ∈ Finset.range (q + 1), a j * E j := by
    rw [hexp]
    simp only [hnu, hE, mul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key, sum_range_succ_eq_add_Icc]
  -- the terms j ≥ 1
  have hEj : ∀ j ∈ Finset.Icc 1 q, |a j * E j| ≤
      (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * ((j : ℝ) ^ (4 * m) * |a j|) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 := hthm.2 N m j hN hm hj1 (chebK K j) (natDegree_chebK_le K j)
    have h2 := cNorm_chebK_le K hK j
    have h3 : (0 : ℝ) ≤ (4 * j * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m := by positivity
    have h4 : |E j| ≤ (4 * j * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m :=
      h1.trans (by simpa using mul_le_mul_of_nonneg_left h2 h3)
    rw [abs_mul]
    calc |a j| * |E j| ≤ |a j| * ((4 * j * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = _ := by
          rw [show (4 * (j : ℝ) * q₀ * (1 + Real.log d)) = j * (4 * q₀ * (1 + Real.log d)) by ring,
            mul_pow]
          ring
  obtain ⟨hz0, hzyg⟩ := Czyg_spec q a K hK
  have hfun : (fun θ => ∑ j ∈ Finset.range (q + 1),
      a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K)) = fun θ => p.eval (K * Real.cos θ) := by
    funext θ; rw [ha_eval]
  have hfun0 : (fun x => ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (x / K)) =
      fun x => p.eval x := by
    funext x; rw [ha_eval]
  rw [hfun0] at hz0
  have hZ := hzyg (4 * m) β hβ
  rw [hfun] at hZ
  have hZ' : ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ (4 * m) * |a j| ≤ max Czyg 0 * conjExp β * lp := by
    refine hZ.trans ?_
    have : 0 ≤ conjExp β * lp := by positivity
    calc Czyg * conjExp β * lp = Czyg * (conjExp β * lp) := by ring
      _ ≤ max Czyg 0 * (conjExp β * lp) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  have hsum : |∑ j ∈ Finset.Icc 1 q, a j * E j| ≤
      max Czyg 0 * (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β * lp := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hEj).trans ?_)
    rw [← Finset.mul_sum]
    have h3 : (0 : ℝ) ≤ (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m := by positivity
    calc (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
          ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ (4 * m) * |a j|
        ≤ (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * (max Czyg 0 * conjExp β * lp) :=
          mul_le_mul_of_nonneg_left hZ' h3
      _ = _ := by ring
  -- the term j = 0
  have hE0 : |a 0 * E 0| ≤ (if m = 1 then cNorm 0 (fun x => p.eval x) (-K) K / N else 0) := by
    have hc0 : (chebK K 0).natDegree = 0 := Nat.le_zero.mp (natDegree_chebK_le K 0)
    obtain ⟨κ, hκ⟩ := expTr_affine_of_degenerate P hP (chebK K 0) (Or.inr (Or.inr hc0))
    obtain ⟨h0, h2⟩ := affine_expansion _ κ hκ
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      simp only [if_true]
      have hE0' : E 0 = -(κ / N) := by
        simp only [hE, Finset.sum_range_one, pow_zero, div_one]
        have hnu0 : nu P 0 (chebK K 0) = κ := h0
        rw [hκ N hN, hnu0]; ring
      have hb := abs_nu_le P hP hq₀ hq₀' 0 1 le_rfl (chebK K 0) (by rw [hc0]; exact zero_le_one)
      simp only [mul_zero, pow_zero, one_mul] at hb
      have hnu0 : nu P 0 (chebK K 0) = κ := h0
      rw [hnu0] at hb
      have hκ1 : |κ| ≤ 1 := hb.trans (cNorm_chebK_le K hK 0)
      rw [hE0', abs_mul, abs_neg, abs_div, abs_of_pos hNpos]
      have ha0 : 0 ≤ |a 0| := abs_nonneg _
      calc |a 0| * (|κ| / N) ≤ cNorm 0 (fun x => p.eval x) (-K) K * (1 / N) := by
            apply mul_le_mul hz0 (div_le_div_of_nonneg_right hκ1 hNpos.le) (by positivity)
              (ha0.trans hz0)
        _ = _ := by ring
    · have hE00 : E 0 = 0 := h2 m hm2 N hN
      rw [hE00, mul_zero, abs_zero]
      have : ¬ m = 1 := by omega
      simp [this]
  calc |a 0 * E 0 + ∑ j ∈ Finset.Icc 1 q, a j * E j|
      ≤ |a 0 * E 0| + |∑ j ∈ Finset.Icc 1 q, a j * E j| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma smooth_coe (h : smoothFun) : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ) := h.2

lemma poly_smooth (p : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => p.eval x) := (polyFun p).2

/-- The `L^β` side passes to the limit: a polynomial close to `h` in `C^(r)[-K, K]`. -/
lemma lp_perturb (h : smoothFun) (p : ℝ[X]) (K : ℝ) (hK : 0 ≤ K) (r : ℕ) (β : ℝ) (hβ : 1 < β)
    (ε : ℝ) (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K,
      |iteratedDeriv i (fun x => (h : ℝ → ℝ) x - p.eval x) x| ≤ ε) :
    lpNormCircle β (iteratedDeriv r (fun θ => p.eval (K * Real.cos θ))) ≤
      lpNormCircle β (iteratedDeriv r (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) +
        (2 * Real.pi + 1) * ((r.factorial : ℝ) * ε * (max K 1) ^ r) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => K * Real.cos θ) :=
    contDiff_const.mul Real.contDiff_cos
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) :=
    (smooth_coe h).comp hc
  have hpc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => p.eval (K * Real.cos θ)) := (poly_smooth p).comp hc
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => (h : ℝ → ℝ) x - p.eval x) :=
    (smooth_coe h).sub (poly_smooth p)
  refine lpNormCircle_le_add β hβ _ _ (hpc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top))
    (hhc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)) _ fun θ => ?_
  have h1 := abs_iteratedDeriv_comp_cos_le _ hg K hK r ε hε θ
  have h2 := iteratedDeriv_sub_of_contDiff _ _ hhc hpc r
  have h3 : (fun θ => (fun x => (h : ℝ → ℝ) x - p.eval x) (K * Real.cos θ)) =
      fun θ => (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) θ - (fun θ => p.eval (K * Real.cos θ)) θ :=
    rfl
  rw [h3, h2] at h1
  rw [abs_sub_comm]
  exact h1

theorem norm_expTr_sub_trTau_le_dev :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
          C * (q₀ * (1 + Real.log d)) ^ 4 / N * conjExp β *
            lpNormCircle β (iteratedDeriv 5 (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) +
          cNorm 0 (h : ℝ → ℝ) (-P.fullNorm) P.fullNorm / N := by
  refine ⟨256 * max Czyg 0, ?_⟩
  intro D d q₀ P hP hq₀ N hN β hβ h
  set K := P.fullNorm with hKdef
  have hK0 : 0 ≤ K := fullNorm_nonneg P
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set A := max Czyg 0 * (4 * q₀ * (1 + Real.log d)) ^ (4 * 1) / (N : ℝ) ^ 1 * conjExp β with hA
  have hA0 : 0 ≤ A := by
    have := le_max_right Czyg 0
    have := conjExp_pos β hβ
    have : (0 : ℝ) ≤ 4 * q₀ * (1 + Real.log d) := by
      have := Real.log_natCast_nonneg d; positivity
    positivity
  set lph := lpNormCircle β (iteratedDeriv (4 * 1 + 1) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)))
  set B := A * ((2 * Real.pi + 1) * (((4 * 1 + 1).factorial : ℝ) * (max K 1) ^ (4 * 1 + 1)))
  have hB0 : 0 ≤ B := by
    have : (0 : ℝ) ≤ max K 1 := le_trans zero_le_one (le_max_right _ _)
    have := Real.pi_pos
    positivity
  set M := 2 + B + 1 / (N : ℝ) with hM
  have hM0 : 0 < M := by have : 0 < 1 / (N : ℝ) := by positivity
                         linarith
  have hY := isSelfAdjoint_eval P hP (sLimit d)
  have main : ∀ ε > 0,
      ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
        A * lph + cNorm 0 (h : ℝ → ℝ) (-K) K / N + ε * M := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_poly_approx (h : ℝ → ℝ) (smooth_coe h) 5 K ε hε
    have hg : ∀ r ≤ 5, ∀ x ∈ Set.Icc (-K) K,
        |iteratedDeriv r (fun x => (h : ℝ → ℝ) x - p.eval x) x| ≤ ε := by
      intro r hr x hx
      rw [iteratedDeriv_sub_of_contDiff _ _ (smooth_coe h) (poly_smooth p) r]
      exact hp r hr x hx
    have h0 : ∀ x ∈ Set.Icc (-K) K, |(h : ℝ → ℝ) x - p.eval x| ≤ ε := fun x hx => by
      simpa using hg 0 (Nat.zero_le _) x hx
    have ha : |expTr P N (h : ℝ → ℝ) - expTr P N (fun x => p.eval x)| ≤ ε :=
      abs_expTr_sub_le P hP N _ _ (smooth_coe h).continuous (poly_smooth p).continuous ε h0
    have hc := poly_master P hP hq₀ p N 1 hN le_rfl β hβ
    simp only [if_true, Finset.sum_range_one, pow_zero, div_one] at hc
    rw [← hKdef, ← hA] at hc
    have hlp := lp_perturb h p K hK0 (4 * 1 + 1) β hβ ε fun i hi x hx => hg i (by omega) x hx
    have hcn : cNorm 0 (fun x => p.eval x) (-K) K ≤ cNorm 0 (h : ℝ → ℝ) (-K) K + ε :=
      cNorm_zero_le_add _ _ (poly_smooth p).continuous (smooth_coe h).continuous K hK0 ε
        fun x hx => by rw [abs_sub_comm]; exact h0 x hx
    have hc' : |expTr P N (fun x => p.eval x) - nu P 0 p| ≤
        A * lph + cNorm 0 (h : ℝ → ℝ) (-K) K / N + ε * (B + 1 / N) := by
      refine hc.trans ?_
      have e1 : A * lpNormCircle β (iteratedDeriv (4 * 1 + 1) (fun θ => p.eval (K * Real.cos θ)))
          ≤ A * lph + ε * B := by
        calc _ ≤ A * (lph + (2 * Real.pi + 1) * (((4 * 1 + 1).factorial : ℝ) * ε *
              (max K 1) ^ (4 * 1 + 1))) := mul_le_mul_of_nonneg_left hlp hA0
          _ = A * lph + ε * B := by ring
      have e2 : cNorm 0 (fun x => p.eval x) (-K) K / N ≤
          cNorm 0 (h : ℝ → ℝ) (-K) K / N + ε * (1 / N) := by
        rw [show cNorm 0 (h : ℝ → ℝ) (-K) K / N + ε * (1 / N) =
          (cNorm 0 (h : ℝ → ℝ) (-K) K + ε) / N by ring]
        exact div_le_div_of_nonneg_right hcn hNpos.le
      linarith
    have ht : ‖trTau (fnCalc (fun x => p.eval x) (P.eval (sLimit d))) -
        trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤ ε :=
      norm_trTau_fnCalc_sub_le P hP _ _ (poly_smooth p).continuous (smooth_coe h).continuous ε
        fun x hx => by rw [abs_sub_comm]; exact h0 x hx
    rw [trTau_fnCalc_poly P hP p] at ht
    have hsplit : (expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d))) =
        ((expTr P N (h : ℝ → ℝ) - expTr P N (fun x => p.eval x) : ℝ) : ℂ) +
        ((expTr P N (fun x => p.eval x) - nu P 0 p : ℝ) : ℂ) +
        (((nu P 0 p : ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))) := by
      push_cast; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have n1 := norm_add_le ((expTr P N (h : ℝ → ℝ) - expTr P N (fun x => p.eval x) : ℝ) : ℂ)
      ((expTr P N (fun x => p.eval x) - nu P 0 p : ℝ) : ℂ)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at n1
    rw [hM]
    nlinarith
  have hfin := le_of_forall_pos_le_add fun δ hδ => by
    have := main (δ / M) (div_pos hδ hM0)
    rwa [div_mul_cancel₀ δ hM0.ne'] at this
  refine hfin.trans (le_of_eq ?_)
  rw [hA]
  ring

end StrongConv
end

section
open Polynomial Filter Topology
open StrongConv
theorem solution :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
          C * (q₀ * (1 + Real.log d)) ^ 4 / N * conjExp β *
            lpNormCircle β (iteratedDeriv 5 (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) +
          cNorm 0 (h : ℝ → ℝ) (-P.fullNorm) P.fullNorm / N := by
  exact StrongConv.norm_expTr_sub_trTau_le_dev
end
