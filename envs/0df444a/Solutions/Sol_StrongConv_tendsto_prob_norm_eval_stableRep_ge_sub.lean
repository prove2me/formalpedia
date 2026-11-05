-- Prove2me | solution 1 for StrongConv.tendsto_prob_norm_eval_stableRep_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:08:49.3342+00:00
-- url     : https://prove2.me/submissions/44ded9b0-188b-49c8-b47a-1c38d1b8f58c

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_tendsto_prob_norm_trace_sub_trTau_ge
import Theorems.Thm_StrongConv_tendsto_re_trTau_pow_rpow

section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T y a = ∑ b, A a b • T (y b) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply,
    PiLp.proj_apply, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.smul_apply, Pi.single_apply]
  simp [Finset.sum_comm (γ := Fin n)]

lemma inner_tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin m => H)) (y : PiLp 2 (fun _ : Fin n => H)) :
    ⟪x, tensorOp A T y⟫_ℂ = ∑ a, ∑ b, A a b * ⟪x a, T (y b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right]

lemma star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- ⟪tensorOp Aᴴ T† x, y⟫ = ⟪x, tensorOp A T y⟫
  rw [inner_tensorOp, ← inner_conj_symm, inner_tensorOp, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, inner_conj_symm]
  simp only [Matrix.conjTranspose_apply, star_star, Complex.star_def]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [Complex.conj_conj]

lemma star_letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : Fin d ⊕ Fin d) :
    star (letterOp u l) = letterOp u l.swap := by
  rcases l with i | i <;> simp [letterOp]

lemma star_list_prod' {A : Type*} [Monoid A] [StarMul A] (l : List A) :
    star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, star_mul]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  rw [star_list_prod']
  simp only [FreeMonoid.toList_ofList, List.map_map, List.map_reverse]
  congr 1
  congr 1
  apply List.map_congr_left
  intro l _
  simp [star_letterOp]

lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  unfold NCPoly.wordStar
  apply FreeMonoid.toList.injective
  simp [Function.comp_def]

end StrongConv.Stable
end
end

section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `NCPoly` as the monoid algebra over the free monoid. -/
abbrev MA (D d : ℕ) := MonoidAlgebra (Matrix (Fin D) (Fin D) ℂ) (FreeMonoid (Fin d ⊕ Fin d))

lemma tensorOp_zero {n : ℕ} (T : H →L[ℂ] H) : tensorOp (0 : Matrix (Fin n) (Fin n) ℂ) T = 0 := by
  ext y a : 2
  simp [tensorOp_apply]

lemma tensorOp_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  ext y a : 2
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

lemma tensorOp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (S T : H →L[ℂ] H) :
    tensorOp (A * B) (S * T) = tensorOp A S * tensorOp B T := by
  ext y a : 2
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, Matrix.mul_apply, Finset.sum_smul,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm


open NCPoly in
lemma eval_eq_sum {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    P.eval u = P.sum (fun w A => tensorOp A (wordOp u w)) := rfl

lemma eval_add {D d : ℕ} (P Q : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (P + Q).eval u = P.eval u + Q.eval u := by
  rw [eval_eq_sum, eval_eq_sum, eval_eq_sum]
  exact Finsupp.sum_add_index' (fun w => tensorOp_zero _) (fun w A B => tensorOp_add A B _)

lemma eval_single {D d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ)
    (u : Fin d → H →L[ℂ] H) :
    NCPoly.eval (D := D) (d := d) (Finsupp.single w A) u = tensorOp A (wordOp u w) := by
  rw [eval_eq_sum, Finsupp.sum_single_index (tensorOp_zero _)]

lemma wordOp_mul {d : ℕ} (u : Fin d → H →L[ℂ] H) (v w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u (v * w) = wordOp u v * wordOp u w := by
  unfold wordOp
  rw [FreeMonoid.toList_mul, List.map_append, List.prod_append]

lemma wordOp_one {d : ℕ} (u : Fin d → H →L[ℂ] H) : wordOp u (1 : FreeMonoid (Fin d ⊕ Fin d)) = 1 := by
  simp [wordOp]

lemma tensorOp_one {n : ℕ} : tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  ext y a : 2
  simp [tensorOp_apply, Matrix.one_apply]

/-- `P.eval` for `P` in the monoid algebra. -/
def evMA {D d : ℕ} (P : MA D d) (u : Fin d → H →L[ℂ] H) :=
  NCPoly.eval (D := D) (d := d) P.coeff u

lemma evMA_mul {D d : ℕ} (P Q : MA D d) (u : Fin d → H →L[ℂ] H) :
    evMA (P * Q) u = evMA P u * evMA Q u := by
  obtain ⟨P0, rfl⟩ : ∃ q, P = MonoidAlgebra.ofCoeff q := ⟨P.coeff, rfl⟩
  obtain ⟨Q0, rfl⟩ : ∃ q, Q = MonoidAlgebra.ofCoeff q := ⟨Q.coeff, rfl⟩
  induction P0 using Finsupp.induction_linear with
  | zero => simp [evMA, eval_eq_sum]
  | add P₁ P₂ h₁ h₂ =>
    have e : MonoidAlgebra.ofCoeff (P₁ + P₂) * MonoidAlgebra.ofCoeff Q0 =
        MonoidAlgebra.ofCoeff P₁ * MonoidAlgebra.ofCoeff Q0 +
          MonoidAlgebra.ofCoeff P₂ * MonoidAlgebra.ofCoeff Q0 := by
      rw [MonoidAlgebra.ofCoeff_add, add_mul]
    rw [e]
    have := eval_add (D := D) (d := d) (MonoidAlgebra.ofCoeff P₁ * MonoidAlgebra.ofCoeff Q0 : MA D d).coeff
      (MonoidAlgebra.ofCoeff P₂ * MonoidAlgebra.ofCoeff Q0 : MA D d).coeff u
    unfold evMA at *
    rw [MonoidAlgebra.coeff_add, this, h₁, h₂]
    have := eval_add (D := D) (d := d) P₁ P₂ u
    simp only [MonoidAlgebra.coeff_ofCoeff] at *
    rw [this, add_mul]
  | single w A =>
    induction Q0 using Finsupp.induction_linear with
    | zero => simp [evMA, eval_eq_sum]
    | add Q₁ Q₂ h₁ h₂ =>
      have e : MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff (Q₁ + Q₂) =
          MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff Q₁ +
            MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff Q₂ := by
        rw [MonoidAlgebra.ofCoeff_add, mul_add]
      rw [e]
      have := eval_add (D := D) (d := d)
        (MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff Q₁ : MA D d).coeff
        (MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff Q₂ : MA D d).coeff u
      unfold evMA at *
      rw [MonoidAlgebra.coeff_add, this, h₁, h₂]
      have := eval_add (D := D) (d := d) Q₁ Q₂ u
      simp only [MonoidAlgebra.coeff_ofCoeff] at *
      rw [this, mul_add]
    | single w' B =>
      have : (MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff (Finsupp.single w' B) :
          MA D d) = MonoidAlgebra.single (w * w') (A * B) := MonoidAlgebra.single_mul_single _ _ _ _
      unfold evMA
      rw [this, MonoidAlgebra.coeff_single]
      simp only [MonoidAlgebra.coeff_ofCoeff]
      rw [eval_single, eval_single, eval_single, wordOp_mul, tensorOp_mul]


lemma wordStar_mul {d : ℕ} (v w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (v * w) = NCPoly.wordStar w * NCPoly.wordStar v := by
  unfold NCPoly.wordStar
  apply FreeMonoid.toList.injective
  simp [List.reverse_append, List.map_append]

lemma wordStar_one {d : ℕ} : NCPoly.wordStar (1 : FreeMonoid (Fin d ⊕ Fin d)) = 1 := by
  unfold NCPoly.wordStar
  apply FreeMonoid.toList.injective
  simp

/-- The formal adjoint on the monoid algebra. -/
def sMA {D d : ℕ} (a : MA D d) : MA D d :=
  a.coeff.sum fun w A => MonoidAlgebra.single (NCPoly.wordStar w) Aᴴ

lemma sMA_add {D d : ℕ} (a b : MA D d) : sMA (a + b) = sMA a + sMA b := by
  unfold sMA
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun w => by simp) (fun w A B => by simp [MonoidAlgebra.single_add])

lemma sMA_single {D d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ) :
    sMA (MonoidAlgebra.single w A) = MonoidAlgebra.single (NCPoly.wordStar w) Aᴴ := by
  unfold sMA
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

lemma sMA_zero {D d : ℕ} : sMA (0 : MA D d) = 0 := by
  unfold sMA; simp

lemma sMA_mul {D d : ℕ} (a b : MA D d) : sMA (a * b) = sMA b * sMA a := by
  obtain ⟨a0, rfl⟩ : ∃ q, a = MonoidAlgebra.ofCoeff q := ⟨a.coeff, rfl⟩
  obtain ⟨b0, rfl⟩ : ∃ q, b = MonoidAlgebra.ofCoeff q := ⟨b.coeff, rfl⟩
  induction a0 using Finsupp.induction_linear with
  | zero => simp [sMA_zero]
  | add a₁ a₂ h₁ h₂ =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, sMA_add, h₁, h₂, sMA_add, mul_add]
  | single w A =>
    induction b0 using Finsupp.induction_linear with
    | zero => simp [sMA_zero]
    | add b₁ b₂ h₁ h₂ =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, sMA_add, h₁, h₂, sMA_add, add_mul]
    | single w' B =>
      have e1 : (MonoidAlgebra.ofCoeff (Finsupp.single w A) * MonoidAlgebra.ofCoeff (Finsupp.single w' B) :
          MA D d) = MonoidAlgebra.single (w * w') (A * B) := MonoidAlgebra.single_mul_single _ _ _ _
      have e2 : (MonoidAlgebra.ofCoeff (Finsupp.single w A) : MA D d) = MonoidAlgebra.single w A := rfl
      have e3 : (MonoidAlgebra.ofCoeff (Finsupp.single w' B) : MA D d) = MonoidAlgebra.single w' B := rfl
      rw [e1, e2, e3, sMA_single, sMA_single, sMA_single, MonoidAlgebra.single_mul_single,
        wordStar_mul, Matrix.conjTranspose_mul]

lemma sMA_sMA {D d : ℕ} (a : MA D d) : sMA (sMA a) = a := by
  obtain ⟨a0, rfl⟩ : ∃ q, a = MonoidAlgebra.ofCoeff q := ⟨a.coeff, rfl⟩
  induction a0 using Finsupp.induction_linear with
  | zero => simp [sMA_zero]
  | add a₁ a₂ h₁ h₂ => rw [MonoidAlgebra.ofCoeff_add, sMA_add, sMA_add, h₁, h₂]
  | single w A =>
    have e2 : (MonoidAlgebra.ofCoeff (Finsupp.single w A) : MA D d) = MonoidAlgebra.single w A := rfl
    rw [e2, sMA_single, sMA_single, wordStar_wordStar, Matrix.conjTranspose_conjTranspose]

lemma sMA_pow {D d : ℕ} (a : MA D d) (ha : sMA a = a) (n : ℕ) : sMA (a ^ n) = a ^ n := by
  induction n with
  | zero =>
    have : (1 : MA D d) = MonoidAlgebra.single 1 1 := rfl
    rw [pow_zero, this, sMA_single, wordStar_one, Matrix.conjTranspose_one]
  | succ n ih =>
    rw [pow_succ, sMA_mul, ha, ih]
    exact (Commute.self_pow a n).eq

lemma evMA_sMA {D d : ℕ} (a : MA D d) (u : Fin d → H →L[ℂ] H) :
    evMA (sMA a) u = star (evMA a u) := by
  obtain ⟨a0, rfl⟩ : ∃ q, a = MonoidAlgebra.ofCoeff q := ⟨a.coeff, rfl⟩
  induction a0 using Finsupp.induction_linear with
  | zero =>
    simp [sMA_zero, evMA, eval_eq_sum, ContinuousLinearMap.star_eq_adjoint]
  | add a₁ a₂ h₁ h₂ =>
    rw [MonoidAlgebra.ofCoeff_add, sMA_add]
    have h3 := eval_add (D := D) (d := d) (sMA (MonoidAlgebra.ofCoeff a₁)).coeff
      (sMA (MonoidAlgebra.ofCoeff a₂)).coeff u
    have h4 := eval_add (D := D) (d := d) a₁ a₂ u
    unfold evMA at *
    rw [MonoidAlgebra.coeff_add, h3, h₁, h₂]
    have h5 : (MonoidAlgebra.ofCoeff a₁ + MonoidAlgebra.ofCoeff a₂ : MA D d).coeff = a₁ + a₂ := rfl
    rw [h5, h4]
    simp only [ContinuousLinearMap.star_eq_adjoint, map_add]
  | single w A =>
    have e2 : (MonoidAlgebra.ofCoeff (Finsupp.single w A) : MA D d) = MonoidAlgebra.single w A := rfl
    unfold evMA
    rw [e2, sMA_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, eval_single,
      eval_single, star_tensorOp, star_wordOp]

lemma evMA_one {D d : ℕ} (u : Fin d → H →L[ℂ] H) : evMA (1 : MA D d) u = 1 := by
  have : (1 : MA D d) = MonoidAlgebra.single 1 1 := rfl
  unfold evMA
  rw [this, MonoidAlgebra.coeff_single, eval_single, wordOp_one, tensorOp_one]

lemma evMA_pow {D d : ℕ} (a : MA D d) (u : Fin d → H →L[ℂ] H) (n : ℕ) :
    evMA (a ^ n) u = (evMA a u) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, evMA_one]
  | succ n ih => rw [pow_succ, evMA_mul, ih, pow_succ]

lemma sMA_coeff_apply {D d : ℕ} (x : MA D d) (v : FreeMonoid (Fin d ⊕ Fin d)) :
    (sMA x).coeff v = (x.coeff (NCPoly.wordStar v))ᴴ := by
  obtain ⟨x0, rfl⟩ : ∃ q, x = MonoidAlgebra.ofCoeff q := ⟨x.coeff, rfl⟩
  induction x0 using Finsupp.induction_linear with
  | zero => simp [sMA_zero]
  | add a b ha hb =>
    rw [MonoidAlgebra.ofCoeff_add, sMA_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add]
    simp only [Finsupp.add_apply, Matrix.conjTranspose_add]
    rw [ha, hb]
  | single w A =>
    have e2 : (MonoidAlgebra.ofCoeff (Finsupp.single w A) : MA D d) = MonoidAlgebra.single w A := rfl
    rw [e2, sMA_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single]
    by_cases h : v = NCPoly.wordStar w
    · subst h
      simp [wordStar_wordStar]
    · have h' : NCPoly.wordStar v ≠ w := by
        intro h2; apply h; rw [← h2, wordStar_wordStar]
      simp [Finsupp.single_apply, h, Ne.symm h, h']

/-- `(P* P)^p` as a self-adjoint noncommutative polynomial. -/
lemma exists_poly_pow {D d : ℕ} (P : NCPoly D d) (p : ℕ) :
    ∃ Q : NCPoly D d, Q.IsSelfAdjoint ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (u : Fin d → H →L[ℂ] H), Q.eval u = (star (P.eval u) * P.eval u) ^ p := by
  set a : MA D d := MonoidAlgebra.ofCoeff P with ha
  set M : MA D d := sMA a * a with hM
  have hMs : sMA M = M := by rw [hM, sMA_mul, sMA_sMA]
  refine ⟨(M ^ p).coeff, ?_, ?_⟩
  · intro w
    have h := sMA_pow M hMs p
    have h2 := sMA_coeff_apply (M ^ p) (NCPoly.wordStar w)
    rw [h, wordStar_wordStar] at h2
    exact h2
  · intro H _ _ _ u
    have := evMA_pow M u p
    rw [hM, evMA_mul, evMA_sMA] at this
    exact this

end StrongConv.Stable
end
end

section
open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace StrongConv.Stable

lemma uniformProb_mono {X : Type*} [Fintype X] {E F : X → Prop} (h : ∀ x, E x → F x) :
    uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

lemma uniformProb_le_one {X : Type*} [Fintype X] (E : X → Prop) : uniformProb E ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_univ _

lemma uniformProb_not {X : Type*} [Fintype X] [Nonempty X] (E : X → Prop) :
    uniformProb (fun x => ¬ E x) = 1 - uniformProb E := by
  classical
  unfold uniformProb
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : ((Finset.univ.filter fun x => ¬ E x).card : ℝ) + (Finset.univ.filter E).card =
      Fintype.card X := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X)) E
    rw [Finset.card_univ, add_comm] at this
    exact_mod_cast this
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hc]
  convert h2 using 3
  congr

lemma uniformProb_true {X : Type*} [Fintype X] [Nonempty X] : uniformProb (fun _ : X => True) = 1 := by
  classical
  unfold uniformProb
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]


lemma finrank_pi' (D n : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin n))) = D * n := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → EuclideanSpace ℂ (Fin n))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

lemma norm_trace_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (Z : E →L[ℂ] E) :
    ‖LinearMap.trace ℂ E (Z : E →ₗ[ℂ] E)‖ ≤ Module.finrank ℂ E * ‖Z‖ := by
  classical
  set b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc ‖∑ i, ⟪b i, Z (b i)⟫_ℂ‖ ≤ ∑ i, ‖⟪b i, Z (b i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℂ E), ‖Z‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
        calc ‖b i‖ * ‖Z (b i)‖ ≤ ‖b i‖ * (‖Z‖ * ‖b i‖) :=
              mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
          _ = ‖Z‖ := by rw [h1]; ring
    _ = Module.finrank ℂ E * ‖Z‖ := by simp

lemma re_trTau_nonneg {D d : ℕ}
    (X : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d))
    (hX : 0 ≤ X) : 0 ≤ (trTau X).re := by
  have hpos : X.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive X).mp hX
  unfold trTau
  have h1 : ((D : ℂ)⁻¹) = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [h1, Complex.re_ofReal_mul, Complex.re_sum]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hpos.re_inner_nonneg_right _)

end StrongConv.Stable

namespace StrongConv

open StrongConv.Stable

theorem tendsto_prob_norm_eval_stableRep_ge_sub_dev (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {D d : ℕ} (P : NCPoly D d) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ‖P.eval (sLimit d)‖ - δ ≤ ‖P.eval (π.model σ)‖)) atTop (𝓝 1) := by
  set ν := ‖P.eval (sLimit d)‖ with hνdef
  by_cases hν : ν ≤ δ
  · have h1 : ∀ N : ℕ, uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ν - δ ≤ ‖P.eval (π.model σ)‖) = 1 := fun N => by
      rw [← uniformProb_true (X := Fin d → Equiv.Perm (Fin N))]
      congr 1
      funext σ
      exact propext ⟨fun _ => trivial, fun _ => by linarith [norm_nonneg (P.eval (π.model σ))]⟩
    simp only [h1]
    exact tendsto_const_nhds
  push_neg at hν
  have hD : 0 < D := by
    by_contra h
    have hD0 : D = 0 := by omega
    subst hD0
    have hsub : Subsingleton (PiLp 2 (fun _ : Fin 0 => L2Free d)) := by infer_instance
    have : P.eval (sLimit d) = 0 := ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
    rw [hνdef, this, norm_zero] at hν
    linarith
  -- choose the exponent `p`
  have hev : ∀ᶠ p : ℕ in atTop, ν - δ / 2 <
      (trTau ((star (P.eval (sLimit d)) * P.eval (sLimit d)) ^ p)).re ^ (1 / (2 * (p : ℝ))) :=
    (tendsto_re_trTau_pow_rpow P).eventually (lt_mem_nhds (by linarith))
  obtain ⟨p, hp, hp1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  obtain ⟨Q, hQ, hQeval⟩ := exists_poly_pow P p
  set K : ℝ := (trTau ((star (P.eval (sLimit d)) * P.eval (sLimit d)) ^ p)).re with hK
  have hK0 : 0 ≤ K := re_trTau_nonneg _ (CStarAlgebra.pow_nonneg (star_mul_self_nonneg _) p)
  have hp0 : (0 : ℝ) < 2 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    linarith
  set t : ℝ := (ν - δ) ^ (2 * p) with ht
  have hKt : t < K := by
    have h1 : ν - δ < K ^ (1 / (2 * (p : ℝ))) := by linarith
    have h2 : (ν - δ) ^ (2 * p) < (K ^ (1 / (2 * (p : ℝ)))) ^ (2 * p) :=
      pow_lt_pow_left₀ h1 (by linarith) (by omega)
    rw [← Real.rpow_natCast (K ^ (1 / (2 * (p : ℝ)))), ← Real.rpow_mul hK0] at h2
    have : 1 / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one] at h2
    exact h2
  set η : ℝ := (K - t) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hR1 := tendsto_prob_norm_trace_sub_trTau_ge π hπ hdim Q hQ η hη0
  have hlow : Tendsto (fun N : ℕ => 1 - uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      η ≤ ‖LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((Q.eval (π.model σ) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) /
          ((D : ℂ) * (π.dim N : ℂ)) - trTau (Q.eval (sLimit d))‖)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hR1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop π.N₀] with N hN
    rw [← uniformProb_not]
    apply uniformProb_mono
    intro σ hσ
    push_neg at hσ
    have hdN := hdim N hN
    have hZ := hQeval (EuclideanSpace ℂ (Fin (π.dim N))) (π.model σ)
    have hZs := hQeval (L2Free d) (sLimit d)
    rw [hZ, hZs] at hσ
    set Y := P.eval (π.model σ) with hY
    set Z := (star Y * Y) ^ p with hZdef
    set τ : ℂ := LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
      (Z : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) /
        ((D : ℂ) * (π.dim N : ℂ)) with hτdef
    have hfr : (Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) : ℝ) =
        D * π.dim N := by
      rw [finrank_pi']; push_cast; ring
    have hDd : (0 : ℝ) < D * π.dim N := by
      have : (0 : ℝ) < D := by exact_mod_cast hD
      have : (0 : ℝ) < π.dim N := by exact_mod_cast hdN
      positivity
    have h1 := norm_trace_le Z
    rw [hfr] at h1
    have h2 : ‖Z‖ ≤ (‖Y‖ ^ 2) ^ p := by
      refine (norm_pow_le' _ (by omega)).trans ?_
      have : ‖star Y * Y‖ ≤ ‖Y‖ ^ 2 := (norm_mul_le _ _).trans (by rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map, sq])
      exact pow_le_pow_left₀ (norm_nonneg _) this p
    have hnormτ : ‖τ‖ ≤ (‖Y‖ ^ 2) ^ p := by
      rw [hτdef, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
        div_le_iff₀ hDd]
      calc ‖LinearMap.trace ℂ _ (Z : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))‖ ≤ D * π.dim N * ‖Z‖ := h1
        _ ≤ (‖Y‖ ^ 2) ^ p * (D * π.dim N) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h2 hDd.le
    have hre : K - η < τ.re := by
      have h3 : |τ.re - K| < η := by
        have := Complex.abs_re_le_norm (τ - trTau ((star (P.eval (sLimit d)) * P.eval (sLimit d)) ^ p))
        rw [Complex.sub_re] at this
        exact lt_of_le_of_lt this hσ
      have := (abs_lt.mp h3).1
      linarith
    have hτre : τ.re ≤ (‖Y‖ ^ 2) ^ p := (Complex.re_le_norm τ).trans hnormτ
    have hlt : t < (‖Y‖ ^ 2) ^ p := by
      have : t < K - η := by rw [hη]; linarith
      linarith
    rw [← pow_mul] at hlt
    have := lt_of_pow_lt_pow_left₀ (2 * p) (norm_nonneg Y) (by rw [ht] at hlt; exact hlt)
    linarith
  · exact Filter.Eventually.of_forall fun N => uniformProb_le_one _

end StrongConv
end
end

theorem solution : type_of% @StrongConv.tendsto_prob_norm_eval_stableRep_ge_sub_dev := @StrongConv.tendsto_prob_norm_eval_stableRep_ge_sub_dev
