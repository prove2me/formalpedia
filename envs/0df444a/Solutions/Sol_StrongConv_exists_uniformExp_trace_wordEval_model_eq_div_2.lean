-- Prove2me | solution 2 for StrongConv.exists_uniformExp_trace_wordEval_model_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:09:22.652706+00:00
-- url     : https://prove2.me/submissions/a684a0a1-b4db-4e76-9498-09b17fa80ed4

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_HananyPuder_uniformExp_prod_xi_eq_sum_quotients

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

section Model

variable (π : StableRep)

/-- the matrix of `π_N` at a permutation, as an operator -/
abbrev opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] EuclideanSpace ℂ (Fin (π.dim N)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ)

lemma opOf_mul {N : ℕ} (τ ρ : Equiv.Perm (Fin N)) : opOf π (τ * ρ) = opOf π τ * opOf π ρ := by
  simp [opOf, map_mul]

lemma opOf_one {N : ℕ} : opOf π (1 : Equiv.Perm (Fin N)) = 1 := by
  simp [opOf]

lemma star_opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) : star (opOf π τ) = opOf π τ⁻¹ := by
  have h1 : star (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) =
      (π.π N τ⁻¹ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) := by
    rw [map_inv]
    simp
  unfold opOf
  rw [← map_star, h1]

lemma wordEval_model {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (π.model σ) w = opOf π (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, opOf_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, opOf_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, opOf_one]
    · simp [letterPerm, letterOp, StableRep.model, opOf]
    · simp [letterPerm, letterOp, StableRep.model, star_opOf]

lemma trace_opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
      (opOf π τ : EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) =
      (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (π.dim N)) ℂ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, opOf, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The trace of `w(Π^N)` as the character polynomial at the cycle counts of the word map. -/
theorem trace_wordEval_model {d N : ℕ} (hN : π.N₀ ≤ N) (σ : Fin d → Equiv.Perm (Fin N))
    (w : List (Letter d)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) =
      MvPolynomial.eval (fun i : Fin π.r =>
        ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (wordFree w)) : ℕ) : ℂ)) π.φ := by
  rw [wordEval_model, trace_opOf, π.trace_eq N hN, wordPerm_eq_lift]

end Model

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

section Expand

variable (π : StableRep)

/-- expectation of the monomial `∏ ξ_{i+1}^{α i}` of the word `u`. -/
def Mexp {d : ℕ} (α : Fin π.r → ℕ) (u : FreeGroup (Fin d)) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    ∏ i : Fin π.r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ u) : ℕ) : ℝ) ^ α i)

lemma re_eval_phi {r : ℕ} (φ : MvPolynomial (Fin r) ℂ) (x : Fin r → ℕ) :
    (MvPolynomial.eval (fun i => ((x i : ℕ) : ℂ)) φ).re =
      ∑ α ∈ φ.support, (φ.coeff α).re * ∏ i, ((x i : ℕ) : ℝ) ^ (α i) := by
  rw [MvPolynomial.eval_eq', Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : (∏ i, ((x i : ℕ) : ℂ) ^ (α i)) = ((∏ i, ((x i : ℕ) : ℝ) ^ (α i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_mul_ofReal]

lemma uniformExp_finset_sum {X ι : Type*} [Fintype X] (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, uniformExp (f a) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformExp_const_mul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    uniformExp (fun x => c * f x) = c * uniformExp f := by
  unfold uniformExp
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The expectation of `Re Tr w(Π^N)` is the character-polynomial combination of the monomial
expectations of the word map. -/
theorem uniformExp_trace_eq_sum {d N : ℕ} (hN : π.N₀ ≤ N) (w : List (Letter d)) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
      ∑ α ∈ π.φ.support, (π.φ.coeff α).re * Mexp π (fun i => α i) (wordFree w) N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re =
      ∑ α ∈ π.φ.support, (π.φ.coeff α).re * ∏ i : Fin π.r,
        ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (wordFree w)) : ℕ) : ℝ) ^ (α i) := by
    intro σ
    rw [trace_wordEval_model π hN, re_eval_phi]
  simp_rw [h]
  rw [uniformExp_finset_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [uniformExp_const_mul]
  rfl

/-- the weighted degree of every monomial of `φ` is at most `β`. -/
theorem weight_le_beta (α : Fin π.r →₀ ℕ) (hα : α ∈ π.φ.support) :
    ∑ i : Fin π.r, ((i : ℕ) + 1) * α i ≤ π.beta := by
  classical
  set Q := MvPolynomial.aeval (fun i : Fin π.r =>
    (MvPolynomial.X i : MvPolynomial (Fin π.r) ℂ) ^ ((i : ℕ) + 1)) π.φ with hQ
  have hexp : Q = ∑ β ∈ π.φ.support, MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i : Fin π.r => ((i : ℕ) + 1) * β i)) (π.φ.coeff β) := by
    rw [hQ, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by intro i; simp),
      MvPolynomial.algebraMap_eq]
    congr 1
    rw [Finset.prod_subset (Finset.subset_univ β.support) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff] at hi; simp [hi])]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [← pow_mul]
  have hcoeff : Q.coeff (Finsupp.equivFunOnFinite.symm
      (fun i : Fin π.r => ((i : ℕ) + 1) * α i)) = π.φ.coeff α := by
    rw [hexp, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      apply hβ
      ext i
      have := congr_fun (Finsupp.equivFunOnFinite.symm.injective h) i
      simp at this
      exact this
    · intro h; exact absurd hα h
  have hne : Q.coeff (Finsupp.equivFunOnFinite.symm
      (fun i : Fin π.r => ((i : ℕ) + 1) * α i)) ≠ 0 := by
    rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hα
  have := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)] at this
  simpa [StableRep.beta, hQ] using this

/-- the real coefficient -/
def cre (α : Fin π.r →₀ ℕ) : ℝ := (π.φ.coeff α).re

end Expand

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

open HananyPuder

lemma norm_wordFree_le {d : ℕ} (w : List (Letter d)) : FreeGroup.norm (wordFree w) ≤ w.length := by
  induction w with
  | nil => simp [wordFree]
  | cons a w ih =>
    have h : wordFree (a :: w) = (match a with
        | none => 1
        | some (Sum.inl i) => FreeGroup.of i
        | some (Sum.inr i) => (FreeGroup.of i)⁻¹) * wordFree w := by
      simp only [wordFree, List.map_cons, List.prod_cons]; rfl
    rw [h]
    refine (FreeGroup.norm_mul_le _ _).trans ?_
    have : FreeGroup.norm (match a with
        | none => (1 : FreeGroup (Fin d))
        | some (Sum.inl i) => FreeGroup.of i
        | some (Sum.inr i) => (FreeGroup.of i)⁻¹) ≤ 1 := by
      rcases a with _ | (i | i) <;> simp [FreeGroup.norm_of, FreeGroup.norm_inv_eq, FreeGroup.norm_one]
    simp only [List.length_cons]
    omega

lemma length_reduceCyclically_le {d : ℕ} (x : FreeGroup (Fin d)) :
    (FreeGroup.reduceCyclically x.toWord).length ≤ FreeGroup.norm x := by
  have := congrArg List.length (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically x.toWord)
  simp only [List.length_append] at this
  unfold FreeGroup.norm
  omega

lemma card_cycleVert {d r : ℕ} (L : List (Fin d × Bool)) (α : Fin r → ℕ) :
    Fintype.card (CycleVert L α) = ∑ i : Fin r, α i * (((i : ℕ) + 1) * L.length) := by
  unfold CycleVert
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, cycleWord, List.length_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  rw [Fintype.sum_sigma]
  simp [mul_comm]

lemma sum_quotEdge_le {d r : ℕ} {L : List (Fin d × Bool)} {α : Fin r → ℕ}
    (P : Finpartition (Finset.univ : Finset (CycleVert L α))) :
    ∑ j, quotEdge P j ≤ Fintype.card (CycleVert L α) := by
  classical
  calc ∑ j, quotEdge P j ≤ ∑ j : Fin d, (Finset.univ.filter fun e : CycleVert L α =>
        (edgeLetter e).1 = j).card :=
        Finset.sum_le_sum fun j _ => Finset.card_image_le
    _ = Fintype.card (CycleVert L α) := by
        rw [← Finset.card_univ]
        exact (Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ _)).symm

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Alg
open Polynomial Finset

/-- The linear factor `1 - j X`. -/
abbrev L (j : ℕ) : ℝ[X] := 1 - (j : ℝ[X]) * X

lemma L_eq (j : ℕ) : L j = C (-(j : ℝ)) * X + C 1 := by
  simp [L, sub_eq_add_neg, add_comm, map_natCast]

lemma natDegree_L (j : ℕ) (hj : 1 ≤ j) : (L j).natDegree = 1 := by
  rw [L_eq]
  apply natDegree_linear
  have : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  simpa using this

lemma natDegree_L_le (j : ℕ) : (L j).natDegree ≤ 1 := by
  rw [L_eq]; exact natDegree_linear_le

lemma eval_L (j : ℕ) (x : ℝ) : (L j).eval x = 1 - j * x := by
  simp [L]

lemma natDegree_gPoly (d q : ℕ) :
    (gPoly d q).natDegree = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
  unfold gPoly
  rw [natDegree_prod]
  · apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    rw [natDegree_pow, natDegree_L j hj.1, mul_one]
  · intro j hj
    rw [mem_Ico] at hj
    apply pow_ne_zero
    intro h
    have := natDegree_L j hj.1
    change L j = 0 at h
    rw [h] at this; simp at this

lemma factor_pos (j q N : ℕ) (hj : j < q) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    0 < 1 - (j : ℝ) * (1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : (j : ℝ) < N := by exact_mod_cast (by omega : j < N)
  rw [mul_one_div, sub_pos, div_lt_one hNpos]
  exact this

lemma eval_prod_pos (q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) (s : Finset ℕ) (hs : ∀ j ∈ s, j < q)
    (k : ℕ → ℕ) : 0 < (∏ j ∈ s, L j ^ k j).eval (1 / (N : ℝ)) := by
  rw [eval_prod]
  apply prod_pos
  intro j hj
  rw [eval_pow, eval_L]
  exact pow_pos (factor_pos j q N (hs j hj) hN hN1) _

theorem gPoly_eval_ne_zero (d q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    (gPoly d q).eval (1 / (N : ℝ)) ≠ 0 := by
  have := eval_prod_pos q N hN hN1 (Ico 1 q) (fun j hj => (mem_Ico.1 hj).2)
    (fun j => min d (q / (j + 1)))
  exact ne_of_gt this

lemma filter_lt_Ico (e q : ℕ) (he : e ≤ q) : (Ico 1 q).filter (· < e) = Ico 1 e := by
  ext j; simp only [mem_filter, mem_Ico]; omega

lemma prod_prod_Ico {d : ℕ} (e : Fin d → ℕ) (q : ℕ) (he : ∀ i, e i ≤ q) (f : ℕ → ℝ) :
    ∏ i, ∏ j ∈ Ico 1 (e i), f j =
      ∏ j ∈ Ico 1 q, f j ^ (univ.filter (fun i => j < e i)).card := by
  have : ∀ i, ∏ j ∈ Ico 1 (e i), f j = ∏ j ∈ Ico 1 q, (if j < e i then f j else 1) := by
    intro i
    rw [← prod_filter, filter_lt_Ico _ _ (he i)]
  simp_rw [this]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro j _
  rw [← prod_filter, prod_const]

/-- `#{j < d : (j+1) b ≤ q} = min d (q / b)`. -/
lemma card_filter_mul_le (d b q : ℕ) (hb : 0 < b) :
    ((range d).filter (fun j => (j + 1) * b ≤ q)).card = min d (q / b) := by
  have : (range d).filter (fun j => (j + 1) * b ≤ q) = range (min d (q / b)) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
    rw [← Nat.le_div_iff_mul_le hb]
    omega
  rw [this, card_range]

theorem natDegree_gPoly_add_min_le (d q : ℕ) (hq : 1 ≤ q) :
    (((gPoly d q).natDegree + min d q : ℕ) : ℝ) ≤ q * (1 + Real.log d) := by
  have key : (gPoly d q).natDegree + min d q = ∑ j ∈ range d, q / (j + 1) := by
    rw [natDegree_gPoly]
    have h1 : ∑ m ∈ range q, min d (q / (m + 1)) =
        min d q + ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
      simp
    rw [add_comm, ← h1]
    have h2 : ∀ m, min d (q / (m + 1)) =
        ∑ j ∈ range d, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro m
      rw [← card_filter_mul_le d (m + 1) q (by omega), card_filter]
    have h3 : ∀ j, q / (j + 1) =
        ∑ m ∈ range q, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro j
      have := card_filter_mul_le q (j + 1) q (by omega)
      rw [min_eq_right (Nat.div_le_self _ _), card_filter] at this
      rw [← this]
      apply sum_congr rfl; intro m _; rw [mul_comm]
    simp_rw [h2, h3]
    rw [sum_comm]
  rw [key]
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc ((∑ j ∈ range d, q / (j + 1) : ℕ) : ℝ) ≤ ∑ j ∈ range d, (q : ℝ) / ((j : ℝ) + 1) := by
        push_cast
        apply sum_le_sum; intro j _
        have := Nat.cast_div_le (α := ℝ) (m := q) (n := j + 1)
        push_cast at this
        exact this
    _ = q * (harmonic d : ℝ) := by
        simp only [harmonic]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro j _
        field_simp
    _ ≤ q * (1 + Real.log d) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) hq0

end StrongConv.W2.Alg

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Alg
open Polynomial Finset

theorem exists_poly_term2 (d q : ℕ) (hq : 1 ≤ q) (v : ℕ) (e : Fin d → ℕ)
    (h2 : v ≤ ∑ i, e i) (h3 : ∑ i, e i ≤ q) :
    ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d q).natDegree + min d q ∧
      ∀ N : ℕ, q ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) ^ (∑ i, e i - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * (1 / (N : ℝ)))) /
            ∏ i, ∏ j ∈ Ico 1 (e i), (1 - (j : ℝ) * (1 / (N : ℝ))) =
          φ.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  set E := ∑ i, e i with hE
  have he : ∀ i, e i ≤ q := fun i =>
    le_trans (single_le_sum (fun i _ => Nat.zero_le (e i)) (mem_univ i)) h3
  set c : ℕ → ℕ := fun j => (univ.filter (fun i => j < e i)).card with hc
  set dd : ℕ → ℕ := fun j => min d (q / (j + 1)) with hdd
  have hcd : ∀ j, c j ≤ dd j := by
    intro j
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc c j * (j + 1) = ∑ i ∈ univ.filter (fun i => j < e i), (j + 1) := by
            simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => j < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  -- Σ_{j<q} c j = E
  have hsumc : ∑ j ∈ range q, c j = E := by
    simp only [hc, card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (range q).filter (fun j => j < e i) = range (e i) := by
      ext j; simp only [mem_filter, mem_range]; have := he i; omega
    rw [this, card_range]
  have hc0 : c 0 ≤ min d q := by
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · calc c 0 = ∑ i ∈ univ.filter (fun i => 0 < e i), 1 := by simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => 0 < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  have hsplit : ∑ j ∈ range q, c j = c 0 + ∑ j ∈ Ico 1 q, c j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  refine ⟨X ^ (E - v) * (∏ j ∈ Ico 1 v, L j) * ∏ j ∈ Ico 1 q, L j ^ (dd j - c j), ?_, ?_⟩
  · rw [natDegree_gPoly]
    have hA : (∏ j ∈ Ico 1 v, L j).natDegree ≤ v - 1 := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ Ico 1 v, (L j).natDegree ≤ ∑ j ∈ Ico 1 v, 1 :=
            sum_le_sum (fun j _ => natDegree_L_le j)
        _ = v - 1 := by simp
    have hR : (∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).natDegree ≤ ∑ j ∈ Ico 1 q, (dd j - c j) := by
      refine (natDegree_prod_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      refine natDegree_pow_le.trans ?_
      calc (dd j - c j) * (L j).natDegree ≤ (dd j - c j) * 1 :=
            Nat.mul_le_mul_left _ (natDegree_L_le j)
        _ = _ := mul_one _
    have hX : (X ^ (E - v) : ℝ[X]).natDegree ≤ E - v := natDegree_X_pow_le _
    have hsub : ∑ j ∈ Ico 1 q, (dd j - c j) + ∑ j ∈ Ico 1 q, c j = ∑ j ∈ Ico 1 q, dd j := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _; have := hcd j; omega
    refine (natDegree_mul_le).trans ?_
    have := (natDegree_mul_le (p := (X ^ (E - v) : ℝ[X])) (q := ∏ j ∈ Ico 1 v, L j))
    have hdd : ∑ j ∈ Ico 1 q, dd j = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := rfl
    omega
  · intro N hN hN1
    set x : ℝ := 1 / (N : ℝ) with hx
    have hD : ∏ i, ∏ j ∈ Ico 1 (e i), (1 - (j : ℝ) * x) =
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j :=
      prod_prod_Ico e q he (fun j => 1 - (j : ℝ) * x)
    have hCpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hRpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hg : (gPoly d q).eval x = (∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      unfold gPoly
      rw [eval_prod, ← prod_mul_distrib]
      apply prod_congr rfl
      intro j _
      rw [← pow_add, eval_pow]
      change (L j).eval x ^ _ = _
      rw [eval_L]
      congr 1
      have := hcd j
      simp only [hdd] at this ⊢
      omega
    have hφ : (X ^ (E - v) * (∏ j ∈ Ico 1 v, L j) *
        ∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).eval x =
        x ^ (E - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      simp [eval_prod]
    rw [hφ, hg, hD]
    exact (mul_div_mul_right _ _ hRpos.ne').symm


end StrongConv.W2.Alg

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

/-- the summand of Hanany–Puder's (10.2) -/
def termV {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) : ℝ :=
  ((1 : ℝ) / N) ^ (((∑ j, e j : ℕ) : ℤ) - V) * (∏ i ∈ Finset.Ico 1 V, (1 - (i : ℝ) / N)) /
    ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (e j), (1 - (i : ℝ) / N)

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Root

open FreeGroup FreeGroup.reduceCyclically

end StrongConv.W2.Root

end
end

section
/-! `v_Γ ≤ e_Γ` for every quotient of the cycle graph of a cyclically reduced word:
each block owns two distinct half-edges (the end of the walk's incoming edge at a chosen vertex
and the start of its outgoing edge), and a half-edge determines its block. -/

noncomputable section

namespace StrongConv.W2.Edge

open HananyPuder

variable {d r : ℕ} {L : List (Fin d × Bool)} {α : Fin r → ℕ}

/-- consecutive letters of a cyclically reduced word, read cyclically, do not cancel -/
lemma cyc_adj {W : List (Fin d × Bool)} (hW : FreeGroup.IsCyclicallyReduced W) (p : ℕ)
    (hp : p < W.length) :
    let q := if p = 0 then W.length - 1 else p - 1
    ∀ hq : q < W.length, W[q].1 = W[p].1 → W[q].2 = W[p].2 := by
  intro q hq
  by_cases h0 : p = 0
  · subst h0
    have hq' : q = W.length - 1 := by simp [q]
    intro h
    have hne : W ≠ [] := List.ne_nil_of_length_pos hp
    have hlast : W[q] ∈ W.getLast? := by
      rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some_inj, List.getLast_eq_getElem]
      simp [hq']
    have hhead : W[0] ∈ W.head? := by
      rw [List.head?_eq_getElem?, Option.mem_def, List.getElem?_eq_getElem hp]
    exact hW.2 _ hlast _ hhead h
  · have hq' : q = p - 1 := by simp [q, h0]
    have hR := hW.1
    unfold FreeGroup.IsReduced at hR
    rw [List.isChain_iff_getElem] at hR
    have := hR (p - 1) (by omega)
    simp only [hq']
    have e : p - 1 + 1 = p := by omega
    simpa [e] using this

/-- the previous position on the same cycle -/
def prevVert (v : CycleVert L α) : CycleVert L α :=
  ⟨v.1, ⟨if (v.2 : ℕ) = 0 then (cycleWord L ((v.1.1 : ℕ) + 1)).length - 1 else (v.2 : ℕ) - 1,
    by have := v.2.2; split <;> omega⟩⟩

lemma nextVert_prevVert (v : CycleVert L α) : nextVert (prevVert v) = v := by
  obtain ⟨c, p, hp⟩ := v
  simp only [nextVert, prevVert]
  congr 1
  ext
  simp only
  split
  · rename_i h; subst h
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  · rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hp]

lemma prev_letter (hL : FreeGroup.IsCyclicallyReduced L) (v : CycleVert L α)
    (h : (edgeLetter (prevVert v)).1 = (edgeLetter v).1) :
    (edgeLetter (prevVert v)).2 = (edgeLetter v).2 := by
  have hW := hL.flatten_replicate ((v.1.1 : ℕ) + 1)
  have := cyc_adj hW v.2 v.2.2 (prevVert v).2.2
  exact this h

variable (P : Finpartition (Finset.univ : Finset (CycleVert L α)))

/-- the edge classes of the quotient, as a sigma type over labels -/
def edgeSet : Finset (Σ _ : Fin d, Finset (CycleVert L α) × Finset (CycleVert L α)) :=
  Finset.univ.sigma fun j =>
    (Finset.univ.filter fun e : CycleVert L α => (edgeLetter e).1 = j).image
      fun e => (P.part (edgeTail e), P.part (edgeHead e))

lemma card_edgeSet : (edgeSet P).card = ∑ j, quotEdge P j := by
  unfold edgeSet; rw [Finset.card_sigma]; rfl

/-- the half-edge of edge `e` at `nextVert e` (if `b`) or at `e` -/
def inc (e : CycleVert L α) (b : Bool) :
    (Σ _ : Fin d, Finset (CycleVert L α) × Finset (CycleVert L α)) × Bool :=
  (⟨(edgeLetter e).1, (P.part (edgeTail e), P.part (edgeHead e))⟩, b == (edgeLetter e).2)

lemma inc_mem (e : CycleVert L α) (b : Bool) : inc P e b ∈ edgeSet P ×ˢ Finset.univ := by
  simp only [inc, edgeSet, Finset.mem_product, Finset.mem_sigma, Finset.mem_univ, true_and,
    and_true, Finset.mem_image, Finset.mem_filter]
  exact ⟨e, rfl, rfl⟩

/-- a half-edge determines the block of its vertex -/
lemma block_of_inc (e : CycleVert L α) (b : Bool) :
    P.part (if b then nextVert e else e) =
      (if (inc P e b).2 then (inc P e b).1.2.2 else (inc P e b).1.2.1) := by
  simp only [inc, edgeTail, edgeHead]
  by_cases hs : (edgeLetter e).2 = true <;> cases b <;> simp [hs]

theorem quotVert_le_sum_quotEdge (hL : FreeGroup.IsCyclicallyReduced L) :
    quotVert P ≤ ∑ j, quotEdge P j := by
  classical
  rcases isEmpty_or_nonempty (CycleVert L α) with hE | hE
  · have : quotVert P ≤ Fintype.card (CycleVert L α) := by
      unfold quotVert; simpa using P.card_parts_le_card
    simp at this; omega
  let rep : Finset (CycleVert L α) → CycleVert L α := fun B => Classical.epsilon (· ∈ B)
  have hrep : ∀ B ∈ P.parts, rep B ∈ B := fun B hB =>
    Classical.epsilon_spec (P.nonempty_of_mem_parts hB)
  have hpart : ∀ B ∈ P.parts, P.part (rep B) = B := fun B hB =>
    P.part_eq_of_mem hB (hrep B hB)
  let h : Finset (CycleVert L α) × Bool →
      (Σ _ : Fin d, Finset (CycleVert L α) × Finset (CycleVert L α)) × Bool :=
    fun x => inc P (if x.2 then prevVert (rep x.1) else rep x.1) x.2
  have hvert : ∀ B ∈ P.parts, ∀ b : Bool,
      P.part (if b then nextVert (if b then prevVert (rep B) else rep B)
        else (if b then prevVert (rep B) else rep B)) = B := by
    intro B hB b
    cases b <;> simp [nextVert_prevVert, hpart B hB]
  have hinj : Set.InjOn h ↑(P.parts ×ˢ (Finset.univ : Finset Bool)) := by
    rintro ⟨B, b⟩ hx ⟨B', b'⟩ hx' hh
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
      Set.mem_univ, and_true] at hx hx'
    have e1 := block_of_inc P (if b then prevVert (rep B) else rep B) b
    have e2 := block_of_inc P (if b' then prevVert (rep B') else rep B') b'
    rw [hvert B hx b] at e1
    rw [hvert B' hx' b'] at e2
    have hBB : B = B' := by
      simp only [h] at hh
      rw [e1, e2, hh]
    subst hBB
    refine Prod.ext rfl ?_
    by_contra hbb
    simp only [h] at hh
    have key : ∀ b₁ b₂ : Bool, b₁ ≠ b₂ →
        inc P (if b₁ then prevVert (rep B) else rep B) b₁ =
          inc P (if b₂ then prevVert (rep B) else rep B) b₂ → False := by
      intro b₁ b₂ hne heq
      have hfst := congrArg (fun x => x.1.1) heq
      have hsnd := congrArg (fun x => x.2) heq
      simp only [inc] at hfst hsnd
      cases b₁ <;> cases b₂ <;> simp at hne hfst hsnd
      · have := prev_letter hL (rep B) hfst.symm
        revert hsnd this
        cases (edgeLetter (rep B)).2 <;> cases (edgeLetter (prevVert (rep B))).2 <;> simp
      · have := prev_letter hL (rep B) hfst
        revert hsnd this
        cases (edgeLetter (rep B)).2 <;> cases (edgeLetter (prevVert (rep B))).2 <;> simp
    exact key b b' hbb hh
  have hcard := Finset.card_le_card_of_injOn h (fun x _ => inc_mem P _ _) hinj
  rw [Finset.card_product, Finset.card_product, card_edgeSet] at hcard
  unfold quotVert
  simp at hcard
  omega

end StrongConv.W2.Edge
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

open HananyPuder

lemma termV_eq_npow {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) (h : V ≤ ∑ j, e j) :
    termV V e N = ((1 / (N : ℝ)) ^ (∑ j, e j - V) *
        (∏ j ∈ Finset.Ico 1 V, (1 - (j : ℝ) * (1 / (N : ℝ))))) /
      ∏ i, ∏ j ∈ Finset.Ico 1 (e i), (1 - (j : ℝ) * (1 / (N : ℝ))) := by
  unfold termV
  rw [show (((∑ j, e j : ℕ) : ℤ) - V) = ((∑ j, e j - V : ℕ) : ℤ) by omega, zpow_natCast]
  simp only [mul_one_div]

variable (π : StableRep)

lemma Mexp_zero {d : ℕ} (u : FreeGroup (Fin d)) (N : ℕ) : Mexp π (fun _ => 0) u N = 1 := by
  unfold Mexp uniformExp
  simp only [pow_zero, Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self this

theorem exists_poly_of_pos {d q : ℕ} (u : FreeGroup (Fin d)) (hu : u ≠ 1)
    (hlen : FreeGroup.norm u ≤ q) (α : Fin π.r → ℕ) (hα : 0 < ∑ i, α i)
    (hwt : ∑ i : Fin π.r, ((i : ℕ) + 1) * α i ≤ π.beta) :
    ∃ p : ℝ[X], p.natDegree ≤ (gPoly d (π.beta * q)).natDegree + min d (π.beta * q) ∧
      ∀ N : ℕ, π.beta * q ≤ N → Mexp π α u N =
        p.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) := by
  classical
  set B := π.beta * q with hBdef
  set L := FreeGroup.reduceCyclically u.toWord with hL
  have hnorm1 : 1 ≤ FreeGroup.norm u := Nat.one_le_iff_ne_zero.mpr (by
    intro h; exact hu (FreeGroup.norm_eq_zero.mp h))
  have hq : 1 ≤ q := hnorm1.trans hlen
  have hβ : 1 ≤ π.beta := by
    have : ∑ i : Fin π.r, α i ≤ ∑ i : Fin π.r, ((i : ℕ) + 1) * α i :=
      Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  have hB : 1 ≤ B := Nat.mul_pos hβ hq
  have hℓ : L.length ≤ q := (length_reduceCyclically_le u).trans hlen
  have hcard : Fintype.card (CycleVert L α) ≤ B := by
    rw [card_cycleVert]
    calc ∑ i : Fin π.r, α i * (((i : ℕ) + 1) * L.length) =
          L.length * ∑ i : Fin π.r, ((i : ℕ) + 1) * α i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ q * π.beta := Nat.mul_le_mul hℓ hwt
      _ = B := mul_comm _ _
  have hEle : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), ∑ j, quotEdge P j ≤ B :=
    fun P => (sum_quotEdge_le P).trans hcard
  have hej : ∀ (P : Finpartition (Finset.univ : Finset (CycleVert L α))) (j : Fin d),
      quotEdge P j ≤ B := fun P j =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (quotEdge P j)) (Finset.mem_univ j)).trans (hEle P)
  have hVle : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), quotVert P ≤ B := by
    intro P
    unfold quotVert
    refine le_trans ?_ hcard
    simpa using P.card_parts_le_card
  have hHP : ∀ N, B ≤ N → Mexp π α u N =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (CycleVert L α)))).filter
        IsFoldFree, termV (quotVert P) (quotEdge P) N := by
    intro N hN
    exact HananyPuder.uniformExp_prod_xi_eq_sum_quotients u hu α hα N
      (fun P _ j => (hej P j).trans hN)
  have hLcr : FreeGroup.IsCyclicallyReduced L :=
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  have hkey : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), IsFoldFree P →
      quotVert P ≤ ∑ j, quotEdge P j := fun P _ => Edge.quotVert_le_sum_quotEdge P hLcr
  have hpoly : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), IsFoldFree P →
      ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d B).natDegree + min d B ∧
        ∀ N : ℕ, B ≤ N → 1 ≤ N →
          ((1 / (N : ℝ)) ^ (∑ j, quotEdge P j - quotVert P) *
            (∏ j ∈ Finset.Ico 1 (quotVert P), (1 - (j : ℝ) * (1 / (N : ℝ))))) /
            ∏ i, ∏ j ∈ Finset.Ico 1 (quotEdge P i), (1 - (j : ℝ) * (1 / (N : ℝ))) =
          φ.eval (1 / (N : ℝ)) / (gPoly d B).eval (1 / (N : ℝ)) := by
    intro P hP
    exact Alg.exists_poly_term2 d B hB (quotVert P) (quotEdge P) (hkey P hP) (hEle P)
  choose! φ hφdeg hφeq using hpoly
  set S := (Finset.univ : Finset (Finpartition (Finset.univ : Finset (CycleVert L α)))).filter
    IsFoldFree with hS
  refine ⟨∑ P ∈ S, φ P, ?_, ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun P hP =>
      hφdeg P (Finset.mem_filter.1 hP).2
  · intro N hN
    have hN1 : 1 ≤ N := hB.trans hN
    rw [hHP N hN, Polynomial.eval_finset_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := (Finset.mem_filter.1 hP).2
    rw [termV_eq_npow _ _ N (hkey P hP'), hφeq P hP' N hN hN1]

end StrongConv.W2
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

theorem lemma101 (π : StableRep) (hπ : π.NoTrivialSummand) (d q : ℕ) (w : List (Letter d))
    (hw : w.length ≤ q) (hw1 : wordFree w ≠ 1) :
    ((gPoly d (π.beta * q)).natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
        ∀ N : ℕ, π.beta * q ≤ N → π.N₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
                (wordEval (π.model σ) w :
                  EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
            f.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) := by
  classical
  set B := π.beta * q with hBdef
  set g := gPoly d B with hg
  have hlen : FreeGroup.norm (wordFree w) ≤ q := (norm_wordFree_le w).trans hw
  -- degree bounds
  have hG : (((g.natDegree + min d B : ℕ)) : ℝ) ≤ B * (1 + Real.log d) := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · have : g = 1 := by rw [hg, h0]; simp [gPoly]
      rw [this, h0]; simp
    · exact Alg.natDegree_gPoly_add_min_le d B h0
  have hgdeg : (g.natDegree : ℝ) ≤ B * (1 + Real.log d) :=
    le_trans (by exact_mod_cast Nat.le_add_right _ _) hG
  have hBc : (B : ℝ) = π.beta * q := by simp [hBdef]
  rw [hBc] at hG hgdeg
  refine ⟨hgdeg, ?_⟩
  have hgne : ∀ N : ℕ, B ≤ N → g.eval (1 / (N : ℝ)) ≠ 0 := by
    intro N hN
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · simp [hg, h0, gPoly]
    · exact Alg.gPoly_eval_ne_zero d B N hN (h0.trans_le hN)
  have hper : ∀ α ∈ π.φ.support, ∃ p : ℝ[X], p.natDegree ≤ g.natDegree + min d B ∧
      ∀ N : ℕ, B ≤ N → Mexp π (fun i => α i) (wordFree w) N =
        p.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)) := by
    intro α hα
    by_cases h0 : ∑ i, α i = 0
    · refine ⟨g, Nat.le_add_right _ _, fun N hN => ?_⟩
      have : (fun i => α i) = fun _ => 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
      rw [this, Mexp_zero, div_self (hgne N hN)]
    · exact exists_poly_of_pos π (wordFree w) hw1 hlen (fun i => α i) (Nat.pos_of_ne_zero h0)
        (weight_le_beta π α hα)
  choose! p hpdeg hpeq using hper
  refine ⟨∑ α ∈ π.φ.support, C (cre π α) * p α, ?_, ?_⟩
  · refine le_trans ?_ hG
    exact_mod_cast Polynomial.natDegree_sum_le_of_forall_le _ _ fun α hα =>
      (Polynomial.natDegree_C_mul_le _ _).trans (hpdeg α hα)
  · intro N hN hN0
    rw [uniformExp_trace_eq_sum π hN0 w, Polynomial.eval_finsetSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [hpeq α hα N hN]
    simp [cre, mul_div_assoc]

end StrongConv.W2

end
end
open StrongConv Polynomial in
theorem solution (π : StableRep) (hπ : π.NoTrivialSummand)
    (d q : ℕ) (w : List (Letter d)) (hw : w.length ≤ q) (hw1 : wordFree w ≠ 1) :
    ((gPoly d (π.beta * q)).natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
        ∀ N : ℕ, π.beta * q ≤ N → π.N₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
                (wordEval (π.model σ) w :
                  EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
            f.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) :=
  StrongConv.W2.lemma101 π hπ d q w hw hw1
