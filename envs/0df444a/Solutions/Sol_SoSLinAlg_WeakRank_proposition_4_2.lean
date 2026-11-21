-- Prove2me | solution 1 for SoSLinAlg.WeakRank.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:40:18.802182+00:00
-- url     : https://prove2.me/submissions/ee899a60-b712-4f52-87ae-7472ddb807e8

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_Z
import Theorems.Thm_SoSLinAlg_WeakRank_membership_of_vanishing_on_orthogonal_rows

section
noncomputable section

namespace SoSLinAlg.Dev.P42

open SoSLinAlg.WeakRank MvPolynomial

/-- Row index: rows of X (left) and rows of Y (right). -/
abbrev T (n : ℕ) := Fin n ⊕ Fin n

def row {n r : ℕ} : Var n r → T n
  | Sum.inl ik => Sum.inl ik.1
  | Sum.inr jk => Sum.inr jk.1

def wt {n r : ℕ} (v : Var n r) : T n →₀ ℕ := Finsupp.single (row v) 1

lemma weight_apply' {n r : ℕ} (s : Var n r →₀ ℕ) (τ : T n) :
    (Finsupp.weight (wt (n := n) (r := r)) s) τ = ∑ v, if row v = τ then s v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [wt, Finsupp.single_apply]

lemma le_weight_apply {n r : ℕ} (s : Var n r →₀ ℕ) (v : Var n r) :
    s v ≤ (Finsupp.weight (wt (n := n) (r := r)) s) (row v) := by
  rw [weight_apply']
  calc s v = if row v = row v then s v else 0 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun v' => if row v' = row v then s v' else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

lemma degree_weight {n r : ℕ} (s : Var n r →₀ ℕ) :
    (Finsupp.weight (wt (n := n) (r := r)) s).degree = s.degree := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  rw [map_sum, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [wt, Finsupp.degree_single]

/-- scaling polynomial map -/
def psi {n r : ℕ} (a : Var n r → ℝ) : Poly n r →ₐ[ℝ] MvPolynomial (T n) ℝ :=
  aeval (fun v => C (a v) * X (row v))

lemma eval_psi {n r : ℕ} (a : Var n r → ℝ) (t : T n → ℝ) (f : Poly n r) :
    eval t (psi a f) = eval (fun v => t (row v) * a v) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [psi]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp [psi] at hp ⊢; rw [hp]; ring

lemma psi_monomial {n r : ℕ} (a : Var n r → ℝ) (s : Var n r →₀ ℕ) (c : ℝ) :
    psi a (monomial s c) = monomial (Finsupp.weight wt s) (c * ∏ v, a v ^ s v) := by
  have h1 : monomial (Finsupp.weight wt s) (1 : ℝ) = ∏ v, X (row v) ^ s v := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), monomial_sum_one]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [X_pow_eq_monomial]
    simp [wt, Finsupp.smul_single]
  have h2 : monomial (Finsupp.weight wt s) (c * ∏ v, a v ^ s v) =
      C (c * ∏ v, a v ^ s v) * ∏ v, X (row v) ^ s v := by
    rw [← h1, C_mul_monomial, mul_one]
  rw [h2, psi, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [map_mul, aeval_C, map_prod, map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib,
    map_prod, map_pow]
  simp [mul_assoc]

lemma coeff_psi {n r : ℕ} (a : Var n r → ℝ) (f : Poly n r) (δ : T n →₀ ℕ) :
    coeff δ (psi a f) = eval a (weightedHomogeneousComponent wt δ f) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum, coeff_sum]
  simp only [psi_monomial, coeff_monomial]
  rw [eval_eq', support_weightedHomogeneousComponent, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_weightedHomogeneousComponent]
  by_cases h : Finsupp.weight wt s = δ <;> simp [h]

lemma scaled_mem {n r d : ℕ} (X Y : Matrix (Fin n) (Fin r) ℝ) (h : (X, Y) ∈ Z n r d)
    (t : T n → ℝ) :
    (Matrix.diagonal (fun i => t (Sum.inl i)) * X,
      Matrix.diagonal (fun i => t (Sum.inr i)) * Y) ∈ Z n r d := by
  obtain ⟨h0, hr⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.diagonal_transpose]
    calc _ = Matrix.diagonal (fun i => t (Sum.inl i)) * (X * Y.transpose) *
          Matrix.diagonal (fun i => t (Sum.inr i)) := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0]; simp
  · exact (add_le_add (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_right _ _)).trans hr

lemma assignment_scaled {n r : ℕ} (X Y : Matrix (Fin n) (Fin r) ℝ) (t : T n → ℝ) :
    assignment (Matrix.diagonal (fun i => t (Sum.inl i)) * X)
      (Matrix.diagonal (fun i => t (Sum.inr i)) * Y) =
    fun v => t (row v) * assignment X Y v := by
  funext v
  rcases v with ⟨i, k⟩ | ⟨j, k⟩ <;> simp [assignment, row, Matrix.diagonal_mul]

lemma comp_vanishes {n r d : ℕ} {f : Poly n r} (hvan : VanishesOnZ d f) (δ : T n →₀ ℕ) :
    VanishesOnZ d (weightedHomogeneousComponent wt δ f) := by
  intro X Y hXY
  have h0 : psi (assignment X Y) f = 0 := by
    apply MvPolynomial.funext
    intro t
    rw [eval_psi, ← assignment_scaled]
    simpa using hvan _ _ (scaled_mem X Y hXY t)
  rw [← coeff_psi, h0]; simp

lemma comp_mul {n r : ℕ} (g p : Poly n r) (e δ : T n →₀ ℕ)
    (hp : p ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) e) (he : e ≤ δ) :
    weightedHomogeneousComponent wt δ (g * p) =
      weightedHomogeneousComponent wt (δ - e) g * p := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra ℝ (wt (n := n) (r := r))
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le
    (weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r))) (a := g) hp he
  simpa [← weightedDecomposition.decompose'_apply] using this

lemma xy_mem {n r : ℕ} (i j : Fin n) :
    xy (r := r) i j ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r))
      (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1) := by
  unfold xy x y
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 : (X (Sum.inl (i, k)) : Poly n r) ∈ weightedHomogeneousSubmodule ℝ wt
      (Finsupp.single (Sum.inl i) 1) := by
    simpa [wt, row] using isWeightedHomogeneous_X ℝ (wt (n := n) (r := r)) (Sum.inl (i, k))
  have h2 : (X (Sum.inr (j, k)) : Poly n r) ∈ weightedHomogeneousSubmodule ℝ wt
      (Finsupp.single (Sum.inr j) 1) := by
    simpa [wt, row] using isWeightedHomogeneous_X ℝ (wt (n := n) (r := r)) (Sum.inr (j, k))
  exact weightedHomogeneousSubmodule_mul _ _ _ (Submodule.mul_mem_mul h1 h2)

lemma sum_eq_degree {σ : Type*} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := rfl

lemma mem_support_degree {n r : ℕ} {F : Poly n r} {δ : T n →₀ ℕ}
    (hF : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ)
    {s : Var n r →₀ ℕ} (hs : s ∈ F.support) : s.degree = δ.degree := by
  rw [mem_weightedHomogeneousSubmodule] at hF
  rw [← degree_weight, hF (mem_support_iff.mp hs)]

lemma totalDegree_le_of_mem {n r : ℕ} {F : Poly n r} {δ : T n →₀ ℕ}
    (hF : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ) :
    F.totalDegree ≤ δ.degree := by
  unfold totalDegree
  refine Finset.sup_le fun s hs => ?_
  rw [sum_eq_degree, mem_support_degree hF hs]

lemma degree_le_totalDegree {n r : ℕ} {F : Poly n r} {δ : T n →₀ ℕ}
    (hF : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ) (h0 : F ≠ 0) :
    δ.degree ≤ F.totalDegree := by
  obtain ⟨s, hs⟩ := (MvPolynomial.support_nonempty).mpr h0
  rw [← mem_support_degree hF hs, ← sum_eq_degree]
  exact le_totalDegree hs

lemma totalDegree_comp_le {n r : ℕ} (f : Poly n r) (δ : T n →₀ ℕ) :
    (weightedHomogeneousComponent wt δ f).totalDegree ≤ f.totalDegree := by
  classical
  apply totalDegree_le_of_support_subset
  rw [support_weightedHomogeneousComponent]
  exact Finset.filter_subset _ _

lemma row_ne_zero {n r : ℕ} {F : Poly n r} {δ : T n →₀ ℕ}
    (hF : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ)
    {s : Var n r →₀ ℕ} (hs : s ∈ F.support) (v : Var n r) (hv : s v ≠ 0) :
    δ (row v) ≠ 0 := by
  rw [mem_weightedHomogeneousSubmodule] at hF
  have := le_weight_apply s v
  rw [hF (mem_support_iff.mp hs)] at this
  omega

lemma eval_congr_rows {n r : ℕ} {F : Poly n r} {δ : T n →₀ ℕ}
    (hF : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ)
    (a b : Var n r → ℝ) (hab : ∀ v, δ (row v) ≠ 0 → a v = b v) :
    eval a F = eval b F := by
  rw [eval_eq', eval_eq']
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases h : s v = 0
  · simp [h]
  · rw [hab v (row_ne_zero hF hs v h)]

end SoSLinAlg.Dev.P42
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.P42

open SoSLinAlg.WeakRank MvPolynomial

/-- THE ISOLATED STEP (the paper's primality of the ideal `a` via [CW19, Thm 8.6(3)],
together with the localization argument): a polynomial vanishing on all real solutions of
`(X Yᵀ)_{ij} = 0` (`i ∈ I`, `j ∈ J`), with `|I| + |J| ≤ r`, lies in the ideal generated by
those entries. -/
theorem key_membership {n r : ℕ} (I J : Finset (Fin n)) (hIJ : I.card + J.card ≤ r)
    (F : Poly n r)
    (hF : ∀ X Y : Matrix (Fin n) (Fin r) ℝ, (∀ i ∈ I, ∀ j ∈ J, (X * Y.transpose) i j = 0) →
      eval (assignment X Y) F = 0) :
    ∃ g : (Fin n × Fin n) → Poly n r, F = ∑ ij ∈ I ×ˢ J, g ij * xy ij.1 ij.2 :=
  SoSLinAlg.WeakRank.membership_of_vanishing_on_orthogonal_rows I J hIJ F hF

/-- zero or low degree -/
def Good {n r : ℕ} (d : ℕ) (p : Poly n r) : Prop := p = 0 ∨ p.totalDegree + 2 ≤ d

lemma good_add {n r d : ℕ} {p q : Poly n r} (hp : Good d p) (hq : Good d q) : Good d (p + q) := by
  rcases hp with rfl | hp
  · simpa using hq
  rcases hq with rfl | hq
  · rw [add_zero]; exact Or.inr hp
  right
  have := totalDegree_add p q
  omega

lemma card_le_degree {n : ℕ} (δ : T n →₀ ℕ) :
    (Finset.univ.filter fun i : Fin n => δ (Sum.inl i) ≠ 0).card +
      (Finset.univ.filter fun i : Fin n => δ (Sum.inr i) ≠ 0).card ≤ δ.degree := by
  rw [← Finset.card_disjSum]
  calc _ ≤ δ.support.card := by
        apply Finset.card_le_card
        intro v hv
        rcases v with i | j <;> simpa using hv
    _ = ∑ v ∈ δ.support, 1 := by simp
    _ ≤ ∑ v ∈ δ.support, δ v :=
        Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    _ = δ.degree := rfl

lemma single_add_le {n : ℕ} (δ : T n →₀ ℕ) (i j : Fin n) (h1 : δ (Sum.inl i) ≠ 0)
    (h2 : δ (Sum.inr j) ≠ 0) :
    (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 : T n →₀ ℕ) ≤ δ := by
  intro v
  rcases v with k | k <;> simp [Finsupp.single_apply]
  · by_cases hk : i = k
    · subst hk; simpa using Nat.one_le_iff_ne_zero.mpr h1
    · simp [hk]
  · by_cases hk : j = k
    · subst hk; simpa using Nat.one_le_iff_ne_zero.mpr h2
    · simp [hk]

lemma extend_mem {n r d : ℕ} (I J : Finset (Fin n)) (hIJ : I.card + J.card ≤ d)
    (X Y : Matrix (Fin n) (Fin r) ℝ) (h : ∀ i ∈ I, ∀ j ∈ J, (X * Y.transpose) i j = 0) :
    (Matrix.diagonal (fun i => if i ∈ I then (1 : ℝ) else 0) * X,
      Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) * Y) ∈ Z n r d := by
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases hi : i ∈ I <;> by_cases hj : j ∈ J
    · have := h i hi j hj
      simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
      simpa [hi, hj] using this
    all_goals simp [hi, hj]
  · have hr : ∀ K : Finset (Fin n), ∀ M : Matrix (Fin n) (Fin r) ℝ,
        (Matrix.diagonal (fun i => if i ∈ K then (1 : ℝ) else 0) * M).rank ≤ K.card := by
      intro K M
      refine (Matrix.rank_mul_le_left _ _).trans ?_
      rw [Matrix.rank_diagonal]
      simp [Fintype.card_subtype]
    exact (add_le_add (hr I X) (hr J Y)).trans hIJ

lemma component_good {n r d : ℕ} (hdr : d ≤ r) {f : Poly n r} (hf : f.totalDegree ≤ d)
    (hvan : VanishesOnZ d f) (δ : T n →₀ ℕ) :
    ∃ h : (Fin n × Fin n) → Poly n r,
      weightedHomogeneousComponent wt δ f = ∑ ij, h ij * xy ij.1 ij.2 ∧
      ∀ ij, Good d (h ij) := by
  classical
  set F := weightedHomogeneousComponent wt δ f with hFdef
  have hFm : F ∈ weightedHomogeneousSubmodule ℝ (wt (n := n) (r := r)) δ :=
    weightedHomogeneousComponent_mem _ _ _
  by_cases h0 : F = 0
  · exact ⟨fun _ => 0, by simp [h0], fun _ => Or.inl rfl⟩
  have hdeg : δ.degree ≤ d :=
    (degree_le_totalDegree hFm h0).trans ((totalDegree_comp_le f δ).trans hf)
  set I := Finset.univ.filter fun i : Fin n => δ (Sum.inl i) ≠ 0 with hI
  set J := Finset.univ.filter fun i : Fin n => δ (Sum.inr i) ≠ 0 with hJ
  have hIJ : I.card + J.card ≤ d := (card_le_degree δ).trans hdeg
  have hvanF := comp_vanishes hvan δ
  obtain ⟨g, hg⟩ := key_membership I J (hIJ.trans hdr) F (by
    intro X Y hXY
    have h1 := hvanF _ _ (extend_mem (d := d) I J hIJ X Y hXY)
    rw [← h1]
    apply eval_congr_rows hFm
    intro v hv
    rcases v with ⟨i, k⟩ | ⟨j, k⟩
    · have : i ∈ I := by simpa [hI, row] using hv
      simp [assignment, Matrix.diagonal_mul, this]
    · have : j ∈ J := by simpa [hJ, row] using hv
      simp [assignment, Matrix.diagonal_mul, this])
  refine ⟨fun ij => if ij ∈ I ×ˢ J then
      weightedHomogeneousComponent wt (δ - (Finsupp.single (Sum.inl ij.1) 1 +
        Finsupp.single (Sum.inr ij.2) 1)) (g ij) else 0, ?_, ?_⟩
  · have hle : ∀ ij ∈ I ×ˢ J, (Finsupp.single (Sum.inl ij.1) 1 + Finsupp.single (Sum.inr ij.2) 1 :
        T n →₀ ℕ) ≤ δ := by
      intro ij hij
      have h1 : δ (Sum.inl ij.1) ≠ 0 := by simpa [hI] using (Finset.mem_product.mp hij).1
      have h2 : δ (Sum.inr ij.2) ≠ 0 := by simpa [hJ] using (Finset.mem_product.mp hij).2
      exact single_add_le δ _ _ h1 h2
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hF1 : F = weightedHomogeneousComponent wt δ F :=
      (weightedHomogeneousComponent_eq_self (by simpa [mem_weightedHomogeneousSubmodule] using hFm)).symm
    calc F = weightedHomogeneousComponent wt δ F := hF1
      _ = weightedHomogeneousComponent wt δ (∑ ij ∈ I ×ˢ J, g ij * xy ij.1 ij.2) := by rw [← hg]
      _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun ij hij => ?_
        rw [comp_mul _ _ _ _ (xy_mem _ _) (hle ij hij)]
  · intro ij
    by_cases hij : ij ∈ I ×ˢ J
    swap
    · simp only [hij, if_false]; exact Or.inl rfl
    simp only [hij, if_true]
    by_cases hz : weightedHomogeneousComponent wt (δ - (Finsupp.single (Sum.inl ij.1) 1 +
        Finsupp.single (Sum.inr ij.2) 1)) (g ij) = 0
    · exact Or.inl hz
    right
    have hle : (Finsupp.single (Sum.inl ij.1) 1 + Finsupp.single (Sum.inr ij.2) 1 :
        T n →₀ ℕ) ≤ δ := by
      have h1 : δ (Sum.inl ij.1) ≠ 0 := by simpa [hI] using (Finset.mem_product.mp hij).1
      have h2 : δ (Sum.inr ij.2) ≠ 0 := by simpa [hJ] using (Finset.mem_product.mp hij).2
      exact single_add_le δ _ _ h1 h2
    have h3 := totalDegree_le_of_mem (weightedHomogeneousComponent_mem (wt (n := n) (r := r))
      (g ij) (δ - (Finsupp.single (Sum.inl ij.1) 1 + Finsupp.single (Sum.inr ij.2) 1)))
    have h4 := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single] at h4
    omega

theorem main {n r d : ℕ} (hdr : d ≤ r) (f : Poly n r) (hf : f.totalDegree ≤ d)
    (hvan : VanishesOnZ d f) :
    ∃ h : (Fin n × Fin n) → Poly n r,
      f = ∑ ij, h ij * xy ij.1 ij.2 ∧
      ∀ ij, h ij = 0 ∨ (h ij).totalDegree + 2 ≤ d := by
  classical
  choose h hh hgood using component_good hdr hf hvan
  obtain ⟨S, hS⟩ : ∃ S : Finset (T n →₀ ℕ),
      f = ∑ δ ∈ S, weightedHomogeneousComponent wt δ f := by
    have h1 := sum_weightedHomogeneousComponent (σ := Var n r) (R := ℝ) (M := T n →₀ ℕ)
      (wt (n := n) (r := r)) (φ := f)
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at h1
    exact ⟨_, h1.symm⟩
  refine ⟨fun ij => ∑ δ ∈ S, h δ ij, ?_, fun ij => ?_⟩
  · conv_lhs => rw [hS]
    simp only [hh, Finset.sum_mul]
    rw [Finset.sum_comm]
  · exact Finset.sum_induction _ (Good d) (fun _ _ => good_add) (Or.inl rfl)
      (fun δ _ => hgood δ ij)

end SoSLinAlg.Dev.P42
end
end

section
namespace SoSLinAlg.WeakRank

theorem chk_proposition_4_2 {n r d : ℕ} (hr : 0 < r) (hrn : r < n) (hdr : d ≤ r)
    (f : Poly n r) (hf : f.totalDegree ≤ d) (hvan : VanishesOnZ d f) :
    ∃ h : (Fin n × Fin n) → Poly n r,
      f = ∑ ij, h ij * xy ij.1 ij.2 ∧
      ∀ ij, h ij = 0 ∨ (h ij).totalDegree + 2 ≤ d :=
  Dev.P42.main hdr f hf hvan

end SoSLinAlg.WeakRank

end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_proposition_4_2 := @SoSLinAlg.WeakRank.chk_proposition_4_2
