-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.quantumIdentities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:01:23.736457+00:00
-- url     : https://prove2.me/submissions/3957893a-885b-4b67-a376-d051586d896e

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

set_option linter.unusedSectionVars false

section S193I_ent
open Matrix Polynomial

lemma S193I_inst {ι : Type*} [Fintype ι] (i1 i2 : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i1 A = @QAlgorithms.vnEntropy ι _ i2 A := by
  congr

lemma S193I_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S193I_vn_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) :
    QAlgorithms.vnEntropy Y = (∑ i, Real.negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold QAlgorithms.vnEntropy
  rw [S193I_cfc_trace hY, Complex.re_sum, Finset.sum_div]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.negMulLog, Real.logb]; ring_nf

lemma S193I_vn_roots {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A =
      ((A.charpoly.roots).map (fun z : ℂ => Real.negMulLog z.re)).sum / Real.log 2 := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, S193I_vn_eig hA]
  rfl

lemma S193I_udiag {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (P : Matrix n n ℂ) (hP : Pᴴ * P = 1) (f : n → ℝ)
    (h : A = P * diagonal (fun i => (f i : ℂ)) * Pᴴ) :
    QAlgorithms.vnEntropy A = (∑ i, Real.negMulLog (f i)) / Real.log 2 := by
  rw [S193I_vn_roots _ hA]
  have hc : A.charpoly = ∏ i, (X - C (f i : ℂ)) := by
    rw [h, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hP, Matrix.mul_one,
      charpoly_diagonal]
  rw [hc, roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
  rfl

lemma S193I_spec {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    ∃ P : Matrix n n ℂ, Pᴴ * P = 1 ∧
      A = P * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Pᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2)
  · conv_lhs => rw [hA.spectral_theorem]
    rfl

lemma S193I_kron0 {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) =
      QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  obtain ⟨P, hP, hAP⟩ := S193I_spec A hA
  obtain ⟨Q, hQ, hBQ⟩ := S193I_spec B hB
  have hK : (A ⊗ₖ B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, hA.eq, hB.eq]
  have htA' : (1 : ℝ) = ∑ i, hA.eigenvalues i := by
    have := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    rw [htA] at this; simpa using this
  have htB' : (1 : ℝ) = ∑ i, hB.eigenvalues i := by
    have := congrArg Complex.re hB.trace_eq_sum_eigenvalues
    rw [htB] at this; simpa using this
  rw [S193I_udiag _ hK (P ⊗ₖ Q) ?_ (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) ?_,
    S193I_udiag _ hA P hP _ hAP, S193I_udiag _ hB Q hQ _ hBQ, ← add_div]
  · congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← htA', ← htB']; ring
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hP, hQ, one_kronecker_one]
  · have hD : diagonal (fun ij : p × q => ((hA.eigenvalues ij.1 * hB.eigenvalues ij.2 : ℝ) : ℂ)) =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext ij
      push_cast
      rfl
    rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hAP, ← hBQ]

lemma S193I_kron {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] {i3 : DecidableEq (p × q)} (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) =
      QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  rw [S193I_inst i3 instDecidableEqProd]
  exact S193I_kron0 A B hA hB htA htB


lemma S193I_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

lemma S193I_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

def S193I_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S193I_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S193I_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S193I_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S193I_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S193I_vn_poly A hA (S193I_interp s)
      (fun x hx => S193I_interp_eval s (by simpa [s] using hx)),
    S193I_vn_poly _ (hA.submatrix e) (S193I_interp s)
      (fun x hx => S193I_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S193I_interp s)) i i)

lemma S193I_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]

end S193I_ent

section S193I_marg
open Matrix
attribute [local instance] Classical.propDecidable
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)


lemma S193I_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma S193I_marg_comp {Y K F K2 F2 : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (k2 : K → K2) (f2 : K → F2) :
    redistributionMarginal (redistributionMarginal ρ k f) k2 f2 =
      redistributionMarginal ρ (k2 ∘ k) (fun y => (f2 (k y), f y)) := by
  ext a b
  simp only [redistributionMarginal, S193I_ite_sum, Function.comp]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [Finset.sum_eq_single (k x)]
  · rw [Finset.sum_eq_single (k y)]
    · by_cases h1 : k2 (k x) = a <;> by_cases h2 : k2 (k y) = b <;>
        by_cases h3 : f2 (k x) = f2 (k y) <;> by_cases h4 : f x = f y <;> simp [h1, h2, h3, h4]
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu
    apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hu]
  · simp

lemma S193I_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    redistributionMarginal ρ k f = redistributionMarginal ρ k f' := by
  ext a b
  simp only [redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma S193I_marg_herm {Y K F : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (hρ : ρ.IsHermitian)
    (k : Y → K) (f : Y → F) : (redistributionMarginal ρ k f).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, redistributionMarginal, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : k x = a ∧ k y = b ∧ f x = f y
  · rw [if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, if_pos h]
    exact congrFun (congrFun hρ x) y
  · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩), if_neg h, star_zero]

lemma S193I_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
    {inst : DecidableEq K} [DecidableEq K'] (ρ : Matrix Y Y ℂ) (hρ : ρ.IsHermitian)
    (k : Y → K) (k' : Y → K') (f : Y → F) (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k') :
    QAlgorithms.vnEntropy (redistributionMarginal ρ k f) =
      QAlgorithms.vnEntropy (redistributionMarginal ρ k' f) := by
  set g : K → K' := fun a => k' (Function.surjInv hs a) with hg
  have hgk : ∀ x a, k' x = g a ↔ k x = a := by
    intro x a
    have := hk x (Function.surjInv hs a)
    rw [Function.surjInv_eq hs a] at this
    exact this.symm
  have hb : Function.Bijective g := by
    constructor
    · intro a b hab
      have h1 := (hgk (Function.surjInv hs a) b).1 hab
      rwa [Function.surjInv_eq hs a] at h1
    · intro c
      obtain ⟨y, rfl⟩ := hs' c
      exact ⟨k y, ((hgk y (k y)).2 rfl).symm⟩
  have hsub : (redistributionMarginal ρ k' f).submatrix (Equiv.ofBijective g hb)
      (Equiv.ofBijective g hb) = redistributionMarginal ρ k f := by
    ext a b
    simp only [Matrix.submatrix_apply, Equiv.ofBijective_apply, redistributionMarginal]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h : k x = a ∧ k y = b ∧ f x = f y
    · rw [if_pos (by rwa [hgk, hgk]), if_pos h]
    · rw [if_neg (by rwa [hgk, hgk]), if_neg h]
  rw [← hsub, S193I_vn_submatrix _ (S193I_marg_herm ρ hρ k' f)]

lemma S193I_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (hinj : Function.Injective (fun y => (k y, f y))) :
    (redistributionMarginal ρ k f).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm, Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single (k x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro y _ hy
    apply Finset.sum_eq_zero; intro a _
    rw [if_neg]; rintro ⟨h1, h2, h3⟩
    exact hy (hinj (Prod.ext (h2.trans h1.symm) h3.symm))
  · simp

lemma S193I_sum_equiv {X X1 X2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (g : X → X1) (h : X → X2) (hb : Function.Bijective (fun x => (g x, h x)))
    (G : X1 → X2 → ℂ) : ∑ x, G (g x) (h x) = ∑ z1, ∑ z2, G z1 z2 := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.ofBijective _ hb) _ _ (fun x => rfl)

lemma S193I_marg_prod {X X1 X2 K1 K2 F1 F2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (ρ : Matrix X X ℂ) (P : Matrix X1 X1 ℂ) (Q : Matrix X2 X2 ℂ) (g : X → X1) (h : X → X2)
    (hb : Function.Bijective (fun x => (g x, h x)))
    (hρ : ∀ x y, ρ x y = P (g x) (g y) * Q (h x) (h y))
    (k1 : X1 → K1) (k2 : X2 → K2) (f1 : X1 → F1) (f2 : X2 → F2) :
    redistributionMarginal ρ (fun x => (k1 (g x), k2 (h x))) (fun x => (f1 (g x), f2 (h x))) =
      redistributionMarginal P k1 f1 ⊗ₖ redistributionMarginal Q k2 f2 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  rw [kronecker_apply]
  simp only [redistributionMarginal]
  set T : X1 → X2 → X1 → X2 → ℂ := fun z1 z2 w1 w2 =>
    (if k1 z1 = a1 ∧ k1 w1 = b1 ∧ f1 z1 = f1 w1 then P z1 w1 else 0) *
    (if k2 z2 = a2 ∧ k2 w2 = b2 ∧ f2 z2 = f2 w2 then Q z2 w2 else 0) with hT
  trans ∑ x, ∑ y, T (g x) (h x) (g y) (h y)
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT, Prod.mk.injEq]
    rw [hρ x y]
    by_cases c1 : k1 (g x) = a1 ∧ k1 (g y) = b1 ∧ f1 (g x) = f1 (g y) <;>
    by_cases c2 : k2 (h x) = a2 ∧ k2 (h y) = b2 ∧ f2 (h x) = f2 (h y)
    · rw [if_pos c1, if_pos c2, if_pos ⟨⟨c1.1, c2.1⟩, ⟨c1.2.1, c2.2.1⟩, ⟨c1.2.2, c2.2.2⟩⟩]
    · rw [if_neg c2, if_neg (fun h' => c2 ⟨h'.1.2, h'.2.1.2, h'.2.2.2⟩), mul_zero]
    · rw [if_neg c1, if_neg (fun h' => c1 ⟨h'.1.1, h'.2.1.1, h'.2.2.1⟩), zero_mul]
    · rw [if_neg c1, if_neg (fun h' => c1 ⟨h'.1.1, h'.2.1.1, h'.2.2.1⟩), zero_mul]
  rw [Finset.sum_congr rfl (fun x _ => S193I_sum_equiv g h hb (fun w1 w2 => T (g x) (h x) w1 w2)),
    S193I_sum_equiv g h hb (fun z1 z2 => ∑ w1, ∑ w2, T z1 z2 w1 w2)]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  rw [Finset.sum_mul_sum]

lemma S193I_trace_prod {X X1 X2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (ρ : Matrix X X ℂ) (P : Matrix X1 X1 ℂ) (Q : Matrix X2 X2 ℂ) (g : X → X1) (h : X → X2)
    (hb : Function.Bijective (fun x => (g x, h x)))
    (hρ : ∀ x y, ρ x y = P (g x) (g y) * Q (h x) (h y)) :
    ρ.trace = P.trace * Q.trace := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.sum_congr rfl (fun x _ => hρ x x), S193I_sum_equiv g h hb (fun z1 z2 => P z1 z1 * Q z2 z2), Finset.sum_mul_sum]

end S193I_marg

section S193I_reg
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

def S193I_rl (s : Finset (Fin n)) (x : RegisterBasis D) : SubBasis D s := fun i => x i.val

def S193I_H (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  entropyAt (trivialExtension ρ) s

lemma S193I_req (s : Finset (Fin n)) (x y : RegisterBasis D) :
    S193I_rl s x = S193I_rl s y ↔ ∀ i ∈ s, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2

lemma S193I_and_iff (s s1 s2 : Finset (Fin n)) (hs : ∀ i, i ∈ s ↔ i ∈ s1 ∨ i ∈ s2)
    (p : Fin n → Prop) : ((∀ i ∈ s1, p i) ∧ (∀ i ∈ s2, p i)) ↔ ∀ i ∈ s, p i := by
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases (hs i).1 hi with h | h
    exacts [h1 i h, h2 i h]
  · intro h
    exact ⟨fun i hi => h i ((hs i).2 (Or.inl hi)), fun i hi => h i ((hs i).2 (Or.inr hi))⟩

def S193I_res {s t : Finset (Fin n)} (h : s ⊆ t) (u : SubBasis D t) : SubBasis D s :=
  fun i => u ⟨i.1, h i.2⟩

lemma S193I_res_restrict {s t : Finset (Fin n)} (h : s ⊆ t) (x : RegisterBasis D) :
    S193I_res h (S193I_rl t x) = S193I_rl s x := rfl

def S193I_ext (T : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D) :
    RegisterBasis D := fun k => if h : k ∈ T then a ⟨k, h⟩ else z k

lemma S193I_restrict_ext (T : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D) :
    S193I_rl T (S193I_ext T a z) = a := by
  funext i; simp [S193I_rl, S193I_ext, i.2]

lemma S193I_restrict_ext_disj (T T' : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D)
    (h : ∀ k ∈ T', k ∉ T) : S193I_rl T' (S193I_ext T a z) = S193I_rl T' z := by
  funext k; simp [S193I_rl, S193I_ext, h k.1 k.2]

lemma S193I_C1 (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    registerMarginal (trivialExtension ρ) T =
      redistributionMarginal ρ (fun x => (S193I_rl T x, ())) (fun x => S193I_rl Tᶜ x) := by
  ext a b
  simp only [registerMarginal, trivialExtension, redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have hiff : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i)) ↔ ((S193I_rl T x, ()) = a ∧ (S193I_rl T y, ()) = b ∧
      S193I_rl Tᶜ x = S193I_rl Tᶜ y) := by
    rw [S193I_req]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Prod.ext (funext fun i => (h1 i.1 i.2).1) rfl,
        Prod.ext (funext fun i => (h1 i.1 i.2).2) rfl, fun i hi => h2 i (by simpa using hi)⟩
    · rintro ⟨h1, h2, h3⟩
      subst h1; subst h2
      exact ⟨fun i hi => ⟨rfl, rfl⟩, fun i hi => h3 i (by simpa using hi)⟩
  by_cases h : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i))
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

lemma S193I_S_eq (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    S193I_H ρ T = QAlgorithms.vnEntropy
      (redistributionMarginal ρ (fun x => (S193I_rl T x, ())) (fun x => S193I_rl Tᶜ x)) := by
  unfold S193I_H entropyAt
  rw [S193I_C1]
  exact S193I_inst _ _ _

lemma S193I_bij (A B : Finset (Fin n)) (hAB : ∀ i, i ∈ B ↔ i ∉ A) :
    Function.Bijective (fun x : RegisterBasis D => (S193I_rl A x, S193I_rl B x)) := by
  constructor
  · intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    funext i
    by_cases hi : i ∈ A
    · exact congrFun hxy.1 ⟨i, hi⟩
    · exact congrFun hxy.2 ⟨i, (hAB i).2 hi⟩
  · rintro ⟨u, v⟩
    refine ⟨fun i => if h : i ∈ A then u ⟨i, h⟩ else v ⟨i, (hAB i).2 h⟩, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · funext i; simp [S193I_rl, i.2]
    · funext i
      have : (i : Fin n) ∉ A := (hAB i).1 i.2
      simp [S193I_rl, this]

lemma S193I_res_inj {U A : Finset (Fin n)} (hU : U ⊆ A) :
    Function.Injective (fun u : SubBasis D A =>
      (S193I_res hU u, S193I_res (Finset.sdiff_subset (s := A) (t := U)) u)) := by
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  funext i
  by_cases hi : i.1 ∈ U
  · exact congrFun huv.1 ⟨i.1, hi⟩
  · exact congrFun huv.2 ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩


lemma S193I_side (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (A B : Finset (Fin n))
    (hAB : ∀ i, i ∈ B ↔ i ∉ A) (P : Matrix (SubBasis D A) (SubBasis D A) ℂ)
    (Q : Matrix (SubBasis D B) (SubBasis D B) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (htP : P.trace = 1) (htQ : Q.trace = 1)
    (hfac : ∀ x y, ρ x y = P (S193I_rl A x) (S193I_rl A y) *
      Q (S193I_rl B x) (S193I_rl B y))
    (U : Finset (Fin n)) (hU : U ⊆ A) :
    S193I_H ρ U = QAlgorithms.vnEntropy (redistributionMarginal P (S193I_res hU)
      (S193I_res (Finset.sdiff_subset (s := A) (t := U)))) := by
  rw [S193I_S_eq, S193I_marg_forget ρ _ _
    (fun x => (S193I_rl (A \ U) x, S193I_rl B x)) ?hf]
  · rw [show redistributionMarginal ρ (fun x => (S193I_rl U x, ()))
        (fun x => (S193I_rl (A \ U) x, S193I_rl B x)) =
        redistributionMarginal ρ (fun x => (S193I_res hU (S193I_rl A x),
          (fun _ : SubBasis D B => ()) (S193I_rl B x)))
        (fun x => (S193I_res (Finset.sdiff_subset (s := A) (t := U)) (S193I_rl A x),
          id (S193I_rl B x))) from rfl]
    rw [S193I_marg_prod ρ P Q _ _ (S193I_bij A B hAB) hfac (S193I_res hU) (fun _ => ())
      (S193I_res (Finset.sdiff_subset (s := A) (t := U))) id]
    rw [S193I_kron _ _ (S193I_marg_herm P hP _ _) (S193I_marg_herm Q hQ _ _)
      (by rw [S193I_marg_trace P _ _ (S193I_res_inj hU), htP])
      (by rw [S193I_marg_trace Q _ _ (fun a b h => by simpa using h), htQ]),
      S193I_vn_unit _ (by rw [S193I_marg_trace Q _ _ (fun a b h => by simpa using h), htQ]),
      add_zero]
  · intro x y
    simp only [Prod.mk.injEq, S193I_req]
    rw [S193I_and_iff Uᶜ (A \ U) B]
    intro i
    have := @hU i
    have := hAB i
    simp only [Finset.mem_compl, Finset.mem_sdiff]
    tauto

lemma S193I_split [∀ i, Nonempty (D i)] (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hρ : ρ.IsHermitian) (A B : Finset (Fin n))
    (hAB : ∀ i, i ∈ B ↔ i ∉ A) (P : Matrix (SubBasis D A) (SubBasis D A) ℂ)
    (Q : Matrix (SubBasis D B) (SubBasis D B) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (htP : P.trace = 1) (htQ : Q.trace = 1)
    (hfac : ∀ x y, ρ x y = P (S193I_rl A x) (S193I_rl A y) *
      Q (S193I_rl B x) (S193I_rl B y))
    (T : Finset (Fin n)) :
    S193I_H ρ T = S193I_H ρ (T ∩ A) + S193I_H ρ (T ∩ B) := by
  have hBA : ∀ i, i ∈ A ↔ i ∉ B := fun i => by rw [hAB i, not_not]
  have hUA : T ∩ A ⊆ A := Finset.inter_subset_right
  have hVB : T ∩ B ⊆ B := Finset.inter_subset_right
  have z : RegisterBasis D := fun i => Classical.arbitrary (D i)
  rw [S193I_side ρ A B hAB P Q hP hQ htP htQ hfac (T ∩ A) hUA,
    S193I_side ρ B A hBA Q P hQ hP htQ htP (fun x y => by rw [hfac, mul_comm]) (T ∩ B) hVB]
  rw [S193I_S_eq, S193I_vn_keep ρ hρ _
    (fun x => (S193I_res hUA (S193I_rl A x), S193I_res hVB (S193I_rl B x))) _ ?hk
    ?hs ?hs']
  case hk =>
    intro x y
    simp only [S193I_res_restrict, Prod.mk.injEq, and_true, S193I_req]
    rw [S193I_and_iff T (T ∩ A) (T ∩ B)]
    intro i
    have := hAB i
    simp only [Finset.mem_inter]
    tauto
  case hs =>
    rintro ⟨a, u⟩
    exact ⟨S193I_ext T a z, Prod.ext (S193I_restrict_ext T a z) rfl⟩
  case hs' =>
    rintro ⟨a1, a2⟩
    refine ⟨S193I_ext (T ∩ A) a1 (S193I_ext (T ∩ B) a2 z), ?_⟩
    simp only [S193I_res_restrict, Prod.mk.injEq]
    refine ⟨S193I_restrict_ext _ _ _, ?_⟩
    rw [S193I_restrict_ext_disj, S193I_restrict_ext]
    intro k hk hk'
    exact (hAB k).1 (Finset.mem_inter.1 hk).2 (Finset.mem_inter.1 hk').2
  rw [S193I_marg_forget ρ _ _ (fun x =>
    (S193I_res (Finset.sdiff_subset (s := A) (t := T ∩ A)) (S193I_rl A x),
     S193I_res (Finset.sdiff_subset (s := B) (t := T ∩ B)) (S193I_rl B x))) ?hf]
  · rw [S193I_marg_prod ρ P Q _ _ (S193I_bij A B hAB) hfac (S193I_res hUA)
      (S193I_res hVB) (S193I_res (Finset.sdiff_subset (s := A) (t := T ∩ A)))
      (S193I_res (Finset.sdiff_subset (s := B) (t := T ∩ B)))]
    rw [S193I_kron _ _ (S193I_marg_herm P hP _ _) (S193I_marg_herm Q hQ _ _)
      (by rw [S193I_marg_trace P _ _ (S193I_res_inj hUA), htP])
      (by rw [S193I_marg_trace Q _ _ (S193I_res_inj hVB), htQ])]
  · intro x y
    simp only [S193I_res_restrict, Prod.mk.injEq, S193I_req]
    rw [S193I_and_iff Tᶜ (A \ (T ∩ A)) (B \ (T ∩ B))]
    intro i
    have := hAB i
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_inter]
    tauto


end S193I_reg

section S193I_gen
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq

def S193I_S {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  @QAlgorithms.vnEntropy ι _ (Classical.decEq ι) A

lemma S193I_toS {ι : Type*} [Fintype ι] (i : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i A = S193I_S A := by
  unfold S193I_S; congr

lemma S193I_marg_psd {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (hρ : ρ.PosSemidef) (k : X → K) (f : X → F) : (redistributionMarginal ρ k f).PosSemidef := by
  set W : F → Matrix X K ℂ := fun z => Matrix.of fun x a => if f x = z ∧ k x = a then 1 else 0
  have : redistributionMarginal ρ k f = ∑ z, (W z)ᴴ * ρ * W z := by
    ext a b
    simp only [redistributionMarginal, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, W, Matrix.of_apply, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single (f x)]
    · by_cases h1 : k x = a <;> by_cases h2 : k y = b <;> by_cases h3 : f x = f y <;>
        simp [h1, h2, h3, eq_comm (a := f y)]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  rw [this]
  exact Matrix.posSemidef_sum _ (fun z _ => hρ.conjTranspose_mul_mul_same _)

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

lemma S193I_Heq (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.IsHermitian)
    (T : Finset (Fin n)) {K F : Type*} [Fintype K] (k : RegisterBasis D → K)
    (f : RegisterBasis D → F) (hk : ∀ x y, k x = k y ↔ ∀ i ∈ T, x i = y i)
    (hks : Function.Surjective k) (hf : ∀ x y, f x = f y ↔ ∀ i ∈ Tᶜ, x i = y i) :
    S193I_S (redistributionMarginal ρ k f) = S193I_H ρ T := by
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  rw [S193I_S_eq, S193I_toS,
    S193I_marg_forget ρ k f (fun x => S193I_rl Tᶜ x) (fun x y => by rw [hf, S193I_req])]
  have hv := S193I_vn_keep (inst := Classical.decEq _) ρ hρ k (fun x => (S193I_rl T x, ())) (fun x => S193I_rl Tᶜ x)
    (fun x y => by rw [hk, Prod.mk.injEq, S193I_req]; simp) hks
    (fun ⟨u, _⟩ => ⟨S193I_ext T u z, Prod.ext (S193I_restrict_ext _ _ _) rfl⟩)
  rw [S193I_toS, S193I_toS] at hv
  exact hv

lemma S193I_kiff2 (s1 s2 s : Finset (Fin n)) (hs : ∀ i, i ∈ s ↔ i ∈ s1 ∨ i ∈ s2)
    (x y : RegisterBasis D) :
    (S193I_rl s1 x, S193I_rl s2 x) = (S193I_rl s1 y, S193I_rl s2 y) ↔ ∀ i ∈ s, x i = y i := by
  rw [Prod.mk.injEq, S193I_req, S193I_req, S193I_and_iff s s1 s2 hs]

lemma S193I_surj2 (s1 s2 : Finset (Fin n)) (h : Disjoint s1 s2) :
    Function.Surjective (fun x : RegisterBasis D => (S193I_rl s1 x, S193I_rl s2 x)) := by
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  rintro ⟨u, v⟩
  refine ⟨S193I_ext s1 u (S193I_ext s2 v z), ?_⟩
  simp only [Prod.mk.injEq]
  refine ⟨S193I_restrict_ext _ _ _, ?_⟩
  rw [S193I_restrict_ext_disj, S193I_restrict_ext]
  intro k hk hk'
  exact Finset.disjoint_left.1 h hk' hk

lemma S193I_surj1 (s : Finset (Fin n)) :
    Function.Surjective (fun x : RegisterBasis D => S193I_rl s x) := by
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  intro u
  exact ⟨S193I_ext s u z, S193I_restrict_ext _ _ _⟩

lemma S193I_cmi (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (a b e : Finset (Fin n)) (hab : Disjoint a b)
    (hae : Disjoint a e) (hbe : Disjoint b e) :
    0 ≤ S193I_H ρ (a ∪ e) + S193I_H ρ (b ∪ e) - S193I_H ρ e - S193I_H ρ (a ∪ b ∪ e) := by
  have hH := hρ.1.isHermitian
  have d1 : ∀ i, i ∈ a → i ∉ b := fun i h => Finset.disjoint_left.1 hab h
  have d2 : ∀ i, i ∈ a → i ∉ e := fun i h => Finset.disjoint_left.1 hae h
  have d3 : ∀ i, i ∈ b → i ∉ e := fun i h => Finset.disjoint_left.1 hbe h
  set r : Finset (Fin n) := (a ∪ b ∪ e)ᶜ with hr
  set k : RegisterBasis D → SubBasis D a × (SubBasis D b × SubBasis D e) :=
    fun x => (S193I_rl a x, (S193I_rl b x, S193I_rl e x)) with hk
  set f : RegisterBasis D → SubBasis D r := fun x => S193I_rl r x with hf
  have hinj : Function.Injective (fun x => (k x, f x)) := by
    intro x y h
    simp only [hk, hf, Prod.mk.injEq, S193I_req] at h
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    funext i
    by_cases ia : i ∈ a
    · exact h1 i ia
    by_cases ib : i ∈ b
    · exact h2 i ib
    by_cases ie : i ∈ e
    · exact h3 i ie
    exact h4 i (by simp [hr, ia, ib, ie])
  have hσ : QAlgorithms.IsDensityMatrix (redistributionMarginal ρ k f) :=
    ⟨S193I_marg_psd ρ hρ.1 k f, by rw [S193I_marg_trace _ _ _ hinj, hρ.2]⟩
  have hssa := QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity _ hσ
  unfold subsystemEntropy at hssa
  rw [S193I_marg_comp, S193I_marg_comp, S193I_marg_comp] at hssa
  simp only [S193I_toS, Function.comp_def, hk, hf] at hssa
  have e1 := S193I_Heq ρ hH (a ∪ e) (fun x => (S193I_rl a x, S193I_rl e x))
    (fun x => (S193I_rl b x, S193I_rl r x))
    (S193I_kiff2 a e _ (fun i => by simp)) (S193I_surj2 a e hae)
    (S193I_kiff2 b r _ (fun i => by simp only [hr, Finset.mem_compl, Finset.mem_union]; tauto))
  have e2 := S193I_Heq ρ hH (b ∪ e) (fun x => (S193I_rl b x, S193I_rl e x))
    (fun x => (S193I_rl a x, S193I_rl r x))
    (S193I_kiff2 b e _ (fun i => by simp)) (S193I_surj2 b e hbe)
    (S193I_kiff2 a r _ (fun i => by
      simp only [hr, Finset.mem_compl, Finset.mem_union]
      have := d1 i; have := d2 i; tauto))
  have e3 := S193I_Heq ρ hH e (fun x => S193I_rl e x)
    (fun x => ((S193I_rl a x, S193I_rl b x), S193I_rl r x))
    (fun x y => S193I_req e x y) (S193I_surj1 e)
    (fun x y => by
      rw [Prod.mk.injEq, S193I_kiff2 a b (a ∪ b) (fun i => by simp), S193I_req,
        S193I_and_iff eᶜ (a ∪ b) r (fun i => by
          simp only [hr, Finset.mem_compl, Finset.mem_union]
          have := d2 i; have := d3 i; tauto)])
  have e4 := S193I_Heq ρ hH (a ∪ b ∪ e) k f
    (fun x y => by
      simp only [hk]
      rw [Prod.mk.injEq, S193I_kiff2 b e (b ∪ e) (fun i => by simp), S193I_req,
        S193I_and_iff (a ∪ b ∪ e) a (b ∪ e) (fun i => by simp only [Finset.mem_union]; tauto)])
    (by
      obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
      rintro ⟨u, v, w⟩
      refine ⟨S193I_ext a u (S193I_ext b v (S193I_ext e w z)), ?_⟩
      simp only [hk, Prod.mk.injEq]
      refine ⟨S193I_restrict_ext _ _ _, ?_, ?_⟩
      · rw [S193I_restrict_ext_disj _ _ _ _ (fun i hi h => d1 i h hi), S193I_restrict_ext]
      · rw [S193I_restrict_ext_disj _ _ _ _ (fun i hi h => d2 i h hi),
          S193I_restrict_ext_disj _ _ _ _ (fun i hi h => d3 i h hi), S193I_restrict_ext])
    (fun x y => by simp only [hf]; exact S193I_req _ x y)
  rw [e1, e2, e3, e4] at hssa
  linarith

end S193I_gen

section S193I_prod
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt partyProduct)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
attribute [local instance] Classical.propDecidable Classical.decEq

lemma S193I_vn_uniq {ι : Type*} [Fintype ι] [Subsingleton ι] {inst : DecidableEq ι}
    (A : Matrix ι ι ℂ) (h : A.trace = 1) : QAlgorithms.vnEntropy A = 0 := by
  have hA : A = 1 := by
    ext a b
    rw [Subsingleton.elim b a, Matrix.one_apply_eq]
    rw [← h, Matrix.trace]
    have : (Finset.univ : Finset ι) = {a} := by
      ext c; simp [Subsingleton.elim c a]
    rw [this, Finset.sum_singleton]; rfl
  rw [hA]; unfold QAlgorithms.vnEntropy; rw [cfc_apply_one]; simp

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

lemma S193I_H_empty (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (htr : ρ.trace = 1) :
    S193I_H ρ ∅ = 0 := by
  rw [S193I_S_eq]
  apply S193I_vn_uniq
  rw [S193I_marg_trace, htr]
  intro x y h
  simp only [Prod.mk.injEq, and_true] at h
  funext i
  exact congrFun h.2 ⟨i, by simp⟩

lemma S193I_prodH (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hH : ρ.IsHermitian)
    (htr : ρ.trace = 1)
    (η : ∀ i, Matrix (D i) (D i) ℂ) (hη : ∀ i, QAlgorithms.IsDensityMatrix (η i))
    (hρ : ∀ x y, ρ x y = ∏ i, η i (x i) (y i)) (T : Finset (Fin n)) :
    S193I_H ρ T = ∑ i ∈ T, S193I_H ρ {i} := by
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  induction T using Finset.induction_on with
  | empty => rw [S193I_H_empty ρ htr, Finset.sum_empty]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, ← ih]
    have hm : i ∈ ({i} : Finset (Fin n)) := Finset.mem_singleton_self i
    set P : Matrix (SubBasis D {i}) (SubBasis D {i}) ℂ :=
      fun u v => η i (u ⟨i, hm⟩) (v ⟨i, hm⟩) with hP
    set Q : Matrix (SubBasis D ({i} : Finset (Fin n))ᶜ) (SubBasis D ({i} : Finset (Fin n))ᶜ) ℂ :=
      fun u v => ∏ j, η j.1 (u j) (v j) with hQ
    have hPH : P.IsHermitian := by
      ext u v; exact congrFun (congrFun (hη i).1.1 _) _
    have hQH : Q.IsHermitian := by
      ext u v
      show star (∏ j, η j.1 (v j) (u j)) = ∏ j, η j.1 (u j) (v j)
      rw [star_prod]
      exact Finset.prod_congr rfl (fun j _ => congrFun (congrFun (hη j.1).1.1 (u j)) (v j))
    have hPt : P.trace = 1 := by
      rw [← (hη i).2]
      simp only [Matrix.trace, Matrix.diag, hP]
      refine Fintype.sum_bijective (fun u : SubBasis D {i} => u ⟨i, hm⟩) ⟨?_, ?_⟩ _ _
        (fun _ => rfl)
      · intro u v h
        funext ⟨j, hj⟩
        have := Finset.mem_singleton.1 hj
        subst this
        exact h
      · intro a
        exact ⟨S193I_rl {i} (Function.update z i a), by simp [S193I_rl]⟩
    have hQt : Q.trace = 1 := by
      have hps := Finset.prod_univ_sum
        (κ := fun j : {j // j ∈ ({i} : Finset (Fin n))ᶜ} => D j.1) (R := ℂ)
        (fun _ => Finset.univ) (fun j a => η j.1 a a)
      rw [Fintype.piFinset_univ] at hps
      simp only [Matrix.trace, Matrix.diag, hQ]
      rw [← hps]
      exact Finset.prod_eq_one (fun j _ => (hη j.1).2)
    have hfac : ∀ x y, ρ x y = P (S193I_rl {i} x) (S193I_rl {i} y) *
        Q (S193I_rl ({i} : Finset (Fin n))ᶜ x) (S193I_rl ({i} : Finset (Fin n))ᶜ y) := by
      intro x y
      rw [hρ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [hP, hQ, S193I_rl]
      congr 1
      exact Finset.prod_subtype _ (fun j => by simp) (fun j => η j (x j) (y j))
    rw [S193I_split ρ hH {i} ({i} : Finset (Fin n))ᶜ (fun j => Finset.mem_compl) P Q hPH hQH hPt hQt
      hfac (insert i T)]
    congr 2
    · ext j; simp
    · ext j; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_compl,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h; exact ⟨Or.inr h, fun e => hi (e ▸ h)⟩

lemma S193I_inj_rl (T : Finset (Fin n)) :
    Function.Injective (fun u : RegisterBasis D => ((S193I_rl T u, ()), S193I_rl Tᶜ u)) := by
  intro x y h
  simp only [Prod.mk.injEq, and_true] at h
  funext i
  by_cases hi : i ∈ T
  · exact congrFun h.1 ⟨i, hi⟩
  · exact congrFun h.2 ⟨i, by simpa using hi⟩

lemma S193I_H_S (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    S193I_H ρ T = S193I_S (redistributionMarginal ρ (fun x => (S193I_rl T x, ()))
      (fun x => S193I_rl Tᶜ x)) := by
  rw [S193I_S_eq, S193I_toS]

lemma S193I_ppH {F : Fin n → Type} [∀ i, Fintype (F i)] [∀ i, Nonempty (F i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (T : Finset (Fin n)) :
    S193I_H (partyProduct ρ σ) T = S193I_H ρ T + S193I_H σ T := by
  obtain ⟨z1⟩ : Nonempty (RegisterBasis D) := inferInstance
  obtain ⟨z2⟩ : Nonempty (RegisterBasis F) := inferInstance
  set R := partyProduct ρ σ with hR
  set g : RegisterBasis (fun i => D i × F i) → RegisterBasis D := fun x i => (x i).1 with hg
  set h : RegisterBasis (fun i => D i × F i) → RegisterBasis F := fun x i => (x i).2 with hh
  have hRH : R.IsHermitian := by
    ext x y
    show star (ρ (g y) (g x) * σ (h y) (h x)) = ρ (g x) (g y) * σ (h x) (h y)
    rw [star_mul', ← Matrix.conjTranspose_apply, ← Matrix.conjTranspose_apply σ, hρ.1.1.eq,
      hσ.1.1.eq]
  have hb : Function.Bijective (fun x => (g x, h x)) := by
    constructor
    · intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      funext i
      exact Prod.ext (congrFun hxy.1 i) (congrFun hxy.2 i)
    · rintro ⟨u, v⟩
      exact ⟨fun i => (u i, v i), rfl⟩
  have e1 := S193I_Heq R hRH T (fun x => ((S193I_rl T (g x), ()), (S193I_rl T (h x), ())))
    (fun x => (S193I_rl Tᶜ (g x), S193I_rl Tᶜ (h x)))
    (fun x y => by
      simp only [Prod.mk.injEq, and_true, S193I_req, hg, hh]
      constructor
      · rintro ⟨h1, h2⟩ i hi; exact Prod.ext (h1 i hi) (h2 i hi)
      · intro h; exact ⟨fun i hi => congrArg Prod.fst (h i hi), fun i hi => congrArg Prod.snd (h i hi)⟩)
    (by
      rintro ⟨⟨u, _⟩, ⟨v, _⟩⟩
      refine ⟨fun i => (S193I_ext T u z1 i, S193I_ext T v z2 i), ?_⟩
      exact Prod.ext (Prod.ext (S193I_restrict_ext _ _ _) rfl) (Prod.ext (S193I_restrict_ext _ _ _) rfl))
    (fun x y => by
      simp only [Prod.mk.injEq, S193I_req, hg, hh]
      constructor
      · rintro ⟨h1, h2⟩ i hi; exact Prod.ext (h1 i hi) (h2 i hi)
      · intro h; exact ⟨fun i hi => congrArg Prod.fst (h i hi), fun i hi => congrArg Prod.snd (h i hi)⟩)
  rw [← e1, S193I_marg_prod R ρ σ g h hb (fun x y => rfl) (fun u => (S193I_rl T u, ()))
    (fun v => (S193I_rl T v, ())) (fun u => S193I_rl Tᶜ u) (fun v => S193I_rl Tᶜ v)]
  have hk := S193I_kron (i3 := Classical.decEq _) _ _
    (S193I_marg_herm ρ hρ.1.1 (fun u => (S193I_rl T u, ())) (fun u => S193I_rl Tᶜ u))
    (S193I_marg_herm σ hσ.1.1 (fun u => (S193I_rl T u, ())) (fun u => S193I_rl Tᶜ u))
    (by rw [S193I_marg_trace _ _ _ (S193I_inj_rl T), hρ.2])
    (by rw [S193I_marg_trace _ _ _ (S193I_inj_rl T), hσ.2])
  rw [S193I_toS, S193I_toS, S193I_toS] at hk
  rw [hk, S193I_H_S ρ T, S193I_H_S σ T]

end S193I_prod

section S193I_cont
open Matrix
open scoped Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

lemma S193I_vn_cont {ι : Type*} [Fintype ι] {inst : DecidableEq ι} :
    Continuous (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => QAlgorithms.vnEntropy A.val) := by
  unfold QAlgorithms.vnEntropy
  have : Continuous (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} =>
      cfc (fun x : ℝ => x * Real.logb 2 x) A.val) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ) (by simp) continuous_subtype_val
      (fun x => x.2.isSelfAdjoint) (by
        apply Continuous.continuousOn
        have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
          funext x; rw [Real.logb]; ring
        rw [this]; exact continuous_const.mul Real.continuous_mul_log)
  exact (Complex.continuous_re.comp (continuous_id.matrix_trace.comp this)).neg

lemma S193I_marg_cont {X K F : Type*} [Fintype X] (k : X → K) (f : X → F) :
    Continuous (fun ρ : Matrix X X ℂ => redistributionMarginal ρ k f) := by
  classical
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [redistributionMarginal]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => ?_
  split_ifs
  · exact (continuous_apply y).comp (continuous_apply x)
  · exact continuous_const

end S193I_cont

section S193I_cont2
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

lemma S193I_H_cont {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] (T : Finset (Fin n)) :
    Continuous (fun r : {r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ //
      QAlgorithms.IsDensityMatrix r} => S193I_H r.val T) := by
  classical
  have h : ∀ r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ, S193I_H r T =
      S193I_S (redistributionMarginal r (fun x => (S193I_rl T x, ())) (fun x => S193I_rl Tᶜ x)) :=
    fun r => by rw [S193I_S_eq, S193I_toS]
  simp only [h]
  unfold S193I_S
  have hc : Continuous (fun r : {r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ //
      QAlgorithms.IsDensityMatrix r} =>
      (⟨redistributionMarginal r.val (fun x => (S193I_rl T x, ())) (fun x => S193I_rl Tᶜ x),
        S193I_marg_herm _ r.2.1.1 _ _⟩ : {A : Matrix (SubBasis D T × Unit) (SubBasis D T × Unit) ℂ //
          A.IsHermitian})) :=
    ((S193I_marg_cont _ _).comp continuous_subtype_val).subtype_mk _
  exact (S193I_vn_cont (inst := Classical.decEq _)).comp hc

end S193I_cont2

section S193I_alg

lemma S193I_tele1 {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), (g (i.val + 1) - g i.val) =
      g (n - 1) - g 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun k => if k + 1 < n then g (k + 1) - g k
    else 0) n, ← Finset.sum_filter]
  have : (Finset.range n).filter (fun k => k + 1 < n) = Finset.range (n - 1) := by
    ext k; simp; omega
  rw [this, Finset.sum_range_sub]

lemma S193I_tele2 {n : ℕ} (h : 1 ≤ n) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val), (g i.val - g (i.val + 1)) =
      g 1 - g n := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun k => if 0 < k then g k - g (k + 1)
    else 0) n]
  have h1 : ∀ m, 1 ≤ m → ∑ k ∈ Finset.range m, (if 0 < k then g k - g (k + 1) else 0) =
      g 1 - g m := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp
      · rw [Finset.sum_range_succ, ih h0, if_pos h0]; ring
  exact h1 n h

lemma S193I_sum_last {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), x i =
      ∑ i, x i - x ⟨n - 1, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val + 1 < n) x]
  have : Finset.univ.filter (fun i : Fin n => ¬ (i.val + 1 < n)) = {⟨n - 1, by omega⟩} := by
    ext i; simp [Fin.ext_iff]; omega
  rw [this, Finset.sum_singleton]; ring

lemma S193I_sum_first {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val), x i =
      ∑ i, x i - x ⟨0, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => 0 < i.val) x]
  have : Finset.univ.filter (fun i : Fin n => ¬ (0 < i.val)) = {⟨0, by omega⟩} := by
    ext i; simp [Fin.ext_iff]
  rw [this, Finset.sum_singleton]; ring

end S193I_alg

section S193I_main
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal conditionalMultipartiteInformation)
attribute [local instance] Classical.propDecidable Classical.decEq

def S193I_P (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < k)
def S193I_Q (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val ≠ k)
def S193I_Sg (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val = k)

lemma S193I_sumQ {n : ℕ} (f : Finset (Fin n) → ℝ) :
    ∑ i : Fin n, f (Finset.univ.erase i) = ∑ k ∈ Finset.range n, f (S193I_Q n k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => f (S193I_Q n k)) n]
  refine Finset.sum_congr rfl (fun i _ => congrArg f ?_)
  ext j; simp [S193I_Q, Fin.ext_iff]

lemma S193I_sumS {n : ℕ} (f : Finset (Fin n) → ℝ) :
    ∑ i : Fin n, f {i} = ∑ k ∈ Finset.range n, f (S193I_Sg n k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => f (S193I_Sg n k)) n]
  refine Finset.sum_congr rfl (fun i _ => congrArg f ?_)
  ext j; simp [S193I_Sg, Fin.ext_iff]

variable {n : ℕ}

lemma S193I_ne (s : FiniteState n) : ∀ i, Nonempty (Fin (s.dims i)) :=
  fun i => ⟨⟨0, s.positive i⟩⟩

lemma S193I_qempty (s : FiniteState n) : qH s ∅ = 0 := by
  have := S193I_ne s
  exact S193I_H_empty s.rho s.normalized.2

lemma S193I_qtot (s : FiniteState n) :
    qValue .total s = ∑ i, qH s {i} - qH s Finset.univ := by
  have hU : allParties (singleParties n) = Finset.univ := by
    ext k; simp [allParties, singleParties]
  have h0 := S193I_qempty s
  unfold qH at h0 ⊢
  unfold qValue informationFunctional info conditionalMultipartiteInformation
  simp only [Finset.union_empty, hU, h0, mul_zero, sub_zero, singleParties]

lemma S193I_qdual (s : FiniteState n) :
    qValue .dual s = ∑ i, qH s (Finset.univ.erase i) - ((n - 1 : ℕ) : ℝ) * qH s Finset.univ := by
  have hU : allParties (singleParties n) = Finset.univ := by
    ext k; simp [allParties, singleParties]
  have hE : ∀ i : Fin n, (Finset.univ.erase i).biUnion (singleParties n) = Finset.univ.erase i := by
    intro i; ext k; simp [singleParties]
  have h0 := S193I_qempty s
  unfold qH at h0 ⊢
  unfold qValue informationFunctional info conditionalMultipartiteInformation
  simp only [Finset.union_empty, hU, hE, h0, sub_zero]

lemma S193I_cmi_s (s : FiniteState n) (a b e : Finset (Fin n)) (hab : Disjoint a b)
    (hae : Disjoint a e) (hbe : Disjoint b e) : 0 ≤ stateCMI s a b e := by
  have := S193I_ne s
  exact S193I_cmi s.rho s.normalized a b e hab hae hbe

lemma S193I_cl_e (hn : 2 ≤ n) (s : FiniteState n) :
    qValue .dual s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
        stateCMI s {i} (later i) (earlier i) := by
  have term : ∀ i : Fin n, stateCMI s {i} (later i) (earlier i) =
      (qH s (S193I_P n (i.val + 1)) - qH s (S193I_P n i.val)) +
        (qH s (Finset.univ.erase i) - qH s Finset.univ) := by
    intro i
    have h1 : {i} ∪ earlier i = S193I_P n (i.val + 1) := by
      ext j; simp [earlier, S193I_P, Fin.ext_iff]; omega
    have h2 : later i ∪ earlier i = Finset.univ.erase i := by
      ext j; simp [earlier, later, Fin.ext_iff]; omega
    have h3 : {i} ∪ later i ∪ earlier i = Finset.univ := by
      ext j; simp [earlier, later, Fin.ext_iff]; omega
    have h4 : earlier i = S193I_P n i.val := rfl
    unfold stateCMI
    rw [h1, h2, h3, h4]; ring
  rw [Finset.sum_congr rfl (fun i _ => term i), Finset.sum_add_distrib,
    S193I_tele1 (by omega) (fun k => qH s (S193I_P n k)), S193I_sum_last (by omega),
    S193I_qdual]
  have hP0 : S193I_P n 0 = ∅ := by ext j; simp [S193I_P]
  have hPl : S193I_P n (n - 1) = Finset.univ.erase ⟨n - 1, by omega⟩ := by
    ext j; simp [S193I_P, Fin.ext_iff]; omega
  rw [hP0, hPl, S193I_qempty, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast; ring

lemma S193I_cl_f (hn : 2 ≤ n) (s : FiniteState n) :
    qValue .total s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
        stateCMI s (earlier i) {i} ∅ := by
  have term : ∀ i : Fin n, stateCMI s (earlier i) {i} ∅ =
      (qH s (S193I_P n i.val) - qH s (S193I_P n (i.val + 1))) + qH s {i} := by
    intro i
    have h1 : earlier i ∪ {i} ∪ ∅ = S193I_P n (i.val + 1) := by
      ext j; simp [earlier, S193I_P, Fin.ext_iff]; omega
    have h4 : earlier i = S193I_P n i.val := rfl
    unfold stateCMI
    rw [h1, Finset.union_empty, Finset.union_empty, h4, S193I_qempty]; ring
  rw [Finset.sum_congr rfl (fun i _ => term i), Finset.sum_add_distrib,
    S193I_tele2 (by omega) (fun k => qH s (S193I_P n k)), S193I_sum_first (by omega),
    S193I_qtot]
  have hP1 : S193I_P n 1 = {⟨0, by omega⟩} := by
    ext j; simp [S193I_P, Fin.ext_iff]
  have hPn : S193I_P n n = Finset.univ := by
    ext j; simp [S193I_P]
  rw [hP1, hPn]; ring

lemma S193I_cl_i (s : FiniteState n) :
    qValue .dual s + qValue .total s = ∑ i, stateCMI s {i} (Finset.univ.erase i) ∅ := by
  have term : ∀ i : Fin n, stateCMI s {i} (Finset.univ.erase i) ∅ =
      qH s {i} + qH s (Finset.univ.erase i) - qH s Finset.univ := by
    intro i
    have h3 : {i} ∪ Finset.univ.erase i ∪ ∅ = Finset.univ := by
      ext j; by_cases h : j = i <;> simp [h]
    unfold stateCMI
    rw [h3, Finset.union_empty, Finset.union_empty, S193I_qempty]; ring
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [S193I_qtot, S193I_qdual, S193I_qempty s]
  rw [Finset.sum_congr rfl (fun i _ => term i), S193I_qtot, S193I_qdual, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast; ring

lemma S193I_allM (hn : 2 ≤ n) : allParties (mergeLast n) = Finset.univ := by
  ext j
  simp only [allParties, Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true, mergeLast,
    Finset.mem_filter]
  by_cases hj : j.val < n - 2
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    simp only
    split_ifs <;> omega
  · refine ⟨⟨n - 2, by omega⟩, ?_⟩
    simp only
    split_ifs <;> omega

lemma S193I_bU (hn : 3 ≤ n) (i : Fin (n - 1)) :
    (Finset.univ.erase i).biUnion (mergeLast n) =
      if i.val + 1 = n - 1 then S193I_P n (n - 2) else S193I_Q n i.val := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true, mergeLast,
    Finset.mem_filter, true_and]
  have hi := i.isLt
  have hjl := j.isLt
  constructor
  · rintro ⟨i', hne, h⟩
    have hv : i'.val ≠ i.val := fun e => hne (Fin.ext e)
    have := i'.isLt
    split_ifs at h ⊢ <;> simp [S193I_P, S193I_Q] <;> omega
  · intro h
    by_cases hj : j.val < n - 2
    · refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
      · intro e
        have := congrArg Fin.val e
        simp only at this
        split_ifs at h <;> simp [S193I_P, S193I_Q] at h <;> omega
      · simp only
        split_ifs <;> omega
    · refine ⟨⟨n - 2, by omega⟩, ?_, ?_⟩
      · intro e
        have := congrArg Fin.val e
        simp only at this
        split_ifs at h <;> simp [S193I_P, S193I_Q] at h <;> omega
      · simp only
        split_ifs <;> omega

lemma S193I_cl_g (hn : 3 ≤ n) (s : FiniteState n) :
    qValue .dual s = info .dual s.rho (mergeLast n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 2 = n)
          (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 2 < n) := by
  have hA : (Finset.univ.filter fun i : Fin n => i.val + 2 = n) = S193I_Sg n (n - 2) := by
    ext j; simp [S193I_Sg]; omega
  have hB : (Finset.univ.filter fun i : Fin n => i.val + 1 = n) = S193I_Sg n (n - 1) := by
    ext j; simp [S193I_Sg]; omega
  have hC : (Finset.univ.filter fun i : Fin n => i.val + 2 < n) = S193I_P n (n - 2) := by
    ext j; simp [S193I_P]; omega
  have h1 : S193I_Sg n (n - 2) ∪ S193I_P n (n - 2) = S193I_Q n (n - 1) := by
    ext j; simp [S193I_Sg, S193I_P, S193I_Q]; omega
  have h2 : S193I_Sg n (n - 1) ∪ S193I_P n (n - 2) = S193I_Q n (n - 2) := by
    ext j; simp [S193I_Sg, S193I_P, S193I_Q]; omega
  have h3 : S193I_Sg n (n - 2) ∪ S193I_Sg n (n - 1) ∪ S193I_P n (n - 2) = Finset.univ := by
    ext j; simp [S193I_Sg, S193I_P]; omega
  unfold stateCMI
  rw [hA, hB, hC, h1, h2, h3, S193I_qdual, S193I_sumQ (fun T => qH s T)]
  unfold info conditionalMultipartiteInformation
  simp only [Finset.union_empty, S193I_allM (by omega : 2 ≤ n), S193I_bU hn]
  rw [Fin.sum_univ_eq_sum_range (fun k => entropyAt (trivialExtension s.rho)
    (if k + 1 = n - 1 then S193I_P n (n - 2) else S193I_Q n k)) (n - 1)]
  have h0 := S193I_qempty s
  unfold qH at h0 ⊢
  rw [h0]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  simp only [e1, e2]
  rw [Finset.sum_range_succ (n := m + 1), if_pos (by omega)]
  have hs : ∑ x ∈ Finset.range (m + 1), entropyAt (trivialExtension s.rho)
      (if x + 1 = m + 2 then S193I_P (m + 3) (m + 1) else S193I_Q (m + 3) x) =
      ∑ x ∈ Finset.range (m + 1), entropyAt (trivialExtension s.rho) (S193I_Q (m + 3) x) :=
    Finset.sum_congr rfl (fun k hk => by rw [if_neg (by simp at hk; omega)])
  have hr : ∑ k ∈ Finset.range (m + 3), entropyAt (trivialExtension s.rho) (S193I_Q (m + 3) k) =
      ∑ k ∈ Finset.range (m + 1), entropyAt (trivialExtension s.rho) (S193I_Q (m + 3) k) +
        entropyAt (trivialExtension s.rho) (S193I_Q (m + 3) (m + 1)) +
        entropyAt (trivialExtension s.rho) (S193I_Q (m + 3) (m + 2)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hs, hr, show m + 2 - 1 = m + 1 by omega]
  push_cast
  ring

lemma S193I_cl_h (hn : 3 ≤ n) (s : FiniteState n) :
    qValue .total s = info .total s.rho (firstParties n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 1 < n) ∅ := by
  have hB : (Finset.univ.filter fun i : Fin n => i.val + 1 = n) = S193I_Sg n (n - 1) := by
    ext j; simp [S193I_Sg]; omega
  have hC : (Finset.univ.filter fun i : Fin n => i.val + 1 < n) = S193I_P n (n - 1) := by
    ext j; simp [S193I_P]; omega
  have hAll : allParties (firstParties n) = S193I_P n (n - 1) := by
    ext j
    simp only [allParties, firstParties, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, S193I_P]
    constructor
    · rintro ⟨i, hi⟩; have := i.isLt; omega
    · intro h; exact ⟨⟨j.val, by omega⟩, rfl⟩
  have h3 : S193I_Sg n (n - 1) ∪ S193I_P n (n - 1) = Finset.univ := by
    ext j; simp [S193I_Sg, S193I_P]; omega
  unfold stateCMI
  rw [hB, hC, h3, S193I_qtot, S193I_sumS (fun T => qH s T)]
  unfold info conditionalMultipartiteInformation
  have hF : ∀ i : Fin (n - 1), firstParties n i = S193I_Sg n i.val := fun i => rfl
  simp only [Finset.union_empty, hAll, hF]
  have h0 := S193I_qempty s
  unfold qH at h0 ⊢
  rw [Fin.sum_univ_eq_sum_range (fun k => entropyAt (trivialExtension s.rho)
    (S193I_Sg n k)) (n - 1)]
  · rw [h0]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [show m + 1 - 1 = m by omega, Finset.sum_range_succ]
    ring

lemma S193I_cl_j (s : FiniteState n) (e : Equiv.Perm (Fin n)) (kind : InformationKind) :
    info kind s.rho (fun i => {e i}) ∅ = qValue kind s := by
  have hU : allParties (fun i => ({e i} : Finset (Fin n))) = Finset.univ := by
    ext k; simp [allParties]; exact ⟨e.symm k, by simp⟩
  have hE : ∀ i : Fin n, (Finset.univ.erase i).biUnion (fun j => ({e j} : Finset (Fin n))) =
      Finset.univ.erase (e i) := by
    intro i; ext k
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact fun h => hj (e.injective h)
    · intro h; exact ⟨e.symm k, fun h' => h (by rw [← h', Equiv.apply_symm_apply]), by simp⟩
  cases kind
  · rw [S193I_qtot]
    unfold info conditionalMultipartiteInformation
    have h0 := S193I_qempty s
    unfold qH at h0 ⊢
    simp only [Finset.union_empty, hU, h0, mul_zero, sub_zero]
    rw [Equiv.sum_comp e (fun i => entropyAt (trivialExtension s.rho) {i})]
  · rw [S193I_qdual]
    unfold info conditionalMultipartiteInformation
    have h0 := S193I_qempty s
    unfold qH at h0 ⊢
    simp only [Finset.union_empty, hU, hE, h0, sub_zero]
    rw [Equiv.sum_comp e (fun i => entropyAt (trivialExtension s.rho) (Finset.univ.erase i))]

lemma S193I_cl_k (hn : 2 ≤ n) (s : FiniteState n)
    (eta : (i : Fin n) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ)
    (heta : ∀ i, IsDensityMatrix (eta i)) (hs : s.rho = labelledProductDensity eta)
    (kind : InformationKind) : qValue kind s = 0 := by
  have := S193I_ne s
  have hT : ∀ T, qH s T = ∑ i ∈ T, qH s {i} := fun T =>
    S193I_prodH s.rho s.normalized.1.isHermitian s.normalized.2 eta heta
      (fun x y => by rw [hs]; rfl) T
  cases kind
  · rw [S193I_qtot, hT Finset.univ]; ring
  · rw [S193I_qdual, hT Finset.univ]
    simp only [hT (Finset.univ.erase _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast; ring

lemma S193I_nonneg (hn : 2 ≤ n) (s : FiniteState n) (kind : InformationKind) :
    0 ≤ qValue kind s := by
  cases kind
  · rw [S193I_cl_f hn]
    refine Finset.sum_nonneg (fun i _ => S193I_cmi_s s _ _ _ ?_ ?_ ?_)
    · rw [Finset.disjoint_singleton_right]; simp [earlier]
    · simp
    · simp
  · rw [S193I_cl_e hn]
    refine Finset.sum_nonneg (fun i _ => S193I_cmi_s s _ _ _ ?_ ?_ ?_)
    · rw [Finset.disjoint_singleton_left]; simp [later]
    · rw [Finset.disjoint_singleton_left]; simp [earlier]
    · rw [Finset.disjoint_left]; intro j h1 h2; simp [earlier, later] at h1 h2; omega

lemma S193I_cont_q (kind : InformationKind) : IsContinuousFunctional (qValue kind : FiniteState n → ℝ) := by
  intro d hd
  cases kind
  · have : (fun r : {r : Matrix (RegisterBasis (fun i => Fin (d i))) (RegisterBasis (fun i => Fin (d i))) ℂ //
        IsDensityMatrix r} => qValue .total (⟨d, hd, r.val, r.property⟩ : FiniteState n)) =
        fun r => ∑ i, S193I_H r.val {i} - S193I_H r.val Finset.univ :=
      funext fun r => S193I_qtot _
    rw [this]
    exact (continuous_finsetSum _ (fun i _ => S193I_H_cont _)).sub (S193I_H_cont _)
  · have : (fun r : {r : Matrix (RegisterBasis (fun i => Fin (d i))) (RegisterBasis (fun i => Fin (d i))) ℂ //
        IsDensityMatrix r} => qValue .dual (⟨d, hd, r.val, r.property⟩ : FiniteState n)) =
        fun r => ∑ i, S193I_H r.val (Finset.univ.erase i) -
          ((n - 1 : ℕ) : ℝ) * S193I_H r.val Finset.univ :=
      funext fun r => S193I_qdual _
    rw [this]
    exact (continuous_finsetSum _ (fun i _ => S193I_H_cont _)).sub
      (continuous_const.mul (S193I_H_cont _))

lemma S193I_cl_pp (s t : FiniteState n) (kind : InformationKind) :
    info kind (partyProduct s.rho t.rho) (singleParties n) ∅ = qValue kind s + qValue kind t := by
  have := S193I_ne s
  have := S193I_ne t
  have hp : ∀ T, entropyAt (trivialExtension (partyProduct s.rho t.rho)) T =
      entropyAt (trivialExtension s.rho) T + entropyAt (trivialExtension t.rho) T :=
    fun T => S193I_ppH s.rho t.rho s.normalized t.normalized T
  unfold qValue informationFunctional info conditionalMultipartiteInformation
  cases kind <;> simp only [hp, Finset.sum_add_distrib] <;> ring

lemma S193I_cl_two (s : FiniteState 2) :
    qValue .dual s = stateCMI s {0} {1} ∅ ∧ qValue .total s = stateCMI s {0} {1} ∅ := by
  have h01 : ({0} : Finset (Fin 2)) ∪ {1} ∪ ∅ = Finset.univ := by decide
  have e0 : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have e1 : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  unfold stateCMI
  rw [h01, Finset.union_empty, Finset.union_empty, S193I_qempty, S193I_qdual, S193I_qtot,
    Fin.sum_univ_two, Fin.sum_univ_two, e0, e1]
  constructor <;> norm_num <;> ring

lemma S193I_cl_b (hn : 2 ≤ n) (s : FiniteState n) :
    qValue .dual s = qH s Finset.univ -
        ∑ i, (qH s Finset.univ - qH s (Finset.univ.erase i)) := by
  rw [S193I_qdual, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast; ring

end S193I_main

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §V.B, PDF pp.9--10, (51),(52), and the cited classical rewritings:
all entropy/chain/recurrence identities and basic properties in bits.
Quantum conditional entropy is NOT asserted nonnegative. -/
theorem solution :
    (∀ (n : ℕ) (hn : 2 ≤ n) (s : FiniteState n),
      (∀ kind : InformationKind, 0 ≤ qValue kind s) ∧
      qValue .dual s = qH s Finset.univ -
        ∑ i, (qH s Finset.univ - qH s (Finset.univ.erase i)) ∧
      qValue .dual s = (∑ i, qH s (Finset.univ.erase i)) -
        (n-1 : ℕ) * qH s Finset.univ ∧
      qValue .total s = (∑ i, qH s {i}) - qH s Finset.univ ∧
      qValue .dual s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
        stateCMI s {i} (later i) (earlier i) ∧
      qValue .total s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
        stateCMI s (earlier i) {i} ∅ ∧
      (3 ≤ n → qValue .dual s = info .dual s.rho (mergeLast n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 2 = n)
          (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 2 < n)) ∧
      (3 ≤ n → qValue .total s = info .total s.rho (firstParties n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 1 < n) ∅) ∧
      qValue .dual s + qValue .total s = ∑ i, stateCMI s {i} (Finset.univ.erase i) ∅ ∧
      (∀ (e : Equiv.Perm (Fin n)) (kind : InformationKind),
        info kind s.rho (fun i => {e i}) ∅ = qValue kind s) ∧
      (∀ eta : (i : Fin n) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ,
        (∀ i, IsDensityMatrix (eta i)) → s.rho = labelledProductDensity eta →
        ∀ kind : InformationKind, qValue kind s = 0)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ kind : InformationKind,
      IsContinuousFunctional (qValue kind : FiniteState n → ℝ)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (s t : FiniteState n) (kind : InformationKind),
      info kind (partyProduct s.rho t.rho) (singleParties n) ∅ = qValue kind s + qValue kind t) ∧
    (∀ s : FiniteState 2, qValue .dual s = stateCMI s {0} {1} ∅ ∧
      qValue .total s = stateCMI s {0} {1} ∅) :=
  ⟨fun _ hn s => ⟨fun kind => S193I_nonneg hn s kind, S193I_cl_b hn s, S193I_qdual s,
      S193I_qtot s, S193I_cl_e hn s, S193I_cl_f hn s, fun h3 => S193I_cl_g h3 s,
      fun h3 => S193I_cl_h h3 s, S193I_cl_i s, fun e kind => S193I_cl_j s e kind,
      fun eta heta hs kind => S193I_cl_k hn s eta heta hs kind⟩,
    fun _ _ kind => S193I_cont_q kind,
    fun _ _ s t kind => S193I_cl_pp s t kind,
    S193I_cl_two⟩
