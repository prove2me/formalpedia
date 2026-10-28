-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P43.alternative_product_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:31:47.519878+00:00
-- url     : https://prove2.me/submissions/097ff1b8-8e95-4640-bab6-fdce820c7d4b

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

section S193P43_ent
open Matrix Polynomial

lemma S193P43_inst {ι : Type*} [Fintype ι] (i1 i2 : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i1 A = @QAlgorithms.vnEntropy ι _ i2 A := by
  congr

lemma S193P43_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S193P43_vn_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) :
    QAlgorithms.vnEntropy Y = (∑ i, Real.negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold QAlgorithms.vnEntropy
  rw [S193P43_cfc_trace hY, Complex.re_sum, Finset.sum_div]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.negMulLog, Real.logb]; ring_nf

lemma S193P43_vn_roots {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A =
      ((A.charpoly.roots).map (fun z : ℂ => Real.negMulLog z.re)).sum / Real.log 2 := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, S193P43_vn_eig hA]
  rfl

lemma S193P43_udiag {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (P : Matrix n n ℂ) (hP : Pᴴ * P = 1) (f : n → ℝ)
    (h : A = P * diagonal (fun i => (f i : ℂ)) * Pᴴ) :
    QAlgorithms.vnEntropy A = (∑ i, Real.negMulLog (f i)) / Real.log 2 := by
  rw [S193P43_vn_roots _ hA]
  have hc : A.charpoly = ∏ i, (X - C (f i : ℂ)) := by
    rw [h, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hP, Matrix.mul_one,
      charpoly_diagonal]
  rw [hc, roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
  rfl

lemma S193P43_spec {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    ∃ P : Matrix n n ℂ, Pᴴ * P = 1 ∧
      A = P * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Pᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2)
  · conv_lhs => rw [hA.spectral_theorem]
    rfl

lemma S193P43_kron0 {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) =
      QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  obtain ⟨P, hP, hAP⟩ := S193P43_spec A hA
  obtain ⟨Q, hQ, hBQ⟩ := S193P43_spec B hB
  have hK : (A ⊗ₖ B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, hA.eq, hB.eq]
  have htA' : (1 : ℝ) = ∑ i, hA.eigenvalues i := by
    have := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    rw [htA] at this; simpa using this
  have htB' : (1 : ℝ) = ∑ i, hB.eigenvalues i := by
    have := congrArg Complex.re hB.trace_eq_sum_eigenvalues
    rw [htB] at this; simpa using this
  rw [S193P43_udiag _ hK (P ⊗ₖ Q) ?_ (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) ?_,
    S193P43_udiag _ hA P hP _ hAP, S193P43_udiag _ hB Q hQ _ hBQ, ← add_div]
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

lemma S193P43_kron {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] {i3 : DecidableEq (p × q)} (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) =
      QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  rw [S193P43_inst i3 instDecidableEqProd]
  exact S193P43_kron0 A B hA hB htA htB


lemma S193P43_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

lemma S193P43_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

def S193P43_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S193P43_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S193P43_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S193P43_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S193P43_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S193P43_vn_poly A hA (S193P43_interp s)
      (fun x hx => S193P43_interp_eval s (by simpa [s] using hx)),
    S193P43_vn_poly _ (hA.submatrix e) (S193P43_interp s)
      (fun x hx => S193P43_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S193P43_interp s)) i i)

lemma S193P43_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]

end S193P43_ent

section S193P43_marg
open Matrix
attribute [local instance] Classical.propDecidable

def S193P43_marg {X K F : Type*} [Fintype X] (ρ : Matrix X X ℂ) (k : X → K) (f : X → F) :
    Matrix K K ℂ :=
  fun a b => ∑ x, ∑ y, if k x = a ∧ k y = b ∧ f x = f y then ρ x y else 0

lemma S193P43_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma S193P43_marg_comp {Y K F K2 F2 : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (k2 : K → K2) (f2 : K → F2) :
    S193P43_marg (S193P43_marg ρ k f) k2 f2 =
      S193P43_marg ρ (k2 ∘ k) (fun y => (f2 (k y), f y)) := by
  ext a b
  simp only [S193P43_marg, S193P43_ite_sum, Function.comp]
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

lemma S193P43_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    S193P43_marg ρ k f = S193P43_marg ρ k f' := by
  ext a b
  simp only [S193P43_marg]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma S193P43_marg_herm {Y K F : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (hρ : ρ.IsHermitian)
    (k : Y → K) (f : Y → F) : (S193P43_marg ρ k f).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, S193P43_marg, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : k x = a ∧ k y = b ∧ f x = f y
  · rw [if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, if_pos h]
    exact congrFun (congrFun hρ x) y
  · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩), if_neg h, star_zero]

lemma S193P43_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
    {inst : DecidableEq K} [DecidableEq K'] (ρ : Matrix Y Y ℂ) (hρ : ρ.IsHermitian)
    (k : Y → K) (k' : Y → K') (f : Y → F) (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k') :
    QAlgorithms.vnEntropy (S193P43_marg ρ k f) =
      QAlgorithms.vnEntropy (S193P43_marg ρ k' f) := by
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
  have hsub : (S193P43_marg ρ k' f).submatrix (Equiv.ofBijective g hb)
      (Equiv.ofBijective g hb) = S193P43_marg ρ k f := by
    ext a b
    simp only [Matrix.submatrix_apply, Equiv.ofBijective_apply, S193P43_marg]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h : k x = a ∧ k y = b ∧ f x = f y
    · rw [if_pos (by rwa [hgk, hgk]), if_pos h]
    · rw [if_neg (by rwa [hgk, hgk]), if_neg h]
  rw [← hsub, S193P43_vn_submatrix _ (S193P43_marg_herm ρ hρ k' f)]

lemma S193P43_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (hinj : Function.Injective (fun y => (k y, f y))) :
    (S193P43_marg ρ k f).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, S193P43_marg]
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

lemma S193P43_sum_equiv {X X1 X2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (g : X → X1) (h : X → X2) (hb : Function.Bijective (fun x => (g x, h x)))
    (G : X1 → X2 → ℂ) : ∑ x, G (g x) (h x) = ∑ z1, ∑ z2, G z1 z2 := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.ofBijective _ hb) _ _ (fun x => rfl)

lemma S193P43_marg_prod {X X1 X2 K1 K2 F1 F2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (ρ : Matrix X X ℂ) (P : Matrix X1 X1 ℂ) (Q : Matrix X2 X2 ℂ) (g : X → X1) (h : X → X2)
    (hb : Function.Bijective (fun x => (g x, h x)))
    (hρ : ∀ x y, ρ x y = P (g x) (g y) * Q (h x) (h y))
    (k1 : X1 → K1) (k2 : X2 → K2) (f1 : X1 → F1) (f2 : X2 → F2) :
    S193P43_marg ρ (fun x => (k1 (g x), k2 (h x))) (fun x => (f1 (g x), f2 (h x))) =
      S193P43_marg P k1 f1 ⊗ₖ S193P43_marg Q k2 f2 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  rw [kronecker_apply]
  simp only [S193P43_marg]
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
  rw [Finset.sum_congr rfl (fun x _ => S193P43_sum_equiv g h hb (fun w1 w2 => T (g x) (h x) w1 w2)),
    S193P43_sum_equiv g h hb (fun z1 z2 => ∑ w1, ∑ w2, T z1 z2 w1 w2)]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  rw [Finset.sum_mul_sum]

lemma S193P43_trace_prod {X X1 X2 : Type*} [Fintype X] [Fintype X1] [Fintype X2]
    (ρ : Matrix X X ℂ) (P : Matrix X1 X1 ℂ) (Q : Matrix X2 X2 ℂ) (g : X → X1) (h : X → X2)
    (hb : Function.Bijective (fun x => (g x, h x)))
    (hρ : ∀ x y, ρ x y = P (g x) (g y) * Q (h x) (h y)) :
    ρ.trace = P.trace * Q.trace := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.sum_congr rfl (fun x _ => hρ x x), S193P43_sum_equiv g h hb (fun z1 z2 => P z1 z1 * Q z2 z2), Finset.sum_mul_sum]

end S193P43_marg

section S193P43_reg
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Support50.P43
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

lemma S193P43_req (s : Finset (Fin n)) (x y : RegisterBasis D) :
    restrictLabel s x = restrictLabel s y ↔ ∀ i ∈ s, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2

lemma S193P43_and_iff (s s1 s2 : Finset (Fin n)) (hs : ∀ i, i ∈ s ↔ i ∈ s1 ∨ i ∈ s2)
    (p : Fin n → Prop) : ((∀ i ∈ s1, p i) ∧ (∀ i ∈ s2, p i)) ↔ ∀ i ∈ s, p i := by
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases (hs i).1 hi with h | h
    exacts [h1 i h, h2 i h]
  · intro h
    exact ⟨fun i hi => h i ((hs i).2 (Or.inl hi)), fun i hi => h i ((hs i).2 (Or.inr hi))⟩

def S193P43_res {s t : Finset (Fin n)} (h : s ⊆ t) (u : SubBasis D t) : SubBasis D s :=
  fun i => u ⟨i.1, h i.2⟩

lemma S193P43_res_restrict {s t : Finset (Fin n)} (h : s ⊆ t) (x : RegisterBasis D) :
    S193P43_res h (restrictLabel t x) = restrictLabel s x := rfl

def S193P43_ext (T : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D) :
    RegisterBasis D := fun k => if h : k ∈ T then a ⟨k, h⟩ else z k

lemma S193P43_restrict_ext (T : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D) :
    restrictLabel T (S193P43_ext T a z) = a := by
  funext i; simp [restrictLabel, S193P43_ext, i.2]

lemma S193P43_restrict_ext_disj (T T' : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D)
    (h : ∀ k ∈ T', k ∉ T) : restrictLabel T' (S193P43_ext T a z) = restrictLabel T' z := by
  funext k; simp [restrictLabel, S193P43_ext, h k.1 k.2]

lemma S193P43_C1 (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    registerMarginal (trivialExtension ρ) T =
      S193P43_marg ρ (fun x => (restrictLabel T x, ())) (fun x => restrictLabel Tᶜ x) := by
  ext a b
  simp only [registerMarginal, trivialExtension, S193P43_marg]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have hiff : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i)) ↔ ((restrictLabel T x, ()) = a ∧ (restrictLabel T y, ()) = b ∧
      restrictLabel Tᶜ x = restrictLabel Tᶜ y) := by
    rw [S193P43_req]
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

lemma S193P43_S_eq (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    marginalEntropyBits ρ T = QAlgorithms.vnEntropy
      (S193P43_marg ρ (fun x => (restrictLabel T x, ())) (fun x => restrictLabel Tᶜ x)) := by
  unfold marginalEntropyBits entropyAt
  rw [S193P43_C1]
  exact S193P43_inst _ _ _

lemma S193P43_bij (A B : Finset (Fin n)) (hAB : ∀ i, i ∈ B ↔ i ∉ A) :
    Function.Bijective (fun x : RegisterBasis D => (restrictLabel A x, restrictLabel B x)) := by
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
    · funext i; simp [restrictLabel, i.2]
    · funext i
      have : (i : Fin n) ∉ A := (hAB i).1 i.2
      simp [restrictLabel, this]

lemma S193P43_res_inj {U A : Finset (Fin n)} (hU : U ⊆ A) :
    Function.Injective (fun u : SubBasis D A =>
      (S193P43_res hU u, S193P43_res (Finset.sdiff_subset (s := A) (t := U)) u)) := by
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  funext i
  by_cases hi : i.1 ∈ U
  · exact congrFun huv.1 ⟨i.1, hi⟩
  · exact congrFun huv.2 ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hi⟩⟩

lemma S193P43_side (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (A B : Finset (Fin n))
    (hAB : ∀ i, i ∈ B ↔ i ∉ A) (P : Matrix (SubBasis D A) (SubBasis D A) ℂ)
    (Q : Matrix (SubBasis D B) (SubBasis D B) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (htP : P.trace = 1) (htQ : Q.trace = 1)
    (hfac : ∀ x y, ρ x y = P (restrictLabel A x) (restrictLabel A y) *
      Q (restrictLabel B x) (restrictLabel B y))
    (U : Finset (Fin n)) (hU : U ⊆ A) :
    marginalEntropyBits ρ U = QAlgorithms.vnEntropy (S193P43_marg P (S193P43_res hU)
      (S193P43_res (Finset.sdiff_subset (s := A) (t := U)))) := by
  rw [S193P43_S_eq, S193P43_marg_forget ρ _ _
    (fun x => (restrictLabel (A \ U) x, restrictLabel B x)) ?hf]
  · rw [show S193P43_marg ρ (fun x => (restrictLabel U x, ()))
        (fun x => (restrictLabel (A \ U) x, restrictLabel B x)) =
        S193P43_marg ρ (fun x => (S193P43_res hU (restrictLabel A x),
          (fun _ : SubBasis D B => ()) (restrictLabel B x)))
        (fun x => (S193P43_res (Finset.sdiff_subset (s := A) (t := U)) (restrictLabel A x),
          id (restrictLabel B x))) from rfl]
    rw [S193P43_marg_prod ρ P Q _ _ (S193P43_bij A B hAB) hfac (S193P43_res hU) (fun _ => ())
      (S193P43_res (Finset.sdiff_subset (s := A) (t := U))) id]
    rw [S193P43_kron _ _ (S193P43_marg_herm P hP _ _) (S193P43_marg_herm Q hQ _ _)
      (by rw [S193P43_marg_trace P _ _ (S193P43_res_inj hU), htP])
      (by rw [S193P43_marg_trace Q _ _ (fun a b h => by simpa using h), htQ]),
      S193P43_vn_unit _ (by rw [S193P43_marg_trace Q _ _ (fun a b h => by simpa using h), htQ]),
      add_zero]
  · intro x y
    simp only [Prod.mk.injEq, S193P43_req]
    rw [S193P43_and_iff Uᶜ (A \ U) B]
    intro i
    have := @hU i
    have := hAB i
    simp only [Finset.mem_compl, Finset.mem_sdiff]
    tauto

lemma S193P43_split [∀ i, Nonempty (D i)] (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hρ : ρ.IsHermitian) (A B : Finset (Fin n))
    (hAB : ∀ i, i ∈ B ↔ i ∉ A) (P : Matrix (SubBasis D A) (SubBasis D A) ℂ)
    (Q : Matrix (SubBasis D B) (SubBasis D B) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (htP : P.trace = 1) (htQ : Q.trace = 1)
    (hfac : ∀ x y, ρ x y = P (restrictLabel A x) (restrictLabel A y) *
      Q (restrictLabel B x) (restrictLabel B y))
    (T : Finset (Fin n)) :
    marginalEntropyBits ρ T = marginalEntropyBits ρ (T ∩ A) + marginalEntropyBits ρ (T ∩ B) := by
  have hBA : ∀ i, i ∈ A ↔ i ∉ B := fun i => by rw [hAB i, not_not]
  have hUA : T ∩ A ⊆ A := Finset.inter_subset_right
  have hVB : T ∩ B ⊆ B := Finset.inter_subset_right
  have z : RegisterBasis D := fun i => Classical.arbitrary (D i)
  rw [S193P43_side ρ A B hAB P Q hP hQ htP htQ hfac (T ∩ A) hUA,
    S193P43_side ρ B A hBA Q P hQ hP htQ htP (fun x y => by rw [hfac, mul_comm]) (T ∩ B) hVB]
  rw [S193P43_S_eq, S193P43_vn_keep ρ hρ _
    (fun x => (S193P43_res hUA (restrictLabel A x), S193P43_res hVB (restrictLabel B x))) _ ?hk
    ?hs ?hs']
  case hk =>
    intro x y
    simp only [S193P43_res_restrict, Prod.mk.injEq, and_true, S193P43_req]
    rw [S193P43_and_iff T (T ∩ A) (T ∩ B)]
    intro i
    have := hAB i
    simp only [Finset.mem_inter]
    tauto
  case hs =>
    rintro ⟨a, u⟩
    exact ⟨S193P43_ext T a z, Prod.ext (S193P43_restrict_ext T a z) rfl⟩
  case hs' =>
    rintro ⟨a1, a2⟩
    refine ⟨S193P43_ext (T ∩ A) a1 (S193P43_ext (T ∩ B) a2 z), ?_⟩
    simp only [S193P43_res_restrict, Prod.mk.injEq]
    refine ⟨S193P43_restrict_ext _ _ _, ?_⟩
    rw [S193P43_restrict_ext_disj, S193P43_restrict_ext]
    intro k hk hk'
    exact (hAB k).1 (Finset.mem_inter.1 hk).2 (Finset.mem_inter.1 hk').2
  rw [S193P43_marg_forget ρ _ _ (fun x =>
    (S193P43_res (Finset.sdiff_subset (s := A) (t := T ∩ A)) (restrictLabel A x),
     S193P43_res (Finset.sdiff_subset (s := B) (t := T ∩ B)) (restrictLabel B x))) ?hf]
  · rw [S193P43_marg_prod ρ P Q _ _ (S193P43_bij A B hAB) hfac (S193P43_res hUA)
      (S193P43_res hVB) (S193P43_res (Finset.sdiff_subset (s := A) (t := T ∩ A)))
      (S193P43_res (Finset.sdiff_subset (s := B) (t := T ∩ B)))]
    rw [S193P43_kron _ _ (S193P43_marg_herm P hP _ _) (S193P43_marg_herm Q hQ _ _)
      (by rw [S193P43_marg_trace P _ _ (S193P43_res_inj hUA), htP])
      (by rw [S193P43_marg_trace Q _ _ (S193P43_res_inj hVB), htQ])]
  · intro x y
    simp only [S193P43_res_restrict, Prod.mk.injEq, S193P43_req]
    rw [S193P43_and_iff Tᶜ (A \ (T ∩ A)) (B \ (T ∩ B))]
    intro i
    have := hAB i
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_inter]
    tauto

lemma S193P43_red_herm (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.IsHermitian)
    (s : Finset (Fin n)) : (reducedDensity ρ s).IsHermitian := by
  have h := S193P43_marg_herm ρ hρ (fun x => (restrictLabel s x, ())) (fun x => restrictLabel sᶜ x)
  rw [← S193P43_C1] at h
  ext u v
  exact congrFun (congrFun h (u, ())) (v, ())

lemma S193P43_red_trace (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (htr : ρ.trace = 1)
    (s : Finset (Fin n)) : (reducedDensity ρ s).trace = 1 := by
  have h := S193P43_marg_trace ρ (fun x => (restrictLabel s x, ())) (fun x => restrictLabel sᶜ x)
    (by
      intro x y hxy
      simp only [Prod.mk.injEq, and_true] at hxy
      funext i
      by_cases hi : i ∈ s
      · exact congrFun hxy.1 ⟨i, hi⟩
      · exact congrFun hxy.2 ⟨i, by simpa using hi⟩)
  rw [← S193P43_C1, htr] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Finset.univ_unique,
    Finset.sum_singleton]
  rfl

def S193P43_Q {m : ℕ} (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (blocks : Fin m → Finset (Fin n)) (k : Fin m) (z : RegisterBasis D) :
    Matrix (SubBasis D (blocks k)ᶜ) (SubBasis D (blocks k)ᶜ) ℂ :=
  fun v w => ∏ j ∈ Finset.univ.erase k, reducedDensity ρ (blocks j)
    (restrictLabel (blocks j) (S193P43_ext _ v z)) (restrictLabel (blocks j) (S193P43_ext _ w z))

lemma S193P43_Q_herm {m : ℕ} (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hρ : ρ.IsHermitian) (blocks : Fin m → Finset (Fin n)) (k : Fin m) (z : RegisterBasis D) :
    (S193P43_Q ρ blocks k z).IsHermitian := by
  ext v w
  simp only [conjTranspose_apply, S193P43_Q, Complex.star_def, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact congrFun (congrFun (S193P43_red_herm ρ hρ (blocks j)) _) _

lemma S193P43_fac {m : ℕ} (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (blocks : Fin m → Finset (Fin n))
    (hdis : ∀ j k, j ≠ k → Disjoint (blocks j) (blocks k))
    (hprod : IsProductAcross ρ blocks) (k : Fin m) (z : RegisterBasis D) (x y : RegisterBasis D) :
    ρ x y = reducedDensity ρ (blocks k) (restrictLabel (blocks k) x) (restrictLabel (blocks k) y) *
      S193P43_Q ρ blocks k z (restrictLabel (blocks k)ᶜ x) (restrictLabel (blocks k)ᶜ y) := by
  have he : ∀ j ∈ Finset.univ.erase k, ∀ x : RegisterBasis D,
      restrictLabel (blocks j) (S193P43_ext (blocks k)ᶜ (restrictLabel (blocks k)ᶜ x) z) =
        restrictLabel (blocks j) x := by
    intro j hj x
    funext i
    have hik : (i : Fin n) ∈ (blocks k)ᶜ := Finset.mem_compl.2
      (Finset.disjoint_left.1 (hdis j k (Finset.ne_of_mem_erase hj)) i.2)
    simp [restrictLabel, S193P43_ext, hik]
  rw [hprod x y, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  simp only [S193P43_Q]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [he j hj x, he j hj y]

end S193P43_reg

section S193P43_final
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)
open QAlgorithms.Papers.Independent.Support50.P43
attribute [local instance] Classical.propDecidable Classical.decEq

theorem S193P43_main {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (blocks : Fin m → Finset (Fin n))
    (hne : ∀ j, (blocks j).Nonempty)
    (hdis : ∀ j k, j ≠ k → Disjoint (blocks j) (blocks k))
    (hcover : Finset.univ.biUnion blocks = Finset.univ)
    (hprod : IsProductAcross rho blocks) :
    alternativeOn rho Finset.univ = ∑ j, alternativeOn rho (blocks j) := by
  obtain ⟨hpsd, htr⟩ := hrho
  have hH : rho.IsHermitian := hpsd.isHermitian
  have z : RegisterBasis D := fun i => Classical.arbitrary (D i)
  have hsplit : ∀ k T, marginalEntropyBits rho T = marginalEntropyBits rho (T ∩ blocks k) +
      marginalEntropyBits rho (T ∩ (blocks k)ᶜ) := by
    intro k T
    have htQ : (S193P43_Q rho blocks k z).trace = 1 := by
      have h := S193P43_trace_prod rho _ _ _ _
        (S193P43_bij (D := D) (blocks k) (blocks k)ᶜ (fun i => Finset.mem_compl))
        (S193P43_fac rho blocks hdis hprod k z)
      rw [htr, S193P43_red_trace rho htr, one_mul] at h
      exact h.symm
    exact S193P43_split rho hH (blocks k) (blocks k)ᶜ (fun i => Finset.mem_compl) _ _
      (S193P43_red_herm rho hH _) (S193P43_Q_herm rho hH blocks k z) (S193P43_red_trace rho htr _)
      htQ (S193P43_fac rho blocks hdis hprod k z) T
  set S := marginalEntropyBits rho with hS
  have hind : ∀ (J : Finset (Fin m)) (T : Finset (Fin n)),
      S T = ∑ j ∈ J, S (T ∩ blocks j) + S (T \ J.biUnion blocks) := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro T; simp
    | insert k J hk ih =>
      intro T
      rw [ih T, Finset.sum_insert hk, hsplit k (T \ J.biUnion blocks)]
      have e1 : (T \ J.biUnion blocks) ∩ blocks k = T ∩ blocks k := by
        ext i
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          refine ⟨⟨h1, fun j hj hij => ?_⟩, h3⟩
          have hjk : j ≠ k := fun h => hk (h ▸ hj)
          exact Finset.disjoint_left.1 (hdis j k hjk) hij h3
      have e2 : (T \ J.biUnion blocks) ∩ (blocks k)ᶜ = T \ (insert k J).biUnion blocks := by
        ext i
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_compl,
          Finset.mem_insert, not_exists, not_and]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun j hj => ?_⟩
          rcases hj with rfl | hj
          · exact h3
          · exact h2 j hj
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun j hj => h2 j (Or.inr hj)⟩, h2 k (Or.inl rfl)⟩
      rw [e1, e2]; ring
  have h0 : S ∅ = 0 := by
    have := hsplit ⟨0, hm⟩ ∅
    simp only [Finset.empty_inter] at this
    linarith
  have hadd : ∀ T, S T = ∑ j, S (T ∩ blocks j) := by
    intro T
    rw [hind Finset.univ T, hcover, Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_univ T),
      h0, add_zero]
  have hE : ∀ i, S (Finset.univ.erase i) = ∑ j, S ((blocks j).erase i) := by
    intro i
    rw [hadd]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ext x
    simp
  have hU : S Finset.univ = ∑ j, S (blocks j) := by
    rw [hadd]; simp
  have hblock : ∀ j, ∑ i : Fin n, S ((blocks j).erase i) =
      ∑ i ∈ blocks j, S ((blocks j).erase i) + ((n : ℝ) - (blocks j).card) * S (blocks j) := by
    intro j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ blocks j)]
    have hf1 : Finset.univ.filter (fun i => i ∈ blocks j) = blocks j := by ext; simp
    rw [hf1]
    congr 1
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [Finset.erase_eq_of_notMem (by simpa using hi)]), Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => i ∈ blocks j)
    rw [hf1, Finset.card_univ, Fintype.card_fin] at hc
    rw [eq_sub_iff_add_eq]
    exact_mod_cast (by omega : (Finset.univ.filter (fun i => i ∉ blocks j)).card +
      (blocks j).card = n)
  unfold alternativeOn
  rw [← hS]
  rw [Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ n),
    Finset.sum_congr rfl (fun i _ => hE i), Finset.sum_comm, hU, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hblock j, Nat.cast_sub (Finset.card_pos.2 (hne j))]
  push_cast
  ring

end S193P43_final

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis) in
open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet) in
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P43 in
theorem solution {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (blocks : Fin m → Finset (Fin n))
    (hne : ∀ j, (blocks j).Nonempty)
    (hdis : ∀ j k, j ≠ k → Disjoint (blocks j) (blocks k))
    (hcover : Finset.univ.biUnion blocks = Finset.univ)
    (hprod : IsProductAcross rho blocks) :
    alternativeOn rho Finset.univ = ∑ j, alternativeOn rho (blocks j) :=
  S193P43_main hn hm rho hrho blocks hne hdis hcover hprod

