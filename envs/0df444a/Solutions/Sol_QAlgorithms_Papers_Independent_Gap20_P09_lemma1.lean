-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P09.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:29:51.101623+00:00
-- url     : https://prove2.me/submissions/915281d6-6495-4bea-a0c9-fff122e89ce5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P09
open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

lemma g74m_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g74m_submatrix_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (σ : Y ≃ X) (k : ℕ) :
    (A.submatrix σ σ) ^ k = (A ^ k).submatrix σ σ := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]

lemma g74m_trace_submatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix X X ℂ) (σ : Y ≃ X) : (A.submatrix σ σ).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp σ (fun i => A i i)

lemma g74m_cfc_trace_submatrix {X Y : Type*} [Fintype X] {_ : DecidableEq X} [Fintype Y]
    {_ : DecidableEq Y} (f : ℝ → ℝ) (hf : f 0 = 0)
    (A : Matrix X X ℂ) (σ : Y ≃ X) :
    (cfc f (A.submatrix σ σ)).trace = (cfc f A).trace := by
  by_cases hA : A.IsHermitian
  · exact g74m_trace_cfc_eq _ _ (hA.submatrix σ) hA _ hf
      (fun k => by rw [g74m_submatrix_pow, g74m_trace_submatrix])
  · have hB : ¬ (A.submatrix σ σ).IsHermitian := by
      intro hB
      apply hA
      have := hB.submatrix σ.symm
      simpa [Matrix.submatrix_submatrix] using this
    have hA' : ¬ IsSelfAdjoint A := hA
    have hB' : ¬ IsSelfAdjoint (A.submatrix σ σ) := hB
    rw [cfc_apply_of_not_predicate (A.submatrix σ σ) hB', cfc_apply_of_not_predicate A hA', Matrix.trace_zero, Matrix.trace_zero]

lemma g74m_entropy_submatrix {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    {_ : DecidableEq Y} (A : Matrix X X ℂ) (σ : Y ≃ X) :
    entropy (A.submatrix σ σ) = entropy A := by
  unfold entropy
  rw [g74m_cfc_trace_submatrix _ (by simp)]

lemma g74m_vn_eq {X : Type*} [Fintype X] {i1 : DecidableEq X} {i2 : DecidableEq X}
    (A : Matrix X X ℂ) :
    Real.log 2 * @QAlgorithms.vnEntropy X _ i1 A = @entropy X _ i2 A := by
  have hi : i1 = i2 := Subsingleton.elim _ _
  subst hi
  unfold QAlgorithms.vnEntropy entropy
  have h : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [h, cfc_const_mul _ _ _ (Real.continuous_mul_log.continuousOn)]
  rw [Matrix.trace_smul]
  have h2 : Real.log 2 ≠ 0 := by positivity
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  field_simp

def g74m_eU {n : ℕ} (D : Fin n → Type) : SubBasis D Finset.univ × Unit ≃ RegisterBasis D where
  toFun a i := a.1 ⟨i, Finset.mem_univ i⟩
  invFun x := (fun i => x i.1, ())
  left_inv a := by ext <;> rfl
  right_inv x := rfl

lemma g74m_regM_univ {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    registerMarginal (trivialExtension M) Finset.univ = M.submatrix (g74m_eU D) (g74m_eU D) := by
  ext a b
  simp only [registerMarginal, trivialExtension, Matrix.submatrix_apply]
  have key : ∀ x y : RegisterBasis D, ((∀ i (hi : i ∈ (Finset.univ : Finset (Fin n))),
      x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧ (∀ i, i ∉ (Finset.univ : Finset (Fin n)) → x i = y i))
      ↔ (x = g74m_eU D a ∧ y = g74m_eU D b) := by
    intro x y
    simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true,
      forall_true_left, funext_iff, g74m_eU, Equiv.coe_fn_mk]
    exact forall_and
  simp_rw [key, ite_and]
  simp

lemma g74m_sel_univ {l : ℕ} {D F : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    ∃ e : SubBasis D Finset.univ × RegisterBasis F ≃ RegisterBasis (fun i => D i × F i),
    selectUnprimed rho Finset.univ = rho.submatrix e e := by
  refine ⟨{ toFun := fun a i => (a.1 ⟨i, Finset.mem_univ i⟩, a.2 i)
            invFun := fun x => (fun i => (x i.1).1, fun i => (x i).2)
            left_inv := fun a => by ext <;> rfl
            right_inv := fun x => rfl }, ?_⟩
  ext a b
  simp only [selectUnprimed, Matrix.submatrix_apply, Equiv.coe_fn_mk]
  have key : ∀ x y : RegisterBasis D, ((∀ i (hi : i ∈ (Finset.univ : Finset (Fin l))),
      x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧ (∀ i, i ∉ (Finset.univ : Finset (Fin l)) → x i = y i))
      ↔ (x = (fun i => a.1 ⟨i, Finset.mem_univ i⟩) ∧ y = (fun i => b.1 ⟨i, Finset.mem_univ i⟩)) := by
    intro x y
    simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true,
      forall_true_left, funext_iff]
    exact forall_and
  simp_rw [key, ite_and]
  simp

def g74m_e0 {n : ℕ} (D : Fin n → Type) : SubBasis D ∅ × Unit ≃ Unit where
  toFun _ := ()
  invFun _ := (fun i => absurd i.2 (Finset.notMem_empty _), ())
  left_inv a := by
    ext i
    exact absurd i.2 (Finset.notMem_empty _)
  right_inv _ := rfl

lemma g74m_regM_empty {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    registerMarginal (trivialExtension M) ∅ =
      (Matrix.of fun _ _ : Unit => M.trace).submatrix (g74m_e0 D) (g74m_e0 D) := by
  ext a b
  simp only [registerMarginal, trivialExtension, Matrix.submatrix_apply, Matrix.of_apply,
    Finset.notMem_empty, IsEmpty.forall_iff, implies_true, not_false_eq_true, forall_const,
    true_and]
  have key : ∀ x y : RegisterBasis D, (∀ i, x i = y i) ↔ x = y := fun x y => funext_iff.symm
  simp_rw [key]
  simp [Matrix.trace]

lemma g74m_sel_empty {l : ℕ} {D F : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    ∃ e : SubBasis D ∅ × RegisterBasis F ≃ RegisterBasis F,
    selectUnprimed rho ∅ = (primedMarginal rho).submatrix e e := by
  refine ⟨{ toFun := fun a => a.2
            invFun := fun z => (fun i => absurd i.2 (Finset.notMem_empty _), z)
            left_inv := fun a => by
              ext i
              · exact absurd i.2 (Finset.notMem_empty _)
              · rfl
            right_inv := fun x => rfl }, ?_⟩
  ext a b
  simp only [selectUnprimed, primedMarginal, Matrix.submatrix_apply, Equiv.coe_fn_mk,
    Finset.notMem_empty, IsEmpty.forall_iff, implies_true, not_false_eq_true, forall_const,
    true_and]
  have key : ∀ x y : RegisterBasis D, (∀ i, x i = y i) ↔ x = y := fun x y => funext_iff.symm
  simp_rw [key]
  simp

lemma g74m_trace_primed {l : ℕ} {D F : Fin l → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    (primedMarginal rho).trace = rho.trace := by
  let e : RegisterBasis F × RegisterBasis D ≃ RegisterBasis (fun i => D i × F i) :=
    { toFun := fun p i => (p.2 i, p.1 i)
      invFun := fun x => (fun i => (x i).2, fun i => (x i).1)
      left_inv := fun p => rfl
      right_inv := fun x => rfl }
  simp only [Matrix.trace, Matrix.diag, primedMarginal]
  rw [← Fintype.sum_prod_type', ← e.sum_comp]
  rfl

lemma g74m_ent_congr {n : ℕ} {D : Fin n → Type} {_ : ∀ i, Fintype (D i)}
    (M : Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ) {s t : Finset (Fin n)}
    (h : s = t) {f1 : Fintype (SubBasis D s × Unit)} {i1 : DecidableEq (SubBasis D s × Unit)}
    {f2 : Fintype (SubBasis D t × Unit)} {i2 : DecidableEq (SubBasis D t × Unit)} :
    @entropy _ f1 i1 (registerMarginal M s) = @entropy _ f2 i2 (registerMarginal M t) := by
  subst h
  rw [Subsingleton.elim f1 f2, Subsingleton.elim i1 i2]

lemma g74m_ent_union_empty {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ) (s : Finset (Fin n))
    {f1 : Fintype (SubBasis D (s ∪ ∅) × Unit)} {i1 : DecidableEq (SubBasis D (s ∪ ∅) × Unit)} :
    @entropy _ f1 i1 (registerMarginal M (s ∪ ∅)) = entropy (registerMarginal M s) :=
  g74m_ent_congr M (Finset.union_empty s)

lemma g74m_ent_single {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ) (x : Fin n)
    {f1 : Fintype (SubBasis D (singleParties n x ∪ ∅) × Unit)}
    {i1 : DecidableEq (SubBasis D (singleParties n x ∪ ∅) × Unit)} :
    @entropy _ f1 i1 (registerMarginal M (singleParties n x ∪ ∅)) =
      entropy (registerMarginal M {x}) :=
  g74m_ent_congr M (by simp [singleParties])

lemma g74m_ent_all {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ)
    {f1 : Fintype (SubBasis D (allParties (singleParties n) ∪ ∅) × Unit)}
    {i1 : DecidableEq (SubBasis D (allParties (singleParties n) ∪ ∅) × Unit)} :
    @entropy _ f1 i1 (registerMarginal M (allParties (singleParties n) ∪ ∅)) =
      entropy (registerMarginal M Finset.univ) :=
  g74m_ent_congr M (by ext i; simp [allParties, singleParties])

lemma g74m_ent_regM_inst {n : ℕ} {D : Fin n → Type} (I1 I2 : ∀ i, Fintype (D i))
    (M : Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ) (s : Finset (Fin n))
    {f1 f2 : Fintype (SubBasis D s × Unit)} {i1 i2 : DecidableEq (SubBasis D s × Unit)} :
    @entropy _ f1 i1 (@registerMarginal n D I1 Unit M s) =
      @entropy _ f2 i2 (@registerMarginal n D I2 Unit M s) := by
  rw [Subsingleton.elim I1 I2, Subsingleton.elim f1 f2, Subsingleton.elim i1 i2]

lemma g74m_ent_empty {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (M : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    {f1 : Fintype (SubBasis D ∅ × Unit)} {i1 : DecidableEq (SubBasis D ∅ × Unit)} :
    @entropy _ f1 i1 (registerMarginal (trivialExtension M) ∅) =
      entropy (Matrix.of fun _ _ : Unit => M.trace) := by
  rw [Subsingleton.elim f1 inferInstance, Subsingleton.elim i1 inferInstance, g74m_regM_empty,
    g74m_entropy_submatrix]

lemma g74m_vn_eq' {X : Type*} [Fintype X] {i1 : DecidableEq X}
    (A : Matrix X X ℂ) :
    @QAlgorithms.vnEntropy X _ i1 A = entropy A / Real.log 2 := by
  have h2 : Real.log 2 ≠ 0 := by positivity
  rw [← g74m_vn_eq (i1 := i1) A]
  field_simp

/-- PDF p.5, Lemma 1,(3.1): the full paired CMI expansion in EVERY order. -/
theorem solution {l : ℕ} (hl : 0 < l) {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∀ order : Equiv.Perm (Fin l), informationGap rho = ∑ k, chainTerm rho order k := by
  intro order
  set pairE : Fin l → ℝ := fun i => entropy (registerMarginal (trivialExtension rho) {i})
    with hpairE
  set primE : Fin l → ℝ := fun i =>
    entropy (registerMarginal (trivialExtension (primedMarginal rho)) {i}) with hprimE
  set S : Finset (Fin l) → ℝ := fun s => entropy (selectUnprimed rho s) with hS
  have hgap : informationGap rho = (∑ i, pairE i) - entropy rho - (∑ i, primE i) +
      entropy (primedMarginal rho) := by
    unfold informationGap multipartiteInformationNats info conditionalMultipartiteInformation
      entropyAt
    simp only [g74m_vn_eq']
    simp only [g74m_ent_single, g74m_ent_all]
    rw [g74m_regM_univ, g74m_regM_univ, g74m_entropy_submatrix, g74m_entropy_submatrix,
      g74m_ent_empty, g74m_ent_empty, g74m_trace_primed]
    have h2 : Real.log 2 ≠ 0 := by positivity
    simp only [hpairE, hprimE]
    rw [← Finset.sum_div, ← Finset.sum_div]
    field_simp
    have hfin : ∀ a a' b c d e : ℝ, a = a' → a - b - e - (c - d - e) = a' - b - c + d := by
      intro a a' b c d e h; subst h; ring
    exact hfin _ _ _ _ _ _ (Finset.sum_congr rfl fun i _ => g74m_ent_regM_inst _ _ _ _)
  have hSu : S Finset.univ = entropy rho := by
    obtain ⟨e, he⟩ := g74m_sel_univ (D := D) (F := F) rho
    simp only [hS, he, g74m_entropy_submatrix]
  have hS0 : S ∅ = entropy (primedMarginal rho) := by
    obtain ⟨e, he⟩ := g74m_sel_empty (D := D) (F := F) rho
    simp only [hS, he, g74m_entropy_submatrix]
  set P : ℕ → Finset (Fin l) := fun n =>
    (Finset.univ.filter fun r : Fin l => r.val < n).image order with hPdef
  have hP : ∀ k : Fin l, insert (order k) (P k.val) = P (k.val + 1) := by
    intro k
    ext x
    simp only [hPdef, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (rfl | ⟨r, hr, rfl⟩)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨r, by omega, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
      · exact Or.inr ⟨r, h, rfl⟩
      · exact Or.inl (by rw [Fin.ext h])
  have hP0 : P 0 = ∅ := by simp [hPdef]
  have hPl : P l = Finset.univ := by
    ext x
    simp only [hPdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨order.symm x, (order.symm x).2, by simp⟩
  have hct : ∀ k : Fin l, chainTerm rho order k =
      (pairE (order k) - primE (order k)) - (S (P (k.val + 1)) - S (P k.val)) := by
    intro k
    show entropy _ - entropy _ - entropy (selectUnprimed rho (insert (order k) (P k.val))) +
      entropy (selectUnprimed rho (P k.val)) = _
    rw [hP k]
    simp only [hpairE, hprimE, hS]
    ring
  have htel : ∑ k : Fin l, (S (P (k.val + 1)) - S (P k.val)) = S (P l) - S (P 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => S (P (n + 1)) - S (P n)) l,
      Finset.sum_range_sub (fun n => S (P n))]
  have hA : ∑ k, pairE (order k) = ∑ i, pairE i := Equiv.sum_comp order pairE
  have hB : ∑ k, primE (order k) = ∑ i, primE i := Equiv.sum_comp order primE
  rw [Finset.sum_congr rfl (fun k _ => hct k), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    htel, hA, hB, hP0, hPl, hSu, hS0, hgap]
  ring

end
