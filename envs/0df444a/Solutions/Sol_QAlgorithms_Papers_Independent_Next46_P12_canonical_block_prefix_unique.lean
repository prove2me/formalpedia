-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P12.canonical_block_prefix_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:41:06.166644+00:00
-- url     : https://prove2.me/submissions/322e301c-a775-473e-8c17-1e88a5a5f051

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12
noncomputable section

open scoped BigOperators Classical

open Filter

open QAlgorithms.Papers.Independent.Next46.P12

universe u v w

namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

lemma block (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A) (i : D.Label) :
    D.equiv z i = algebraMap k _ (centralSpectrum D z i) := by
  have hc : ∀ M, Commute M (D.equiv z i) := by
    intro M
    have := (Subalgebra.mem_center_iff.mp hz) (D.equiv.symm (Pi.single i M))
    have h2 := congrArg (fun x => D.equiv x i) this
    simp only [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same] at h2
    exact h2
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun a b => hc _)
  have : centralSpectrum D z i = r := by
    simp [centralSpectrum, ← hr]
  rw [this, ← hr]; rfl

lemma mem_center_of (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) : z ∈ Subalgebra.center k A := by
  rw [Subalgebra.mem_center_iff]
  intro b
  apply D.equiv.injective
  funext i
  simp only [map_mul, Pi.mul_apply, h i]
  exact (Algebra.commutes _ _).symm

lemma spec_alg (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) (i : D.Label) : centralSpectrum D z i = c i := by
  simp only [centralSpectrum, h i, Matrix.algebraMap_matrix_apply]; simp

lemma spec_aeval (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A)
    (p : Polynomial k) (j : D.Label) :
    D.equiv (Polynomial.aeval z p) j = algebraMap k _ (p.eval (centralSpectrum D z j)) := by
  have : D.equiv (Polynomial.aeval z p) j =
      ((Pi.evalAlgHom k _ j).comp D.equiv.toAlgHom) (Polynomial.aeval z p) := rfl
  rw [this, ← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (D.equiv z j) p = _
  rw [block D hz j, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

lemma ci_block (D : SplitPresentation k A) (i j : D.Label) :
    D.equiv (centralIdempotent D i) j = algebraMap k _ (if j = i then 1 else 0) := by
  simp only [centralIdempotent, blockElement, AlgEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma eval_cp (D : SplitPresentation k A) (z : A) (hinj : Function.Injective (centralSpectrum D z))
    (i j : D.Label) :
    (centralPolynomial D z i).eval (centralSpectrum D z j) = if j = i then 1 else 0 := by
  unfold centralPolynomial
  rw [Polynomial.eval_prod]
  by_cases h : j = i
  · subst h
    simp only [if_true]
    apply Finset.prod_eq_one
    intro l hl
    have hne : centralSpectrum D z j - centralSpectrum D z l ≠ 0 :=
      sub_ne_zero.mpr (fun e => (Finset.ne_of_mem_erase hl) (hinj e).symm)
    simp [interpolationFactor, hne]
  · simp only [h, if_false]
    apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    simp [interpolationFactor]

theorem crit [FiniteDimensional k A] (D : SplitPresentation k A) (z : A)
    (hz : z ∈ Subalgebra.center k A) :
    GeneratesCenter (k := k) z ↔ Function.Injective (centralSpectrum D z) := by
  constructor
  · intro hg i j hij
    by_contra hne
    have hm : centralIdempotent D i ∈ Algebra.adjoin k ({z} : Set A) := by
      rw [hg]; exact mem_center_of D _ _ (ci_block D i)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨p, hp⟩ := hm
    have h1 := spec_alg D _ _ (ci_block D i) i
    have h2 := spec_alg D _ _ (ci_block D i) j
    have e1 := spec_alg D _ _ (spec_aeval D hz p) i
    have e2 := spec_alg D _ _ (spec_aeval D hz p) j
    change Polynomial.aeval z p = _ at hp
    rw [hp] at e1 e2
    rw [e1, if_pos rfl] at h1
    rw [e2, if_neg (Ne.symm hne), ← hij] at h2
    rw [h1] at h2; exact one_ne_zero h2
  · intro hinj
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]; intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hz
    · intro w hw
      let P : Polynomial k := ∑ i, Polynomial.C (centralSpectrum D w i) * centralPolynomial D z i
      have : w = Polynomial.aeval z P := by
        apply D.equiv.injective
        funext j
        rw [spec_aeval D hz, block D hw]
        congr 1
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          eval_cp D z hinj]
        simp
      rw [this]; exact Polynomial.aeval_mem_adjoin_singleton k z

end G62K

namespace G62K

lemma desc_cast (q m : ℕ) : (q.descFactorial m : ℝ) = ∏ i ∈ Finset.range m, ((q : ℝ) - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    by_cases h : m ≤ q
    · rw [Nat.cast_sub h]; ring
    · have h0 : q.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0] at ih
      rw [← ih]; simp

lemma frac_eq (m q : ℕ) (hq : q ≠ 0) :
    generatorFraction m q = (∏ i ∈ Finset.range m, ((q : ℝ) - i)) / (q : ℝ) ^ m := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  unfold generatorFraction
  rw [show (q:ℝ)^m = ∏ _i ∈ Finset.range m, (q:ℝ) by simp, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  field_simp

lemma frac_lim (m : ℕ) : Filter.Tendsto (generatorFraction m) Filter.atTop (nhds 1) := by
  unfold generatorFraction
  rw [show (nhds (1:ℝ)) = nhds (∏ i ∈ Finset.range m, (1 - (0:ℝ))) by simp]
  apply tendsto_finsetProd
  intro i _
  exact tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

def cenEquiv (D : SplitPresentation k A) : Subalgebra.center k A ≃ (D.Label → k) where
  toFun z := centralSpectrum D (z : A)
  invFun f := ⟨D.equiv.symm (fun i => algebraMap k _ (f i)),
    mem_center_of D _ f (fun i => by simp)⟩
  left_inv z := by
    apply Subtype.ext
    apply D.equiv.injective
    funext i
    simp [block D z.2 i]
  right_inv f := funext (spec_alg D _ f (fun i => by simp))

end G62K
namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

def bas (D : SplitPresentation k A) : Module.Basis (Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) k A :=
  (Pi.basis fun i => Matrix.stdBasis k (Fin (D.size i)) (Fin (D.size i))).map D.equiv.symm.toLinearEquiv

lemma bas_repr (D : SplitPresentation k A) (x : A) (p : Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) :
    (bas D).repr x p = D.equiv x p.1 p.2.1 p.2.2 := by
  simp [bas, Matrix.stdBasis]

lemma bas_apply (D : SplitPresentation k A) (p : Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) :
    D.equiv (bas D p) = Pi.single p.1 (Matrix.single p.2.1 p.2.2 1) := by
  simp only [bas, Module.Basis.map_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Pi.basis_apply]
  rw [Matrix.stdBasis_eq_single]

lemma reg (D : SplitPresentation k A) (a : A) :
    regularCharacter (k := k) a = ∑ lam : D.Label, simpleCharacter D lam 1 * simpleCharacter D lam a := by
  unfold regularCharacter
  rw [LinearMap.trace_eq_matrix_trace k (bas D)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, bas_repr]
  have h : ∀ p : (Σ i : D.Label, Fin (D.size i) × Fin (D.size i)),
      D.equiv (leftRegularAction (k := k) a (bas D p)) p.1 p.2.1 p.2.2 = D.equiv a p.1 p.2.1 p.2.1 := by
    intro p
    simp only [leftRegularAction, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Pi.mul_apply, bas_apply,
      Pi.single_eq_same]
    simp [Matrix.mul_apply, Matrix.single_apply]
  simp only [h]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro lam _
  rw [Fintype.sum_prod_type]
  simp [simpleCharacter, Matrix.trace, Finset.mul_sum]

lemma tau_eq (a : A) : regularCharacter (k := k) a = LinearMap.trace k A (LinearMap.mul k A a) := by
  unfold regularCharacter; congr 1

lemma tau_sum {I : Type*} [Fintype I] (c : I → k) (z : I → A) :
    regularCharacter (k := k) (∑ i, c i • z i) = ∑ i, c i * regularCharacter (k := k) (z i) := by
  simp only [tau_eq, map_sum, map_smul, smul_eq_mul]

lemma ci_mul (D : SplitPresentation k A) (lam mu : D.Label) (x : A) :
    simpleCharacter D mu (centralIdempotent D lam * x) =
      if mu = lam then simpleCharacter D lam x else 0 := by
  unfold simpleCharacter
  rw [map_mul, Pi.mul_apply]
  simp only [centralIdempotent, blockElement, AlgEquiv.apply_symm_apply]
  by_cases h : mu = lam
  · subst h; simp
  · simp [h]

lemma tau_e (D : SplitPresentation k A) (lam : D.Label) (x : A) :
    regularCharacter (k := k) (centralIdempotent D lam * x) =
      simpleCharacter D lam 1 * simpleCharacter D lam x := by
  rw [reg D]
  simp only [ci_mul]
  simp

lemma Tmul {I : Type*} [Fintype I] (b : Module.Basis I k A) (c : I → k) (i : I) :
    (Matrix.mulVec (traceMatrix b) c) i = regularCharacter (k := k) ((∑ j, c j • b j) * b i) := by
  simp only [Matrix.mulVec, dotProduct, traceMatrix, Finset.sum_mul, smul_mul_assoc, tau_sum]
  apply Finset.sum_congr rfl; intro j _; ring

lemma det_ne [CharZero k] (D : SplitPresentation k A) {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I k A) : (traceMatrix b).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y := ∑ j, c j • b j with hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c h0 j
  have hall : ∀ x : A, regularCharacter (k := k) (y * x) = 0 := by
    intro x
    rw [← b.sum_repr x, Finset.mul_sum]
    simp only [mul_smul_comm, tau_sum]
    apply Finset.sum_eq_zero; intro i _
    rw [← Tmul, hc]; simp
  have hY : D.equiv y ≠ 0 := by
    intro h; exact hy0 (D.equiv.injective (by rw [h, map_zero]))
  obtain ⟨lam, hlam⟩ := Function.ne_iff.mp hY
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hlam
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hp
  have := hall (D.equiv.symm (Pi.single lam (Matrix.single q p 1)))
  rw [reg D] at this
  rw [Finset.sum_eq_single lam] at this
  · simp only [simpleCharacter, map_one, Pi.one_apply, Matrix.trace_one, map_mul,
      AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same, Matrix.trace_mul_single] at this
    simp at this
    rcases this with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (D.positive lam).ne')
    · exact hq h
  · intro mu _ hmu
    simp [simpleCharacter, Pi.single_eq_of_ne hmu]
  · simp
end G62K
namespace G62K
variable {k : Type u} [Field k]

lemma tau_single {G : Type v} [Group G] [Fintype G] (h : G) :
    regularCharacter (k := k) (MonoidAlgebra.single h (1 : k)) =
      if h = 1 then (Fintype.card G : k) else 0 := by
  rw [tau_eq, LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    LinearMap.mul_apply', MonoidAlgebra.single_mul_single, mul_one]
  have : ∀ i : G, (MonoidAlgebra.basis G k).repr (MonoidAlgebra.single (h * i) 1) i =
      if h = 1 then 1 else 0 := by
    intro i
    change (MonoidAlgebra.single (h * i) (1:k)).coeff i = _
    rw [MonoidAlgebra.coeff_single_apply]
    simp
  simp only [this]
  split_ifs <;> simp
end G62K

namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

lemma ci_mem (D : SplitPresentation k A) (i : D.Label) :
    centralIdempotent D i ∈ Subalgebra.center k A := mem_center_of D _ _ (ci_block D i)

lemma ci_idem (D : SplitPresentation k A) (i : D.Label) :
    centralIdempotent D i * centralIdempotent D i = centralIdempotent D i := by
  apply D.equiv.injective; funext j
  simp only [map_mul, Pi.mul_apply, ci_block]
  split_ifs <;> simp

lemma ci_orth (D : SplitPresentation k A) (i j : D.Label) (h : i ≠ j) :
    centralIdempotent D i * centralIdempotent D j = 0 := by
  apply D.equiv.injective; funext l
  simp only [map_mul, Pi.mul_apply, ci_block, map_zero, Pi.zero_apply]
  split_ifs with h1 h2 <;> simp_all

lemma central_mul_ci (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A)
    (i : D.Label) : z * centralIdempotent D i = centralSpectrum D z i • centralIdempotent D i := by
  apply D.equiv.injective; funext j
  simp only [map_mul, Pi.mul_apply, ci_block, map_smul, Pi.smul_apply, block D hz]
  split_ifs with h
  · subst h; simp [Algebra.smul_def]
  · simp

lemma list_absorb {x : A} (hx : x * x = x) : ∀ (L : List A), x ∈ L → (∀ a ∈ L, Commute x a) →
    x * L.prod = L.prod
  | [], h, _ => by simp at h
  | y :: L, h, hc => by
    rw [List.prod_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; rw [← mul_assoc, hx]
    · rw [← mul_assoc, (hc y (by simp)).eq, mul_assoc,
        list_absorb hx L h (fun a ha => hc a (by simp [ha]))]

section T
variable {AA : ℕ → Type v} [∀ n, Ring (AA n)] [∀ n, Algebra k (AA n)] (D : Tower k AA)

lemma incc {i j l : ℕ} (h1 : i ≤ j) (h2 : j ≤ l) (x : AA i) :
    D.inc j l h2 (D.inc i j h1 x) = D.inc i l (h1.trans h2) x :=
  DFunLike.congr_fun (D.inc_comp i j l h1 h2) x

lemma inc_id {i : ℕ} (h : i ≤ i) (x : AA i) : D.inc i i h x = x := by
  rw [D.inc_self]; rfl

def Gen (n : ℕ) : Set (AA n) :=
  {a | ∃ i, ∃ hi : i ≤ n, ∃ z : Subalgebra.center k (AA i), D.inc i n hi z = a}

lemma gtA_eq (n : ℕ) : towerGTAlgebra D n = Algebra.adjoin k (Gen D n) := rfl

lemma gen_comm (n : ℕ) {a b : AA n} (ha : a ∈ Gen D n) (hb : b ∈ Gen D n) : Commute a b := by
  obtain ⟨i, hi, z, rfl⟩ := ha
  obtain ⟨j, hj, w, rfl⟩ := hb
  rcases le_total i j with h | h
  · rw [← incc D h hj]
    have := (Subalgebra.mem_center_iff.mp w.2) (D.inc i j h z)
    show _ = _
    rw [← map_mul, ← map_mul, this]
  · rw [← incc D h hi]
    have := (Subalgebra.mem_center_iff.mp z.2) (D.inc j i h w)
    show _ = _
    rw [← map_mul, ← map_mul, this]

lemma X_comm (n : ℕ) {a b : AA n} (ha : a ∈ towerGTAlgebra D n) (hb : b ∈ towerGTAlgebra D n) :
    Commute a b := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb
  intro y hy
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha
    (fun x hx => gen_comm D n hy hx)).symm

lemma E_gen {i n : ℕ} (hi : i ≤ n) (lam : (D.split i).Label) :
    D.inc i n hi (centralIdempotent (D.split i) lam) ∈ Gen D n :=
  ⟨i, hi, ⟨_, ci_mem _ lam⟩, rfl⟩

lemma pe_list_mem {n : ℕ} (t : TowerPath D n) : ∀ x ∈ (List.ofFn fun i : Fin n => D.inc (i.val + 1) n (by omega)
    (centralIdempotent (D.split (i.val + 1)) (towerVertex D t (i.val + 1) (by omega)))), x ∈ Gen D n := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact E_gen D _ _

lemma pe_mem {n : ℕ} (t : TowerPath D n) : pathIdempotent D t ∈ towerGTAlgebra D n := by
  unfold pathIdempotent
  apply Subalgebra.list_prod_mem
  intro x hx
  exact Algebra.subset_adjoin (pe_list_mem D t x hx)

lemma pe_absorb {n : ℕ} (t : TowerPath D n) (j : ℕ) (hj : j + 1 ≤ n) :
    D.inc (j + 1) n hj (centralIdempotent (D.split (j + 1)) (t.val ⟨j + 1, by omega⟩)) *
      pathIdempotent D t = pathIdempotent D t := by
  unfold pathIdempotent
  apply list_absorb
  · rw [← map_mul, ci_idem]
  · exact List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩
  · intro a ha
    exact gen_comm D n (E_gen D _ _) (pe_list_mem D t a ha)

lemma base_alg (z : AA 0) : z = algebraMap k (AA 0) (D.base z) := by
  apply D.base.injective
  simp

lemma X_scalar {n : ℕ} (t : TowerPath D n) {a : AA n} (ha : a ∈ towerGTAlgebra D n) :
    ∃ c : k, a * pathIdempotent D t = c • pathIdempotent D t := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, z, rfl⟩ := hx
    cases i with
    | zero =>
      refine ⟨D.base z, ?_⟩
      rw [base_alg D (z : AA 0), AlgHom.commutes, Algebra.smul_def]
      simp
    | succ j =>
      refine ⟨centralSpectrum (D.split (j+1)) (z : AA (j+1)) (t.val ⟨j + 1, by omega⟩), ?_⟩
      rw [← pe_absorb D t j hi, ← mul_assoc, ← map_mul, central_mul_ci _ z.2, map_smul,
        smul_mul_assoc]
  | algebraMap r => exact ⟨r, by rw [Algebra.smul_def]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [add_mul, hc, hd, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, by rw [mul_assoc, hd, mul_smul_comm, hc, smul_smul]⟩

lemma pe_succ {n : ℕ} (t : TowerPath D (n+1)) :
    pathIdempotent D t = D.inc n (n+1) (Nat.le_succ n)
      (pathIdempotent D (towerPrefix D t n (Nat.le_succ n))) *
      centralIdempotent (D.split (n+1)) (towerTerminal D t) := by
  unfold pathIdempotent
  rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton, map_list_prod, List.map_ofFn]
  congr 1
  · refine congrArg _ (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply]; rw [incc]; rfl
  · exact inc_id D _ _

lemma pe_zero (t : TowerPath D 0) : pathIdempotent D t = 1 := by simp [pathIdempotent]

lemma ps_succ (J : (i : ℕ) → AA (i + 1)) (n : ℕ) :
    towerPartialSum D J (n+1) = D.inc n (n+1) (Nat.le_succ n) (towerPartialSum D J n) + J n := by
  unfold towerPartialSum embeddedSequence initialSequence
  rw [List.ofFn_succ_last, List.sum_append, List.sum_singleton, map_list_sum, List.map_ofFn]
  congr 1
  · refine congrArg _ (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply]; rw [incc]; rfl
  · exact inc_id D _ _

lemma central_on_path {n : ℕ} {z : AA n} (hz : z ∈ Subalgebra.center k (AA n)) (t : TowerPath D n) :
    z * pathIdempotent D t = centralSpectrum (D.split n) z (towerTerminal D t) • pathIdempotent D t := by
  cases n with
  | zero =>
    rw [pe_zero]
    have hb : ∀ i, (D.split 0).equiv z i = algebraMap k _ (D.base z) := by
      intro i; conv_lhs => rw [base_alg D z]
      rw [AlgEquiv.commutes]; rfl
    rw [spec_alg _ _ _ hb, mul_one, Algebra.smul_def, mul_one]
    exact base_alg D z
  | succ m =>
    rw [pe_succ D t, ← mul_assoc, ((Subalgebra.mem_center_iff.mp hz) _).symm, mul_assoc,
      central_mul_ci _ hz, mul_smul_comm]

end T

lemma sa_mul (D : SplitPresentation k A) (i : D.Label) (a b : A) :
    simpleAction D i (a * b) = simpleAction D i a ∘ₗ simpleAction D i b := by
  simp [simpleAction, Matrix.toLin'_mul]

lemma sa_one (D : SplitPresentation k A) (i : D.Label) :
    simpleAction D i 1 = LinearMap.id := by
  simp [simpleAction]

lemma sa_ci_self (D : SplitPresentation k A) (i : D.Label) :
    simpleAction D i (centralIdempotent D i) = LinearMap.id := by
  simp [simpleAction, ci_block]

lemma sa_ci_ne (D : SplitPresentation k A) (i j : D.Label) (h : j ≠ i) :
    simpleAction D i (centralIdempotent D j) = 0 := by
  simp [simpleAction, ci_block, Ne.symm h]

lemma hom_inj {B : Type*} [Ring B] [Algebra k B]
    (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (mu : DB.Label) (lam : DA.Label) (f : SimpleSpace DB mu →ₗ[k] SimpleSpace DA lam)
    (hf : f ∈ restrictionHom DB DA inc mu lam) (hf0 : f ≠ 0) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  apply hf0
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hx0
  refine LinearMap.ext fun y => ?_
  let M : Matrix (Fin (DB.size mu)) (Fin (DB.size mu)) k :=
    Matrix.of fun i j => if j = p then y i / x p else 0
  have hM : simpleAction DB mu (DB.equiv.symm (Pi.single mu M)) x = y := by
    funext i
    have hp' : x p ≠ 0 := hp
    simp [simpleAction, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, M]
    field_simp
  rw [← hM, hf, hx, map_zero]; rfl


lemma one_sum_single (d : ℕ) : (1 : Matrix (Fin d) (Fin d) k) = ∑ j, Matrix.single j j 1 := by
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single a (fun x _ hx => by simp [Matrix.single_apply, hx])
    (by simp)]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.single_apply, Matrix.one_apply, h]

lemma sa_zero_mul (D : SplitPresentation k A) (x : A) (lam : D.Label)
    (h : simpleAction D lam x = 0) : x * centralIdempotent D lam = 0 := by
  apply D.equiv.injective; funext j
  simp only [map_mul, Pi.mul_apply, ci_block, map_zero, Pi.zero_apply]
  split_ifs with hj
  · subst hj
    have : D.equiv x j = 0 := by
      have := congrArg LinearMap.toMatrix' h
      simpa [simpleAction] using this
    simp [this]
  · simp

def colmat {d : ℕ} (j : Fin d) (v : Fin d → k) : Matrix (Fin d) (Fin d) k :=
  Matrix.of fun i l => if l = j then v i else 0

lemma branch_exists {B : Type*} [Ring B] [Algebra k B]
    (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (mu : DB.Label) (lam : DA.Label)
    (h : simpleAction DA lam (inc (centralIdempotent DB mu)) ≠ 0) :
    ∃ f : SimpleSpace DB mu →ₗ[k] SimpleSpace DA lam, f ∈ restrictionHom DB DA inc mu lam ∧ f ≠ 0 := by
  let β : Matrix (Fin (DB.size mu)) (Fin (DB.size mu)) k → B := fun M => DB.equiv.symm (Pi.single mu M)
  let P : B → (SimpleSpace DA lam →ₗ[k] SimpleSpace DA lam) := fun b => simpleAction DA lam (inc b)
  have hPm : ∀ a b, P (a * b) = P a ∘ₗ P b := fun a b => by simp only [P, map_mul, sa_mul]
  have hPa : ∀ a b, P (a + b) = P a + P b := fun a b => by
    simp only [P, map_add, simpleAction, Pi.add_apply, map_add]
  have hPs : ∀ (c : k) a, P (c • a) = c • P a := fun c a => by
    simp only [P, map_smul, simpleAction, Pi.smul_apply, map_smul]
  have hβm : ∀ M N, β M * β N = β (M * N) := fun M N => by
    apply DB.equiv.injective; funext l
    simp only [β, map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply]
    by_cases hl : l = mu
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  have hβb : ∀ b M, b * β M = β (DB.equiv b mu * M) := fun b M => by
    apply DB.equiv.injective; funext l
    simp only [β, map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply]
    by_cases hl : l = mu
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  have hβa : ∀ M N, β (M + N) = β M + β N := fun M N => by
    simp only [β, Pi.single_add, map_add]
  have hβs : ∀ (c : k) M, β (c • M) = c • β M := fun c M => by
    simp only [β, Pi.single_smul, map_smul]
  have hβsum : ∀ (s : Finset (Fin (DB.size mu))) (F : Fin (DB.size mu) → Matrix _ _ k),
      β (∑ j ∈ s, F j) = ∑ j ∈ s, β (F j) := fun s F => by
    simp only [β, Finset.univ, ← map_sum]
    congr 1
    funext l
    by_cases hl : l = mu
    · subst hl; simp [Finset.sum_apply]
    · simp [Pi.single_eq_of_ne hl, Finset.sum_apply]
  have hE : centralIdempotent DB mu = ∑ j, β (Matrix.single j j 1) := by
    rw [← hβsum, ← one_sum_single]; rfl
  obtain ⟨w, hw⟩ : ∃ w, P (centralIdempotent DB mu) w ≠ 0 := by
    by_contra hc; push Not at hc; exact h (LinearMap.ext hc)
  obtain ⟨j, hj⟩ : ∃ j, P (β (Matrix.single j j 1)) w ≠ 0 := by
    by_contra hc; push Not at hc
    apply hw
    rw [hE]
    have : ∀ (s : Finset (Fin (DB.size mu))), P (∑ j ∈ s, β (Matrix.single j j 1)) w = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [P, simpleAction]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, hPa, LinearMap.add_apply, ih, hc a, add_zero]
    exact this Finset.univ
  set w0 := P (β (Matrix.single j j 1)) w with hw0
  let f : SimpleSpace DB mu →ₗ[k] SimpleSpace DA lam :=
    { toFun := fun v => P (β (colmat j v)) w0
      map_add' := fun v v' => by
        have : colmat j (v + v') = colmat j v + colmat j v' := by
          ext a b; simp only [colmat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
          split_ifs <;> simp
        rw [this, hβa, hPa, LinearMap.add_apply]
      map_smul' := fun c v => by
        have : colmat j (c • v) = c • colmat j v := by
          ext a b; simp only [colmat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
          split_ifs <;> simp
        rw [this, hβs, hPs, LinearMap.smul_apply]; rfl }
  refine ⟨f, ?_, ?_⟩
  · intro b v
    show P (β (colmat j (simpleAction DB mu b v))) w0 = simpleAction DA lam (inc b) (P (β (colmat j v)) w0)
    have : colmat j (simpleAction DB mu b v) = DB.equiv b mu * colmat j v := by
      ext a l
      simp only [colmat, simpleAction, Matrix.toLin'_apply, Matrix.of_apply, Matrix.mul_apply]
      split_ifs with hl
      · simp [Matrix.mulVec, dotProduct]
      · simp
    rw [this, ← hβb, hPm]; rfl
  · intro hf
    have := LinearMap.congr_fun hf (Pi.single j 1)
    have hc : colmat j (Pi.single j (1:k)) = Matrix.single j j 1 := by
      ext a b; simp only [colmat, Matrix.of_apply, Matrix.single_apply]
      by_cases hb : b = j
      · subst hb; by_cases ha : a = b
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · simp [hb, Ne.symm hb]
    change P (β (colmat j (Pi.single j 1))) w0 = 0 at this
    rw [hc, hw0, ← LinearMap.comp_apply, ← hPm, hβm, Matrix.single_mul_single_same, mul_one] at this
    exact hj this

lemma ci_sum (D : SplitPresentation k A) : ∑ i, centralIdempotent D i = 1 := by
  apply D.equiv.injective; funext j
  rw [map_sum, Finset.sum_apply]
  simp [ci_block]

lemma ci_ne (D : SplitPresentation k A) (i : D.Label) : centralIdempotent D i ≠ 0 := by
  intro h0
  have := congrArg (fun x => D.equiv x i ⟨0, D.positive i⟩ ⟨0, D.positive i⟩) h0
  simp [ci_block] at this

section T2
variable {AA : ℕ → Type v} [∀ n, Ring (AA n)] [∀ n, Algebra k (AA n)] (D : Tower k AA)

lemma pe_sa_ne : ∀ (n : ℕ) (t : TowerPath D n),
    simpleAction (D.split n) (towerTerminal D t) (pathIdempotent D t) ≠ 0
  | 0, t => by
    rw [pe_zero, sa_one]
    intro h
    have := LinearMap.congr_fun h (Pi.single ⟨0, (D.split 0).positive _⟩ 1)
    simp at this
  | n + 1, t => by
    rw [pe_succ D t, sa_mul, sa_ci_self, LinearMap.comp_id]
    have hB := t.property ⟨n, by omega⟩
    unfold Branch at hB
    obtain ⟨⟨f, hf⟩, hf0⟩ := (nontrivial_iff_exists_ne 0).mp (Module.nontrivial_of_finrank_pos hB)
    have hf0' : f ≠ 0 := fun h => hf0 (Subtype.ext h)
    have ih := pe_sa_ne n (towerPrefix D t n (Nat.le_succ n))
    obtain ⟨v, hv⟩ : ∃ v, simpleAction (D.split n) (towerTerminal D (towerPrefix D t n (Nat.le_succ n)))
        (pathIdempotent D (towerPrefix D t n (Nat.le_succ n))) v ≠ 0 := by
      by_contra h; push Not at h; exact ih (LinearMap.ext h)
    intro h0
    have := hf (pathIdempotent D (towerPrefix D t n (Nat.le_succ n))) v
    have hinj := hom_inj _ _ _ _ _ f hf hf0'
    apply hv
    apply hinj
    exact this.trans ((LinearMap.congr_fun h0 (f v)).trans (map_zero f).symm)

lemma pe_ne {n : ℕ} (t : TowerPath D n) : pathIdempotent D t ≠ 0 := by
  intro h; apply pe_sa_ne D n t; rw [h]; simp [simpleAction]

lemma ps_eq {n : ℕ} (t : TowerPath D n) (a : AA n) (c : k)
    (h : a * pathIdempotent D t = c • pathIdempotent D t) : pathScalar D t a = c := by
  unfold pathScalar
  have hex : ∃ c : k, a * pathIdempotent D t = c • pathIdempotent D t := ⟨c, h⟩
  rw [dif_pos hex]
  have h2 : a * pathIdempotent D t = Classical.choose hex • pathIdempotent D t :=
    Classical.choose_spec hex
  have h3 : (c - Classical.choose hex) • pathIdempotent D t = 0 := by
    rw [sub_smul, ← h, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 (pe_ne D t)

lemma lcd (J : (i : ℕ) → AA (i + 1)) (hJ : IsAdditivelyCentral D J) (n : ℕ) (t : TowerPath D (n + 1)) :
    lastContent D J t = edgeContent D J n
      (towerTerminal D (towerPrefix D t n (by omega))) (towerTerminal D t) := by
  have hS1 := hJ.2 (n+1)
  have hS0 := hJ.2 n
  have hJn : J n = towerPartialSum D J (n+1) - D.inc n (n+1) (Nat.le_succ n) (towerPartialSum D J n) := by
    rw [ps_succ]; abel
  unfold lastContent contentVector embeddedSequence initialSequence edgeContent
  simp only [inc_id]
  apply ps_eq
  rw [hJn, sub_mul, central_on_path D hS1 t, pe_succ D t, ← mul_assoc, ← map_mul,
    central_on_path D hS0, map_smul, smul_mul_assoc, ← pe_succ, sub_smul]

lemma X_inc {j n : ℕ} (h : j ≤ n) {x : AA j} (hx : x ∈ towerGTAlgebra D j) :
    D.inc j n h x ∈ towerGTAlgebra D n := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, z, rfl⟩ := hx
    rw [incc]; exact Algebra.subset_adjoin ⟨i, _, z, rfl⟩
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

lemma ps_spec {n : ℕ} (t : TowerPath D n) {a : AA n} (ha : a ∈ towerGTAlgebra D n) :
    a * pathIdempotent D t = pathScalar D t a • pathIdempotent D t := by
  obtain ⟨c, hc⟩ := X_scalar D t ha
  rw [ps_eq D t a c hc, hc]

lemma ps_add {n : ℕ} (t : TowerPath D n) {a b : AA n} (ha : a ∈ towerGTAlgebra D n)
    (hb : b ∈ towerGTAlgebra D n) : pathScalar D t (a + b) = pathScalar D t a + pathScalar D t b := by
  apply ps_eq; rw [add_mul, ps_spec D t ha, ps_spec D t hb, add_smul]

lemma ps_mul {n : ℕ} (t : TowerPath D n) {a b : AA n} (ha : a ∈ towerGTAlgebra D n)
    (hb : b ∈ towerGTAlgebra D n) : pathScalar D t (a * b) = pathScalar D t a * pathScalar D t b := by
  apply ps_eq; rw [mul_assoc, ps_spec D t hb, mul_smul_comm, ps_spec D t ha, smul_smul, mul_comm]

lemma ps_inc {n : ℕ} (t : TowerPath D (n+1)) {a : AA n} (ha : a ∈ towerGTAlgebra D n) :
    pathScalar D t (D.inc n (n+1) (Nat.le_succ n) a) =
      pathScalar D (towerPrefix D t n (Nat.le_succ n)) a := by
  apply ps_eq
  rw [pe_succ D t, ← mul_assoc, ← map_mul, ps_spec D _ ha, map_smul, smul_mul_assoc]

lemma path_ext {n : ℕ} (s t : TowerPath D (n+1))
    (hp : towerPrefix D s n (Nat.le_succ n) = towerPrefix D t n (Nat.le_succ n))
    (ht : towerTerminal D s = towerTerminal D t) : s = t := by
  apply Subtype.ext; funext i
  obtain ⟨iv, hi⟩ := i
  by_cases h : iv ≤ n
  · exact congrFun (congrArg Subtype.val hp) ⟨iv, by omega⟩
  · have : iv = n+1 := by omega
    subst this; exact ht

lemma cps1 (J : (i : ℕ) → AA (i + 1)) (hJ : ∀ i, J i ∈ towerGTAlgebra D (i + 1)) (n : ℕ)
    (t : TowerPath D (n + 1)) (i : Fin n) :
    contentVector D (initialSequence J (n + 1)) t ⟨i.val, by omega⟩ =
      contentVector D (initialSequence J n) (towerPrefix D t n (by omega)) i := by
  unfold contentVector embeddedSequence initialSequence
  rw [← ps_inc D t (X_inc D _ (hJ i.val)), incc]

lemma E_X {n : ℕ} (lam : (D.split n).Label) : centralIdempotent (D.split n) lam ∈ towerGTAlgebra D n := by
  have := Algebra.subset_adjoin (R := k) (E_gen D (le_refl n) lam)
  rwa [inc_id] at this

lemma cps2 (J : (i : ℕ) → AA (i + 1)) (hJ : IsSeparating D J) (n : ℕ) (s t : TowerPath D (n + 1))
    (hp : towerPrefix D s n (by omega) = towerPrefix D t n (by omega)) (hst : s ≠ t) :
    lastContent D J s ≠ lastContent D J t := by
  intro hl
  have hall : ∀ a ∈ Algebra.adjoin k (Set.range (embeddedSequence D (n+1) (initialSequence J (n+1)))),
      pathScalar D s a = pathScalar D t a := by
    intro a ha
    have haX : ∀ b ∈ Algebra.adjoin k (Set.range (embeddedSequence D (n+1) (initialSequence J (n+1)))),
        b ∈ towerGTAlgebra D (n+1) := fun b hb => by rwa [hJ.2 (n+1)] at hb
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      by_cases hi : i.val < n
      · have h1 := cps1 D J hJ.1 n s ⟨i.val, hi⟩
        have h2 := cps1 D J hJ.1 n t ⟨i.val, hi⟩
        rw [hp] at h1
        exact h1.trans h2.symm
      · obtain ⟨iv, hiv⟩ := i
        have : iv = n := by simp at hi; omega
        subst this
        exact hl
    | algebraMap r =>
      rw [ps_eq D s _ r (by rw [Algebra.smul_def]), ps_eq D t _ r (by rw [Algebra.smul_def])]
    | add x y hx hy ihx ihy =>
      rw [ps_add D s (haX x hx) (haX y hy), ps_add D t (haX x hx) (haX y hy), ihx, ihy]
    | mul x y hx hy ihx ihy =>
      rw [ps_mul D s (haX x hx) (haX y hy), ps_mul D t (haX x hx) (haX y hy), ihx, ihy]
  have hE := E_X D (towerTerminal D s)
  rw [← hJ.2 (n+1)] at hE
  have h := hall _ hE
  have hne : towerTerminal D s ≠ towerTerminal D t := fun h => hst (path_ext D s t hp h)
  have e1 : pathScalar D s (centralIdempotent (D.split (n+1)) (towerTerminal D s)) = 1 := by
    apply ps_eq
    rw [one_smul, pe_succ D s, ← mul_assoc, ((Subalgebra.mem_center_iff.mp (ci_mem _ _)) _).symm,
      mul_assoc, ci_idem]
  have e2 : pathScalar D t (centralIdempotent (D.split (n+1)) (towerTerminal D s)) = 0 := by
    apply ps_eq
    rw [zero_smul, pe_succ D t, ← mul_assoc, ((Subalgebra.mem_center_iff.mp (ci_mem _ _)) _).symm,
      mul_assoc, ci_orth _ _ _ hne, mul_zero]
  rw [e1, e2] at h
  exact one_ne_zero h

def pextF {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label) :
    (i : Fin (n+2)) → (D.split i.val).Label :=
  Fin.snoc (α := fun i : Fin (n+2) => (D.split i.val).Label) t.val lam

lemma pextF_lt {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label) (i : ℕ) (hi : i < n + 1) :
    pextF D t lam ⟨i, by omega⟩ = t.val ⟨i, hi⟩ := by
  simp [pextF, Fin.snoc, hi]

lemma pextF_last {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label) :
    pextF D t lam ⟨n + 1, by omega⟩ = lam := by
  simp [pextF, Fin.snoc]

def pext {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label)
    (h : Branch D n (towerTerminal D t) lam) : TowerPath D (n+1) :=
  ⟨pextF D t lam, fun i => by
    obtain ⟨iv, hiv⟩ := i
    by_cases hlt : iv < n
    · have := t.property ⟨iv, hlt⟩
      simp only at this ⊢
      rw [pextF_lt D t lam iv (by omega), pextF_lt D t lam (iv+1) (by omega)]
      exact this
    · have : iv = n := by omega
      subst this
      simp only
      rw [pextF_lt D t lam iv (by omega), pextF_last]
      exact h⟩

lemma pext_prefix {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label)
    (h : Branch D n (towerTerminal D t) lam) : towerPrefix D (pext D t lam h) n (Nat.le_succ n) = t := by
  apply Subtype.ext; funext i
  exact pextF_lt D t lam i.val i.isLt

lemma pext_term {n : ℕ} (t : TowerPath D n) (lam : (D.split (n+1)).Label)
    (h : Branch D n (towerTerminal D t) lam) : towerTerminal D (pext D t lam h) = lam :=
  pextF_last D t lam

lemma path_branch {n : ℕ} (t : TowerPath D (n+1)) :
    Branch D n (towerTerminal D (towerPrefix D t n (Nat.le_succ n))) (towerTerminal D t) :=
  t.property ⟨n, by omega⟩

lemma sib_edge (J : (i : ℕ) → AA (i + 1)) (hJ : IsAdditivelyCentral D J) (n : ℕ)
    (t : TowerPath D (n + 1)) : siblingPolynomial D J t = edgePolynomial D J n
      (towerTerminal D (towerPrefix D t n (by omega))) (towerTerminal D t) := by
  unfold siblingPolynomial edgePolynomial
  apply Finset.prod_bij (fun s _ => towerTerminal D s)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    refine ⟨?_, fun h => hs.2 (path_ext D s t hs.1 h)⟩
    have := path_branch D s
    rwa [hs.1] at this
  · intro s1 hs1 s2 hs2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
    exact path_ext D s1 s2 (hs1.1.trans hs2.1.symm) h
  · intro nu hnu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnu
    refine ⟨pext D _ nu hnu.1, ?_, pext_term D _ nu hnu.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨pext_prefix D _ nu hnu.1, fun h => hnu.2 ?_⟩
    rw [← pext_term D _ nu hnu.1, h]
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [lcd D J hJ n t, lcd D J hJ n s, hs.1]

lemma nonbranch {n : ℕ} (mu : (D.split n).Label) (lam : (D.split (n+1)).Label)
    (h : ¬ Branch D n mu lam) :
    D.inc n (n+1) (Nat.le_succ n) (centralIdempotent (D.split n) mu) *
      centralIdempotent (D.split (n+1)) lam = 0 := by
  apply sa_zero_mul
  by_contra hne
  obtain ⟨f, hf, hf0⟩ := branch_exists _ _ _ mu lam hne
  apply h
  unfold Branch
  exact (Module.finrank_pos_iff_exists_ne_zero (R := k)).mpr ⟨⟨f, hf⟩, fun h0 => hf0 (congrArg Subtype.val h0)⟩

lemma ci0 (lam : (D.split 0).Label) : centralIdempotent (D.split 0) lam = 1 := by
  have hid := ci_idem (D.split 0) lam
  have hne := ci_ne (D.split 0) lam
  set x := D.base (centralIdempotent (D.split 0) lam) with hx
  have h1 : x * x = x := by rw [hx, ← map_mul, hid]
  have hx0 : x ≠ 0 := by
    intro h0; apply hne; apply D.base.injective; rw [map_zero]; exact h0
  have hx1 : x = 1 := mul_left_cancel₀ hx0 (h1.trans (mul_one x).symm)
  apply D.base.injective; rw [map_one]; exact hx1

lemma label0 (a b : (D.split 0).Label) : a = b := by
  by_contra hab
  have := ci_orth (D.split 0) a b hab
  rw [ci0, ci0, one_mul] at this
  apply one_ne_zero (α := k)
  have h2 := congrArg D.base this
  rwa [map_one, map_zero] at h2

lemma path0 (s t : TowerPath D 0) : s = t := by
  apply Subtype.ext; funext i
  obtain ⟨iv, hi⟩ := i
  have : iv = 0 := by omega
  subst this; exact label0 D _ _

lemma inc_ci_comm {n : ℕ} (a : AA n) (lam : (D.split (n+1)).Label) :
    D.inc n (n+1) (Nat.le_succ n) a * centralIdempotent (D.split (n+1)) lam =
      centralIdempotent (D.split (n+1)) lam * D.inc n (n+1) (Nat.le_succ n) a :=
  (Subalgebra.mem_center_iff.mp (ci_mem _ lam)) _

lemma pe_idem : ∀ {n : ℕ} (t : TowerPath D n), pathIdempotent D t * pathIdempotent D t = pathIdempotent D t
  | 0, t => by rw [pe_zero, one_mul]
  | n + 1, t => by
    rw [pe_succ D t, mul_assoc, ← mul_assoc (centralIdempotent _ _), ← inc_ci_comm, mul_assoc _ _
      (centralIdempotent _ _), ci_idem, ← mul_assoc, ← map_mul, pe_idem]

lemma pe_orth : ∀ {n : ℕ} (s t : TowerPath D n), s ≠ t → pathIdempotent D s * pathIdempotent D t = 0
  | 0, s, t, h => absurd (path0 D s t) h
  | n + 1, s, t, h => by
    rw [pe_succ D s, pe_succ D t, mul_assoc, ← mul_assoc (centralIdempotent _ _), ← inc_ci_comm,
      mul_assoc _ _ (centralIdempotent _ _), ← mul_assoc, ← map_mul]
    by_cases hp : towerPrefix D s n (Nat.le_succ n) = towerPrefix D t n (Nat.le_succ n)
    · have ht : towerTerminal D s ≠ towerTerminal D t := fun ht => h (path_ext D s t hp ht)
      rw [ci_orth _ _ _ ht, mul_zero]
    · rw [pe_orth _ _ hp, map_zero, zero_mul]

lemma ci_pe : ∀ {n : ℕ} (t : TowerPath D n) (lam : (D.split n).Label),
    centralIdempotent (D.split n) lam * pathIdempotent D t =
      if towerTerminal D t = lam then pathIdempotent D t else 0
  | 0, t, lam => by rw [ci0, one_mul, if_pos (label0 D _ _)]
  | n + 1, t, lam => by
    rw [pe_succ D t, ← mul_assoc, ← inc_ci_comm, mul_assoc]
    split_ifs with h
    · rw [h, ci_idem]
    · rw [ci_orth _ _ _ (Ne.symm h), mul_zero]

lemma pe_ci_comm {n : ℕ} (t : TowerPath D n) (lam : (D.split n).Label) :
    pathIdempotent D t * centralIdempotent (D.split n) lam =
      centralIdempotent (D.split n) lam * pathIdempotent D t :=
  ((Subalgebra.mem_center_iff.mp (ci_mem _ lam)) _)

lemma pre_sum {n : ℕ} (t' : TowerPath D n) :
    ∑ t ∈ Finset.univ.filter (fun t : TowerPath D (n+1) => towerPrefix D t n (Nat.le_succ n) = t'),
      pathIdempotent D t = D.inc n (n+1) (Nat.le_succ n) (pathIdempotent D t') := by
  have h1 : D.inc n (n+1) (Nat.le_succ n) (pathIdempotent D t') =
      ∑ lam ∈ Finset.univ.filter (fun lam => Branch D n (towerTerminal D t') lam),
        D.inc n (n+1) (Nat.le_succ n) (pathIdempotent D t') * centralIdempotent (D.split (n+1)) lam := by
    rw [Finset.sum_filter_of_ne, ← Finset.mul_sum, ci_sum, mul_one]
    intro lam _ hne
    by_contra hb
    apply hne
    have : pathIdempotent D t' = pathIdempotent D t' * centralIdempotent (D.split n) (towerTerminal D t') := by
      rw [pe_ci_comm, ci_pe, if_pos rfl]
    rw [this, map_mul, mul_assoc, nonbranch D _ _ hb, mul_zero]
  rw [h1]
  apply Finset.sum_bij (fun s _ => towerTerminal D s)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    have := path_branch D s
    rwa [hs] at this
  · intro s1 hs1 s2 hs2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
    exact path_ext D s1 s2 (hs1.trans hs2.symm) h
  · intro nu hnu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnu
    exact ⟨pext D _ nu hnu, by simp [pext_prefix], pext_term D _ nu hnu⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [pe_succ D s, hs]

lemma pe_sum : ∀ (n : ℕ), ∑ t : TowerPath D n, pathIdempotent D t = 1
  | 0 => by
    have hne : Nonempty (D.split 0).Label := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := ci_sum (D.split 0)
      rw [Finset.univ_eq_empty, Finset.sum_empty] at this
      apply one_ne_zero (α := k)
      have h2 := congrArg D.base this
      rwa [map_one, map_zero, eq_comm] at h2
    obtain ⟨l⟩ := hne
    let t0 : TowerPath D 0 := ⟨fun i => by
      obtain ⟨iv, hi⟩ := i
      have : iv = 0 := by omega
      subst this; exact l, fun i => i.elim0⟩
    rw [Finset.sum_eq_single t0 (fun b _ hb => absurd (path0 D b t0) hb) (by simp), pe_zero]
  | n + 1 => by
    rw [← Finset.sum_fiberwise Finset.univ (fun t : TowerPath D (n+1) => towerPrefix D t n (Nat.le_succ n))]
    simp only [pre_sum]
    rw [← map_sum, pe_sum n, map_one]

lemma sum_pathsTo {M : Type*} [AddCommMonoid M] (n : ℕ) (lam : (D.split n).Label) (F : TowerPath D n → M) :
    ∑ t : TowerPathsTo D n lam, F t.val =
      ∑ t ∈ Finset.univ.filter (fun t => towerTerminal D t = lam), F t :=
  (Finset.sum_subtype _ (by simp) F).symm

lemma pe_E_sum (n : ℕ) (lam : (D.split n).Label) :
    ∑ t : TowerPathsTo D n lam, pathIdempotent D t.val = centralIdempotent (D.split n) lam := by
  rw [sum_pathsTo, ← mul_one (centralIdempotent _ lam), ← pe_sum D n, Finset.mul_sum]
  simp only [ci_pe]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

end T2

end G62K


open G62K

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

section TowerStatements

variable {AA : ℕ → Type v} [∀ n, Ring (AA n)] [∀ n, Algebra k (AA n)]

variable [∀ n, FiniteDimensional k (AA n)]

/-- Corollary 1.7, source PDF pp. 5–6. Prefix absorption bars the FIRST path;
orthogonality is within each level, and uniqueness is simultaneous over all levels. -/
theorem solution (D : Tower k AA) :
    (∀ n (lam : (D.split n).Label),
      (∑ t : TowerPathsTo D n lam, pathIdempotent D t.val) = centralIdempotent (D.split n) lam) ∧
    (∀ n (t : TowerPath D (n + 1)),
      D.inc n (n + 1) (by omega) (pathIdempotent D (towerPrefix D t n (by omega))) *
        pathIdempotent D t = pathIdempotent D t) ∧
    (∀ g : (n : ℕ) → TowerPath D n → AA n,
      (∀ n (t : TowerPath D n), g n t * g n t = g n t) →
      (∀ n (s t : TowerPath D n), s ≠ t → g n s * g n t = 0) →
      (∀ n (lam : (D.split n).Label), (∑ t : TowerPathsTo D n lam, g n t.val) =
        centralIdempotent (D.split n) lam) →
      (∀ n (t : TowerPath D (n + 1)),
        D.inc n (n + 1) (by omega) (g n (towerPrefix D t n (by omega))) * g (n + 1) t = g (n + 1) t) →
      ∀ n t, g n t = pathIdempotent D t) := by
  refine ⟨fun n lam => G62K.pe_E_sum D n lam, fun n t => ?_, ?_⟩
  · rw [G62K.pe_succ D t, ← mul_assoc, ← map_mul, G62K.pe_idem]
  · intro g hidem horth hsum habs n
    induction n with
    | zero =>
      intro t
      have := hsum 0 (towerTerminal D t)
      rw [G62K.sum_pathsTo, Finset.sum_eq_single t
        (fun b _ hbt => absurd (G62K.path0 D b t) hbt) (by simp), G62K.ci0] at this
      rw [this, G62K.pe_zero]
    | succ n ih =>
      intro t
      have hEg : centralIdempotent (D.split (n+1)) (towerTerminal D t) * g (n+1) t = g (n+1) t := by
        rw [← hsum (n+1) (towerTerminal D t), G62K.sum_pathsTo, Finset.sum_mul,
          Finset.sum_eq_single t]
        · exact hidem _ t
        · intro b _ hbt; exact horth _ b t hbt
        · intro h; simp at h
      have hgt : g (n+1) t = pathIdempotent D t * g (n+1) t := by
        rw [G62K.pe_succ D t, mul_assoc, hEg, ← ih, habs]
      have hpt : pathIdempotent D t = pathIdempotent D t * g (n+1) t := by
        have e1 : pathIdempotent D t =
            pathIdempotent D t * centralIdempotent (D.split (n+1)) (towerTerminal D t) := by
          rw [G62K.pe_ci_comm, G62K.ci_pe, if_pos rfl]
        conv_lhs => rw [e1]
        rw [← hsum (n+1) _, G62K.sum_pathsTo, Finset.mul_sum, Finset.sum_eq_single t]
        · intro s hs hst
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          have hp : towerPrefix D s n (by omega) ≠ towerPrefix D t n (by omega) :=
            fun hp => hst (G62K.path_ext D s t hp hs)
          rw [← habs n s, ih, ← mul_assoc, G62K.pe_succ D t,
            mul_assoc (D.inc n (n+1) _ _) (centralIdempotent _ _), ← G62K.inc_ci_comm, ← mul_assoc,
            ← map_mul, G62K.pe_orth D _ _ (Ne.symm hp), map_zero, zero_mul, zero_mul]
        · intro h; simp at h
      exact hgt.trans hpt.symm


end TowerStatements


end
