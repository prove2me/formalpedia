-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P12.last_content_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:31:09.678438+00:00
-- url     : https://prove2.me/submissions/5c660b11-d6b8-4f50-bfa9-1abe3b112de4

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

end T2

end G62K


open G62K

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

section TowerStatements

variable {AA : ℕ → Type v} [∀ n, Ring (AA n)] [∀ n, Algebra k (AA n)]

variable [∀ n, FiniteDimensional k (AA n)]

/-- Proposition 3.3, source PDF pp. 11–12. Additive centrality alone suffices;
positive length excludes a nonexistent last edge at zero. -/
theorem solution (D : Tower k AA) (J : (i : ℕ) → AA (i + 1))
    (hJ : IsAdditivelyCentral D J) (n : ℕ) (t : TowerPath D (n + 1)) :
    lastContent D J t = edgeContent D J n
      (towerTerminal D (towerPrefix D t n (by omega))) (towerTerminal D t) := by
  exact G62K.lcd D J hJ n t


end TowerStatements


end
