-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P12.restriction_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T21:12:27.992919+00:00
-- url     : https://prove2.me/submissions/ff5eb7ca-2f26-4f79-87e5-53db1dd309ee

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

lemma aeval_eig {a e : A} {c : k} (h : a * e = c • e) (p : Polynomial k) :
    Polynomial.aeval a p * e = p.eval c • e := by
  induction p using Polynomial.induction_on with
  | C r => simp [Algebra.smul_def]
  | add p q hp hq => rw [map_add, add_mul, hp, hq, Polynomial.eval_add, add_smul]
  | monomial m r ih =>
    have : Polynomial.aeval a (Polynomial.C r * Polynomial.X ^ (m + 1)) =
        Polynomial.aeval a (Polynomial.C r * Polynomial.X ^ m) * a := by
      simp [pow_succ, mul_assoc]
    rw [this, mul_assoc, h, mul_smul_comm, ih, smul_smul]
    congr 1
    simp [pow_succ]; ring

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

lemma ps_last (J : (i : ℕ) → AA (i + 1)) {n : ℕ} (s : TowerPath D (n+1)) :
    pathScalar D s (J n) = lastContent D J s := by
  unfold lastContent contentVector embeddedSequence initialSequence
  rw [inc_id]

lemma rpi1 (J : (i : ℕ) → AA (i + 1)) (hJ : IsSeparating D J) (n : ℕ) (t : TowerPath D (n + 1)) :
    pathIdempotent D t =
      D.inc n (n + 1) (by omega) (pathIdempotent D (towerPrefix D t n (by omega))) *
        Polynomial.aeval (J n) (siblingPolynomial D J t) := by
  have hq : Polynomial.aeval (J n) (siblingPolynomial D J t) ∈ towerGTAlgebra D (n+1) := by
    have := Polynomial.aeval_mem_adjoin_singleton k (J n) (p := siblingPolynomial D J t)
    exact Algebra.adjoin_le (by simpa using hJ.1 n) this
  rw [← pre_sum D, Finset.sum_mul]
  have hterm : ∀ s ∈ Finset.univ.filter (fun s : TowerPath D (n+1) =>
      towerPrefix D s n (Nat.le_succ n) = towerPrefix D t n (Nat.le_succ n)),
      pathIdempotent D s * Polynomial.aeval (J n) (siblingPolynomial D J t) =
        (siblingPolynomial D J t).eval (lastContent D J s) • pathIdempotent D s := by
    intro s _
    rw [← (X_comm D (n+1) hq (pe_mem D s)).eq, ← ps_last]
    exact aeval_eig (ps_spec D s (hJ.1 n)) _
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single t]
  · rw [eq_comm]
    convert one_smul k (pathIdempotent D t)
    unfold siblingPolynomial
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hne := cps2 D J hJ n t s hs.1.symm (Ne.symm hs.2)
    have : lastContent D J t - lastContent D J s ≠ 0 := sub_ne_zero.mpr hne
    simp [interpolationFactor, this]
  · intro s hs hst
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    unfold siblingPolynomial
    rw [Polynomial.eval_prod, Finset.prod_eq_zero (i := s), zero_smul]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hs, hst⟩
    · simp [interpolationFactor]
  · intro h; simp at h

lemma rpi2 (J : (i : ℕ) → AA (i + 1)) (hJ : IsSeparating D J) : ∀ (n : ℕ) (t : TowerPath D n),
    pathIdempotent D t =
      (List.ofFn fun i : Fin n => D.inc (i.val + 1) n (by omega)
        (Polynomial.aeval (J i.val)
          (siblingPolynomial D J (towerPrefix D t (i.val + 1) (by omega))))).prod
  | 0, t => by simp [pe_zero]
  | n + 1, t => by
    rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton, rpi1 D J hJ n t]
    congr 1
    · rw [rpi2 J hJ n, map_list_prod, List.map_ofFn]
      refine congrArg _ (congrArg List.ofFn (funext fun i => ?_))
      simp only [Function.comp_apply]; rw [incc]; rfl
    · exact (inc_id D _ _).symm

lemma path_to (n : ℕ) (mu : (D.split n).Label) : ∃ t : TowerPath D n, towerTerminal D t = mu := by
  by_contra h
  push Not at h
  have := pe_E_sum D n mu
  rw [sum_pathsTo, Finset.sum_eq_zero (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht; exact absurd ht (h t))] at this
  exact ci_ne _ _ this.symm

lemma rci1 (J : (i : ℕ) → AA (i + 1)) (hJ : IsJMSequence D J) (n : ℕ)
    (lam : (D.split (n + 1)).Label) :
    ∀ mu nu, Branch D n mu lam → Branch D n mu nu → nu ≠ lam →
      edgeContent D J n mu lam - edgeContent D J n mu nu ≠ 0 := by
  intro mu nu hmu hnu hne
  obtain ⟨t', ht'⟩ := path_to D n mu
  subst ht'
  have hc := cps2 D J hJ.1 n (pext D t' lam hmu) (pext D t' nu hnu)
    (by rw [pext_prefix, pext_prefix])
    (fun h => hne (by
      have := congrArg (towerTerminal D) h
      rw [pext_term, pext_term] at this; exact this.symm))
  rw [lcd D J hJ.2, lcd D J hJ.2, pext_prefix, pext_prefix, pext_term, pext_term] at hc
  exact sub_ne_zero.mpr hc

lemma rci2 (J : (i : ℕ) → AA (i + 1)) (hJ : IsJMSequence D J) (n : ℕ)
    (lam : (D.split (n + 1)).Label) :
    centralIdempotent (D.split (n + 1)) lam =
      ∑ mu ∈ Finset.univ.filter (fun mu => Branch D n mu lam),
        Polynomial.aeval (J n) (edgePolynomial D J n mu lam) *
          D.inc n (n + 1) (by omega) (centralIdempotent (D.split n) mu) := by
  have hq : ∀ p : Polynomial k, Polynomial.aeval (J n) p ∈ towerGTAlgebra D (n+1) := fun p =>
    Algebra.adjoin_le (by simpa using hJ.1.1 n) (Polynomial.aeval_mem_adjoin_singleton k (J n))
  let f : TowerPath D n → AA (n+1) := fun t' =>
    Polynomial.aeval (J n) (edgePolynomial D J n (towerTerminal D t') lam) *
      D.inc n (n+1) (Nat.le_succ n) (pathIdempotent D t')
  have hR : ∀ mu, Polynomial.aeval (J n) (edgePolynomial D J n mu lam) *
      D.inc n (n+1) (Nat.le_succ n) (centralIdempotent (D.split n) mu) =
      ∑ t' ∈ Finset.univ.filter (fun t' => towerTerminal D t' = mu), f t' := by
    intro mu
    rw [← pe_E_sum D n mu, sum_pathsTo, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
    simp only [f, ht']
  rw [Finset.sum_congr rfl (fun mu _ => hR mu)]
  have hfib := (Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun t' : TowerPath D n => Branch D n (towerTerminal D t') lam))
    (t := Finset.univ.filter (fun mu => Branch D n mu lam)) (g := towerTerminal D)
    (by intro x hx; simpa using hx) f).symm
  have hsets : ∀ mu ∈ Finset.univ.filter (fun mu => Branch D n mu lam),
      ∑ t' ∈ Finset.univ.filter (fun t' => towerTerminal D t' = mu), f t' =
      ∑ t' ∈ (Finset.univ.filter (fun t' : TowerPath D n => Branch D n (towerTerminal D t') lam)).filter
        (fun t' => towerTerminal D t' = mu), f t' := by
    intro mu hmu
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmu ⊢
    constructor
    · intro h; exact ⟨h ▸ hmu, h⟩
    · intro h; exact h.2
  rw [Finset.sum_congr rfl hsets, ← hfib]
  rw [← pe_E_sum D (n+1) lam, sum_pathsTo]
  apply Finset.sum_bij (fun t _ => towerPrefix D t n (Nat.le_succ n))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have := path_branch D t
    rwa [ht] at this
  · intro t1 ht1 t2 ht2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    exact path_ext D t1 t2 h (ht1.trans ht2.symm)
  · intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
    refine ⟨pext D t' lam ht', ?_, pext_prefix D t' lam ht'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact pext_term D t' lam ht'
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [rpi1 D J hJ.1 n t, sib_edge D J hJ.2 n t, ht]
    exact (X_comm D (n+1) (X_inc D _ (pe_mem D _)) (hq _)).eq

lemma ps_aeval {n : ℕ} (s : TowerPath D n) {a : AA n} (ha : a ∈ towerGTAlgebra D n) (p : Polynomial k) :
    pathScalar D s (Polynomial.aeval a p) = p.eval (pathScalar D s a) :=
  ps_eq D s _ _ (aeval_eig (ps_spec D s ha) p)

lemma list_act {n : ℕ} (s : TowerPath D n) : ∀ L : List (AA n), (∀ a ∈ L, a ∈ towerGTAlgebra D n) →
    L.prod * pathIdempotent D s = (L.map (pathScalar D s)).prod • pathIdempotent D s
  | [], _ => by simp
  | a :: L, h => by
    rw [List.prod_cons, mul_assoc, list_act s L (fun b hb => h b (by simp [hb])), mul_smul_comm,
      ps_spec D s (h a (by simp)), smul_smul, List.map_cons, List.prod_cons, mul_comm]

lemma sep_inj (n : ℕ) (J : (i : Fin n) → AA (i.val + 1))
    (hsep : Algebra.adjoin k (Set.range (embeddedSequence D n J)) = towerGTAlgebra D n)
    (s t : TowerPath D n) (h : contentVector D J s = contentVector D J t) : s = t := by
  by_contra hst
  have haX : ∀ b ∈ Algebra.adjoin k (Set.range (embeddedSequence D n J)), b ∈ towerGTAlgebra D n :=
    fun b hb => by rwa [hsep] at hb
  have hall : ∀ a ∈ Algebra.adjoin k (Set.range (embeddedSequence D n J)),
      pathScalar D s a = pathScalar D t a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact congrFun h i
    | algebraMap r =>
      rw [ps_eq D s _ r (by rw [Algebra.smul_def]), ps_eq D t _ r (by rw [Algebra.smul_def])]
    | add x y hx hy ihx ihy =>
      rw [ps_add D s (haX x hx) (haX y hy), ps_add D t (haX x hx) (haX y hy), ihx, ihy]
    | mul x y hx hy ihx ihy =>
      rw [ps_mul D s (haX x hx) (haX y hy), ps_mul D t (haX x hx) (haX y hy), ihx, ihy]
  obtain ⟨⟨iv, hiv⟩, hi⟩ : ∃ i, s.val i ≠ t.val i := by
    by_contra hc; push Not at hc; exact hst (Subtype.ext (funext hc))
  cases iv with
  | zero => exact hi (label0 D _ _)
  | succ j =>
    have hmem : D.inc (j+1) n (by omega) (centralIdempotent (D.split (j+1)) (s.val ⟨j+1, hiv⟩)) ∈
        towerGTAlgebra D n := Algebra.subset_adjoin (E_gen D _ _)
    rw [← hsep] at hmem
    have hh := hall _ hmem
    have e1 : pathScalar D s (D.inc (j+1) n (by omega)
        (centralIdempotent (D.split (j+1)) (s.val ⟨j+1, hiv⟩))) = 1 := by
      apply ps_eq; rw [one_smul]; exact pe_absorb D s j (by omega)
    have e2 : pathScalar D t (D.inc (j+1) n (by omega)
        (centralIdempotent (D.split (j+1)) (s.val ⟨j+1, hiv⟩))) = 0 := by
      apply ps_eq
      rw [zero_smul, ← pe_absorb D t j (by omega), ← mul_assoc, ← map_mul, ci_orth _ _ _ hi,
        map_zero, zero_mul]
    rw [e1, e2] at hh
    exact one_ne_zero hh

lemma emi2 (n : ℕ) (J : (i : Fin n) → AA (i.val + 1)) (hJ : ∀ i, J i ∈ towerGTAlgebra D (i.val + 1))
    (hinj : ∀ s t : TowerPath D n, contentVector D J s = contentVector D J t → s = t)
    (t : TowerPath D n) : pathIdempotent D t = multivariateInterpolant D J t := by
  have hX : ∀ i, embeddedSequence D n J i ∈ towerGTAlgebra D n := fun i => X_inc D _ (hJ i)
  have hQ : ∀ s, multivariateInterpolant D J t * pathIdempotent D s =
      (if s = t then (1:k) else 0) • pathIdempotent D s := by
    intro s
    unfold multivariateInterpolant
    rw [list_act D s _ (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact Algebra.adjoin_le (by simpa using hX i) (Polynomial.aeval_mem_adjoin_singleton k _))]
    rw [List.map_ofFn, List.prod_ofFn]
    congr 1
    simp only [Function.comp_apply, ps_aeval D s (hX _)]
    have hcv : ∀ i, pathScalar D s (embeddedSequence D n J i) = contentVector D J s i := fun i => rfl
    simp only [hcv]
    split_ifs with hst
    · subst hst
      apply Finset.prod_eq_one
      intro i _
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_one
      intro c hc
      have := Finset.ne_of_mem_erase hc
      simp [interpolationFactor, sub_ne_zero.mpr (Ne.symm this)]
    · have hne : contentVector D J s ≠ contentVector D J t := fun h => hst (hinj s t h)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (i := contentVector D J s i)
      · rw [Finset.mem_erase]
        refine ⟨hi, ?_⟩
        unfold contentWeights
        exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
      · simp [interpolationFactor]
  rw [eq_comm]
  calc multivariateInterpolant D J t
      = multivariateInterpolant D J t * ∑ s, pathIdempotent D s := by rw [pe_sum, mul_one]
    _ = pathIdempotent D t := by
      rw [Finset.mul_sum]
      simp only [hQ, ite_smul, one_smul, zero_smul]
      simp

lemma interp_mem (n : ℕ) (J : (i : Fin n) → AA (i.val + 1)) (t : TowerPath D n) :
    multivariateInterpolant D J t ∈ Algebra.adjoin k (Set.range (embeddedSequence D n J)) := by
  unfold multivariateInterpolant
  apply Subalgebra.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact Algebra.adjoin_mono (by simp) (Polynomial.aeval_mem_adjoin_singleton k _)

lemma cis (n : ℕ) (J : (i : Fin n) → AA (i.val + 1)) (hJ : ∀ i, J i ∈ towerGTAlgebra D (i.val + 1)) :
    (∀ s t : TowerPath D n, s = t ↔ contentVector D J s = contentVector D J t) ↔
      Algebra.adjoin k (Set.range (embeddedSequence D n J)) = towerGTAlgebra D n := by
  constructor
  · intro h
    have hinj : ∀ s t : TowerPath D n, contentVector D J s = contentVector D J t → s = t :=
      fun s t hst => (h s t).mpr hst
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact X_inc D _ (hJ i)
    · rw [gtA_eq]
      apply Algebra.adjoin_le
      intro g hg
      have hgX : g ∈ towerGTAlgebra D n := Algebra.subset_adjoin hg
      have : g = ∑ t, pathScalar D t g • multivariateInterpolant D J t := by
        conv_lhs => rw [← mul_one g, ← pe_sum D n, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [ps_spec D t hgX, emi2 D n J hJ hinj t]
      rw [this]
      exact Subalgebra.sum_mem _ (fun t _ => Subalgebra.smul_mem _ (interp_mem D n J t) _)
  · intro hsep s t
    exact ⟨fun h => h ▸ rfl, sep_inj D n J hsep s t⟩

end T2

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

open G62K

section G63H
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable {B : Type w} [Ring B] [Algebra k B]

def g63a_E (DB : SplitPresentation k B) (μ : DB.Label) (p q : Fin (DB.size μ)) : B :=
  DB.equiv.symm (Pi.single μ (Matrix.single p q 1))

def g63a_ρ (DA : SplitPresentation k A) (l : DA.Label) (inc : B →ₐ[k] A) :
    B →ₗ[k] Module.End k (SimpleSpace DA l) where
  toFun b := simpleAction DA l (inc b)
  map_add' a b := by simp [simpleAction]
  map_smul' c a := by simp [simpleAction]

lemma g63a_ρ_apply (DA : SplitPresentation k A) (l : DA.Label) (inc : B →ₐ[k] A) (b : B) :
    g63a_ρ DA l inc b = simpleAction DA l (inc b) := rfl

lemma g63a_ρ_mul (DA : SplitPresentation k A) (l : DA.Label) (inc : B →ₐ[k] A) (a b : B) (x) :
    g63a_ρ DA l inc (a * b) x = g63a_ρ DA l inc a (g63a_ρ DA l inc b x) := by
  simp [g63a_ρ_apply, map_mul, sa_mul]

lemma g63a_ρ_one (DA : SplitPresentation k A) (l : DA.Label) (inc : B →ₐ[k] A) (x) :
    g63a_ρ DA l inc 1 x = x := by
  simp [g63a_ρ_apply, sa_one]

lemma g63a_E_mul (DB : SplitPresentation k B) (μ : DB.Label) (p q r s : Fin (DB.size μ)) :
    g63a_E DB μ p q * g63a_E DB μ r s = if q = r then g63a_E DB μ p s else 0 := by
  apply DB.equiv.injective; funext ν
  by_cases hν : ν = μ
  · subst hν
    split_ifs with h
    · subst h; simp [g63a_E]
    · simp [g63a_E, h]
  · split_ifs <;> simp [g63a_E, Pi.single_eq_of_ne hν]

lemma g63a_L1 (DB : SplitPresentation k B) (μ : DB.Label) (b : B) (l q : Fin (DB.size μ)) :
    b * g63a_E DB μ l q = ∑ j, (DB.equiv b μ j l) • g63a_E DB μ j q := by
  apply DB.equiv.injective; funext ν
  simp only [map_mul, map_sum, map_smul, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, g63a_E,
    AlgEquiv.apply_symm_apply]
  by_cases hν : ν = μ
  · subst hν
    ext a c
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply]
    by_cases hq : q = c <;> simp [hq]
  · simp [Pi.single_eq_of_ne hν]

lemma g63a_L2 (DB : SplitPresentation k B) (μ : DB.Label) (b : B) (p j : Fin (DB.size μ)) :
    g63a_E DB μ p j * b = ∑ l, (DB.equiv b μ j l) • g63a_E DB μ p l := by
  apply DB.equiv.injective; funext ν
  simp only [map_mul, map_sum, map_smul, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, g63a_E,
    AlgEquiv.apply_symm_apply]
  by_cases hν : ν = μ
  · subst hν
    ext a c
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply]
    by_cases hq : p = a <;> simp [hq]
  · simp [Pi.single_eq_of_ne hν]

def g63a_F (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (u : SimpleSpace DA l) :
    SimpleSpace DB μ →ₗ[k] SimpleSpace DA l :=
  ∑ j, (LinearMap.proj j : SimpleSpace DB μ →ₗ[k] k).smulRight
    (g63a_ρ DA l inc (g63a_E DB μ j ⟨0, DB.positive μ⟩) u)

lemma g63a_F_apply (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (u : SimpleSpace DA l) (w : SimpleSpace DB μ) :
    g63a_F DB DA inc μ l u w = ∑ j, w j • g63a_ρ DA l inc (g63a_E DB μ j ⟨0, DB.positive μ⟩) u := by
  simp [g63a_F]

lemma g63a_F_mem (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (u : SimpleSpace DA l) :
    g63a_F DB DA inc μ l u ∈ restrictionHom DB DA inc μ l := by
  intro b w
  rw [g63a_F_apply, g63a_F_apply, ← g63a_ρ_apply, map_sum]
  simp only [map_smul, ← g63a_ρ_mul, g63a_L1, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [simpleAction, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [mul_comm]

def g63a_G (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (φ : SimpleSpace DA l →ₗ[k] k) :
    SimpleSpace DA l →ₗ[k] SimpleSpace DB μ :=
  LinearMap.pi (fun j => φ ∘ₗ g63a_ρ DA l inc (g63a_E DB μ ⟨0, DB.positive μ⟩ j))

lemma g63a_G_int (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (φ : SimpleSpace DA l →ₗ[k] k) (b : B) (v) :
    g63a_G DB DA inc μ l φ (simpleAction DA l (inc b) v) =
      simpleAction DB μ b (g63a_G DB DA inc μ l φ v) := by
  funext j
  simp only [g63a_G, LinearMap.pi_apply, LinearMap.comp_apply]
  rw [← g63a_ρ_apply, ← g63a_ρ_mul, g63a_L2]
  simp [simpleAction, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, LinearMap.sum_apply,
    g63a_G]

lemma g63a_F_U (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (u : SimpleSpace DA l)
    (hu : g63a_ρ DA l inc (g63a_E DB μ ⟨0, DB.positive μ⟩ ⟨0, DB.positive μ⟩) u = u) (c : k) :
    g63a_F DB DA inc μ l u (Pi.single ⟨0, DB.positive μ⟩ c) = c • u := by
  rw [g63a_F_apply, Finset.sum_eq_single ⟨0, DB.positive μ⟩ (fun j _ hj => by simp [hj]) (by simp),
    Pi.single_eq_same, hu]

lemma g63a_G_U (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (φ : SimpleSpace DA l →ₗ[k] k) (u : SimpleSpace DA l)
    (hu : g63a_ρ DA l inc (g63a_E DB μ ⟨0, DB.positive μ⟩ ⟨0, DB.positive μ⟩) u = u) :
    g63a_G DB DA inc μ l φ u = Pi.single ⟨0, DB.positive μ⟩ (φ u) := by
  funext j
  simp only [g63a_G, LinearMap.pi_apply, LinearMap.comp_apply]
  conv_lhs => rw [← hu, ← g63a_ρ_mul, g63a_E_mul]
  by_cases hj : j = ⟨0, DB.positive μ⟩
  · subst hj; simp [hu]
  · rw [if_neg hj, Pi.single_eq_of_ne hj]; simp

lemma g63a_hom_U (DB : SplitPresentation k B) (DA : SplitPresentation k A) (inc : B →ₐ[k] A)
    (μ : DB.Label) (l : DA.Label) (f : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l)
    (hf : f ∈ restrictionHom DB DA inc μ l) :
    g63a_ρ DA l inc (g63a_E DB μ ⟨0, DB.positive μ⟩ ⟨0, DB.positive μ⟩)
      (f (Pi.single ⟨0, DB.positive μ⟩ 1)) = f (Pi.single ⟨0, DB.positive μ⟩ 1) := by
  rw [g63a_ρ_apply, ← hf]
  congr 1
  funext i
  simp [simpleAction, g63a_E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.single_apply,
    Pi.single_apply]
  by_cases h : i = ⟨0, DB.positive μ⟩
  · subst h; simp
  · simp [h, Ne.symm h]

lemma g63a_sum_one (DB : SplitPresentation k B) :
    ∑ μ, ∑ i, g63a_E DB μ i ⟨0, DB.positive μ⟩ * g63a_E DB μ ⟨0, DB.positive μ⟩ i = 1 := by
  simp only [g63a_E_mul, if_true]
  apply DB.equiv.injective; funext ν
  simp only [map_sum, Finset.sum_apply, g63a_E, AlgEquiv.apply_symm_apply, map_one, Pi.one_apply]
  rw [Finset.sum_eq_single ν (fun j _ hj => by simp [Pi.single_eq_of_ne (Ne.symm hj)]) (by simp)]
  simp only [Pi.single_eq_same]
  exact (one_sum_single _).symm

end G63H

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Proposition 1.2, source PDF p. 3. One adjacent unital inclusion suffices;
multiplicity-free restriction is not assumed before stating the equivalence. -/
theorem solution {B : Type w} [Ring B] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B]
    (DB : SplitPresentation k B) (DA : SplitPresentation k A)
    (inc : B →ₐ[k] A) (hinj : Function.Injective inc) :
    MultiplicityFreeRestriction DB DA inc ↔
      ∀ x y : Subalgebra.centralizer k (Set.range inc), x * y = y * x := by
  set e0 : ∀ μ : DB.Label, Fin (DB.size μ) := fun μ => ⟨0, DB.positive μ⟩ with he0
  haveI : ∀ μ l, Module.Free k (restrictionHom DB DA inc μ l) := fun μ l => by first | infer_instance | exact Module.Free.of_basis (Module.Basis.ofVectorSpace k _) | exact (Module.Free.of_divisionRing k (restrictionHom DB DA inc μ l) :)
  haveI : ∀ μ l, Module.Finite k (restrictionHom DB DA inc μ l) := fun _ _ => inferInstance
  constructor
  · intro hmf x y
    have hc : ∀ (z : Subalgebra.centralizer k (Set.range inc)) (l : DA.Label) (b : B) (v),
        simpleAction DA l z (g63a_ρ DA l inc b v) = g63a_ρ DA l inc b (simpleAction DA l z v) := by
      intro z l b v
      have := (Subalgebra.mem_centralizer_iff k).mp z.2 (inc b) ⟨b, rfl⟩
      rw [g63a_ρ_apply, ← LinearMap.comp_apply, ← sa_mul, ← this, sa_mul]; rfl
    apply Subtype.ext
    show (x : A) * y = y * x
    apply DA.equiv.injective; funext l
    rw [map_mul, map_mul, Pi.mul_apply, Pi.mul_apply]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    change simpleAction DA l x ∘ₗ simpleAction DA l y = simpleAction DA l y ∘ₗ simpleAction DA l x
    have key : ∀ μ (u : SimpleSpace DA l), g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) u = u →
        simpleAction DA l x (simpleAction DA l y u) = simpleAction DA l y (simpleAction DA l x u) := by
      intro μ u hu
      obtain ⟨g0, hg0⟩ := (finrank_le_one_iff (K := k) (V := ↥(restrictionHom DB DA inc μ l))).mp (hmf μ l)
      have hU : ∀ u, g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) u = u →
          ∃ c : k, u = c • (g0 : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) (Pi.single (e0 μ) 1) := by
        intro u hu
        obtain ⟨c, hc⟩ := hg0 ⟨_, g63a_F_mem DB DA inc μ l u⟩
        refine ⟨c, ?_⟩
        have := congrArg (fun f : restrictionHom DB DA inc μ l =>
          (f : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) (Pi.single (e0 μ) 1)) hc
        simp only [Submodule.coe_smul, LinearMap.smul_apply] at this
        rw [this, g63a_F_U DB DA inc μ l u hu, one_smul]
      have hz : ∀ z : Subalgebra.centralizer k (Set.range inc), ∀ u,
          g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) u = u →
          g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) (simpleAction DA l z u) = simpleAction DA l z u := by
        intro z u hu; rw [← hc, hu]
      have hu0 := g63a_hom_U DB DA inc μ l g0.1 g0.2
      obtain ⟨c, rfl⟩ := hU u hu
      obtain ⟨a, ha⟩ := hU _ (hz x _ hu0)
      obtain ⟨b, hb⟩ := hU _ (hz y _ hu0)
      simp only [map_smul]
      change c • simpleAction DA l x (simpleAction DA l y (g0.1 (Pi.single (e0 μ) 1))) =
        c • simpleAction DA l y (simpleAction DA l x (g0.1 (Pi.single (e0 μ) 1)))
      rw [hb, map_smul, ha, map_smul, hb, smul_smul, smul_smul, smul_smul, smul_smul]; ring_nf
    apply LinearMap.ext; intro v
    have hv : v = ∑ μ, ∑ i, g63a_ρ DA l inc (g63a_E DB μ i (e0 μ))
        (g63a_ρ DA l inc (g63a_E DB μ (e0 μ) i) v) := by
      have := congrArg (fun b => g63a_ρ DA l inc b v) (g63a_sum_one DB)
      simp only [map_sum, LinearMap.sum_apply, g63a_ρ_mul, g63a_ρ_one] at this
      exact this.symm
    rw [hv]
    simp only [map_sum, LinearMap.comp_apply]
    refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [hc y l (g63a_E DB μ i (e0 μ)), hc x l (g63a_E DB μ i (e0 μ)), hc x l (g63a_E DB μ i (e0 μ)),
      hc y l (g63a_E DB μ i (e0 μ)), key μ]
    rw [← g63a_ρ_mul, g63a_E_mul, if_pos rfl]
  · intro hcomm μ l
    by_contra hlt
    push_neg at hlt
    have hn : ¬ ∃ v : restrictionHom DB DA inc μ l, ∀ w, ∃ c : k, c • v = w :=
      fun h => (not_le.mpr hlt) ((finrank_le_one_iff (K := k) (V := ↥(restrictionHom DB DA inc μ l))).mpr h)
    push_neg at hn
    obtain ⟨f, hf⟩ := hn 0
    have hf0 : (f : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) ≠ 0 := by
      intro h; apply hf 0; rw [zero_smul]; exact (Subtype.ext h).symm
    obtain ⟨g, hg⟩ := hn f
    set u1 := (f : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) (Pi.single (e0 μ) 1) with hu1d
    set u2 := (g : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) (Pi.single (e0 μ) 1) with hu2d
    have hsing : (Pi.single (e0 μ) (1 : k) : SimpleSpace DB μ) ≠ 0 := by
      intro h; have := congrFun h (e0 μ); simp at this
    have hu1 : u1 ≠ 0 := by
      intro h
      apply hsing
      apply hom_inj DB DA inc μ l f.1 f.2 hf0
      rw [map_zero]; exact h
    have hu2 : u2 ∉ Submodule.span k {u1} := by
      intro hm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      have hne : ((g - c • f : restrictionHom DB DA inc μ l) : SimpleSpace DB μ →ₗ[k] SimpleSpace DA l) ≠ 0 := by
        intro h
        apply hg c
        have := Subtype.ext (p := fun x => x ∈ restrictionHom DB DA inc μ l) (a1 := g - c • f) (a2 := 0) h
        exact (sub_eq_zero.mp this).symm
      apply hsing
      apply hom_inj DB DA inc μ l _ (g - c • f).2 hne
      simp only [Submodule.coe_sub, Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        map_zero]
      rw [← hu1d, ← hu2d, hc, sub_self]
    obtain ⟨φ, hφ2, hφ1⟩ := Submodule.exists_le_ker_of_notMem hu2
    have hφu1 : φ u1 = 0 := hφ1 (Submodule.mem_span_singleton_self u1)
    have hU1 := g63a_hom_U DB DA inc μ l f.1 f.2
    have hU2 := g63a_hom_U DB DA inc μ l g.1 g.2
    let Φ : SimpleSpace DA l → (SimpleSpace DA l →ₗ[k] SimpleSpace DA l) :=
      fun x => g63a_F DB DA inc μ l x ∘ₗ g63a_G DB DA inc μ l φ
    have hΦ : ∀ x u, g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) x = x → g63a_ρ DA l inc (g63a_E DB μ (e0 μ) (e0 μ)) u = u → Φ x u = φ u • x := by
      intro x u hx hu
      simp only [Φ, LinearMap.comp_apply]
      rw [g63a_G_U DB DA inc μ l φ u hu]
      exact g63a_F_U DB DA inc μ l x hx _
    have hint : ∀ x b v, Φ x (simpleAction DA l (inc b) v) = simpleAction DA l (inc b) (Φ x v) := by
      intro x b v
      simp only [Φ, LinearMap.comp_apply]
      rw [g63a_G_int, g63a_F_mem DB DA inc μ l x b]
    let X : (SimpleSpace DA l →ₗ[k] SimpleSpace DA l) → A :=
      fun T => DA.equiv.symm (Pi.single l (LinearMap.toMatrix' T))
    have hX : ∀ T : SimpleSpace DA l →ₗ[k] SimpleSpace DA l,
        (∀ b v, T (simpleAction DA l (inc b) v) = simpleAction DA l (inc b) (T v)) →
        X T ∈ Subalgebra.centralizer k (Set.range inc) := by
      intro T hT
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      apply DA.equiv.injective; funext ν
      simp only [X, map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply]
      by_cases hν : ν = l
      · subst hν
        simp only [Pi.single_eq_same]
        apply Matrix.toLin'.injective
        rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
        apply LinearMap.ext; intro v
        exact (hT b v).symm
      · simp [Pi.single_eq_of_ne hν]
    have hXT : ∀ T, Matrix.toLin' (DA.equiv (X T) l) = T := by
      intro T; simp [X]
    have hcm := hcomm ⟨X (Φ u1), hX _ (hint u1)⟩ ⟨X (Φ u2), hX _ (hint u2)⟩
    have h2 := congrArg (fun z : Subalgebra.centralizer k (Set.range inc) =>
      Matrix.toLin' (DA.equiv (z : A) l) u2) hcm
    simp only [Subalgebra.coe_mul, map_mul, Pi.mul_apply, Matrix.toLin'_mul, LinearMap.comp_apply,
      hXT] at h2
    rw [hΦ u2 u2 hU2 hU2, hΦ u1 u2 hU1 hU2] at h2
    simp only [map_smul] at h2
    rw [hΦ u1 u2 hU1 hU2, hΦ u2 u1 hU2 hU1, hφu1, zero_smul, smul_zero, smul_smul] at h2
    exact hu1 ((smul_eq_zero.mp h2).resolve_left (mul_ne_zero hφ2 hφ2))



end
