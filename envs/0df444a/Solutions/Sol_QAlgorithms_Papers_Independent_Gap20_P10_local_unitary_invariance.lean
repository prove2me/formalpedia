-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P10.local_unitary_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:06:09.121784+00:00
-- url     : https://prove2.me/submissions/d88a789f-e1e2-4a0e-a29b-4e34214880e2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq
lemma g73d_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

def g73d_ptr {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ) : Matrix X X ℂ :=
  fun a b => ∑ r, M (e.symm (a, r)) (e.symm (b, r))

lemma g73d_ptr_conj {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y] [DecidableEq Y]
    (e : Z ≃ X × Y) (M W : Matrix Z Z ℂ) (A : Matrix X X ℂ) (B : Matrix Y Y ℂ)
    (hB : Bᴴ * B = 1)
    (hW : ∀ a r p t, W (e.symm (a, r)) (e.symm (p, t)) = A a p * B r t) :
    g73d_ptr e (W * M * Wᴴ) = A * g73d_ptr e M * Aᴴ := by
  have h1 : ∀ f : Z → ℂ, ∑ z, f z = ∑ p, ∑ t, f (e.symm (p, t)) := fun f => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hB' : ∀ t t', ∑ r, star (B r t') * B r t = if t' = t then 1 else 0 := by
    intro t t'
    have := congrFun (congrFun hB t') t
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext a b
  simp only [g73d_ptr, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [h1 (fun z => _ * star _), h1 (fun z => W _ z * M z _), hW]
  simp only [star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc _ = ∑ r, ∑ p, ∑ t, ∑ t', A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
        (star (A b q) * star (B r t')) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ t, ∑ t', ∑ r, A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
        (star (A b q) * star (B r t')) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun t _ => ?_
        have : ∀ t', ∑ r, A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
            (star (A b q) * star (B r t')) = A a p * M (e.symm (p, t)) (e.symm (q, t')) *
            star (A b q) * (∑ r, star (B r t') * B r t) := by
          intro t'; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
        simp_rw [this, hB']
        simp

lemma g73d_ptr_herm {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ)
    (hM : M.IsHermitian) : (g73d_ptr e M).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, g73d_ptr, star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Matrix.conjTranspose_apply, hM]

def g73d_prodU {ι : Type*} [Fintype ι] {F : ι → Type*} (U : ∀ i, Matrix (F i) (F i) ℂ) :
    Matrix (∀ i, F i) (∀ i, F i) ℂ := fun a b => ∏ i, U i (a i) (b i)

lemma g73d_prodU_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*} [∀ i, Fintype (F i)]
    (U W : ∀ i, Matrix (F i) (F i) ℂ) :
    g73d_prodU U * g73d_prodU W = g73d_prodU (fun i => U i * W i) := by
  ext a c
  simp only [g73d_prodU, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma g73d_prodU_ct {ι : Type*} [Fintype ι] {F : ι → Type*}
    (U : ∀ i, Matrix (F i) (F i) ℂ) :
    (g73d_prodU U)ᴴ = g73d_prodU (fun i => (U i)ᴴ) := by
  ext a b
  simp [g73d_prodU, Matrix.conjTranspose_apply]

lemma g73d_prodU_one {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, DecidableEq (F i)] :
    g73d_prodU (fun i => (1 : Matrix (F i) (F i) ℂ)) = 1 := by
  ext a b
  simp only [g73d_prodU, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma g73d_prodU_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (U : ∀ i, Matrix (F i) (F i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (g73d_prodU U)ᴴ * g73d_prodU U = 1 := by
  rw [g73d_prodU_ct, g73d_prodU_mul]
  simp_rw [hU]
  exact g73d_prodU_one

lemma g73d_conj_pow {X : Type*} [Fintype X] [DecidableEq X] (A M : Matrix X X ℂ)
    (hA : Aᴴ * A = 1) (k : ℕ) : (A * M * Aᴴ) ^ (k + 1) = A * M ^ (k + 1) * Aᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * M ^ (k + 1) * Aᴴ * (A * M * Aᴴ) = A * M ^ (k + 1) * (Aᴴ * A) * M * Aᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, Matrix.mul_one, pow_succ M (k + 1)]; simp only [Matrix.mul_assoc]

lemma g73d_entropy_conj {X : Type*} [Fintype X] {_ : DecidableEq X} (A M : Matrix X X ℂ)
    (hA : Aᴴ * A = 1) (hM : M.IsHermitian) : vnEntropy (A * M * Aᴴ) = vnEntropy M := by
  unfold vnEntropy
  have hH : (A * M * Aᴴ).IsHermitian := by
    exact Matrix.isHermitian_mul_mul_conjTranspose A hM
  rw [g73d_trace_cfc_eq _ _ hH hM _ (by simp)]
  intro k
  rw [g73d_conj_pow A M hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, Matrix.one_mul]

lemma g73d_unprimed_ptr {n : ℕ} {D G : Fin n → Type} [∀ i, Fintype (G i)]
    (X : Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ) :
    unprimedMarginal X = g73d_ptr (Equiv.arrowProdEquivProdArrow _ D G) X := by
  ext a b; rfl

lemma g73d_primed_ptr {n : ℕ} {D G : Fin n → Type} [∀ i, Fintype (D i)]
    (X : Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ) :
    primedMarginal X = g73d_ptr ((Equiv.arrowProdEquivProdArrow _ D G).trans (Equiv.prodComm _ _)) X := by
  ext a b; rfl

def g73d_es {n : ℕ} (F : Fin n → Type) (s : Finset (Fin n)) :
    RegisterBasis F ≃ (SubBasis F s × Unit) × ((i : {x : Fin n // ¬ x ∈ s}) → F i.1) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ s) F).trans
    (Equiv.prodCongr (Equiv.prodPUnit _).symm (Equiv.refl _))

lemma g73d_es_pos {n : ℕ} (F : Fin n → Type) (s : Finset (Fin n)) (a : SubBasis F s × Unit)
    (r : (i : {x : Fin n // ¬ x ∈ s}) → F i.1) (i : Fin n) (hi : i ∈ s) :
    (g73d_es F s).symm (a, r) i = a.1 ⟨i, hi⟩ := by
  simp [g73d_es, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

lemma g73d_es_neg {n : ℕ} (F : Fin n → Type) (s : Finset (Fin n)) (a : SubBasis F s × Unit)
    (r : (i : {x : Fin n // ¬ x ∈ s}) → F i.1) (i : Fin n) (hi : i ∉ s) :
    (g73d_es F s).symm (a, r) i = r ⟨i, hi⟩ := by
  simp [g73d_es, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

lemma g73d_reg_ptr {n : ℕ} {F : Fin n → Type} [∀ i, Fintype (F i)]
    (X : Matrix (RegisterBasis F) (RegisterBasis F) ℂ) (s : Finset (Fin n)) :
    registerMarginal (trivialExtension X) s = g73d_ptr (g73d_es F s) X := by
  ext a b
  set e := Equiv.piEquivPiSubtypeProd (· ∈ s) F
  simp only [registerMarginal, trivialExtension, g73d_ptr]
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp (fun y => if _ then _ else _)]
  simp only [Fintype.sum_prod_type]
  have key : ∀ x y x1 y1, ((∀ (i : Fin n) (hi : i ∈ s), e.symm (x, y) i = a.1 ⟨i, hi⟩ ∧
      e.symm (x1, y1) i = b.1 ⟨i, hi⟩) ∧ ∀ i ∉ s, e.symm (x, y) i = e.symm (x1, y1) i) ↔
      (x = a.1 ∧ x1 = b.1 ∧ y = y1) := by
    intro x y x1 y1
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · funext i; have := (h1 i.1 i.2).1; simpa [i.2] using this
      · funext i; have := (h1 i.1 i.2).2; simpa [i.2] using this
      · funext i; have := h2 i.1 i.2; simpa [i.2] using this
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨fun i hi => by simp [hi], fun i hi => by simp [hi]⟩
  simp_rw [key, ite_and]
  simp [e, g73d_es]

lemma g73d_kron_unitary {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (U : Matrix X X ℂ) (hU : Uᴴ * U = 1) :
    (Matrix.kroneckerMap (· * ·) U (1 : Matrix Y Y ℂ))ᴴ *
      Matrix.kroneckerMap (· * ·) U (1 : Matrix Y Y ℂ) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU]
  simp

def g73d_liftU {X : Type*} (A : Matrix X X ℂ) : Matrix (X × Unit) (X × Unit) ℂ :=
  Matrix.of fun x y => A x.1 y.1

lemma g73d_unitU {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ)
    (hA : Aᴴ * A = 1) : (g73d_liftU A)ᴴ * g73d_liftU A = 1 := by
  ext a b
  have := congrFun (congrFun hA a.1) b.1
  simp only [g73d_liftU, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton] at this ⊢
  rw [this]
  simp [Matrix.one_apply, Prod.ext_iff]

section
variable {n : ℕ} {D G : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (G i)]

def g73d_W (U : ∀ i, Matrix (D i) (D i) ℂ) :
    Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ :=
  g73d_prodU (fun i => Matrix.kroneckerMap (· * ·) (U i) (1 : Matrix (G i) (G i) ℂ))

lemma g73d_W_unitary (U : ∀ i, Matrix (D i) (D i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (g73d_W (G := G) U)ᴴ * g73d_W U = 1 :=
  g73d_prodU_unitary _ (fun i => g73d_kron_unitary (U i) (hU i))

lemma g73d_W_unprimed (U : ∀ i, Matrix (D i) (D i) ℂ)
    (X : Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ) :
    unprimedMarginal (g73d_W U * X * (g73d_W U)ᴴ) =
      g73d_prodU U * unprimedMarginal X * (g73d_prodU U)ᴴ := by
  rw [g73d_unprimed_ptr, g73d_unprimed_ptr]
  apply g73d_ptr_conj _ _ _ _ 1 (by simp)
  intro a r p t
  rw [← g73d_prodU_one]
  simp [g73d_W, g73d_prodU, Matrix.kroneckerMap_apply, Finset.prod_mul_distrib]

lemma g73d_W_primed (U : ∀ i, Matrix (D i) (D i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1)
    (X : Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ) :
    primedMarginal (g73d_W U * X * (g73d_W U)ᴴ) = primedMarginal X := by
  rw [g73d_primed_ptr, g73d_primed_ptr]
  rw [g73d_ptr_conj _ _ _ 1 (g73d_prodU U) (g73d_prodU_unitary U hU)]
  · simp
  intro a r p t
  rw [← g73d_prodU_one]
  simp [g73d_W, g73d_prodU, Matrix.kroneckerMap_apply, Finset.prod_mul_distrib, mul_comm]

lemma g73d_W_entropy (U : ∀ i, Matrix (D i) (D i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1)
    (X : Matrix (RegisterBasis (fun i => D i × G i)) (RegisterBasis (fun i => D i × G i)) ℂ)
    (hX : X.IsHermitian) (s : Finset (Fin n)) :
    entropyAt (trivialExtension (g73d_W U * X * (g73d_W U)ᴴ)) s =
      entropyAt (trivialExtension X) s := by
  unfold entropyAt
  rw [g73d_reg_ptr, g73d_reg_ptr]
  have hKu : ∀ i, (Matrix.kroneckerMap (· * ·) (U i) (1 : Matrix (G i) (G i) ℂ))ᴴ *
      Matrix.kroneckerMap (· * ·) (U i) (1 : Matrix (G i) (G i) ℂ) = 1 :=
    fun i => g73d_kron_unitary (U i) (hU i)
  have hAu := g73d_unitU _ (g73d_prodU_unitary
    (fun i : {x : Fin n // x ∈ s} => Matrix.kroneckerMap (· * ·) (U i.1) (1 : Matrix (G i.1) (G i.1) ℂ))
    (fun i => hKu i.1))
  rw [g73d_ptr_conj _ _ _ _ (g73d_prodU (fun i : {x : Fin n // ¬ x ∈ s} =>
      Matrix.kroneckerMap (· * ·) (U i.1) (1 : Matrix (G i.1) (G i.1) ℂ)))
    (g73d_prodU_unitary _ (fun i => hKu i.1))]
  · exact g73d_entropy_conj _ _ (by convert hAu) (g73d_ptr_herm _ _ hX)
  intro a r p t
  simp only [g73d_W, g73d_prodU, g73d_liftU, Matrix.of_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ s)]
  congr 1
  · refine (Finset.prod_congr rfl fun (i : {x // x ∈ s}) _ => ?_).trans
      (Finset.prod_congr (by ext; simp) (fun _ _ => rfl))
    rw [g73d_es_pos _ _ _ _ _ i.2, g73d_es_pos _ _ _ _ _ i.2]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [g73d_es_neg _ _ _ _ _ i.2, g73d_es_neg _ _ _ _ _ i.2]
end

lemma g73d_values_sub {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (U : ∀ i, Matrix (D i) (D i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1)
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    cemiValues ρ ⊆ cemiValues (g73d_prodU U * ρ * (g73d_prodU U)ᴴ) := by
  rintro v ⟨d, hd, ω, hω, hm, rfl⟩
  refine ⟨d, hd, g73d_W (G := fun i => Fin (d i)) U * ω * (g73d_W U)ᴴ, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact hω.1.mul_mul_conjTranspose_same _
  · have hWu : (g73d_W (G := fun i => Fin (d i)) U)ᴴ * g73d_W U = 1 := by
      convert g73d_W_unitary (G := fun i => Fin (d i)) U hU
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWu, Matrix.one_mul]
    exact hω.2
  · rw [g73d_W_unprimed, hm]
  · unfold pairedDifference info conditionalMultipartiteInformation
    rw [g73d_W_primed U hU]
    simp_rw [g73d_W_entropy U hU ω hω.1.isHermitian]

theorem solution :
    IsLocalUnitaryInvariant (cemiFunctional (n := 2)) := by
  intro s t hdims U V hV
  obtain ⟨dt, ht, rt, hnt⟩ := t
  simp only at hdims
  subst hdims
  have hrt : rt = V * s.rho * Vᴴ := by
    ext x y
    rw [← hV x y]
    simp [stateEntry]
  have hUu : ∀ i, ((U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ))ᴴ * (U i : Matrix _ _ ℂ) = 1 :=
    fun i => Matrix.mem_unitaryGroup_iff'.mp (U i).2
  have hVdef : V = g73d_prodU (fun i => (U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ)) := rfl
  have hUu' : ∀ i, (((U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ))ᴴ)ᴴ *
      ((U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ))ᴴ = 1 := by
    intro i
    rw [Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (U i).2
  have hVu : Vᴴ * V = 1 := by rw [hVdef]; exact g73d_prodU_unitary _ hUu
  show cemi rt = cemi s.rho
  unfold cemi
  congr 1
  apply le_antisymm
  · have h2 := g73d_values_sub (fun i => ((U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ))ᴴ)
      (fun i => by convert hUu' i) rt
    rw [← g73d_prodU_ct, ← hVdef, hrt, Matrix.conjTranspose_conjTranspose] at h2
    have : Vᴴ * (V * s.rho * Vᴴ) * V = s.rho := by
      simp only [← Matrix.mul_assoc, hVu, Matrix.one_mul]
      rw [Matrix.mul_assoc, hVu, Matrix.mul_one]
    rw [hrt]; rwa [this] at h2
  · rw [hrt, hVdef]; exact g73d_values_sub _ (fun i => by convert hUu i) s.rho
