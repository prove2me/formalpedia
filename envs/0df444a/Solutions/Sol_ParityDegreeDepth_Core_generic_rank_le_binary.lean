-- Prove2me | solution 1 for ParityDegreeDepth.Core.generic_rank_le_binary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:54.636151+00:00
-- url     : https://prove2.me/submissions/b1f0b9e8-af28-4f3e-a582-f129d1185a89

import Mathlib

-- ===== T35b =====

open Matrix

namespace T35aux

section rank
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

theorem exists_li_cols (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (fun j => A.col (c j)) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have hbfin : b.Finite := (Set.finite_range A.col).subset hb
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = k := by
    have h1 := finrank_span_eq_card (R := K) hli
    rw [Subtype.range_coe, hspan, ← Matrix.rank_eq_finrank_span_cols, hk] at h1
    exact h1.symm
  let e : Fin k ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hchoice : ∀ x : b, ∃ j, A.col j = x := fun x => hb x.2
  choose c hc using hchoice
  refine ⟨fun j => c (e j), ?_⟩
  have : (fun j => A.col (c (e j))) = fun j => ((e j : b) : m → K) := by
    funext j; exact hc (e j)
  rw [this]
  exact hli.comp e e.injective

theorem exists_minor_of_le_rank [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c0, hc0⟩ := exists_li_cols A rfl
  let c : Fin k → n := fun j => c0 (Fin.castLE hk j)
  have hc : LinearIndependent K (fun j => A.col (c j)) :=
    hc0.comp _ (Fin.castLE_injective hk)
  set N : Matrix m (Fin k) K := A.submatrix id c with hN
  have hNcol : N.col = fun j => A.col (c j) := by
    funext j; ext i; rfl
  have hNrank : N.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, hNcol, finrank_span_eq_card hc, Fintype.card_fin]
  have hNt : Nᵀ.rank = k := by rw [Matrix.rank_transpose, hNrank]
  obtain ⟨r, hr⟩ := exists_li_cols Nᵀ hNt
  refine ⟨r, c, ?_⟩
  have hrows : LinearIndependent K (A.submatrix r c).row := by
    have : (A.submatrix r c).row = fun i => Nᵀ.col (r i) := by
      funext i; ext j; rfl
    rw [this]; exact hr
  have hunit : IsUnit (A.submatrix r c) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

theorem le_rank_of_minor [Fintype m] (A : Matrix m n K) {k : ℕ} (r : Fin k → m) (c : Fin k → n)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  classical
  have h1 := Matrix.rank_submatrix_le A r c
  have h2 : (A.submatrix r c).rank = k := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))]
    simp
  omega

end rank

theorem det_map_hom {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [Fintype k] [DecidableEq k]
    (f : R →+* S) (M : Matrix k k R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem adj_map_hom {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [Fintype k] [DecidableEq k]
    (f : R →+* S) (M : Matrix k k R) : (M.map f).adjugate = M.adjugate.map f :=
  (RingHom.map_adjugate f M).symm

section domain
variable {S : Type*} [CommRing S] [IsDomain S] {m n : Type*} [Fintype m] [Fintype n]

local notation "Kf" => FractionRing S

theorem rank_le_of_minors (A : Matrix m n S) (k : ℕ)
    (h : ∀ (r : Fin (k+1) → m) (c : Fin (k+1) → n), (A.submatrix r c).det = 0) :
    (A.map (algebraMap S Kf)).rank ≤ k := by
  by_contra hk
  push Not at hk
  obtain ⟨r, c, hrc⟩ := exists_minor_of_le_rank (A.map (algebraMap S Kf)) (k := k+1) hk
  apply hrc
  rw [show (A.map (algebraMap S Kf)).submatrix r c = (A.submatrix r c).map (algebraMap S Kf) from rfl,
    det_map_hom, h r c, map_zero]

theorem le_rank_of_minor' (A : Matrix m n S) {k : ℕ} (r : Fin k → m) (c : Fin k → n)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ (A.map (algebraMap S Kf)).rank := by
  apply le_rank_of_minor _ r c
  rw [show (A.map (algebraMap S Kf)).submatrix r c = (A.submatrix r c).map (algebraMap S Kf) from rfl,
    det_map_hom]
  exact (map_ne_zero_iff _ (IsFractionRing.injective S Kf)).mpr h

theorem minors_zero_of_rank_le (A : Matrix m n S) {k : ℕ} (hk : (A.map (algebraMap S Kf)).rank ≤ k)
    (r : Fin (k+1) → m) (c : Fin (k+1) → n) : (A.submatrix r c).det = 0 := by
  by_contra h
  have := le_rank_of_minor' A r c h
  omega

end domain

section bordered

theorem det_bordered_field {K : Type*} [Field K] {R : ℕ} (P : Matrix (Fin R) (Fin R) K)
    (hP : P.det ≠ 0) (β γ : Fin R → K) (e : K) :
    (Matrix.fromBlocks P (Matrix.of fun i (_ : Unit) => β i) (Matrix.of fun (_ : Unit) j => γ j)
      (Matrix.of fun (_ : Unit) (_ : Unit) => e)).det = P.det * e - γ ⬝ᵥ (P.adjugate *ᵥ β) := by
  have : Invertible P := Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)
  have hu : ∀ A : Matrix Unit Unit K, A.det = A () () := fun A => Matrix.det_unique A
  rw [Matrix.det_fromBlocks₁₁, hu]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv, Matrix.inv_def,
    Ring.inverse_eq_inv']
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Fintype.univ_unit,
    Finset.sum_singleton, dotProduct, mulVec]
  rw [mul_sub]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  field_simp

variable {S : Type*} [CommRing S] [IsDomain S] {n : ℕ}

/-- Bordered-minor identity for a matrix of rank `≤ R` over the fraction field. -/
theorem bordered_identity (M : Matrix (Fin n) (Fin n) S) {R : ℕ}
    (hM : (M.map (algebraMap S (FractionRing S))).rank ≤ R) (I I' : Fin R → Fin n)
    (hP : (M.submatrix I I').det ≠ 0) (x y : Fin n → S) :
    (M.submatrix I I').det * (x ⬝ᵥ (M *ᵥ y)) =
      (fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ (fun b => (M *ᵥ y) (I b))) := by
  classical
  let φ := algebraMap S (FractionRing S)
  have hinj : Function.Injective φ := IsFractionRing.injective S (FractionRing S)
  -- the bordered matrix over S
  let X : Matrix (Fin R ⊕ Unit) (Fin n) S :=
    Matrix.of fun r j => Sum.elim (fun b => (Pi.single (I b) 1 : Fin n → S) j) (fun _ => x j) r
  let Y : Matrix (Fin n) (Fin R ⊕ Unit) S :=
    Matrix.of fun j c => Sum.elim (fun a => (Pi.single (I' a) 1 : Fin n → S) j) (fun _ => y j) c
  have hXM : ∀ r j, (X * M) r j = Sum.elim (fun b => M (I b) j) (fun _ => (x ᵥ* M) j) r := by
    intro r j
    rcases r with b | u
    · simp only [X, Matrix.mul_apply, Matrix.of_apply, Sum.elim_inl, Pi.single_apply]
      simp
    · simp only [X, Matrix.mul_apply, Matrix.of_apply, Sum.elim_inr, vecMul, dotProduct]
  have hG : X * M * Y = Matrix.fromBlocks (M.submatrix I I')
      (Matrix.of fun i (_ : Unit) => (M *ᵥ y) (I i))
      (Matrix.of fun (_ : Unit) j => (x ᵥ* M) (I' j))
      (Matrix.of fun (_ : Unit) (_ : Unit) => x ⬝ᵥ (M *ᵥ y)) := by
    ext r c
    rw [Matrix.mul_apply]
    simp only [hXM]
    rcases r with b | u <;> rcases c with a | v
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Pi.single_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.submatrix_apply]
      simp
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂, mulVec,
        dotProduct]
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Pi.single_apply,
        Matrix.fromBlocks_apply₂₁]
      simp
    · simp only [Y, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
      rw [Matrix.dotProduct_mulVec]; rfl
  have hdet0 : (X * M * Y).det = 0 := by
    by_contra hne
    have hmap : ((X * M * Y).map φ).det ≠ 0 := by
      rw [det_map_hom]; exact (map_ne_zero_iff _ hinj).mpr hne
    have hrank : ((X * M * Y).map φ).rank = R + 1 := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hmap))]
      simp
    have hle : ((X * M * Y).map φ).rank ≤ R := by
      rw [Matrix.map_mul, Matrix.map_mul]
      exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hM)
    omega
  rw [hG] at hdet0
  have hPK : ((M.submatrix I I').map φ).det ≠ 0 := by
    rw [det_map_hom]; exact (map_ne_zero_iff _ hinj).mpr hP
  have key := det_bordered_field ((M.submatrix I I').map φ) hPK
    (fun b => φ ((M *ᵥ y) (I b))) (fun a => φ ((x ᵥ* M) (I' a))) (φ (x ⬝ᵥ (M *ᵥ y)))
  have hmapG : (Matrix.fromBlocks ((M.submatrix I I').map φ)
      (Matrix.of fun i (_ : Unit) => φ ((M *ᵥ y) (I i)))
      (Matrix.of fun (_ : Unit) j => φ ((x ᵥ* M) (I' j)))
      (Matrix.of fun (_ : Unit) (_ : Unit) => φ (x ⬝ᵥ (M *ᵥ y)))) =
      (Matrix.fromBlocks (M.submatrix I I')
      (Matrix.of fun i (_ : Unit) => (M *ᵥ y) (I i))
      (Matrix.of fun (_ : Unit) j => (x ᵥ* M) (I' j))
      (Matrix.of fun (_ : Unit) (_ : Unit) => x ⬝ᵥ (M *ᵥ y))).map φ := by
    rw [Matrix.fromBlocks_map]; rfl
  rw [hmapG, det_map_hom, hdet0, map_zero, det_map_hom] at key
  apply hinj
  have : φ ((M.submatrix I I').det * (x ⬝ᵥ (M *ᵥ y))) =
      φ ((fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ (fun b => (M *ᵥ y) (I b)))) := by
    rw [map_mul]
    have h2 : φ ((fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ
        (fun b => (M *ᵥ y) (I b)))) = (fun a => φ ((x ᵥ* M) (I' a))) ⬝ᵥ
        (((M.submatrix I I').map φ).adjugate *ᵥ (fun b => φ ((M *ᵥ y) (I b)))) := by
      rw [adj_map_hom]
      simp [dotProduct, mulVec, map_sum, map_mul]
    rw [h2]
    linear_combination -key
  exact this

end bordered

end T35aux

-- ===== GridSZ =====

open MvPolynomial
open scoped BigOperators

/-- multiplicity of a root (least total degree of a monomial of `p(a + z)`) -/
noncomputable def rootMult {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K)
    (p : MvPolynomial (Fin n) K) : ℕ :=
  sInf ((fun s : Fin n →₀ ℕ => ∑ i, s i) '' ↑(aeval (fun i => X i + C (a i)) p).support)

namespace GridSZ
section
variable {K : Type*} [CommRing K] {n : ℕ}

noncomputable def shift (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun j => X j + C (a j)

lemma shift_add (a b : Fin n → K) (p : MvPolynomial (Fin n) K) :
    shift a (shift b p) = shift (a + b) p := by
  have h : (shift a).comp (shift b) = shift (a + b) := by
    ext j
    simp [shift, add_assoc]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

lemma shift_zero (p : MvPolynomial (Fin n) K) : shift 0 p = p := by
  have h : shift (0 : Fin n → K) = AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp [shift]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

lemma shift_ne_zero (a : Fin n → K) {p : MvPolynomial (Fin n) K} (hp : p ≠ 0) :
    shift a p ≠ 0 := by
  intro h
  have hh := congrArg (shift (-a)) h
  rw [shift_add, neg_add_cancel, shift_zero, map_zero] at hh
  exact hp hh

lemma rootMult_le (a : Fin n → K) (p : MvPolynomial (Fin n) K)
    (s : Fin n →₀ ℕ) (hs : coeff s (shift a p) ≠ 0) : rootMult a p ≤ ∑ j, s j := by
  apply Nat.sInf_le
  exact ⟨s, mem_support_iff.mpr hs, rfl⟩

lemma exists_rootMult (a : Fin n → K) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∃ s : Fin n →₀ ℕ, coeff s (shift a p) ≠ 0 ∧ (∑ j, s j) = rootMult a p := by
  have hs : (shift a p).support.Nonempty := by
    change (MvPolynomial.support (shift a p)).Nonempty
    exact MvPolynomial.support_nonempty.mpr (shift_ne_zero a hp)
  have hn : (((fun s : Fin n →₀ ℕ => ∑ j, s j) '' ↑(shift a p).support) : Set ℕ).Nonempty := by
    obtain ⟨s, hs⟩ := hs
    exact ⟨_, s, hs, rfl⟩
  obtain ⟨s, hs, he⟩ := Nat.sInf_mem hn
  exact ⟨s, mem_support_iff.mp hs, he⟩

noncomputable def splitR (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) (Polynomial K) :=
  (renameEquiv K (_root_.finSuccEquiv n)).trans (optionEquivRight K (Fin n))

lemma splitR_C (c : K) : splitR n (C c) = C (Polynomial.C c) := by
  simp [splitR, optionEquivRight_C]

lemma splitR_X_zero : splitR n (X 0 : MvPolynomial (Fin (n+1)) K) = C Polynomial.X := by
  simp [splitR, optionEquivRight_X_none]

lemma splitR_X_succ (j : Fin n) : splitR n (X j.succ : MvPolynomial (Fin (n+1)) K) = X j := by
  simp [splitR, optionEquivRight_X_some]

lemma splitR_apply (p : MvPolynomial (Fin (n+1)) K) :
    splitR n p = aeval (Fin.cases (C Polynomial.X) (fun j => X j)) p := by
  have h : (splitR (K := K) n).toAlgHom =
      aeval (Fin.cases (C Polynomial.X) (fun j => X j)) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [splitR_X_zero]
    · simp [splitR_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) (Polynomial K) => f p) h

lemma splitR_monomial (t : Fin (n+1) →₀ ℕ) (c : K) :
    splitR n (monomial t c) = monomial t.tail (Polynomial.monomial (t 0) c) := by
  classical
  rw [splitR_apply, aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [monomial_eq, Finsupp.prod_pow]
  simp only [Finsupp.tail_apply]
  rw [← map_pow]
  rw [show algebraMap K (MvPolynomial (Fin n) (Polynomial K)) c = C (Polynomial.C c) from rfl,
    ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

lemma splitR_coeff (s : Fin n →₀ ℕ) (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (splitR n p)).coeff k = coeff (s.cons k) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hr]
  | monomial t c =>
    rw [splitR_monomial, coeff_monomial]
    by_cases ht : t.tail = s
    · rw [if_pos ht, Polynomial.coeff_monomial, coeff_monomial]
      have he : t = s.cons k ↔ t 0 = k := by
        constructor
        · intro he; simpa using congrArg (fun z => z 0) he
        · intro hk
          rw [← Finsupp.cons_tail t, ht, hk]
      simp [he]
    · rw [if_neg ht, Polynomial.coeff_zero, coeff_monomial]
      have he : t ≠ s.cons k := by intro h; apply ht; rw [h]; simp
      simp [he]


lemma splitR_shift (a : Fin n → K) (b : K)
    (p : MvPolynomial (Fin (n+1)) K) :
    splitR n (shift (Fin.cons b a) p) =
      MvPolynomial.map (Polynomial.compRingHom (Polynomial.X + Polynomial.C b))
        (shift (fun j => Polynomial.C (a j)) (splitR n p)) := by
  let f := Polynomial.compRingHom (Polynomial.X + Polynomial.C b)
  have h : (splitR (K := K) n).toRingHom.comp (shift (Fin.cons b a)).toRingHom =
      (MvPolynomial.map f).comp
        ((shift (fun j => Polynomial.C (a j))).toRingHom.comp (splitR (K := K) n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, splitR_C, f, Polynomial.coe_compRingHom]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, splitR_X_zero, splitR_C, f, Polynomial.coe_compRingHom]
      · simp [shift, splitR_X_succ, splitR_C, f, Polynomial.coe_compRingHom]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* MvPolynomial (Fin n) (Polynomial K) => h p) h

lemma splitL_shift (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K) :
    finSuccEquiv K n (shift (Fin.cons 0 a) p) =
      Polynomial.map (shift a).toRingHom (finSuccEquiv K n p) := by
  have h : (finSuccEquiv K n).toRingHom.comp (shift (Fin.cons 0 a)).toRingHom =
      (Polynomial.mapRingHom (shift a).toRingHom).comp (finSuccEquiv K n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, finSuccEquiv_X_zero, finSuccEquiv_apply]
      · simp [shift, finSuccEquiv_X_succ, finSuccEquiv_apply]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* Polynomial (MvPolynomial (Fin n) K) => h p) h

lemma slice_coeff (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).coeff k =
      coeff s (shift a ((finSuccEquiv K n p).coeff k)) := by
  have hr := splitR_shift a 0 p
  have hid : Polynomial.compRingHom (Polynomial.X : Polynomial K) = RingHom.id _ :=
    RingHom.ext fun _ => Polynomial.comp_X
  simp only [Polynomial.C_0, add_zero, hid, MvPolynomial.map_id] at hr
  rw [← hr, splitR_coeff, ← finSuccEquiv_coeff_coeff s (shift (Fin.cons 0 a) p) k,
    splitL_shift, Polynomial.coeff_map]
  rfl

lemma slice_shift_coeff (a : Fin n → K) (b : K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    coeff (s.cons k) (shift (Fin.cons b a) p) =
      ((coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).comp
        (Polynomial.X + Polynomial.C b)).coeff k := by
  rw [← splitR_coeff, splitR_shift, coeff_map]
  rfl

lemma univariate_sum [IsDomain K] (S : Finset K) (p : Polynomial K) :
    ∑ a ∈ S, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  have h1 : ∑ a ∈ S, p.rootMultiplicity a = ∑ a ∈ S, (p.roots.filter (· ∈ S)).count a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Multiset.count_filter_of_pos ha, Polynomial.count_roots]
  have h2 : ∑ a ∈ S, (p.roots.filter (· ∈ S)).count a = Multiset.card (p.roots.filter (· ∈ S)) := by
    rw [← Multiset.toFinset_sum_count_eq]
    symm
    apply Finset.sum_subset
    · intro a ha
      rw [Multiset.mem_toFinset, Multiset.mem_filter] at ha
      exact ha.2
    · intro a _ ha
      rw [Multiset.mem_toFinset] at ha
      exact Multiset.count_eq_zero.mpr ha
  rw [h1, h2]
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (Polynomial.card_roots' p)

lemma slice_degree (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).natDegree ≤
      (finSuccEquiv K n p).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [slice_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero, coeff_zero]

lemma slice_root_bound [IsDomain K] (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K)
    (s : Fin n →₀ ℕ)
    (hs : coeff s (shift a (finSuccEquiv K n p).leadingCoeff) ≠ 0)
    (hm : (∑ j, s j) = rootMult a (finSuccEquiv K n p).leadingCoeff) (b : K) :
    rootMult (Fin.cons b a) p ≤ rootMult a (finSuccEquiv K n p).leadingCoeff +
      (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).rootMultiplicity b := by
  let r := coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))
  have hr : r ≠ 0 := by
    intro he
    have hz := congrArg (fun t : Polynomial K => t.coeff (finSuccEquiv K n p).natDegree) he
    rw [Polynomial.coeff_zero] at hz
    exact hs (by simpa only [r, slice_coeff, Polynomial.leadingCoeff] using hz)
  have hcoef : (r.comp (Polynomial.X + Polynomial.C b)).coeff (r.rootMultiplicity b) ≠ 0 := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Polynomial.comp_X_add_C_ne_zero_iff.mpr hr)
  have hb := rootMult_le (Fin.cons b a) p (s.cons (r.rootMultiplicity b)) (by
    rw [slice_shift_coeff]; exact hcoef)
  have hd : (∑ j, s.cons (r.rootMultiplicity b) j) = r.rootMultiplicity b + ∑ j, s j := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hd, hm] at hb
  exact hb.trans_eq (add_comm _ _)

lemma sum_slices [IsDomain K] (S : Finset K)
    (p : MvPolynomial (Fin (n+1)) K) (hp : p ≠ 0) (a : Fin n → K) :
    ∑ b ∈ S, rootMult (Fin.cons b a) p ≤
      S.card * rootMult a (finSuccEquiv K n p).leadingCoeff + (finSuccEquiv K n p).natDegree := by
  have hP : finSuccEquiv K n p ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
  have hg : (finSuccEquiv K n p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  obtain ⟨s, hs, hm⟩ := exists_rootMult a _ hg
  have h := Finset.sum_le_sum (fun b (_ : b ∈ S) =>
    slice_root_bound a p s hs hm b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h
  exact h.trans (Nat.add_le_add_left ((univariate_sum S _).trans (slice_degree a s p)) _)

/-- the DKSS multiplicity grid inequality on `S^n` -/
lemma grid_sum_bound [IsDomain K] (S : Finset K) (n : ℕ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    (∑ a : Fin n → S, rootMult (fun i => (a i : K)) p) * S.card ≤ p.totalDegree * S.card ^ n := by
  classical
  induction n with
  | zero =>
    have hm (a : Fin 0 → K) : rootMult a p = 0 := by
      obtain ⟨s, _, hs⟩ := exists_rootMult a p hp
      simpa using hs.symm
    simp only [hm, Finset.sum_const_zero, zero_mul]
    exact Nat.zero_le _
  | succ n ih =>
    let P := finSuccEquiv K n p
    have hP : P ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
    let g := P.leadingCoeff
    have hg : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hdeg : g.totalDegree + P.natDegree ≤ p.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le p P.natDegree hg
    have hrec := ih g hg
    have hs : ∑ a : Fin (n+1) → S, rootMult (fun i => (a i : K)) p =
        ∑ a : Fin n → S, ∑ b ∈ S, rootMult (Fin.cons b (fun i => (a i : K))) p := by
      have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => S))
        (fun z => rootMult (Fin.cons (z.1 : K) (fun i => (z.2 i : K))) p)
        (fun a => rootMult (fun i => (a i : K)) p) (fun z => by
          congr 1; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv])
      rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (Finset.sum_coe_sort S (fun b => rootMult (Fin.cons b (fun i => (a i : K))) p))
    have hsum : ∑ a : Fin (n+1) → S, rootMult (fun i => (a i : K)) p ≤
        S.card * (∑ a : Fin n → S, rootMult (fun i => (a i : K)) g) + P.natDegree * S.card ^ n := by
      rw [hs]
      have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n → S))) =>
        sum_slices S p hp (fun i => (a i : K)))
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, smul_eq_mul,
        mul_comm] using h
    have hscaled := Nat.mul_le_mul_right S.card hsum
    have hi := Nat.mul_le_mul_left S.card hrec
    have hd := Nat.mul_le_mul_right (S.card ^ (n+1)) hdeg
    rw [pow_succ] at hd ⊢
    nlinarith

end
end GridSZ

-- ===== L33a =====

open MvPolynomial Matrix

namespace L33aux

noncomputable section

variable {D : Type*} [CommRing D] {n : ℕ}

/-- all monomials have degree at least `k` -/
def LowOrd (k : ℕ) (q : MvPolynomial (Fin n) D) : Prop := ∀ e ∈ q.support, k ≤ ∑ i, e i

/-- all monomials have degree at most `k` -/
def UpDeg (k : ℕ) (q : MvPolynomial (Fin n) D) : Prop := ∀ e ∈ q.support, ∑ i, e i ≤ k

lemma lowOrd_zero (q : MvPolynomial (Fin n) D) : LowOrd 0 q := fun _ _ => Nat.zero_le _

lemma lowOrd_add {k : ℕ} {p q : MvPolynomial (Fin n) D} (hp : LowOrd k p) (hq : LowOrd k q) :
    LowOrd k (p + q) := by
  classical
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

lemma lowOrd_sum {ι : Type*} (s : Finset ι) {k : ℕ} (f : ι → MvPolynomial (Fin n) D)
    (h : ∀ i ∈ s, LowOrd k (f i)) : LowOrd k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro e he; simp at he
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lowOrd_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma lowOrd_mul {k l : ℕ} {p q : MvPolynomial (Fin n) D} (hp : LowOrd k p) (hq : LowOrd l q) :
    LowOrd (k + l) (p * q) := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  have := hp a ha
  have := hq b hb
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

lemma lowOrd_prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (f : ι → MvPolynomial (Fin n) D)
    (h : ∀ i ∈ s, LowOrd (k i) (f i)) : LowOrd (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact lowOrd_zero _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact lowOrd_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma lowOrd_mono {k l : ℕ} (hkl : l ≤ k) {p : MvPolynomial (Fin n) D} (hp : LowOrd k p) :
    LowOrd l p := fun e he => hkl.trans (hp e he)

lemma lowOrd_C_mul {k : ℕ} (c : D) {p : MvPolynomial (Fin n) D} (hp : LowOrd k p) :
    LowOrd k (C c * p) := by
  have := lowOrd_mul (lowOrd_zero (C c)) hp
  simpa using this

lemma lowOrd_intCast_mul {k : ℕ} (z : ℤ) {p : MvPolynomial (Fin n) D} (hp : LowOrd k p) :
    LowOrd k ((z : MvPolynomial (Fin n) D) * p) := by
  have := lowOrd_mul (lowOrd_zero (z : MvPolynomial (Fin n) D)) hp
  simpa using this

lemma lowOrd_linear (β : Fin n → D) : LowOrd 1 (∑ v, X v * C (β v) : MvPolynomial (Fin n) D) := by
  apply lowOrd_sum
  intro v _ e he
  rw [mul_comm, X, C_mul_monomial, mul_one] at he
  have he' := support_monomial_subset he
  rw [Finset.mem_singleton] at he'
  subst he'
  simp

lemma upDeg_add {k : ℕ} {p q : MvPolynomial (Fin n) D} (hp : UpDeg k p) (hq : UpDeg k q) :
    UpDeg k (p + q) := by
  classical
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

lemma upDeg_sum {ι : Type*} (s : Finset ι) {k : ℕ} (f : ι → MvPolynomial (Fin n) D)
    (h : ∀ i ∈ s, UpDeg k (f i)) : UpDeg k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro e he; simp at he
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact upDeg_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma upDeg_mul {k l : ℕ} {p q : MvPolynomial (Fin n) D} (hp : UpDeg k p) (hq : UpDeg l q) :
    UpDeg (k + l) (p * q) := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  have := hp a ha
  have := hq b hb
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

lemma upDeg_prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (f : ι → MvPolynomial (Fin n) D)
    (h : ∀ i ∈ s, UpDeg (k i) (f i)) : UpDeg (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    intro e he
    have h1 : (1 : MvPolynomial (Fin n) D) = monomial 0 1 := rfl
    rw [h1] at he
    have := support_monomial_subset he
    rw [Finset.mem_singleton] at this
    simp [this]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact upDeg_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma upDeg_intCast (z : ℤ) : UpDeg 0 (z : MvPolynomial (Fin n) D) := by
  intro e he
  rw [show (z : MvPolynomial (Fin n) D) = C (z : D) by simp, C_apply] at he
  have := support_monomial_subset he
  simp at this; simp [this]

lemma upDeg_linear (β : Fin n → D) : UpDeg 1 (∑ v, X v * C (β v) : MvPolynomial (Fin n) D) := by
  apply upDeg_sum
  intro v _ e he
  rw [mul_comm, X, C_mul_monomial, mul_one] at he
  have he' := support_monomial_subset he
  rw [Finset.mem_singleton] at he'
  subst he'
  simp

lemma totalDegree_le_of_upDeg {k : ℕ} {p : MvPolynomial (Fin n) D} (hp : UpDeg k p) :
    p.totalDegree ≤ k := by
  unfold totalDegree
  apply Finset.sup_le
  intro e he
  have := hp e he
  rwa [Finsupp.sum_fintype _ _ (by simp)]

lemma le_rootMult_of_lowOrd [IsDomain D] {k : ℕ} (a : Fin n → D) (p : MvPolynomial (Fin n) D)
    (hp : p ≠ 0) (h : LowOrd k (aeval (fun i => X i + C (a i)) p)) : k ≤ rootMult a p := by
  unfold rootMult
  have hne : ((fun s : Fin n →₀ ℕ => ∑ i, s i) ''
      ↑(aeval (fun i => X i + C (a i)) p).support).Nonempty := by
    have := GridSZ.shift_ne_zero a hp
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr this
    exact ⟨_, s, hs, rfl⟩
  apply le_csInf hne
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- determinant of a sum, expanded by choosing for each column one of the two summands
(`t` = the columns taken from `A`) -/
lemma det_add_cols {R : Type*} [CommRing R] {m : ℕ} (A Z : Matrix (Fin m) (Fin m) R) :
    (A + Z).det = ∑ t : Finset (Fin m),
      (Matrix.of fun i j => if j ∈ t then A i j else Z i j).det := by
  classical
  simp only [Matrix.det_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  simp only [Matrix.add_apply]
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.prod_mul_prod_compl t (fun i => (Matrix.of fun i j => if j ∈ t then A i j else Z i j) (σ i) i),
    Finset.compl_eq_univ_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    simp [hi]

end

end L33aux

-- ===== L33b =====

open MvPolynomial Matrix T35aux

namespace L33aux

noncomputable section

/-- rank over the fraction field -/
abbrev rk {S : Type*} [CommRing S] [IsDomain S] {m r : ℕ} (N : Matrix (Fin m) (Fin r) S) : ℕ :=
  (N.map (algebraMap S (FractionRing S))).rank

lemma rk_map_le {S T : Type*} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (φ : S →+* T) {m r : ℕ} (N : Matrix (Fin m) (Fin r) S) : rk (N.map φ) ≤ rk N := by
  apply rank_le_of_minors
  intro r' c'
  rw [show (N.map φ).submatrix r' c' = (N.submatrix r' c').map φ from rfl, det_map_hom,
    minors_zero_of_rank_le N le_rfl r' c', map_zero]

lemma rk_le_map {S T : Type*} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (φ : S →+* T) (hφ : Function.Injective φ) {m r : ℕ} (N : Matrix (Fin m) (Fin r) S) :
    rk N ≤ rk (N.map φ) := by
  obtain ⟨r', c', h⟩ := exists_minor_of_le_rank (N.map (algebraMap S (FractionRing S))) le_rfl
  apply le_rank_of_minor' (N.map φ) r' c'
  rw [show (N.map φ).submatrix r' c' = (N.submatrix r' c').map φ from rfl, det_map_hom]
  intro h0
  apply h
  rw [show (N.map (algebraMap S (FractionRing S))).submatrix r' c' =
    (N.submatrix r' c').map (algebraMap S (FractionRing S)) from rfl, det_map_hom,
    (map_eq_zero_iff φ hφ).mp h0, map_zero]

lemma rk_submatrix_le {S : Type*} [CommRing S] [IsDomain S] {m r m' r' : ℕ}
    (N : Matrix (Fin m) (Fin r) S) (I : Fin m' → Fin m) (J : Fin r' → Fin r) :
    rk (N.submatrix I J) ≤ rk N := by
  unfold rk
  rw [show (N.submatrix I J).map (algebraMap S (FractionRing S)) =
    (N.map (algebraMap S (FractionRing S))).submatrix I J from rfl]
  exact Matrix.rank_submatrix_le _ _ _

variable {D : Type*} [CommRing D] [IsDomain D]

lemma exists_ker_of_rk_lt {R : ℕ} (A0 : Matrix (Fin R) (Fin R) D) (s : Finset (Fin R))
    (hs : rk A0 < s.card) :
    ∃ l : Fin R → D, l ≠ 0 ∧ (∀ c ∉ s, l c = 0) ∧ A0 *ᵥ l = 0 := by
  classical
  set K := FractionRing D
  set A0K := A0.map (algebraMap D K)
  let f : s → (Fin R → K) := fun c => fun i => A0K i c
  have hnot : ¬ LinearIndependent K f := by
    intro hli
    have h1 : Fintype.card s ≤ A0K.rank := by
      rw [Matrix.rank_eq_finrank_span_cols]
      calc Fintype.card s = Module.finrank K (Submodule.span K (Set.range f)) :=
            (finrank_span_eq_card hli).symm
        _ ≤ Module.finrank K (Submodule.span K (Set.range A0K.col)) := by
            apply Submodule.finrank_mono
            apply Submodule.span_mono
            rintro _ ⟨c, rfl⟩
            exact ⟨c, rfl⟩
    rw [Fintype.card_coe] at h1
    exact absurd h1 (not_le.mpr hs)
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let G : Fin R → K := fun c => if h : c ∈ s then g ⟨c, h⟩ else 0
  have hG : ∀ i, ∑ c, A0K i c * G c = 0 := by
    intro i
    have := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply] at this
    rw [← Finset.sum_subset (Finset.subset_univ s) (fun c _ hc => by simp [G, hc])]
    rw [← Finset.sum_attach s, ← this, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [G, dif_pos c.2]
    ring
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D) G
  have hb' : ∀ c, ∃ y : D, algebraMap D K y = (b : D) • G c := fun c => hb c
  choose l hl using hb'
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  have hbne : algebraMap D K (b : D) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero b)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro h
    have := hl i0.1
    rw [h, Pi.zero_apply, map_zero, Algebra.smul_def] at this
    have hG0 : G i0.1 = g i0 := by simp [G, i0.2]
    rw [hG0] at this
    exact mul_ne_zero hbne hi0 this.symm
  · intro c hc
    have := hl c
    simp only [G, dif_neg hc, smul_zero] at this
    exact (map_eq_zero_iff _ hinj).mp this
  · funext i
    apply hinj
    rw [Pi.zero_apply, map_zero]
    simp only [mulVec, dotProduct, map_sum, map_mul, hl, Algebra.smul_def]
    have := hG i
    simp only [A0K, Matrix.map_apply] at this
    calc ∑ x, algebraMap D K (A0 i x) * (algebraMap D K (b : D) * G x)
        = algebraMap D K (b : D) * ∑ x, algebraMap D K (A0 i x) * G x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [this, mul_zero]

end

end L33aux

-- ===== L33c =====

open MvPolynomial Matrix T35aux

namespace L33aux

noncomputable section

variable {D : Type*} [CommRing D] [IsDomain D] {n : ℕ}

lemma shift_linear (a : Fin n → D) (β : Fin n → D) :
    aeval (fun i => X i + C (a i)) (∑ v, X v * C (β v) : MvPolynomial (Fin n) D) =
      C (∑ v, a v * β v) + ∑ v, X v * C (β v) := by
  simp only [map_sum, map_mul, aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- the multiplicity bound `mult_a(det) ≥ R - rank N(a)` for a linear pencil -/
lemma mult_bound {R : ℕ} (β : Fin n → Matrix (Fin R) (Fin R) D) (a : Fin n → D)
    (hP : (Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j)).det ≠ 0) :
    R - rk (∑ v, a v • β v) ≤
      rootMult a (Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j)).det := by
  classical
  apply le_rootMult_of_lowOrd a _ hP
  set A0 := ∑ v, a v • β v with hA0
  set Zm : Matrix (Fin R) (Fin R) (MvPolynomial (Fin n) D) :=
    Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j) with hZm
  have hshift : aeval (fun i => X i + C (a i)) (Zm.det) = (A0.map C + Zm).det := by
    rw [show (aeval (fun i => X i + C (a i)) : MvPolynomial (Fin n) D →ₐ[D] _) Zm.det =
      (aeval (fun i => X i + C (a i)) : MvPolynomial (Fin n) D →ₐ[D] _).toRingHom Zm.det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Zm, Matrix.of_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.add_apply]
    rw [shift_linear]
    congr 1
    simp [A0, Matrix.sum_apply, Matrix.smul_apply]
  rw [hshift, det_add_cols]
  apply lowOrd_sum
  intro t _
  by_cases ht : rk A0 < t.card
  · obtain ⟨l, hl0, hlt, hAl⟩ := exists_ker_of_rk_lt A0 t ht
    have hdet : (Matrix.of fun i j => if j ∈ t then A0.map C i j else Zm i j).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun c => C (l c), ?_, ?_⟩
      · intro h
        apply hl0
        funext c
        have := congrFun h c
        simpa using this
      · funext i
        simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        have : ∀ c, (if c ∈ t then A0.map C i c else Zm i c) * C (l c) = C (A0 i c * l c) := by
          intro c
          by_cases hc : c ∈ t
          · simp [hc]
          · simp [hc, hlt c hc]
        simp only [this, ← map_sum]
        have := congrFun hAl i
        simp only [mulVec, dotProduct, Pi.zero_apply] at this
        rw [this, map_zero]
    rw [hdet]
    intro e he; simp at he
  · push Not at ht
    have hrank : rk A0 ≤ rk (∑ v, a v • β v) := le_rfl
    rw [Matrix.det_apply']
    apply lowOrd_sum
    intro σ _
    apply lowOrd_intCast_mul
    have := lowOrd_prod Finset.univ (fun i => if i ∈ t then 0 else 1)
      (fun i => (Matrix.of fun i j => if j ∈ t then A0.map C i j else Zm i j) (σ i) i) (by
        intro i _
        by_cases hi : i ∈ t
        · simp only [hi, if_true, Matrix.of_apply]; exact lowOrd_zero _
        · simp only [hi, if_false, Matrix.of_apply, Zm]; exact lowOrd_linear _)
    apply lowOrd_mono _ this
    have hsum : ∑ i : Fin R, (if i ∈ t then 0 else 1) = R - t.card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp
    rw [hsum]
    omega

end

end L33aux

-- ===== L33d =====

open MvPolynomial Matrix T35aux

namespace L33aux

noncomputable section

theorem one_block {D : Type*} [CommRing D] [IsDomain D] {n m r : ℕ}
    (M : Fin n → Matrix (Fin m) (Fin r) D) :
    ∃ a : Fin n → D, (∀ v, a v = 0 ∨ a v = 1) ∧
      rk (∑ v, (X v : MvPolynomial (Fin n) D) • (M v).map (C : D →+* MvPolynomial (Fin n) D)) ≤
        2 * rk (∑ v, a v • M v) := by
  classical
  set N := ∑ v, (X v : MvPolynomial (Fin n) D) • (M v).map (C : D →+* MvPolynomial (Fin n) D)
    with hN
  set R := rk N with hR
  obtain ⟨I, J, hIJ⟩ := exists_minor_of_le_rank
    (N.map (algebraMap (MvPolynomial (Fin n) D) (FractionRing (MvPolynomial (Fin n) D)))) (k := R)
    le_rfl
  let β : Fin n → Matrix (Fin R) (Fin R) D := fun v => (M v).submatrix I J
  have hNsub : N.submatrix I J =
      Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j) := by
    ext i j
    simp [hN, Matrix.sum_apply, β]
  set P := (Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j)).det with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply hIJ
    rw [show (N.map (algebraMap (MvPolynomial (Fin n) D) (FractionRing (MvPolynomial (Fin n) D)))).submatrix I J =
      (N.submatrix I J).map (algebraMap (MvPolynomial (Fin n) D) (FractionRing (MvPolynomial (Fin n) D)))
      from rfl, det_map_hom, hNsub, ← hPdef, h0, map_zero]
  have hdeg : P.totalDegree ≤ R := by
    apply totalDegree_le_of_upDeg
    rw [hPdef, Matrix.det_apply']
    apply upDeg_sum
    intro σ _
    have := upDeg_mul (upDeg_intCast (D := D) (n := n) (Equiv.Perm.sign σ : ℤ))
      (upDeg_prod Finset.univ (fun _ => 1)
        (fun i => (Matrix.of fun i j => ∑ v, (X v : MvPolynomial (Fin n) D) * C (β v i j)) (σ i) i)
        (fun i _ => by simp only [Matrix.of_apply]; exact upDeg_linear _))
    simpa using this
  let S : Finset D := {0, 1}
  have hS : S.card = 2 := Finset.card_pair zero_ne_one
  have hgrid := GridSZ.grid_sum_bound S n P hP
  rw [hS] at hgrid
  by_contra hcon
  push Not at hcon
  have hpt : ∀ a : Fin n → S, R + 1 ≤ 2 * rootMult (fun i => (a i : D)) P := by
    intro a
    have hbin : ∀ v, ((a v : S) : D) = 0 ∨ ((a v : S) : D) = 1 := by
      intro v
      have := (a v).2
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have h1 : 2 * rk (∑ v, ((a v : S) : D) • M v) < R := hcon (fun i => (a i : D)) hbin
    have h2 : R - rk (∑ v, ((a v : S) : D) • β v) ≤ rootMult (fun i => (a i : D)) P :=
      mult_bound β (fun i => (a i : D)) hP
    have h3 : rk (∑ v, ((a v : S) : D) • β v) ≤ rk (∑ v, ((a v : S) : D) • M v) := by
      have : (∑ v, ((a v : S) : D) • β v) = (∑ v, ((a v : S) : D) • M v).submatrix I J :=
        Matrix.ext fun i j => by
          simp only [β, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
      rw [this]
      exact rk_submatrix_le _ I J
    omega
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n → S))) => hpt a)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hS, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at hsum
  have : (∑ a : Fin n → S, rootMult (fun i => (a i : D)) P) * 2 ≤ R * 2 ^ n :=
    hgrid.trans (Nat.mul_le_mul_right _ hdeg)
  nlinarith [Nat.one_le_two_pow (n := n)]

section blocks

variable {n : ℕ}

def gen {D : Type*} [CommRing D] {k m r : ℕ} (Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D) :
    Matrix (Fin m) (Fin r) (MvPolynomial (Fin k × Fin n) D) :=
  ∑ g, (∏ l, (X (l, g l) : MvPolynomial (Fin k × Fin n) D)) • (Ng g).map C

def spec {D : Type*} [CommRing D] {k m r : ℕ} (Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D)
    (a : Fin k × Fin n → D) : Matrix (Fin m) (Fin r) D :=
  ∑ g, (∏ l, a (l, g l)) • Ng g

def splitE (k n : ℕ) : Fin (k+1) × Fin n ≃ Fin n ⊕ (Fin k × Fin n) where
  toFun p := Fin.cases (Sum.inl p.2) (fun l => Sum.inr (l, p.2)) p.1
  invFun s := Sum.elim (fun v => ((0 : Fin (k+1)), v)) (fun q => (q.1.succ, q.2)) s
  left_inv p := by
    rcases p with ⟨l, v⟩
    refine Fin.cases ?_ (fun l' => ?_) l <;> simp
  right_inv s := by rcases s with v | ⟨l, v⟩ <;> simp

def psi (D : Type*) [CommRing D] (k n : ℕ) :
    MvPolynomial (Fin (k+1) × Fin n) D ≃ₐ[D] MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) D) :=
  (renameEquiv D (splitE k n)).trans (sumAlgEquiv D (Fin n) (Fin k × Fin n))

lemma psi_X0 {D : Type*} [CommRing D] {k : ℕ} (v : Fin n) :
    psi D k n (X ((0 : Fin (k+1)), v)) = X v := by
  simp [psi, splitE, sumAlgEquiv_X_inl]

lemma psi_Xs {D : Type*} [CommRing D] {k : ℕ} (l : Fin k) (v : Fin n) :
    psi D k n (X (l.succ, v)) = C (X (l, v)) := by
  simp [psi, splitE, sumAlgEquiv_X_inr]

lemma psi_C {D : Type*} [CommRing D] {k : ℕ} (d : D) :
    psi D k n (C d) = C (C d) := by
  simp [psi, sumAlgEquiv_C_inl]

theorem blocks : ∀ (k : ℕ) (D : Type) [CommRing D] [IsDomain D] (m r : ℕ)
    (Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D),
    ∃ a : Fin k × Fin n → D, (∀ p, a p = 0 ∨ a p = 1) ∧ rk (gen Ng) ≤ 2 ^ k * rk (spec Ng a) := by
  intro k
  induction k with
  | zero =>
    intro D _ _ m r Ng
    refine ⟨fun _ => 0, fun _ => Or.inl rfl, ?_⟩
    have h1 : gen Ng = (Ng Fin.elim0).map C := by
      unfold gen
      rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
      congr
    have h2 : spec Ng (fun _ => 0) = Ng Fin.elim0 := by
      unfold spec
      rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
      congr
    rw [h1, h2, pow_zero, one_mul]
    exact rk_map_le C _
  | succ k ih =>
    intro D _ _ m r Ng
    classical
    let Mv : Fin n → Matrix (Fin m) (Fin r) (MvPolynomial (Fin k × Fin n) D) :=
      fun v => gen (fun g' : Fin k → Fin n => Ng (Fin.cons v g'))
    have hψ : (gen Ng).map (psi D k n) =
        ∑ v, (X v : MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) D)) •
          (Mv v).map (C : MvPolynomial (Fin k × Fin n) D →+* _) := by
      refine Matrix.ext fun i j => ?_
      simp only [gen, Mv, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        map_sum, map_mul, map_prod]
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n)
        (fun z => (∏ l, (psi D k n) (X (l, (Fin.cons z.1 z.2 : Fin (k+1) → Fin n) l))) *
          (psi D k n) (C (Ng (Fin.cons z.1 z.2) i j))) _ (fun z => rfl)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [Finset.mul_sum, map_sum, map_mul, map_prod]
      refine Finset.sum_congr rfl fun g' _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, psi_X0, psi_Xs, psi_C]
      ring
    obtain ⟨a0, ha0, hOB⟩ := one_block Mv
    let b0 : Fin n → D := fun v => if a0 v = 0 then 0 else 1
    have hb0 : ∀ v, C (b0 v) = a0 v := by
      intro v
      rcases ha0 v with h | h <;> simp [b0, h]
    let Ng' : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D :=
      fun g' => ∑ v, b0 v • Ng (Fin.cons v g')
    have hgen' : (∑ v, a0 v • Mv v) = gen Ng' := by
      refine Matrix.ext fun i j => ?_
      simp only [Mv, gen, Ng', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
        map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g' _ => Finset.sum_congr rfl fun v _ => ?_
      rw [← hb0]; ring
    obtain ⟨a', ha', hIH⟩ := ih D m r Ng'
    let a : Fin (k+1) × Fin n → D := fun p => Fin.cases (b0 p.2) (fun l' => a' (l', p.2)) p.1
    have ha : ∀ p, a p = 0 ∨ a p = 1 := by
      rintro ⟨l, v⟩
      refine Fin.cases ?_ (fun l' => ?_) l
      · simp only [a, Fin.cases_zero, b0]; split_ifs <;> simp
      · simp only [a, Fin.cases_succ]; exact ha' _
    have hspec : spec Ng a = spec Ng' a' := by
      unfold spec
      simp only [Ng', Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n)
        (fun z => (∏ l, a (l, (Fin.cons z.1 z.2 : Fin (k+1) → Fin n) l)) • Ng (Fin.cons z.1 z.2))
        _ (fun z => rfl)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun g' _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [a, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ]
      rw [mul_comm]
    refine ⟨a, ha, ?_⟩
    have hinj : Function.Injective (psi D k n : MvPolynomial (Fin (k+1) × Fin n) D →+*
        MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) D)) := (psi D k n).injective
    calc rk (gen Ng) ≤ rk ((gen Ng).map (psi D k n : MvPolynomial (Fin (k+1) × Fin n) D →+*
          MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) D))) := rk_le_map _ hinj _
      _ = rk (∑ v, (X v : MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) D)) •
          (Mv v).map (C : MvPolynomial (Fin k × Fin n) D →+* _)) := by
          congr 1
      _ ≤ 2 * rk (∑ v, a0 v • Mv v) := hOB
      _ = 2 * rk (gen Ng') := by rw [hgen']
      _ ≤ 2 * (2 ^ k * rk (spec Ng' a')) := Nat.mul_le_mul_left _ hIH
      _ = 2 ^ (k+1) * rk (spec Ng a) := by rw [hspec, pow_succ]; ring

end blocks

end

end L33aux

-- ===== adapter =====

theorem solution (k : ℕ) (D : Type) [CommRing D] [IsDomain D]
    {n m r : ℕ} (N : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D) :
    ∃ a : Fin k × Fin n → D, (∀ q, a q = 0 ∨ a q = 1) ∧
      ((∑ g : Fin k → Fin n, (∏ l, (MvPolynomial.X (l, g l) : MvPolynomial (Fin k × Fin n) D)) •
          (N g).map (MvPolynomial.C : D →+* MvPolynomial (Fin k × Fin n) D)).map
          (algebraMap (MvPolynomial (Fin k × Fin n) D)
            (FractionRing (MvPolynomial (Fin k × Fin n) D)))).rank ≤
        2 ^ k * ((∑ g : Fin k → Fin n, (∏ l, a (l, g l)) • N g).map
          (algebraMap D (FractionRing D))).rank := by
  exact L33aux.blocks k D m r N

