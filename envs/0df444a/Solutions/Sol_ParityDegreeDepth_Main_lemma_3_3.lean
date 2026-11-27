-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:27:11.89591+00:00
-- url     : https://prove2.me/submissions/97b38ec3-0d79-4f6c-b03f-ae9e97c97ded

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Theorems.Thm_ParityDegreeDepth_Core_generic_rank_le_binary

open scoped BigOperators
noncomputable section

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

namespace ParityDegreeDepth.Main

private abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F

private abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

private def BlockMultilinear {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : Prop :=
  ∀ i j e, e ∈ (N i j).support → ∀ b : Fin k, ∑ v : Fin n, e (b, v) = 1

private def matrixGenericRank {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : ℕ :=
  (N.map (algebraMap (AnchorRing F n k) (AnchorField F n k))).rank

private def matrixBinaryRank {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing (ZMod 2) n k)) : ℕ :=
  Finset.univ.sup fun a : (Fin k × Fin n) → ZMod 2 =>
    (N.map (MvPolynomial.eval a)).rank



open MvPolynomial in
private lemma blockMultilinear_eq_gen {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (MvPolynomial (Fin k × Fin n) F))
    (hN : ∀ i j e, e ∈ (N i j).support → ∀ b : Fin k, ∑ v : Fin n, e (b, v) = 1) :
    N = ∑ g : Fin k → Fin n, (∏ l, (MvPolynomial.X (l, g l) : MvPolynomial (Fin k × Fin n) F)) •
      (Matrix.of fun i j => coeff (∑ l, Finsupp.single (l, g l) 1) (N i j)).map
        (MvPolynomial.C : F →+* MvPolynomial (Fin k × Fin n) F) := by
  classical
  set mono : (Fin k → Fin n) → (Fin k × Fin n →₀ ℕ) := fun g => ∑ l, Finsupp.single (l, g l) 1
  have hmono_apply : ∀ g l v, mono g (l, v) = if g l = v then 1 else 0 := by
    intro g l v
    simp only [mono, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hmono_inj : Function.Injective mono := by
    intro g g' h
    funext l
    have := congrArg (fun e => e (l, g l)) h
    simp only [hmono_apply, if_true] at this
    by_contra hne
    rw [if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  have hsupp : ∀ i j e, e ∈ (N i j).support → ∃ g, mono g = e := by
    intro i j e he
    have hb := hN i j e he
    have hex : ∀ l : Fin k, ∃ v, e (l, v) = 1 ∧ ∀ v', v' ≠ v → e (l, v') = 0 := by
      intro l
      have hs := hb l
      have : ∃ v, e (l, v) ≠ 0 := by
        by_contra hc; push Not at hc; simp [hc] at hs
      obtain ⟨v, hv⟩ := this
      refine ⟨v, ?_, ?_⟩
      · have := Finset.single_le_sum (f := fun v => e (l, v)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        omega
      · intro v' hv'
        have h2 : e (l, v) + e (l, v') ≤ ∑ w, e (l, w) := by
          rw [← Finset.sum_pair (f := fun w => e (l, w)) (Ne.symm hv')]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        omega
    choose g hg1 hg2 using hex
    refine ⟨g, ?_⟩
    ext ⟨l, v⟩
    rw [hmono_apply]
    by_cases hv : g l = v
    · subst hv; rw [if_pos rfl, hg1]
    · rw [if_neg hv, hg2 l v (Ne.symm hv)]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  ext e
  rw [coeff_sum]
  have hterm : ∀ g, coeff e ((∏ l, (X (l, g l) : MvPolynomial (Fin k × Fin n) F)) *
      C (coeff (mono g) (N i j))) = if mono g = e then coeff e (N i j) else 0 := by
    intro g
    have : (∏ l, (X (l, g l) : MvPolynomial (Fin k × Fin n) F)) = monomial (mono g) 1 := by
      simp only [mono]
      rw [monomial_sum_one]
      rfl
    rw [this, mul_comm, C_mul_monomial, mul_one, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  by_cases he : e ∈ (N i j).support
  · obtain ⟨g, hg⟩ := hsupp i j e he
    rw [Finset.sum_eq_single g]
    · rw [if_pos hg]
    · intro g' _ hg'; rw [if_neg]; intro h; exact hg' (hmono_inj (h.trans hg.symm))
    · simp
  · rw [MvPolynomial.notMem_support_iff.mp he]
    simp

private lemma rk_field' {m r : ℕ} (N : Matrix (Fin m) (Fin r) (ZMod 2)) :
    (N.map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank = N.rank := by
  apply le_antisymm
  · obtain ⟨r', c', h⟩ := T35aux.exists_minor_of_le_rank
      (N.map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))) le_rfl
    apply T35aux.le_rank_of_minor N r' c'
    intro h0; apply h
    rw [show (N.map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).submatrix r' c' =
      (N.submatrix r' c').map (algebraMap (ZMod 2) (FractionRing (ZMod 2))) from rfl,
      T35aux.det_map_hom, h0, map_zero]
  · obtain ⟨r', c', h⟩ := T35aux.exists_minor_of_le_rank N le_rfl
    exact T35aux.le_rank_of_minor' N r' c' h

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 3 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing (ZMod 2) n k))
    (hN : BlockMultilinear N) : matrixGenericRank N ≤ 2 ^ k * matrixBinaryRank N := by
  classical
  set Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) (ZMod 2) :=
    fun g => Matrix.of fun i j => MvPolynomial.coeff (∑ l, Finsupp.single (l, g l) 1) (N i j)
  have hgen := blockMultilinear_eq_gen N hN
  obtain ⟨a, -, ha⟩ := ParityDegreeDepth.Core.generic_rank_le_binary k (ZMod 2) Ng
  have hspec : (∑ g : Fin k → Fin n, (∏ l, a (l, g l)) • Ng g) = N.map (MvPolynomial.eval a) := by
    conv_rhs => rw [hgen]
    refine Matrix.ext fun i j => ?_
    simp [Matrix.sum_apply, map_sum, map_prod, Ng]
  unfold matrixGenericRank matrixBinaryRank
  rw [hspec, rk_field'] at ha
  conv_lhs => rw [hgen]
  refine ha.trans (Nat.mul_le_mul_left _ ?_)
  exact Finset.le_sup (f := fun a : (Fin k × Fin n) → ZMod 2 => (N.map (MvPolynomial.eval a)).rank)
    (Finset.mem_univ a)



