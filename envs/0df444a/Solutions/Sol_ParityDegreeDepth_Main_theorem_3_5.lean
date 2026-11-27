-- Prove2me | solution 1 for ParityDegreeDepth.Main.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:00:10.94228+00:00
-- url     : https://prove2.me/submissions/2948047f-6285-49e8-ad38-f5fe77f53325

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol


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


open MvPolynomial

namespace T35F

/-- evaluation of the multilinear form with coefficient tensor `c` over an `F`-algebra -/
noncomputable def evF {F R : Type*} [Field F] [CommRing R] [Algebra F R] {d n : ℕ}
    (c : (Fin d → Fin n) → F) (x : Fin d → Fin n → R) : R :=
  ∑ a : Fin d → Fin n, algebraMap F R (c a) * ∏ j, x j (a j)

variable {F : Type*} [Field F]

section ev
variable {R : Type*} [CommRing R] [Algebra F R] {d n : ℕ}

lemma ev_def (c : (Fin d → Fin n) → F) (x : Fin d → Fin n → R) :
    evF c x = ∑ a : Fin d → Fin n, algebraMap F R (c a) * ∏ j, x j (a j) := rfl

lemma ev_map {S : Type*} [CommRing S] [Algebra F S] (φ : R →ₐ[F] S)
    (c : (Fin d → Fin n) → F) (x : Fin d → Fin n → R) :
    φ (evF c x) = evF c (fun j v => φ (x j v)) := by
  simp only [ev_def, map_sum, map_mul, map_prod, AlgHom.commutes]

/-- multilinear expansion -/
lemma ev_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (Fin d → Fin n) → F)
    (s : Fin d → ι → R) (y : Fin d → ι → Fin n → R) :
    evF c (fun j v => ∑ l, s j l * y j l v) =
      ∑ f : Fin d → ι, (∏ j, s j (f j)) * evF c (fun j => y j (f j)) := by
  simp only [ev_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]; ring

lemma ev_smul (c : (Fin d → Fin n) → F) (s : Fin d → R) (y : Fin d → Fin n → R) :
    evF c (fun j v => s j * y j v) = (∏ j, s j) * evF c y := by
  simp only [ev_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib]; ring

lemma ev_perm (c : (Fin d → Fin n) → F)
    (hc : ∀ (σ : Equiv.Perm (Fin d)) a, c (a ∘ σ) = c a) (σ : Equiv.Perm (Fin d))
    (x : Fin d → Fin n → R) : evF c (x ∘ σ) = evF c x := by
  simp only [ev_def]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ ?_
  intro a
  have he : (Equiv.arrowCongr σ (Equiv.refl (Fin n))) a = a ∘ σ.symm := rfl
  rw [he, hc σ.symm a]
  congr 1
  rw [← Equiv.prod_comp σ (fun j => x j ((a ∘ σ.symm) j))]
  simp

lemma ev_zero_slot (c : (Fin d → Fin n) → F) (x : Fin d → Fin n → R) (j : Fin d)
    (hj : x j = 0) : evF c x = 0 := by
  simp only [ev_def]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]

end ev

noncomputable section sq
variable {σ : Type*} [DecidableEq σ]

/-- squarefree monomial exponent of a finite set -/
def sq (J : Finset σ) : σ →₀ ℕ := ∑ i ∈ J, Finsupp.single i 1

lemma sq_apply (J : Finset σ) (i : σ) : sq J i = if i ∈ J then 1 else 0 := by
  unfold sq
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

lemma sq_injective : Function.Injective (sq : Finset σ → σ →₀ ℕ) := by
  intro J K h
  ext i
  have := DFunLike.congr_fun h i
  rw [sq_apply, sq_apply] at this
  split_ifs at this <;> simp_all

lemma sq_empty : sq (∅ : Finset σ) = 0 := by simp [sq]

lemma sq_support (J : Finset σ) : (sq J).support = J := by
  ext i; simp [sq_apply]

lemma sq_add_sdiff {I J : Finset σ} (h : J ⊆ I) : sq J + sq (I \ J) = sq I := by
  ext i
  simp only [Finsupp.add_apply, sq_apply, Finset.mem_sdiff]
  by_cases hi : i ∈ J
  · simp [hi, h hi]
  · by_cases hI : i ∈ I <;> simp [hi, hI]

lemma eq_sq_of_add {I : Finset σ} {μ ν : σ →₀ ℕ} (h : μ + ν = sq I) :
    μ = sq μ.support ∧ ν = sq (I \ μ.support) ∧ μ.support ⊆ I := by
  have hle : ∀ i, μ i + ν i = if i ∈ I then 1 else 0 := by
    intro i; rw [← sq_apply, ← h]; rfl
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [sq_apply]
    have := hle i
    have hμ : μ i ≤ 1 := by split_ifs at this <;> omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hμ with h1 | h1 <;> simp [h1]
  · ext i
    rw [sq_apply]
    have := hle i
    simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not]
    by_cases hI : i ∈ I
    · rw [if_pos hI] at this
      by_cases h1 : μ i = 0
      · simp [hI, h1]; omega
      · simp [hI, h1]; omega
    · rw [if_neg hI] at this
      simp [hI]; omega
  · intro i hi
    rw [Finsupp.mem_support_iff] at hi
    have := hle i
    by_contra hI
    simp [hI] at this
    omega

variable {S : Type*} [CommRing S]

lemma coeff_sq_mul (I : Finset σ) (f g : MvPolynomial σ S) :
    coeff (sq I) (f * g) = ∑ J ∈ I.powerset, coeff (sq J) f * coeff (sq (I \ J)) g := by
  rw [coeff_mul]
  symm
  refine Finset.sum_nbij' (fun J => (sq J, sq (I \ J))) (fun p => p.1.support) ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    have hJ' : J ⊆ I := Finset.mem_powerset.mp hJ
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (sq_add_sdiff hJ')
  · intro p hp
    exact Finset.mem_powerset.mpr (eq_sq_of_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)).2.2
  · intro J hJ
    simp [sq_support]
  · intro p hp
    obtain ⟨h1, h2, -⟩ := eq_sq_of_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
    ext <;> simp [← h1, ← h2]
  · intro J _; rfl

lemma coeff_sq_prod_lin (I : Finset σ) [Fintype σ] (α β : σ → S) :
    coeff (sq I) (∏ l, (C (α l) + X l * C (β l))) =
      ∏ l, if l ∈ I then β l else α l := by
  have hterm : ∀ T ∈ (Finset.univ : Finset σ).powerset,
      (∏ l ∈ T, (C (α l) : MvPolynomial σ S)) * ∏ l ∈ Finset.univ \ T, X l * C (β l) =
      monomial (sq (Finset.univ \ T)) ((∏ l ∈ T, α l) * ∏ l ∈ Finset.univ \ T, β l) := by
    intro T _
    rw [← map_prod, Finset.prod_mul_distrib, ← map_prod]
    have : (∏ l ∈ Finset.univ \ T, (X l : MvPolynomial σ S)) =
        monomial (sq (Finset.univ \ T)) 1 := by
      unfold sq
      rw [monomial_sum_one]
      rfl
    rw [this, ← mul_assoc, C_mul_monomial, mul_one, mul_comm, C_mul_monomial, mul_comm]
  rw [Finset.prod_add, Finset.sum_congr rfl hterm, coeff_sum]
  simp only [coeff_monomial]
  have hII : Finset.univ \ (Finset.univ \ I) = I := Finset.sdiff_sdiff_eq_self (Finset.subset_univ I)
  rw [Finset.sum_eq_single (Finset.univ \ I)]
  · rw [hII, if_pos rfl]
    rw [← Finset.prod_mul_prod_compl I (fun l => if l ∈ I then β l else α l), mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun l hl => by simp [hl]
    · refine Finset.prod_congr (by ext; simp) fun l hl => ?_
      rw [Finset.mem_compl] at hl
      simp [hl]
  · intro T _ hT
    rw [if_neg]
    intro h
    apply hT
    have h' := sq_injective h
    ext l
    have := congrArg (fun s : Finset σ => l ∈ s) h'
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, eq_iff_iff] at this
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  · intro h; simp at h

end sq

end T35F


open MvPolynomial Matrix

namespace T35F

noncomputable section

variable {F : Type*} [Field F]

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → F)

/-- contraction: anchors `w` in the first `m+1` slots, then `x`, `y`. -/
def con {S : Type*} [CommRing S] [Algebra F S] (w : Fin (m+1) → Fin n → S)
    (x y : Fin n → S) : S :=
  evF c (Fin.append w ![x, y])

def ee {S : Type*} [Semiring S] (i : Fin n) : Fin n → S := Pi.single i 1

lemma con_explicit {S : Type*} [CommRing S] [Algebra F S] (w : Fin (m+1) → Fin n → S)
    (x y : Fin n → S) :
    con c w x y = ∑ a : Fin (m+1+2) → Fin n, algebraMap F S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
        (x (a (Fin.natAdd (m+1) 0)) * y (a (Fin.natAdd (m+1) 1)))) := by
  unfold con
  rw [ev_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right, Fin.prod_univ_two]

variable {S : Type*} [CommRing S] [Algebra F S]

lemma sum_single_mul (x : Fin n → S) (v : Fin n) :
    ∑ i, x i * (ee i : Fin n → S) v = x v := by
  simp [ee, Pi.single_apply]

omit [Algebra F S] in
lemma sum_ee_left {α : Type*} [Fintype α] (F : α → S) (g : α → Fin n) (y : Fin n → S) :
    ∑ j, (∑ a, F a * (ee j : Fin n → S) (g a)) * y j = ∑ a, F a * y (g a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [ee, Pi.single_apply, mul_assoc]

omit [Algebra F S] in
lemma sum_ee_right {α : Type*} [Fintype α] (F : α → S) (g : α → Fin n) (x : Fin n → S) :
    ∑ i, x i * (∑ a, F a * (ee i : Fin n → S) (g a)) = ∑ a, F a * x (g a) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [ee, Pi.single_apply, mul_comm]

lemma con_bilin (w : Fin (m+1) → Fin n → S) (x y : Fin n → S) :
    con c w x y = x ⬝ᵥ ((Matrix.of fun i j => con c w (ee i) (ee j)) *ᵥ y) := by
  simp only [dotProduct, mulVec, Matrix.of_apply]
  have h1 : ∀ i, ∑ j, con c w (ee i) (ee j) * y j = con c w (ee i) y := by
    intro i
    simp only [con_explicit]
    have := sum_ee_left (fun a : Fin (m+1+2) → Fin n => algebraMap F S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) * (ee i : Fin n → S) (a (Fin.natAdd (m+1) 0))))
      (fun a => a (Fin.natAdd (m+1) 1)) y
    simp only [mul_assoc] at this ⊢
    exact this
  simp only [h1]
  simp only [con_explicit]
  have := sum_ee_right (fun a : Fin (m+1+2) → Fin n => algebraMap F S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) * y (a (Fin.natAdd (m+1) 1))))
      (fun a => a (Fin.natAdd (m+1) 0)) x
  rw [← Finset.sum_congr rfl (fun i _ => congrArg (x i * ·) (Finset.sum_congr rfl fun a _ =>
    (by ring : algebraMap F S (c a) * ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
      ((ee i : Fin n → S) (a (Fin.natAdd (m+1) 0)) * y (a (Fin.natAdd (m+1) 1)))) =
      algebraMap F S (c a) * ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
      y (a (Fin.natAdd (m+1) 1))) * (ee i : Fin n → S) (a (Fin.natAdd (m+1) 0)))))] at this
  rw [this]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma mulVec_con (w : Fin (m+1) → Fin n → S) (y : Fin n → S) (i : Fin n) :
    ((Matrix.of fun i j => con c w (ee i) (ee j)) *ᵥ y) i = con c w (ee i) y := by
  rw [con_bilin c w (ee i) y]
  simp [ee, dotProduct, Pi.single_apply]

lemma vecMul_con (w : Fin (m+1) → Fin n → S) (x : Fin n → S) (j : Fin n) :
    (x ᵥ* (Matrix.of fun i j => con c w (ee i) (ee j))) j = con c w x (ee j) := by
  rw [con_bilin c w x (ee j)]
  simp [ee, dotProduct, mulVec, vecMul, Pi.single_apply]

variable (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a)
include hc

lemma con_symm (w : Fin (m+1) → Fin n → S) (x y : Fin n → S) :
    con c w x y = con c w y x := by
  unfold con
  rw [← ev_perm c hc (Equiv.swap (Fin.natAdd (m+1) 0) (Fin.natAdd (m+1) 1))]
  congr 1
  funext j
  refine Fin.addCases (fun l => ?_) (fun t => ?_) j
  · have h0 : Fin.castAdd 2 l ≠ Fin.natAdd (m+1) (0 : Fin 2) := by
      simp [Fin.ext_iff]; omega
    have h1 : Fin.castAdd 2 l ≠ Fin.natAdd (m+1) (1 : Fin 2) := by
      simp [Fin.ext_iff]; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.append_left]
  · fin_cases t
    · simp [Function.comp, Fin.append_right]
    · simp [Function.comp, Fin.append_right]

lemma con_swap_anchor [DecidableEq (Fin n → S)] (w : Fin (m+1) → Fin n → S) (l : Fin (m+1))
    (x y : Fin n → S) :
    con c w x y = con c (Function.update w l x) (w l) y := by
  unfold con
  rw [← ev_perm c hc (Equiv.swap (Fin.castAdd 2 l) (Fin.natAdd (m+1) 0))
    (Fin.append (Function.update w l x) ![w l, y])]
  congr 1
  funext j
  refine Fin.addCases (fun l' => ?_) (fun t => ?_) j
  · by_cases hl : l' = l
    · subst hl
      simp [Function.comp, Fin.append_left, Fin.append_right]
    · have h0 : Fin.castAdd 2 l' ≠ Fin.castAdd 2 l := by
        simp [Fin.ext_iff, Fin.val_ne_of_ne hl]
      have h1 : Fin.castAdd 2 l' ≠ Fin.natAdd (m+1) (0 : Fin 2) := by
        simp [Fin.ext_iff]; omega
      simp [Function.comp, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.append_left, hl]
  · fin_cases t
    · simp [Function.comp, Fin.append_right, Fin.append_left]
    · have h0 : Fin.natAdd (m+1) (1 : Fin 2) ≠ Fin.castAdd 2 l := by
        simp [Fin.ext_iff]; omega
      have h1 : Fin.natAdd (m+1) (1 : Fin 2) ≠ Fin.natAdd (m+1) (0 : Fin 2) := by
        simp [Fin.ext_iff]
      simp [Function.comp, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.append_right]

end

end T35F


open MvPolynomial Matrix T35aux

namespace T35F

noncomputable section

variable {F : Type*} [Field F]

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → F)

abbrev PP (F : Type*) [Field F] (m n : ℕ) := MvPolynomial (Fin (m+1) × Fin n) F
abbrev QQ (F : Type*) [Field F] (m n : ℕ) := MvPolynomial (Fin (m+1)) (PP F m n)

def tv : Fin (m+1) → Fin n → PP F m n := fun l v => X (l, v)
def AA : Matrix (Fin n) (Fin n) (PP F m n) := Matrix.of fun i j => con c tv (ee i) (ee j)
def pert (w : Fin (m+1) → Fin n → PP F m n) : Fin (m+1) → Fin n → QQ F m n :=
  fun l v => C (X (l, v)) + X l * C (w l v)
def bsel (w : Fin (m+1) → Fin n → PP F m n) (J : Finset (Fin (m+1))) :
    Fin (m+1) → Fin n → PP F m n := fun l => if l ∈ J then w l else tv l
def cv (x : Fin n → PP F m n) : Fin n → QQ F m n := fun v => C (x v)

lemma bsel_empty (w : Fin (m+1) → Fin n → PP F m n) : bsel w ∅ = tv := by
  funext l; simp [bsel]

lemma coeff_pert (w : Fin (m+1) → Fin n → PP F m n) (J : Finset (Fin (m+1)))
    (x y : Fin n → PP F m n) :
    coeff (sq J) (con c (pert w) (cv x) (cv y)) = con c (bsel w J) x y := by
  rw [con_explicit, con_explicit, coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MvPolynomial.algebraMap_apply, coeff_C_mul]
  congr 1
  have h : (∏ l : Fin (m+1), pert w l (a (Fin.castAdd 2 l))) *
      (cv x (a (Fin.natAdd (m+1) 0)) * cv y (a (Fin.natAdd (m+1) 1))) =
      (∏ l : Fin (m+1), (C (X (l, a (Fin.castAdd 2 l))) + X l * C (w l (a (Fin.castAdd 2 l))))) *
        C (x (a (Fin.natAdd (m+1) 0)) * y (a (Fin.natAdd (m+1) 1))) := by
    simp [pert, cv, map_mul]
  rw [h, mul_comm, coeff_C_mul, coeff_sq_prod_lin, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [bsel, tv]
  split_ifs <;> rfl

def phiw (w : Fin (m+1) → Fin n → PP F m n) : PP F m n →ₐ[F] QQ F m n :=
  aeval fun p : Fin (m+1) × Fin n => C (X p) + X p.1 * C (w p.1 p.2)

lemma con_map {S T : Type*} [CommRing S] [Algebra F S] [CommRing T] [Algebra F T]
    (φ : S →ₐ[F] T) (w : Fin (m+1) → Fin n → S) (x y : Fin n → S) :
    φ (con c w x y) = con c (fun l v => φ (w l v)) (fun v => φ (x v)) (fun v => φ (y v)) := by
  unfold con
  rw [ev_map]
  congr 1
  funext j v
  refine Fin.addCases (fun l => ?_) (fun t => ?_) j
  · simp [Fin.append_left]
  · fin_cases t <;> simp [Fin.append_right]

lemma ee_cv (i : Fin n) : (ee i : Fin n → QQ F m n) = cv (ee i) := by
  funext v; by_cases h : v = i
  · subst h; simp [ee, cv]
  · simp [ee, cv, Pi.single_apply, h]

lemma phiw_ee (w : Fin (m+1) → Fin n → PP F m n) (i : Fin n) :
    (fun v => phiw w ((ee i : Fin n → PP F m n) v)) = ee i := by
  funext v; by_cases h : v = i
  · subst h; simp [ee]
  · simp [ee, Pi.single_apply, h]

lemma phiw_tv (w : Fin (m+1) → Fin n → PP F m n) :
    (fun l v => phiw w (tv l v)) = pert w := by
  funext l v; simp [phiw, tv, pert]

lemma map_AA (w : Fin (m+1) → Fin n → PP F m n) :
    (AA c).map (phiw w) = Matrix.of fun i j => con c (pert w) (ee i) (ee j) := by
  ext i j
  simp only [AA, Matrix.map_apply, Matrix.of_apply]
  rw [con_map, phiw_ee, phiw_ee, phiw_tv]

lemma constantCoeff_phiw (w : Fin (m+1) → Fin n → PP F m n) (p : PP F m n) :
    constantCoeff (phiw w p) = p := by
  have : (constantCoeff : QQ F m n →+* PP F m n).comp (phiw w).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [phiw, MvPolynomial.algebraMap_apply]
    · intro p; simp [phiw]
  exact congrArg (fun f => f p) this

def InKer (u : Fin n → PP F m n) : Prop := ∀ i, con c tv (ee i) u = 0

def AtMostOne (w : Fin (m+1) → Fin n → PP F m n) (I : Finset (Fin (m+1))) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ¬ InKer c (w i) → ¬ InKer c (w j) → i = j

variable (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a)

lemma con_tv_left (u : Fin n → PP F m n) (hu : InKer c u) (v : Fin n → PP F m n) :
    con c tv v u = 0 := by
  rw [con_bilin]
  simp only [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mulVec_con, hu i, mul_zero]

include hc in
lemma con_tv_right (u : Fin n → PP F m n) (hu : InKer c u) (v : Fin n → PP F m n) :
    con c tv u v = 0 := by
  rw [con_symm c hc]; exact con_tv_left c u hu v

lemma rank_map_le {R : ℕ}
    (hrank : ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).rank ≤ R)
    (w : Fin (m+1) → Fin n → PP F m n) :
    (((AA c).map (phiw w)).map (algebraMap (QQ F m n) (FractionRing (QQ F m n)))).rank ≤ R := by
  apply rank_le_of_minors
  intro r c'
  rw [show ((AA c).map (phiw w)).submatrix r c' = ((AA c).submatrix r c').map (phiw w) from rfl]
  rw [show (((AA c).submatrix r c').map (phiw w)).det =
    (((AA c).submatrix r c').map (phiw w).toRingHom).det from rfl, det_map_hom,
    minors_zero_of_rank_le (AA c) hrank r c', map_zero]

include hc in
theorem claims {R : ℕ}
    (hrank : ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).rank ≤ R)
    (I0 I0' : Fin R → Fin n) (hδ : ((AA c).submatrix I0 I0').det ≠ 0) :
    ∀ I : Finset (Fin (m+1)),
      (∀ w, AtMostOne c w I → ∀ u u', InKer c u → InKer c u' → con c (bsel w I) u u' = 0) ∧
      (∀ w, (∀ i ∈ I, InKer c (w i)) → ∀ v u, InKer c u → con c (bsel w I) v u = 0) := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  have cl1 : ∀ w, AtMostOne c w I → ∀ u u', InKer c u → InKer c u' →
      con c (bsel w I) u u' = 0 := by
    intro w hw u u' hu hu'
    set M := (AA c).map (phiw w) with hMdef
    have hrkM := rank_map_le c hrank w
    have hcc : ∀ (r c' : Fin R → Fin n), constantCoeff ((M.submatrix r c').det) =
        ((AA c).submatrix r c').det := by
      intro r c'
      rw [show (constantCoeff : QQ F m n →+* PP F m n) (M.submatrix r c').det =
        ((M.submatrix r c').map constantCoeff).det from (det_map_hom _ _).symm]
      congr 1
      ext i j
      simp [M, constantCoeff_phiw]
    have hPw : (M.submatrix I0 I0').det ≠ 0 := by
      intro h0; apply hδ; rw [← hcc, h0, map_zero]
    have key := bordered_identity M hrkM I0 I0' hPw (cv u) (cv u')
    rw [hMdef, map_AA] at key
    rw [← con_bilin] at key
    simp only [vecMul_con, mulVec_con] at key
    simp only [ee_cv] at key
    -- names
    set D := ((Matrix.of fun i j => con c (pert w) (cv (ee i)) (cv (ee j))).submatrix I0 I0').det
      with hD
    have hD0 : coeff 0 D = ((AA c).submatrix I0 I0').det := by
      rw [← constantCoeff_eq, hD]
      have : (Matrix.of fun i j => con c (pert w) (cv (ee i)) (cv (ee j))) = M := by
        rw [hMdef, map_AA]; simp only [ee_cv]
      rw [this, hcc]
    have hkey := congrArg (coeff (sq I)) key
    -- LHS
    rw [coeff_sq_mul, Finset.sum_eq_single ∅] at hkey
    · rw [sq_empty, hD0, Finset.sdiff_empty] at hkey
      rw [coeff_pert] at hkey
      -- RHS is zero
      have hR : coeff (sq I) ((fun a => con c (pert w) (cv u) (cv (ee (I0' a)))) ⬝ᵥ
          (((Matrix.of fun i j => con c (pert w) (cv (ee i)) (cv (ee j))).submatrix I0 I0').adjugate
            *ᵥ fun b => con c (pert w) (cv (ee (I0 b))) (cv u'))) = 0 := by
        simp only [dotProduct, mulVec, coeff_sum, Finset.mul_sum]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [coeff_sq_mul]
        refine Finset.sum_eq_zero fun J hJ => ?_
        rw [Finset.mem_powerset] at hJ
        rw [coeff_sq_mul, Finset.mul_sum]
        refine Finset.sum_eq_zero fun K hK => ?_
        rw [Finset.mem_powerset] at hK
        rw [coeff_pert, coeff_pert]
        by_cases hJe : J = ∅
        · subst hJe; rw [bsel_empty, con_tv_right c hc u hu, zero_mul]
        by_cases hLe : (I \ J) \ K = ∅
        · rw [hLe, bsel_empty, con_tv_left c u' hu', mul_zero, mul_zero]
        set L := ((I \ J) \ K) with hL
        have hJL : Disjoint J L := by
          rw [hL]; exact Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.disjoint_sdiff
        have hLI : L ⊆ I := fun x hx => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
        by_cases hJker : ∀ j ∈ J, InKer c (w j)
        · have hJI : J ⊂ I := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hJ, fun h => hLe ?_⟩
            rw [hL, h]; simp
          have := (ih J hJI).2 w hJker (ee (I0' a)) u hu
          rw [con_symm c hc] at this
          rw [this, zero_mul]
        · push Not at hJker
          obtain ⟨j, hjJ, hj⟩ := hJker
          have hLker : ∀ l ∈ L, InKer c (w l) := by
            intro l hl
            by_contra hlk
            have := hw l (hLI hl) j (hJ hjJ) hlk hj
            subst this
            exact Finset.disjoint_left.mp hJL hjJ hl
          have hLI' : L ⊂ I := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hLI, fun h => ?_⟩
            obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hJe
            have : x ∈ L := h ▸ hJ hx
            exact Finset.disjoint_left.mp hJL hx this
          have := (ih L hLI').2 w hLker (ee (I0 b)) u' hu'
          rw [this, mul_zero, mul_zero]
      rw [hR] at hkey
      exact (mul_eq_zero.mp hkey).resolve_left hδ
    · intro J hJ hJne
      rw [Finset.mem_powerset] at hJ
      have hsub : I \ J ⊂ I := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => hJne ?_⟩
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hJne
        exfalso
        have : x ∈ I \ J := by rw [h]; exact hJ hx
        exact (Finset.mem_sdiff.mp this).2 hx
      rw [coeff_pert]
      rw [(ih (I \ J) hsub).1 w (fun i hi j hj => hw i (Finset.sdiff_subset hi) j
        (Finset.sdiff_subset hj)) u u' hu hu', mul_zero]
    · intro h; exact absurd (Finset.empty_mem_powerset I) h
  refine ⟨cl1, ?_⟩
  intro w hw v u hu
  by_cases hI : I = ∅
  · subst hI; rw [bsel_empty]; exact con_tv_left c u hu v
  obtain ⟨i₁, hi₁⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  rw [con_swap_anchor c hc (bsel w I) i₁ v u]
  have h1 : bsel w I i₁ = w i₁ := by simp [bsel, hi₁]
  have h2 : Function.update (bsel w I) i₁ v = bsel (Function.update w i₁ v) I := by
    funext l
    by_cases hl : l = i₁
    · subst hl; simp [bsel, hi₁]
    · simp [bsel, Function.update_of_ne hl]
  rw [h1, h2]
  refine cl1 _ ?_ (w i₁) u (hw i₁ hi₁) hu
  intro i hi j hj hni hnj
  have hi' : i = i₁ := by
    by_contra hne
    exact hni (by rw [Function.update_of_ne hne]; exact hw i hi)
  have hj' : j = i₁ := by
    by_contra hne
    exact hnj (by rw [Function.update_of_ne hne]; exact hw j hj)
  rw [hi', hj']

end

end T35F


open MvPolynomial Matrix T35aux

namespace T35F

noncomputable section

variable {F : Type*} [Field F]

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → F)

lemma mulVec_ee (M : Matrix (Fin n) (Fin n) (PP F m n)) (i k : Fin n) :
    (M *ᵥ (ee k : Fin n → PP F m n)) i = M i k := by
  simp [ee, mulVec, dotProduct, Pi.single_apply]

lemma AA_mulVec (y : Fin n → PP F m n) (i : Fin n) : (AA c *ᵥ y) i = con c tv (ee i) y := by
  rw [AA, mulVec_con]

theorem main_T35 (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a) :
    ∃ (r : ℕ) (Λ : Matrix (Fin n) (Fin r) (PP F m n)),
      r + ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).rank = n ∧
      (∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) ∧
      (∀ x : Fin (m+1+2) → Fin n → PP F m n, (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ i l) →
        evF c x = 0) ∧ (∀ (l : Fin r) (i : Fin n), con c tv (ee i) (fun v => Λ v l) = 0) := by
  classical
  set R := ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).rank with hR
  obtain ⟨I0, I0', hmin⟩ := exists_minor_of_le_rank
    ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))) (k := R) le_rfl
  have hδ : ((AA c).submatrix I0 I0').det ≠ 0 := by
    intro h; apply hmin
    rw [show ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).submatrix I0 I0' =
      ((AA c).submatrix I0 I0').map (algebraMap (PP F m n) (FractionRing (PP F m n))) from rfl,
      det_map_hom, h, map_zero]
  have hinj : Function.Injective I0' := by
    intro a b hab
    by_contra hne
    apply hδ
    exact Matrix.det_zero_of_column_eq hne (by intro i; simp [hab])
  set δ := ((AA c).submatrix I0 I0').det with hδdef
  set Sc : Finset (Fin n) := (Finset.univ.image I0')ᶜ with hSc
  have hcard : Sc.card + R = n := by
    have h1 : (Finset.univ.image I0').card = R := by
      rw [Finset.card_image_of_injective _ hinj]; simp
    have h2 := Finset.card_compl_add_card (Finset.univ.image I0')
    rw [h1, Fintype.card_fin] at h2
    exact h2
  set r := Sc.card with hr
  let J' : Fin r → Fin n := fun j => (Sc.equivFin.symm j : Fin n)
  have hJ'mem : ∀ j, J' j ∈ Sc := fun j => (Sc.equivFin.symm j).2
  have hJ'ne : ∀ j a, J' j ≠ I0' a := by
    intro j a h
    have := hJ'mem j
    rw [hSc, Finset.mem_compl, h] at this
    exact this (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  have hJ'inj : Function.Injective J' := by
    intro a b h
    have := Subtype.ext h
    exact Sc.equivFin.symm.injective this
  set P0 := (AA c).submatrix I0 I0' with hP0
  let β : Fin r → Fin R → PP F m n := fun j b => AA c (I0 b) (J' j)
  let col : Fin r → Fin n → PP F m n := fun j =>
    δ • (ee (J' j) : Fin n → PP F m n) - ∑ a, (P0.adjugate *ᵥ β j) a • (ee (I0' a) : Fin n → PP F m n)
  have hrank : ((AA c).map (algebraMap (PP F m n) (FractionRing (PP F m n)))).rank ≤ R := le_rfl
  have hker : ∀ j, InKer c (col j) := by
    intro j i
    rw [← AA_mulVec]
    simp only [col, mulVec_sub, mulVec_smul, mulVec_sum, Pi.sub_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, mulVec_ee]
    have key := bordered_identity (AA c) hrank I0 I0' hδ (ee i) (ee (J' j))
    have e1 : (ee i : Fin n → PP F m n) ⬝ᵥ (AA c *ᵥ ee (J' j)) = AA c i (J' j) := by
      simp [ee, dotProduct, mulVec, Pi.single_apply]
    have e2 : ∀ k, ((ee i : Fin n → PP F m n) ᵥ* AA c) k = AA c i k := by
      intro k; simp [ee, vecMul, dotProduct, Pi.single_apply]
    rw [e1] at key
    simp only [e2, mulVec_ee] at key
    rw [← hδdef, ← hP0] at key
    rw [key]
    simp only [dotProduct, β]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  let Λ : Matrix (Fin n) (Fin r) (PP F m n) := Matrix.of fun v j => col j v
  refine ⟨r, Λ, by rw [hR] at hcard; exact hcard, ⟨J', ?_⟩, ?_, fun l i => hker l i⟩
  · have hsub : Λ.submatrix J' id = δ • (1 : Matrix (Fin r) (Fin r) (PP F m n)) := by
      ext j' j
      simp only [Λ, col, Matrix.submatrix_apply, Matrix.of_apply, id, Pi.sub_apply,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
      have hz : ∀ a, (ee (I0' a) : Fin n → PP F m n) (J' j') = 0 := by
        intro a; simp [ee, Pi.single_apply, hJ'ne j' a]
      simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero]
      by_cases hjj : j' = j
      · subst hjj; simp [ee]
      · have : J' j' ≠ J' j := fun h => hjj (hJ'inj h)
        simp [ee, Pi.single_apply, this, hjj]
    rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hδ
  · intro x hx
    let w : Fin (m+1) → Fin n → PP F m n := fun l => x (Fin.castAdd 2 l)
    have hw : bsel w Finset.univ = w := by funext l; simp [bsel]
    have hcolker : ∀ j, j ≠ 0 → InKer c (x j) := by
      intro j hj
      obtain ⟨l, hl⟩ := hx j hj
      rw [hl]; exact hker l
    have hAMO : AtMostOne c w Finset.univ := by
      intro i _ j _ hi hj
      have h0 : ∀ l : Fin (m+1), ¬ InKer c (w l) → l = 0 := by
        intro l hl
        by_contra hne
        apply hl
        apply hcolker
        intro h
        apply hne
        have := congrArg Fin.val h
        simp at this
        exact this
      rw [h0 i hi, h0 j hj]
    have hu : InKer c (x (Fin.natAdd (m+1) 0)) := hcolker _ (by simp [Fin.ext_iff])
    have hu' : InKer c (x (Fin.natAdd (m+1) 1)) := hcolker _ (by simp [Fin.ext_iff])
    have := (claims c hc hrank I0 I0' hδ Finset.univ).1 w hAMO _ _ hu hu'
    rw [hw] at this
    have hxe : Fin.append w ![x (Fin.natAdd (m+1) 0), x (Fin.natAdd (m+1) 1)] = x := by
      funext j
      refine Fin.addCases (fun l => ?_) (fun t => ?_) j
      · simp [w, Fin.append_left]
      · fin_cases t <;> simp [Fin.append_right]
    unfold con at this
    rw [hxe] at this
    exact this

end

end T35F



open Matrix

namespace L37F

noncomputable section

variable {F : Type*} [Field F] {d n : ℕ} (c : (Fin (d+1) → Fin n) → F)

section lin
variable {R : Type*} [CommRing R] [Algebra F R]

lemma ev_update_add (x : Fin (d+1) → Fin n → R) (j : Fin (d+1)) (a b : Fin n → R) :
    T35F.evF c (Function.update x j (a + b)) =
      T35F.evF c (Function.update x j a) + T35F.evF c (Function.update x j b) := by
  simp only [T35F.ev_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_add]
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have h : ∀ y : Fin n → R, ∏ k ∈ Finset.univ.erase j, Function.update x j y k (t k) =
      ∏ k ∈ Finset.univ.erase j, x k (t k) := by
    intro y
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h, h, h]
  simp only [Function.update_self, Pi.add_apply]
  ring

lemma ev_update_smul (x : Fin (d+1) → Fin n → R) (j : Fin (d+1)) (s : R) (a : Fin n → R) :
    T35F.evF c (Function.update x j (s • a)) = s * T35F.evF c (Function.update x j a) := by
  simp only [T35F.ev_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have h : ∀ y : Fin n → R, ∏ k ∈ Finset.univ.erase j, Function.update x j y k (t k) =
      ∏ k ∈ Finset.univ.erase j, x k (t k) := by
    intro y
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h, h]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
  ring

lemma ev_update_zero (x : Fin (d+1) → Fin n → R) (j : Fin (d+1)) :
    T35F.evF c (Function.update x j 0) = 0 :=
  T35F.ev_zero_slot c _ j (by simp)

lemma sv_span (S : Set (Fin n → R))
    (hS : ∀ x : Fin (d+1) → Fin n → R, (∀ j, j ≠ 0 → x j ∈ S) → T35F.evF c x = 0) :
    ∀ x : Fin (d+1) → Fin n → R, (∀ j, j ≠ 0 → x j ∈ Submodule.span R S) →
      T35F.evF c x = 0 := by
  classical
  have key : ∀ F : Finset (Fin (d+1)), ∀ x : Fin (d+1) → Fin n → R,
      (∀ j, j ≠ 0 → j ∉ F → x j ∈ S) → (∀ j ∈ F, j ≠ 0 → x j ∈ Submodule.span R S) →
      T35F.evF c x = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro x h1 _
      exact hS x fun j hj => h1 j hj (Finset.notMem_empty j)
    | insert a F haF ih =>
      intro x h1 h2
      by_cases ha0 : a = 0
      · apply ih x
        · intro j hj hjF
          exact h1 j hj (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hj (h ▸ ha0), hjF⟩)
        · intro j hj hj0; exact h2 j (Finset.mem_insert_of_mem hj) hj0
      have hxa := h2 a (Finset.mem_insert_self a F) ha0
      have : ∀ y ∈ Submodule.span R S, T35F.evF c (Function.update x a y) = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hyS =>
          apply ih
          · intro j hj hjF
            by_cases hja : j = a
            · subst hja; simp [hyS]
            · rw [Function.update_of_ne hja]
              exact h1 j hj (by rw [Finset.mem_insert]; push Not; exact ⟨hja, hjF⟩)
          · intro j hjF hj0
            have hja : j ≠ a := fun h => haF (h ▸ hjF)
            rw [Function.update_of_ne hja]
            exact h2 j (Finset.mem_insert_of_mem hjF) hj0
        | zero => exact ev_update_zero c x a
        | add y z _ _ hy hz => rw [ev_update_add, hy, hz, add_zero]
        | smul s y _ hy => rw [ev_update_smul, hy, mul_zero]
      have := this (x a) hxa
      rwa [Function.update_eq_self] at this
  intro x hx
  exact key Finset.univ x (fun j _ hj => absurd (Finset.mem_univ j) hj) (fun j _ hj => hx j hj)


end lin

end

end L37F

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

private def IsSymmetric {F : Type} {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) x, T (x ∘ σ) = T x

private def StrongVanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop :=
  ∀ (v : Vec n F) (u : Fin (d - 1) → U),
    T (fun i => if hi : i.val = 0 then v else (u ⟨i.val - 1, by omega⟩ : Vec n F)) = 0

private def extendForm {F E : Type} [Field F] [Field E] [Algebra F E] {n d : ℕ}
    (T : Form F n d) : Form E n d :=
  fun x => ∑ a : Fin d → Fin n,
    algebraMap F E (T (fun i => Pi.single (a i) 1)) * ∏ i, x i (a i)

private abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F

private abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

private def genericMatrix {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorRing F n (d - 2)) :=
  fun i j => ∑ a : Fin (d - 2) → Fin n,
    MvPolynomial.C (T (fun s => if hs : s.val < d - 2 then Pi.single (a ⟨s.val, hs⟩) 1
      else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)) *
    ∏ t, MvPolynomial.X (t, a t)

private def genericContraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorField F n (d - 2)) :=
  (genericMatrix T).map (algebraMap (AnchorRing F n (d - 2)) (AnchorField F n (d - 2)))

private def genericRank {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : ℕ :=
  (genericContraction T).rank

private def genericRadical {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Submodule (AnchorField F n (d - 2)) (Vec n (AnchorField F n (d - 2))) :=
  LinearMap.ker (Matrix.mulVecLin (genericContraction T))




private lemma form_eq_evF {F : Type} [Field F] {n d : ℕ} (T : Form F n d) (hT : IsMultilinear T)
    (x : Fin d → Vec n F) :
    T x = T35F.evF (fun a => T (fun i => Pi.single (a i) 1)) x := by
  classical
  let f : MultilinearMap F (fun _ : Fin d => Vec n F) F :=
    { toFun := T
      map_update_add' := fun x i u v => by convert hT.1 x i u v
      map_update_smul' := fun x i c u => by rw [smul_eq_mul]; convert hT.2 x i c u }
  have hx : x = fun i => ∑ v, x i v • (Pi.single v 1 : Vec n F) := by
    funext i v; simp [Finset.sum_apply, Pi.single_apply]
  show f x = _
  conv_lhs => rw [hx, MultilinearMap.map_sum]
  unfold T35F.evF
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  rw [mul_comm]; rfl

private lemma sel_eqF {F : Type} [Field F] {n m : ℕ} (g : Fin (m + 1 + 2 - 2) → Fin n) (i j : Fin n) :
    (fun s : Fin (m + 1 + 2) => if hs : s.val < m + 1 + 2 - 2 then
        (Pi.single (g ⟨s.val, hs⟩) 1 : Fin n → F)
      else if s.val = m + 1 + 2 - 2 then Pi.single i 1 else Pi.single j 1) =
    fun l => Pi.single ((Fin.append (fun t : Fin (m+1) => g ⟨t.val, by omega⟩) ![i, j] :
      Fin (m + 1 + 2) → Fin n) l) 1 := by
  funext s
  refine Fin.addCases (fun l => ?_) (fun t => ?_) s
  · simp only [Fin.append_left, Fin.val_castAdd]
    rw [dif_pos (by omega)]
  · simp only [Fin.append_right, Fin.val_natAdd]
    fin_cases t
    · simp
    · simp

private lemma gm_eq_AA {F : Type} [Field F] {n m : ℕ} (T : Form F n (m + 1 + 2)) :
    genericMatrix T = T35F.AA (fun a : Fin (m+1+2) → Fin n => T (fun i => Pi.single (a i) 1)) := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [genericMatrix, T35F.AA, Matrix.of_apply]
  rw [T35F.con_explicit]
  rw [← Fintype.sum_equiv (Fin.appendEquiv (m+1) 2)
    (fun z => algebraMap F (T35F.PP F m n) (T (fun s => Pi.single ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) s) 1)) *
      ((∏ l : Fin (m+1), T35F.tv l ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) (Fin.castAdd 2 l))) *
        ((T35F.ee i : Fin n → T35F.PP F m n) ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n)
          (Fin.natAdd (m+1) 0)) * (T35F.ee j : Fin n → T35F.PP F m n)
          ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) (Fin.natAdd (m+1) 1))))) _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Fin.append_left, Fin.append_right]
  rw [← Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n).symm
    (fun z => algebraMap F (T35F.PP F m n) (T (fun s => Pi.single ((Fin.append g
        ((piFinTwoEquiv fun _ => Fin n).symm z) : Fin (m+1+2) → Fin n) s) 1)) *
      ((∏ l : Fin (m+1), T35F.tv l (g l)) *
        ((T35F.ee i : Fin n → T35F.PP F m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 0) *
          (T35F.ee j : Fin n → T35F.PP F m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 1))))
    _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, T35F.ee, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [Fin.cons_zero, Fin.cons_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [T35F.tv, MvPolynomial.algebraMap_eq]
  refine congrArg (· * _) (congrArg _ (congrArg T ?_))
  funext s
  refine Fin.addCases (fun l => ?_) (fun t => ?_) s
  · simp only [Fin.append_left, Fin.val_castAdd]
    rw [dif_pos (by omega)]; rfl
  · simp only [Fin.append_right, Fin.val_natAdd]
    fin_cases t
    · simp
    · simp

private lemma t35_core {F : Type} [Field F] {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → F)
    (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a) :
    Module.finrank (FractionRing (T35F.PP F m n)) (LinearMap.ker (Matrix.mulVecLin ((T35F.AA c).map
      (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n)))))) =
      n - ((T35F.AA c).map (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n)))).rank ∧
    ∀ x : Fin (m+1+2) → Fin n → FractionRing (T35F.PP F m n),
      (∀ j, j ≠ 0 → x j ∈ LinearMap.ker (Matrix.mulVecLin ((T35F.AA c).map
        (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n)))))) → T35F.evF c x = 0 := by
  classical
  obtain ⟨r, Λ, hrR, hmin, hSV, hker⟩ := T35F.main_T35 c hc
  set K := FractionRing (T35F.PP F m n) with hKdef
  set M := (T35F.AA c).map (algebraMap (T35F.PP F m n) K) with hM
  have hfin : Module.finrank K (LinearMap.ker (Matrix.mulVecLin M)) = n - M.rank := by
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [Module.finrank_fin_fun] at this
    have h2 : M.rank = Module.finrank K (LinearMap.range (Matrix.mulVecLin M)) := rfl
    omega
  refine ⟨hfin, ?_⟩
  let colK : Fin r → Fin n → K := fun l i => algebraMap (T35F.PP F m n) K (Λ i l)
  have hmem : ∀ l, colK l ∈ LinearMap.ker (Matrix.mulVecLin M) := by
    intro l
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    funext i
    show ((T35F.AA c).map (algebraMap (T35F.PP F m n) K) *ᵥ
      (algebraMap (T35F.PP F m n) K ∘ fun v => Λ v l)) i = 0
    rw [← RingHom.map_mulVec]
    show algebraMap (T35F.PP F m n) K (((Matrix.of fun i j =>
      T35F.con c T35F.tv (T35F.ee i) (T35F.ee j)) *ᵥ (fun v => Λ v l)) i) = 0
    rw [T35F.mulVec_con, hker, map_zero]
  have hinj : Function.Injective (algebraMap (T35F.PP F m n) K) :=
    IsFractionRing.injective _ _
  have hli : LinearIndependent K colK := by
    obtain ⟨ρ, hρ⟩ := hmin
    have hρK : ((Λ.map (algebraMap (T35F.PP F m n) K)).submatrix ρ id).det ≠ 0 := by
      rw [show (Λ.map (algebraMap (T35F.PP F m n) K)).submatrix ρ id =
        (Λ.submatrix ρ id).map (algebraMap (T35F.PP F m n) K) from rfl, T35aux.det_map_hom]
      exact fun h => hρ (hinj (by rw [h, map_zero]))
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 : ((Λ.map (algebraMap (T35F.PP F m n) K)).submatrix ρ id) *ᵥ g = 0 := by
      funext i
      have := congrFun hg (ρ i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colK, Pi.zero_apply] at this
      simp only [mulVec, dotProduct, Matrix.submatrix_apply, Matrix.map_apply, id, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hρK h1) l
  have hspan : Submodule.span K (Set.range colK) = LinearMap.ker (Matrix.mulVecLin M) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨l, rfl⟩; exact hmem l
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hfin]; omega
  let φ : T35F.PP F m n →ₐ[F] K := IsScalarTower.toAlgHom F (T35F.PP F m n) K
  have hS : ∀ x : Fin (m+1+2) → Fin n → K, (∀ j, j ≠ 0 → x j ∈ Set.range colK) →
      T35F.evF c x = 0 := by
    intro x hx
    have hterm : ∀ v : Fin n, T35F.evF c (Function.update x 0 (Pi.single v 1)) = 0 := by
      intro v
      let y : Fin (m+1+2) → Fin n → T35F.PP F m n := fun j =>
        if h : j = 0 then Pi.single v 1 else fun i => Λ i (Classical.choose (hx j h))
      have hy : Function.update x 0 (Pi.single v 1) = fun j w => φ (y j w) := by
        funext j w
        by_cases h : j = 0
        · subst h
          simp only [Function.update_self, y, dif_pos rfl]
          by_cases hw : w = v
          · subst hw; simp
          · simp [Pi.single_apply, hw]
        · rw [Function.update_of_ne h]
          have := Classical.choose_spec (hx j h)
          simp only [y, dif_neg h]
          exact (congrFun this w).symm
      rw [hy, ← T35F.ev_map φ]
      rw [hSV y (fun j hj => ⟨Classical.choose (hx j hj), by simp only [y, dif_neg hj]⟩), map_zero]
    have key : ∀ s : Finset (Fin n), T35F.evF c
        (Function.update x 0 (∑ v ∈ s, x 0 v • (Pi.single v 1 : Fin n → K))) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact L37F.ev_update_zero c x 0
      | insert v s hv ih =>
        rw [Finset.sum_insert hv, L37F.ev_update_add, L37F.ev_update_smul, ih, add_zero, hterm,
          mul_zero]
    have hx0 : x = Function.update x 0 (∑ v, x 0 v • (Pi.single v 1 : Fin n → K)) := by
      funext j w
      by_cases h : j = 0
      · subst h; simp [Finset.sum_apply, Pi.single_apply]
      · rw [Function.update_of_ne h]
    rw [hx0]; exact key _
  intro x hx
  refine L37F.sv_span c (Set.range colK) hS x ?_
  intro j hj
  rw [hspan]
  exact hx j hj

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- theorem 3 5; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {F : Type} [Field F] {n d : ℕ} (hd : 3 ≤ d)
    (T : Form F n d) (hT : IsMultilinear T) (hs : IsSymmetric T) :
    Module.finrank (AnchorField F n (d - 2)) (genericRadical T) = n - genericRank T ∧
    StrongVanishes (extendForm (E := AnchorField F n (d - 2)) T) (genericRadical T) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 + 2 := ⟨d - 3, by omega⟩
  set c : (Fin (m+1+2) → Fin n) → F := fun a => T (fun i => Pi.single (a i) 1) with hcdef
  have hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a := by
    intro σ a; exact hs σ (fun i => Pi.single (a i) 1)
  have hGC : genericContraction T = (T35F.AA c).map
      (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n))) := by
    unfold genericContraction; rw [gm_eq_AA]; rfl
  obtain ⟨h1, h2⟩ := t35_core c hc
  have hrad : genericRadical T = LinearMap.ker (Matrix.mulVecLin ((T35F.AA c).map
      (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n))))) := by
    unfold genericRadical; rw [hGC]; rfl
  have hrk : genericRank T = ((T35F.AA c).map
      (algebraMap (T35F.PP F m n) (FractionRing (T35F.PP F m n)))).rank := by
    unfold genericRank; rw [hGC]
  rw [hrad, hrk]
  refine ⟨h1, ?_⟩
  intro v u
  refine h2 _ ?_
  intro j hj
  have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
  simp only [dif_neg hj']
  exact (u _).2

