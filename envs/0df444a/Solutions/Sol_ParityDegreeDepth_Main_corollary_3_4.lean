-- Prove2me | solution 1 for ParityDegreeDepth.Main.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:30:02.899128+00:00
-- url     : https://prove2.me/submissions/85f4deb3-9402-4192-84ed-a50d7af79ccf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Theorems.Thm_ParityDegreeDepth_Core_generic_radical_strong_vanishing
import Theorems.Thm_ParityDegreeDepth_Core_binary_descent
import Theorems.Thm_ParityDegreeDepth_Core_generic_rank_le_binary
import Theorems.Thm_ParityDegreeDepth_Core_contraction_rank_bound
import Theorems.Thm_ParityDegreeDepth_Core_sign_spectral_bounds
import Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences
import Theorems.Thm_ParityDegreeDepth_Main_lemma_3_2

open scoped BigOperators
noncomputable section

open MvPolynomial ParityDegreeDepth.Core

namespace T35aux

section ev
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R] {d n : ℕ}

lemma ev_def (c : (Fin d → Fin n) → ZMod 2) (x : Fin d → Fin n → R) :
    tensorEval c x = ∑ a : Fin d → Fin n, algebraMap (ZMod 2) R (c a) * ∏ j, x j (a j) := rfl

lemma ev_map {S : Type*} [CommRing S] [Algebra (ZMod 2) S] (φ : R →ₐ[ZMod 2] S)
    (c : (Fin d → Fin n) → ZMod 2) (x : Fin d → Fin n → R) :
    φ (tensorEval c x) = tensorEval c (fun j v => φ (x j v)) := by
  simp only [ev_def, map_sum, map_mul, map_prod, AlgHom.commutes]

/-- multilinear expansion -/
lemma ev_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (Fin d → Fin n) → ZMod 2)
    (s : Fin d → ι → R) (y : Fin d → ι → Fin n → R) :
    tensorEval c (fun j v => ∑ l, s j l * y j l v) =
      ∑ f : Fin d → ι, (∏ j, s j (f j)) * tensorEval c (fun j => y j (f j)) := by
  simp only [ev_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]; ring

lemma ev_smul (c : (Fin d → Fin n) → ZMod 2) (s : Fin d → R) (y : Fin d → Fin n → R) :
    tensorEval c (fun j v => s j * y j v) = (∏ j, s j) * tensorEval c y := by
  simp only [ev_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib]; ring

lemma ev_perm (c : (Fin d → Fin n) → ZMod 2)
    (hc : ∀ (σ : Equiv.Perm (Fin d)) a, c (a ∘ σ) = c a) (σ : Equiv.Perm (Fin d))
    (x : Fin d → Fin n → R) : tensorEval c (x ∘ σ) = tensorEval c x := by
  simp only [ev_def]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ ?_
  intro a
  have he : (Equiv.arrowCongr σ (Equiv.refl (Fin n))) a = a ∘ σ.symm := rfl
  rw [he, hc σ.symm a]
  congr 1
  rw [← Equiv.prod_comp σ (fun j => x j ((a ∘ σ.symm) j))]
  simp

lemma ev_zero_slot (c : (Fin d → Fin n) → ZMod 2) (x : Fin d → Fin n → R) (j : Fin d)
    (hj : x j = 0) : tensorEval c x = 0 := by
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

end T35aux


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


open MvPolynomial ParityDegreeDepth.Core Matrix

namespace T35aux

noncomputable section

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2)

/-- contraction: anchors `w` in the first `m+1` slots, then `x`, `y`. -/
def con {S : Type*} [CommRing S] [Algebra (ZMod 2) S] (w : Fin (m+1) → Fin n → S)
    (x y : Fin n → S) : S :=
  tensorEval c (Fin.append w ![x, y])

def ee {S : Type*} [Semiring S] (i : Fin n) : Fin n → S := Pi.single i 1

lemma con_explicit {S : Type*} [CommRing S] [Algebra (ZMod 2) S] (w : Fin (m+1) → Fin n → S)
    (x y : Fin n → S) :
    con c w x y = ∑ a : Fin (m+1+2) → Fin n, algebraMap (ZMod 2) S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
        (x (a (Fin.natAdd (m+1) 0)) * y (a (Fin.natAdd (m+1) 1)))) := by
  unfold con
  rw [ev_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right, Fin.prod_univ_two]

variable {S : Type*} [CommRing S] [Algebra (ZMod 2) S]

lemma sum_single_mul (x : Fin n → S) (v : Fin n) :
    ∑ i, x i * (ee i : Fin n → S) v = x v := by
  simp [ee, Pi.single_apply]

omit [Algebra (ZMod 2) S] in
lemma sum_ee_left {α : Type*} [Fintype α] (F : α → S) (g : α → Fin n) (y : Fin n → S) :
    ∑ j, (∑ a, F a * (ee j : Fin n → S) (g a)) * y j = ∑ a, F a * y (g a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [ee, Pi.single_apply, mul_assoc]

omit [Algebra (ZMod 2) S] in
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
    have := sum_ee_left (fun a : Fin (m+1+2) → Fin n => algebraMap (ZMod 2) S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) * (ee i : Fin n → S) (a (Fin.natAdd (m+1) 0))))
      (fun a => a (Fin.natAdd (m+1) 1)) y
    simp only [mul_assoc] at this ⊢
    exact this
  simp only [h1]
  simp only [con_explicit]
  have := sum_ee_right (fun a : Fin (m+1+2) → Fin n => algebraMap (ZMod 2) S (c a) *
      ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) * y (a (Fin.natAdd (m+1) 1))))
      (fun a => a (Fin.natAdd (m+1) 0)) x
  rw [← Finset.sum_congr rfl (fun i _ => congrArg (x i * ·) (Finset.sum_congr rfl fun a _ =>
    (by ring : algebraMap (ZMod 2) S (c a) * ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
      ((ee i : Fin n → S) (a (Fin.natAdd (m+1) 0)) * y (a (Fin.natAdd (m+1) 1)))) =
      algebraMap (ZMod 2) S (c a) * ((∏ l : Fin (m+1), w l (a (Fin.castAdd 2 l))) *
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

end T35aux


open ParityDegreeDepth.Core Matrix

namespace L37aux

noncomputable section

open T35aux

variable {d n : ℕ} (c : (Fin (d+1) → Fin n) → ZMod 2)

def SV {R : Type*} [CommRing R] [Algebra (ZMod 2) R] {r : ℕ} (Λ : Matrix (Fin n) (Fin r) R) :
    Prop :=
  ∀ x : Fin (d+1) → Fin n → R, (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ i l) → tensorEval c x = 0

section lin
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]

lemma ev_update_add (x : Fin (d+1) → Fin n → R) (j : Fin (d+1)) (a b : Fin n → R) :
    tensorEval c (Function.update x j (a + b)) =
      tensorEval c (Function.update x j a) + tensorEval c (Function.update x j b) := by
  simp only [ev_def, ← Finset.sum_add_distrib]
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
    tensorEval c (Function.update x j (s • a)) = s * tensorEval c (Function.update x j a) := by
  simp only [ev_def, Finset.mul_sum]
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
    tensorEval c (Function.update x j 0) = 0 :=
  ev_zero_slot c _ j (by simp)

lemma sv_span (S : Set (Fin n → R))
    (hS : ∀ x : Fin (d+1) → Fin n → R, (∀ j, j ≠ 0 → x j ∈ S) → tensorEval c x = 0) :
    ∀ x : Fin (d+1) → Fin n → R, (∀ j, j ≠ 0 → x j ∈ Submodule.span R S) →
      tensorEval c x = 0 := by
  classical
  have key : ∀ F : Finset (Fin (d+1)), ∀ x : Fin (d+1) → Fin n → R,
      (∀ j, j ≠ 0 → j ∉ F → x j ∈ S) → (∀ j ∈ F, j ≠ 0 → x j ∈ Submodule.span R S) →
      tensorEval c x = 0 := by
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
      have : ∀ y ∈ Submodule.span R S, tensorEval c (Function.update x a y) = 0 := by
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

lemma sv_mul {r r' : ℕ} (Λ : Matrix (Fin n) (Fin r) R) (B : Matrix (Fin r) (Fin r') R)
    (h : SV c Λ) : SV c (Λ * B) := by
  intro x hx
  apply sv_span c (Set.range fun l => fun i => Λ i l)
  · intro y hy
    apply h y
    intro j hj
    obtain ⟨l, hl⟩ := hy j hj
    exact ⟨l, hl.symm⟩
  · intro j hj
    obtain ⟨l, hl⟩ := hx j hj
    rw [hl]
    have : (fun i => (Λ * B) i l) = ∑ k, B k l • fun i => Λ i k := by
      funext i; simp [Matrix.mul_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

lemma sv_smul [IsDomain R] {r : ℕ} (Λ : Matrix (Fin n) (Fin r) R) (s : R) (hs : s ≠ 0)
    (h : SV c (s • Λ)) : SV c Λ := by
  classical
  intro x hx
  let x' : Fin (d+1) → Fin n → R := fun j i => (if j = 0 then 1 else s) * x j i
  have h1 : tensorEval c x' = 0 := by
    apply h
    intro j hj
    obtain ⟨l, hl⟩ := hx j hj
    refine ⟨l, ?_⟩
    funext i
    simp [x', hj, hl, Matrix.smul_apply]
  have h2 : tensorEval c x' = (∏ j : Fin (d+1), if j = 0 then 1 else s) * tensorEval c x :=
    ev_smul c _ x
  rw [h2] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h3
    obtain ⟨j, _, hj⟩ := h3
    split_ifs at hj
    · exact one_ne_zero hj
    · exact hs hj
  · exact h3

lemma sv_map {S : Type*} [CommRing S] [Algebra (ZMod 2) S] {r : ℕ} (φ : R →ₐ[ZMod 2] S)
    (hφ : Function.Surjective φ) (Λ : Matrix (Fin n) (Fin r) R) (h : SV c Λ) :
    SV c (Λ.map φ) := by
  classical
  intro x hx
  choose f hf using fun i => hφ (x 0 i)
  let y : Fin (d+1) → Fin n → R := fun j =>
    if hj : j = 0 then f else fun i => Λ i (Classical.choose (hx j hj))
  have hy : (fun j i => φ (y j i)) = x := by
    funext j i
    by_cases hj : j = 0
    · subst hj; simp [y, hf]
    · simp only [y, dif_neg hj]
      have h2 := congrFun (Classical.choose_spec (hx j hj)) i
      exact h2.symm
  have : tensorEval c x = φ (tensorEval c y) := by
    rw [ev_map, hy]
  rw [this]
  have : tensorEval c y = 0 := by
    apply h
    intro j hj
    exact ⟨Classical.choose (hx j hj), by simp [y, hj]⟩
  rw [this, map_zero]

end lin

end

end L37aux


open scoped BigOperators
noncomputable section

namespace P2MDiff

variable {n : ℕ}

/-- iterated finite differences, as a left fold (first `h 0`, then `h 1`, …) -/
def diffs {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v x => q (x + v) + q x) p

def dl (u : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x => q (x + u) + q x

lemma diffs_zero (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin 0 → Fin n → ZMod 2) :
    diffs p h = p := by
  simp [diffs]

lemma diffs_succ {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin (k+1) → Fin n → ZMod 2) :
    diffs p h = diffs (dl (h 0) p) (Fin.tail h) := by
  simp only [diffs, List.ofFn_succ, List.foldl_cons]; rfl

lemma diffs_closed {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (x : Fin n → ZMod 2) :
    diffs p h x = ∑ ε : Fin k → ZMod 2, p (x + ∑ i, ε i • h i) := by
  induction k generalizing p with
  | zero => simp [diffs_zero]
  | succ k ih =>
    rw [diffs_succ, ih]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ZMod 2)
      (fun z => p (x + ∑ i, (Fin.cons z.1 z.2 : Fin (k+1) → ZMod 2) i • h i)) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have h01 : ∀ F : ZMod 2 → ZMod 2, ∑ b : ZMod 2, F b = F 0 + F 1 := by
      intro F
      have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      rw [this, Finset.sum_pair (by decide)]
    rw [h01, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    simp only [dl, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, zero_smul, one_smul,
      zero_add]
    rw [add_comm (p _)]
    congr 2
    abel

lemma dl_comm (u v : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) :
    dl u (dl v q) = dl v (dl u q) := by
  funext x; simp only [dl]
  rw [show x + u + v = x + v + u by abel]
  abel

lemma diffs_perm {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (σ : Equiv.Perm (Fin k)) : diffs p (h ∘ σ) = diffs p h := by
  funext x
  rw [diffs_closed, diffs_closed]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ fun ε => ?_
  congr 2
  have he : (Equiv.arrowCongr σ (Equiv.refl (ZMod 2))) ε = ε ∘ σ.symm := rfl
  rw [he]
  rw [← Equiv.sum_comp σ (fun i => (ε ∘ σ.symm) i • h i)]
  simp

lemma diffs_snoc {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (u : Fin n → ZMod 2) : diffs p (Fin.snoc h u) = dl u (diffs p h) := by
  rw [diffs, List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.foldl_cons, List.foldl_nil]
  rfl

/-- `p` has degree at most `j`: all `(j+1)`-fold differences vanish -/
def DegLe (j : ℕ) (p : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ (h : Fin (j+1) → Fin n → ZMod 2) (x : Fin n → ZMod 2), diffs p h x = 0

lemma diffs_const {j : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe j p)
    (h : Fin j → Fin n → ZMod 2) (x : Fin n → ZMod 2) : diffs p h x = diffs p h 0 := by
  have := hp (Fin.snoc h x) 0
  rw [diffs_snoc] at this
  simp only [dl, zero_add] at this
  have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h2 _ _ this

lemma top_add_last {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p)
    (h : Fin k → Fin n → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs p (Fin.snoc h (u + v)) 0 = diffs p (Fin.snoc h u) 0 + diffs p (Fin.snoc h v) 0 := by
  rw [diffs_snoc, diffs_snoc, diffs_snoc]
  have h2 := hp (Fin.snoc (Fin.snoc h u) v) 0
  rw [diffs_snoc, diffs_snoc] at h2
  simp only [dl, zero_add] at h2 ⊢
  have e : ∀ a b c d : ZMod 2, a + b + c + d = 0 → a + d = (c + d) + (b + d) := by decide
  apply e
  rw [show u + v = v + u by abel]
  linear_combination h2

end P2MDiff


open scoped BigOperators
open ParityDegreeDepth.Core
noncomputable section

namespace P2MDiff

variable {n : ℕ}

lemma diffs_cons {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (h : Fin k → Fin n → ZMod 2) : diffs p (Fin.cons u h) = diffs (dl u p) h := by
  rw [diffs_succ]; rfl

lemma degLe_dl {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p) (u : Fin n → ZMod 2) :
    DegLe k (dl u p) := by
  intro h x
  rw [← diffs_cons]; exact hp _ x

lemma degLe_succ {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe k p) : DegLe (k+1) p := by
  intro h x
  rw [← Fin.snoc_init_self h, diffs_snoc]
  simp only [dl]
  rw [hp (Fin.init h), hp (Fin.init h), add_zero]

lemma diffs_dl {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (g : Fin k → Fin n → ZMod 2) : diffs (dl u p) g = dl u (diffs p g) := by
  funext x
  simp only [diffs_closed, dl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [show x + ∑ i, ε i • g i + u = x + u + ∑ i, ε i • g i by abel]

/-- additive maps on `𝔽₂ⁿ` are linear -/
lemma additive_expand (L : (Fin n → ZMod 2) → ZMod 2) (hL : ∀ u v, L (u + v) = L u + L v)
    (w : Fin n → ZMod 2) : L w = ∑ v, w v * L (Pi.single v 1) := by
  have h0 : L 0 = 0 := by
    have := hL 0 0
    simp only [add_zero] at this
    have h2 : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
    exact h2 _ this
  let Lh : (Fin n → ZMod 2) →+ ZMod 2 := ⟨⟨L, h0⟩, hL⟩
  have hw : w = ∑ v, w v • (Pi.single v 1 : Fin n → ZMod 2) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  change Lh _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (w v) with h | h
  · rw [h, zero_smul, map_zero, zero_mul]
  · rw [h, one_smul, one_mul]; rfl

/-- coefficient tensor of the top form -/
def cT (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) : (Fin j → Fin n) → ZMod 2 :=
  fun a => diffs p (fun l => Pi.single (a l) 1) 0

lemma top_eq_tensorEval : ∀ (k : ℕ) (p : (Fin n → ZMod 2) → ZMod 2), DegLe k p →
    ∀ h : Fin k → Fin n → ZMod 2, diffs p h 0 = tensorEval (cT p k) h := by
  intro k
  induction k with
  | zero =>
    intro p _ h
    simp only [tensorEval, cT, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1 <;> funext l <;> exact Fin.elim0 l
  | succ k ih =>
    intro p hp h
    rw [← Fin.snoc_init_self h]
    generalize Fin.init h = g
    generalize h (Fin.last k) = w
    have hlin : ∀ u v, diffs p (Fin.snoc g (u + v)) 0 =
        diffs p (Fin.snoc g u) 0 + diffs p (Fin.snoc g v) 0 := top_add_last hp g
    rw [additive_expand (fun u => diffs p (Fin.snoc g u) 0) hlin w]
    have hstep : ∀ v, diffs p (Fin.snoc g (Pi.single v 1)) 0 =
        ∑ a : Fin k → Fin n, (∏ l, g l (a l)) * cT p (k+1) (Fin.snoc a v) := by
      intro v
      rw [diffs_snoc, ← diffs_dl, ih _ (degLe_dl hp _) g]
      simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 1
      simp only [cT]
      rw [diffs_dl, ← diffs_snoc]
      congr 2
      funext l
      refine Fin.lastCases ?_ (fun l' => ?_) l <;> simp
    simp only [hstep]
    simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin n)
      (fun z => cT p (k+1) (Fin.snoc z.2 z.1) * ∏ l, (Fin.snoc g w : Fin (k+1) → Fin n → ZMod 2) l
        ((Fin.snoc z.2 z.1 : Fin (k+1) → Fin n) l)) _ (fun z => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

lemma cT_symm (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) (σ : Equiv.Perm (Fin j))
    (a : Fin j → Fin n) : cT p j (a ∘ σ) = cT p j a := by
  unfold cT
  have := diffs_perm p (fun l => (Pi.single (a l) 1 : Fin n → ZMod 2)) σ
  rw [← this]
  rfl

/-- differences commute with affine reparametrisation -/
lemma diffs_comp {m k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (h : Fin k → Fin m → ZMod 2) (y : Fin m → ZMod 2) :
    diffs (fun y => p (a + B y)) h y = diffs p (fun i => B (h i)) (a + B y) := by
  rw [diffs_closed, diffs_closed]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [map_add, map_sum, map_smul, add_assoc]

end P2MDiff

open scoped BigOperators
open Matrix MvPolynomial ParityDegreeDepth.Core
noncomputable section

namespace P2MK3

open P2MDiff

variable {n : ℕ}

lemma rk_field {m r : ℕ} (N : Matrix (Fin m) (Fin r) (ZMod 2)) :
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

abbrev PPx (m n : ℕ) := MvPolynomial (Fin (m+1) × Fin n) (ZMod 2)

def AAx {m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2) : Matrix (Fin n) (Fin n) (PPx m n) :=
  Matrix.of fun i j : Fin n => tensorEval c
    (Fin.append (fun l v => (MvPolynomial.X (l, v) : PPx m n)) ![Pi.single i 1, Pi.single j 1])

def genx {D : Type*} [CommRing D] {k m r : ℕ} (N : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D) :
    Matrix (Fin m) (Fin r) (MvPolynomial (Fin k × Fin n) D) :=
  ∑ g : Fin k → Fin n, (∏ l, (MvPolynomial.X (l, g l) : MvPolynomial (Fin k × Fin n) D)) •
    (N g).map (MvPolynomial.C : D →+* MvPolynomial (Fin k × Fin n) D)

def specx {D : Type*} [CommRing D] {k m r : ℕ} (N : (Fin k → Fin n) → Matrix (Fin m) (Fin r) D)
    (a : Fin k × Fin n → D) : Matrix (Fin m) (Fin r) D :=
  ∑ g : Fin k → Fin n, (∏ l, a (l, g l)) • N g

lemma AAx_eq_gen {m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2) :
    AAx c = genx (fun g : Fin (m+1) → Fin n => Matrix.of fun i j => c (Fin.append g ![i, j])) := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [AAx, Matrix.of_apply, genx, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul]
  rw [show tensorEval c (Fin.append (fun l v => (MvPolynomial.X (l, v) : PPx m n))
      ![Pi.single i 1, Pi.single j 1]) =
      T35aux.con c (fun l v => (MvPolynomial.X (l, v) : PPx m n)) (T35aux.ee i) (T35aux.ee j) from rfl]
  rw [T35aux.con_explicit]
  rw [← Fintype.sum_equiv (Fin.appendEquiv (m+1) 2)
    (fun z => algebraMap (ZMod 2) (PPx m n) (c (Fin.append z.1 z.2)) *
      ((∏ l : Fin (m+1), (MvPolynomial.X (l, (Fin.append z.1 z.2 : Fin (m+1+2) → Fin n)
          (Fin.castAdd 2 l)) : PPx m n)) *
        ((T35aux.ee i : Fin n → PPx m n) ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n)
          (Fin.natAdd (m+1) 0)) * (T35aux.ee j : Fin n → PPx m n)
          ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) (Fin.natAdd (m+1) 1))))) _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Fin.append_left, Fin.append_right]
  rw [← Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n).symm
    (fun z => algebraMap (ZMod 2) (PPx m n) (c (Fin.append g ((piFinTwoEquiv fun _ => Fin n).symm z))) *
      ((∏ l : Fin (m+1), (MvPolynomial.X (l, g l) : PPx m n)) *
        ((T35aux.ee i : Fin n → PPx m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 0) *
          (T35aux.ee j : Fin n → PPx m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 1))))
    _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, T35aux.ee, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [Fin.cons_zero, Fin.cons_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [MvPolynomial.algebraMap_eq]
  rw [mul_comm]; rfl

lemma genx_map_eval {m r k : ℕ} (Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) (ZMod 2))
    (a : Fin k × Fin n → ZMod 2) :
    (genx Ng).map (MvPolynomial.aeval a : MvPolynomial (Fin k × Fin n) (ZMod 2) →ₐ[ZMod 2] ZMod 2)
      = specx Ng a := by
  refine Matrix.ext fun i j => ?_
  simp [genx, specx, Matrix.sum_apply, map_sum, map_prod]

theorem eq7 {j : ℕ} (hj : 3 ≤ j) (p : (Fin n → ZMod 2) → ZMod 2) (hp : DegLe j p) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin j → Fin n → ZMod 2, (∀ i, h i ∈ U) → diffs p h 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤
        2 ^ (2 * j - 3) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 + 2 := ⟨j - 3, by omega⟩
  set c := cT p (m+1+2) with hcdef
  have hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a := cT_symm p _
  obtain ⟨r, Λ, hrR, hmin, hSV⟩ := ParityDegreeDepth.Core.generic_radical_strong_vanishing c hc
  obtain ⟨Λ0, hmin0, hSV0⟩ := ParityDegreeDepth.Core.binary_descent c Λ hmin hSV
  let cols : Fin r → (Fin n → ZMod 2) := fun l i => Λ0 i l
  let U := Submodule.span (ZMod 2) (Set.range cols)
  have hli : LinearIndependent (ZMod 2) cols := by
    obtain ⟨ρ, hρ⟩ := hmin0
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 : (Λ0.submatrix ρ id) *ᵥ g = 0 := by
      funext i
      have := congrFun hg (ρ i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [mulVec, dotProduct, Matrix.submatrix_apply, id, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hρ h1) l
  have hfr : Module.finrank (ZMod 2) U = r := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine ⟨U, ?_, ?_⟩
  · intro h hh
    rw [top_eq_tensorEval _ p hp h]
    apply L37aux.sv_span c (Set.range cols) _ h (fun j _ => hh j)
    intro x hx
    apply hSV0 x
    intro j hj
    obtain ⟨l, hl⟩ := hx j hj
    exact ⟨l, hl.symm⟩
  · set R := ((AAx c).map (algebraMap (PPx m n) (FractionRing (PPx m n)))).rank with hRdef
    have hcod : (n : ℝ) - Module.finrank (ZMod 2) U = R := by
      rw [hfr]; have : (n : ℝ) = r + R := by exact_mod_cast hrR.symm
      linarith
    rw [hcod]
    let Ng : (Fin (m+1) → Fin n) → Matrix (Fin n) (Fin n) (ZMod 2) :=
      fun g => Matrix.of fun i j => c (Fin.append g ![i, j])
    obtain ⟨a, -, hblk⟩ := ParityDegreeDepth.Core.generic_rank_le_binary (m+1) (ZMod 2) Ng
    have hblk' : R ≤ 2 ^ (m+1) * ((specx Ng a).map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank := by
      rw [hRdef, AAx_eq_gen]; exact hblk
    let h : Fin (m+1) → Fin n → ZMod 2 := fun l v => a (l, v)
    have hspec : specx Ng a =
        Matrix.of fun i j : Fin n => diffs p (Fin.append h ![Pi.single i 1, Pi.single j 1]) 0 := by
      rw [← genx_map_eval, ← AAx_eq_gen]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, AAx, Matrix.of_apply]
      rw [top_eq_tensorEval _ p hp, T35aux.ev_map]
      congr 1
      funext l v
      refine Fin.addCases (fun l' => ?_) (fun t => ?_) l
      · simp [Fin.append_left, h]
      · fin_cases t
        · by_cases hv : v = i
          · subst hv; simp [Fin.append_right]
          · simp [Fin.append_right, Pi.single_apply, hv]
        · by_cases hv : v = j
          · subst hv; simp [Fin.append_right]
          · simp [Fin.append_right, Pi.single_apply, hv]
    have hbin := ParityDegreeDepth.Core.contraction_rank_bound (k := m+1) p hp h
    have hbin' : ((specx Ng a).map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank ≤
        (2 : ℝ) ^ (m+1+1) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by
      rw [rk_field, hspec]; exact hbin
    have hlog : 0 ≤ Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) :=
      Real.logb_nonneg (by norm_num) (ParityDegreeDepth.Core.sign_spectral_bounds p).1
    have hR : (R : ℝ) ≤ 2 ^ (m+1) *
        (((specx Ng a).map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank : ℝ) := by
      exact_mod_cast hblk'
    calc (R : ℝ) ≤ 2 ^ (m+1) * (((specx Ng a).map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank : ℝ) := hR
      _ ≤ 2 ^ (m+1) * (2 ^ (m+1+1) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|)) := by
        gcongr
      _ = 2 ^ (2 * (m+1+2) - 3) * Real.logb 2 (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) := by
        rw [show 2 * (m+1+2) - 3 = (m+1) + (m+1+1) by omega, pow_add]; ring

end P2MK3

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

private def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

private def contraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (h : Fin (d - 2) → Vec n F) : Matrix (Fin n) (Fin n) F :=
  fun i j => T (fun s => if hs : s.val < d - 2 then h ⟨s.val, hs⟩
    else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)

private def binaryRank {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  Finset.univ.sup fun h : Fin (d - 2) → Vec n (ZMod 2) => (contraction T h).rank

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



/-- ANF degree `d` gives vanishing `(d+1)`-fold differences -/
private lemma degLe_of_anf {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : anfDegree p = (d : WithBot ℕ)) :
    P2MDiff.DegLe d p := by
  classical
  apply (ParityDegreeDepth.Core.anf_degree_differences (d := d) p).1
  intro S hS
  by_contra hne
  have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
    unfold anfDegree
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
      if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
    simp only [show coefficient p S = (if ParityCubes.anfCoeff
      (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S then (1 : ZMod 2) else 0) from rfl,
      if_neg hne]
  rw [hp] at this
  have : S.card ≤ d := by exact_mod_cast this
  omega

/-- the slot selection of `genericMatrix` is the basis tuple of `Fin.append` -/
private lemma sel_eq {n m : ℕ} (g : Fin (m + 1 + 2 - 2) → Fin n) (i j : Fin n) :
    (fun s : Fin (m + 1 + 2) => if hs : s.val < m + 1 + 2 - 2 then
        (Pi.single (g ⟨s.val, hs⟩) 1 : Fin n → ZMod 2)
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

private lemma con_eq {n m : ℕ} (h : Fin (m + 1 + 2 - 2) → Vec n (ZMod 2)) (i j : Fin n) :
    (fun s : Fin (m + 1 + 2) => if hs : s.val < m + 1 + 2 - 2 then h ⟨s.val, hs⟩
      else if s.val = m + 1 + 2 - 2 then (Pi.single i 1 : Fin n → ZMod 2) else Pi.single j 1) =
    Fin.append (fun l : Fin (m+1) => h ⟨l.val, by omega⟩) ![Pi.single i 1, Pi.single j 1] := by
  funext s
  refine Fin.addCases (fun l => ?_) (fun t => ?_) s
  · simp only [Fin.append_left, Fin.val_castAdd]
    rw [dif_pos (by omega)]
  · simp only [Fin.append_right, Fin.val_natAdd]
    fin_cases t
    · simp
    · simp

private lemma gm_eq {n m : ℕ} (p : Vec n (ZMod 2) → ZMod 2) :
    genericMatrix (topForm p (m + 1 + 2)) = P2MK3.AAx (P2MDiff.cT p (m + 1 + 2)) := by
  rw [P2MK3.AAx_eq_gen]
  refine Matrix.ext fun i j => ?_
  simp only [genericMatrix, P2MK3.genx, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.of_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  congr 2
  show P2MDiff.diffs p _ 0 = P2MDiff.diffs p _ 0
  rw [sel_eq]
  rfl

private lemma contraction_apply {n m : ℕ} (T : Form (ZMod 2) n (m + 1 + 2))
    (h : Fin (m + 1 + 2 - 2) → Vec n (ZMod 2)) (i j : Fin n) :
    contraction T h i j = T (Fin.append (fun l : Fin (m+1) => h ⟨l.val, by omega⟩)
      ![Pi.single i 1, Pi.single j 1]) := by
  unfold contraction
  rw [con_eq]

private lemma spec_eq {n m : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : P2MDiff.DegLe (m + 1 + 2) p)
    (a : Fin (m + 1) × Fin n → ZMod 2) :
    P2MK3.specx (fun g : Fin (m+1) → Fin n => Matrix.of fun i j => P2MDiff.cT p (m+1+2)
      (Fin.append g ![i, j])) a =
    contraction (topForm p (m + 1 + 2)) (fun l v => a (⟨l.val, by omega⟩, v)) := by
  rw [← P2MK3.genx_map_eval, ← P2MK3.AAx_eq_gen]
  refine Matrix.ext fun i j => ?_
  rw [contraction_apply]
  simp only [Matrix.map_apply, P2MK3.AAx, Matrix.of_apply, topForm]
  rw [T35aux.ev_map]
  show _ = P2MDiff.diffs p _ 0
  rw [P2MDiff.top_eq_tensorEval _ p hp]
  congr 1
  funext l v
  refine Fin.addCases (fun l' => ?_) (fun t => ?_) l
  · simp [Fin.append_left]
  · fin_cases t
    · by_cases hv : v = i
      · subst hv; simp [Fin.append_right]
      · simp [Fin.append_right, Pi.single_apply, hv]
    · by_cases hv : v = j
      · subst hv; simp [Fin.append_right]
      · simp [Fin.append_right, Pi.single_apply, hv]

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- corollary 3 4; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 3 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    genericRank (topForm p d) ≤ 2 ^ (d - 2) * binaryRank (topForm p d) ∧
    ((2 ^ (d - 2) * binaryRank (topForm p d) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (2 * d - 3) * logTwo (spectralNorm (phase p)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 + 2 := ⟨d - 3, by omega⟩
  have hdeg := degLe_of_anf p hp
  set Ng : (Fin (m+1) → Fin n) → Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun g => Matrix.of fun i j => P2MDiff.cT p (m+1+2) (Fin.append g ![i, j]) with hNg
  obtain ⟨a, -, hblk⟩ := ParityDegreeDepth.Core.generic_rank_le_binary (m+1) (ZMod 2) Ng
  have hG : genericRank (topForm p (m + 1 + 2)) =
      ((P2MK3.genx Ng).map (algebraMap (MvPolynomial (Fin (m+1) × Fin n) (ZMod 2))
        (FractionRing (MvPolynomial (Fin (m+1) × Fin n) (ZMod 2))))).rank := by
    unfold genericRank genericContraction
    rw [gm_eq, P2MK3.AAx_eq_gen]
    rfl
  have hS := spec_eq p hdeg a
  have hrk : ((P2MK3.specx Ng a).map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).rank ≤
      binaryRank (topForm p (m + 1 + 2)) := by
    rw [P2MK3.rk_field, hS]
    exact Finset.le_sup (f := fun h : Fin (m + 1 + 2 - 2) → Vec n (ZMod 2) =>
      (contraction (topForm p (m + 1 + 2)) h).rank) (Finset.mem_univ _)
  have part1 : genericRank (topForm p (m + 1 + 2)) ≤ 2 ^ (m + 1 + 2 - 2) * binaryRank (topForm p (m + 1 + 2)) := by
    rw [hG]
    exact hblk.trans (Nat.mul_le_mul_left _ hrk)
  refine ⟨part1, ?_⟩
  have h32 : (binaryRank (topForm p (m + 1 + 2)) : ℝ) ≤
      (2 : ℝ) ^ (m + 1 + 2 - 1) * logTwo (spectralNorm (phase p)) :=
    ParityDegreeDepth.Main.lemma_3_2 p (by omega) hp
  push_cast
  calc (2 : ℝ) ^ (m + 1 + 2 - 2) * (binaryRank (topForm p (m + 1 + 2)) : ℝ)
      ≤ 2 ^ (m + 1 + 2 - 2) * (2 ^ (m + 1 + 2 - 1) * logTwo (spectralNorm (phase p))) := by
        gcongr
    _ = (2 : ℝ) ^ (2 * (m + 1 + 2) - 3) * logTwo (spectralNorm (phase p)) := by
        rw [← mul_assoc, ← pow_add, show m + 1 + 2 - 2 + (m + 1 + 2 - 1) = 2 * (m + 1 + 2) - 3 by omega]



