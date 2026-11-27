-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:37:21.852455+00:00
-- url     : https://prove2.me/submissions/bf81eb2a-69c6-4699-ba94-0473d827b70d

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Theorems.Thm_ParityDegreeDepth_Core_binary_descent

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

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0

private def StrongVanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop :=
  ∀ (v : Vec n F) (u : Fin (d - 1) → U),
    T (fun i => if hi : i.val = 0 then v else (u ⟨i.val - 1, by omega⟩ : Vec n F)) = 0

private def extendForm {F E : Type} [Field F] [Field E] [Algebra F E] {n d : ℕ}
    (T : Form F n d) : Form E n d :=
  fun x => ∑ a : Fin d → Fin n,
    algebraMap F E (T (fun i => Pi.single (a i) 1)) * ∏ i, x i (a i)




/-- a multilinear form over `𝔽₂` is evaluated by its coefficient tensor -/
private lemma form_eq_tensorEval {n d : ℕ} (T : Form (ZMod 2) n d) (hT : IsMultilinear T)
    (x : Fin d → Vec n (ZMod 2)) :
    T x = ParityDegreeDepth.Core.tensorEval (fun a => T (fun i => Pi.single (a i) 1)) x := by
  classical
  let f : MultilinearMap (ZMod 2) (fun _ : Fin d => Vec n (ZMod 2)) (ZMod 2) :=
    { toFun := T
      map_update_add' := fun x i u v => by convert hT.1 x i u v
      map_update_smul' := fun x i c u => by rw [smul_eq_mul]; convert hT.2 x i c u }
  have hx : x = fun i => ∑ v, x i v • (Pi.single v 1 : Vec n (ZMod 2)) := by
    funext i v; simp [Finset.sum_apply, Pi.single_apply]
  show f x = _
  conv_lhs => rw [hx, MultilinearMap.map_sum]
  unfold ParityDegreeDepth.Core.tensorEval
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  rw [mul_comm]; rfl

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 3 7; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n d L k : ℕ} (hd : 1 ≤ d) (T : Form (ZMod 2) n d)
    (hT : IsMultilinear T)
    (U : Submodule (FractionRing (MvPolynomial (Fin L) (ZMod 2)))
      (Vec n (FractionRing (MvPolynomial (Fin L) (ZMod 2)))))
    (hk : Module.finrank (FractionRing (MvPolynomial (Fin L) (ZMod 2))) U = k)
    (hU : StrongVanishes (extendForm (E := FractionRing (MvPolynomial (Fin L) (ZMod 2))) T) U) :
    ∃ U' : Submodule (ZMod 2) (Vec n (ZMod 2)),
      Module.finrank (ZMod 2) U' = Module.finrank (FractionRing (MvPolynomial (Fin L) (ZMod 2))) U ∧
      Module.finrank (ZMod 2) U' = k ∧ StrongVanishes T U' ∧ Vanishes T U' := by
  classical
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  set K := FractionRing (MvPolynomial (Fin L) (ZMod 2))
  set P := MvPolynomial (Fin L) (ZMod 2)
  set c : (Fin (d' + 1) → Fin n) → ZMod 2 := fun a => T (fun i => Pi.single (a i) 1) with hc
  have hext : ∀ x : Fin (d' + 1) → Vec n K, extendForm (E := K) T x =
      ParityDegreeDepth.Core.tensorEval c x := fun x => rfl
  -- a polynomial basis of U
  let b := Module.finBasisOfFinrankEq K U hk
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors P)
    (fun q : Fin n × Fin k => ((b q.2 : Vec n K) q.1))
  have hD' : ∀ i j, ∃ y : P, algebraMap P K y = (D : P) • ((b j : Vec n K) i) := fun i j => hD (i, j)
  choose Λ hΛ using hD'
  have hinj : Function.Injective (algebraMap P K) := IsFractionRing.injective P K
  have hDne : algebraMap P K (D : P) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero D)
  have hcol : ∀ j, (fun i => algebraMap P K (Λ i j)) = (algebraMap P K (D : P)) • (b j : Vec n K) := by
    intro j; funext i; rw [hΛ, Algebra.smul_def]; rfl
  have hcolU : ∀ j, (fun i => algebraMap P K (Λ i j)) ∈ U := by
    intro j; rw [hcol]; exact U.smul_mem _ (b j).2
  -- nonzero maximal minor
  have hli : LinearIndependent K (fun j => fun i => algebraMap P K (Λ i j)) := by
    have : (fun j => fun i => algebraMap P K (Λ i j)) = fun j => (algebraMap P K (D : P)) • (b j : Vec n K) := by
      funext j; rw [hcol]
    rw [this]
    exact (b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)).units_smul
      (fun _ => Units.mk0 _ hDne)
  let Λm : Matrix (Fin n) (Fin k) P := Matrix.of Λ
  set φ := algebraMap P K
  have hrank : k ≤ (Λm.map φ).rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have := finrank_span_eq_card hli
    rw [Fintype.card_fin] at this
    exact le_of_eq this.symm
  obtain ⟨ρ, ρ', hρ⟩ := T35aux.exists_minor_of_le_rank (Λm.map φ) hrank
  have hmin : ∃ ρ : Fin k → Fin n, (Λm.submatrix ρ id).det ≠ 0 := by
    have hρ'inj : Function.Injective ρ' := by
      intro a b' hab
      by_contra hne
      apply hρ
      exact Matrix.det_zero_of_column_eq hne (by intro i; simp [hab])
    let σ := Equiv.ofBijective ρ' (Finite.injective_iff_bijective.mp hρ'inj)
    have e1 : (Λm.map φ).submatrix ρ ρ' = ((Λm.map φ).submatrix ρ id).submatrix id σ := rfl
    rw [e1, Matrix.det_permute'] at hρ
    refine ⟨ρ, fun h0 => hρ ?_⟩
    rw [show ((Λm.map φ).submatrix ρ id) = (Λm.submatrix ρ id).map φ from rfl, T35aux.det_map_hom,
      h0, map_zero, mul_zero]
  let φA : P →ₐ[ZMod 2] K := IsScalarTower.toAlgHom (ZMod 2) P K
  have hSVP : ∀ x : Fin (d' + 1) → Fin n → P, (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λm i l) →
      ParityDegreeDepth.Core.tensorEval c x = 0 := by
    intro x hx
    apply hinj
    rw [map_zero]
    have e2 := T35aux.ev_map φA c x
    simp only [φA, IsScalarTower.coe_toAlgHom'] at e2
    rw [e2]
    set y : Fin (d' + 1) → Vec n K := fun j v => algebraMap P K (x j v) with hy
    have hyU : ∀ j : Fin (d' + 1), j ≠ 0 → y j ∈ U := by
      intro j hj
      obtain ⟨l, hl⟩ := hx j hj
      have : y j = fun i => algebraMap P K (Λ i l) := by
        funext i; simp [hy, hl, Λm]
      rw [this]; exact hcolU l
    let u : Fin (d' + 1 - 1) → U := fun j => ⟨y ⟨j.val + 1, by omega⟩, hyU _ (by
      intro h; have := congrArg Fin.val h; simp at this)⟩
    have hyeq : y = fun i : Fin (d' + 1) => if hi : i.val = 0 then y 0
        else ((u ⟨i.val - 1, by omega⟩ : U) : Vec n K) := by
      funext i
      by_cases hi : i.val = 0
      · rw [dif_pos hi]; congr 1; exact Fin.ext hi
      · rw [dif_neg hi]; simp only [u]; congr 1; ext; simp; omega
    have := hU (y 0) u
    rw [hext] at this
    rw [hyeq]
    exact this
  obtain ⟨Λ0, hmin0, hSV0⟩ := ParityDegreeDepth.Core.binary_descent (σ := Fin L) c Λm hmin hSVP
  let cols : Fin k → Vec n (ZMod 2) := fun l i => Λ0 i l
  let U' := Submodule.span (ZMod 2) (Set.range cols)
  have hli0 : LinearIndependent (ZMod 2) cols := by
    obtain ⟨ρ0, hρ0⟩ := hmin0
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 : (Λ0.submatrix ρ0 id) *ᵥ g = 0 := by
      funext i
      have := congrFun hg (ρ0 i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hρ0 h1) l
  have hfr : Module.finrank (ZMod 2) U' = k := by
    rw [finrank_span_eq_card hli0, Fintype.card_fin]
  have hS : ∀ x : Fin (d' + 1) → Vec n (ZMod 2), (∀ j, j ≠ 0 → x j ∈ Set.range cols) →
      ParityDegreeDepth.Core.tensorEval c x = 0 := by
    intro x hx
    apply hSV0 x
    intro j hj
    obtain ⟨l, hl⟩ := hx j hj
    exact ⟨l, hl.symm⟩
  refine ⟨U', by rw [hfr, hk], hfr, ?_, ?_⟩
  · intro v u
    rw [form_eq_tensorEval T hT]
    apply L37aux.sv_span c (Set.range cols) hS
    intro j hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp only [dif_neg hj']
    exact (u _).2
  · intro x hx
    rw [form_eq_tensorEval T hT]
    exact L37aux.sv_span c (Set.range cols) hS x (fun j _ => hx j)



