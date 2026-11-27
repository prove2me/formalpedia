-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:33:28.962505+00:00
-- url     : https://prove2.me/submissions/f6ab5928-fa5e-4903-bb80-6766b818ef51

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences

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


open scoped BigOperators
noncomputable section

namespace P2MFourier

/-- the sign `(-1)^z` of `z ∈ 𝔽₂` -/
def sg (z : ZMod 2) : ℝ := (-1 : ℝ) ^ z.val

lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  unfold sg; rw [ZMod.val_add, ← pow_add, ← neg_one_pow_eq_pow_mod_two]

lemma sg_zero : sg 0 = 1 := by simp [sg]

lemma sg_one : sg 1 = -1 := by unfold sg; simp [ZMod.val_one]

lemma pself {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero (x i)

lemma eq_of_add_eq_zero' {n : ℕ} {x y : Fin n → ZMod 2} (h : y + x = 0) : y = x := by
  calc y = y + (x + x) := by rw [pself, add_zero]
    _ = (y + x) + x := by rw [add_assoc]
    _ = x := by rw [h, zero_add]

lemma zmod2_eq_one (z : ZMod 2) (h : z ≠ 0) : z = 1 := by revert z; decide

lemma sg_mul_self (a : ZMod 2) : sg a * sg a = 1 := by
  rw [← sg_add]; simp [sg_zero, CharTwo.add_self_eq_zero]

lemma abs_sg (a : ZMod 2) : |sg a| = 1 := by
  unfold sg; fin_cases a <;> norm_num [ZMod.val]

variable {n : ℕ}

lemma dot_add_right (ξ x y : Fin n → ZMod 2) : ξ ⬝ᵥ (x + y) = ξ ⬝ᵥ x + ξ ⬝ᵥ y := by
  simp [dotProduct_add]

lemma dot_add_left (ξ η x : Fin n → ZMod 2) : (ξ + η) ⬝ᵥ x = ξ ⬝ᵥ x + η ⬝ᵥ x := by
  simp [add_dotProduct]

/-- character sum -/
lemma sum_sg_dot (ξ : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ x) = if ξ = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · subst h; simp [sg_zero, Finset.card_univ, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
      by_contra hc; push Not at hc; exact h (funext hc)
    have hi1 : ξ i = 1 := zmod2_eq_one _ hi
    have key : ∀ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ (x + Pi.single i 1)) = - sg (ξ ⬝ᵥ x) := by
      intro x
      rw [dot_add_right, sg_add, dotProduct_single, mul_one, hi1, sg_one, mul_neg_one]
    have hS : ∑ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ x) = ∑ x : Fin n → ZMod 2, - sg (ξ ⬝ᵥ x) := by
      rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2))) (fun x => sg (ξ ⬝ᵥ x))]
      exact Finset.sum_congr rfl fun x _ => key x
    rw [Finset.sum_neg_distrib] at hS
    linarith

lemma boolFourier_eq (f : (Fin n → ZMod 2) → ℝ) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier f ξ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * sg (ξ ⬝ᵥ x) := by
  rw [QAlgorithms.boolFourier]; rfl

lemma two_pow_ne : ((2 : ℝ) ^ n) ≠ 0 := by positivity

/-- Fourier inversion -/
lemma fourier_inversion (f : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    f x = ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
  simp only [boolFourier_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ y : Fin n → ZMod 2, ∑ ξ : Fin n → ZMod 2, ((2:ℝ) ^ n)⁻¹ * (f y * sg (ξ ⬝ᵥ y)) *
      sg (ξ ⬝ᵥ x) = if y = x then f x else 0 := by
    intro y
    have h2 : ∀ ξ : Fin n → ZMod 2, ((2:ℝ) ^ n)⁻¹ * (f y * sg (ξ ⬝ᵥ y)) * sg (ξ ⬝ᵥ x) =
        ((2:ℝ) ^ n)⁻¹ * f y * sg ((y + x) ⬝ᵥ ξ) := by
      intro ξ
      rw [dot_add_left, sg_add, dotProduct_comm y, dotProduct_comm x]; ring
    simp only [h2, ← Finset.mul_sum, sum_sg_dot]
    by_cases hyx : y = x
    · subst hyx; simp [pself]; field_simp
    · have : y + x ≠ 0 := by
        intro h; apply hyx; exact eq_of_add_eq_zero' h
      simp [this, hyx]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- product formula -/
lemma fourier_mul (f g : (Fin n → ZMod 2) → ℝ) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f x * g x) ξ =
      ∑ η, QAlgorithms.boolFourier f η * QAlgorithms.boolFourier g (ξ + η) := by
  conv_lhs => rw [boolFourier_eq]
  conv_lhs =>
    enter [2, 2, x]
    rw [fourier_inversion f x]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [boolFourier_eq g (ξ + η), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_left, sg_add]
  ring

def l1 (f : (Fin n → ZMod 2) → ℝ) : ℝ := ∑ a, |QAlgorithms.boolFourier f a|

lemma l1_nonneg (f : (Fin n → ZMod 2) → ℝ) : 0 ≤ l1 f :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1_mul_le (f g : (Fin n → ZMod 2) → ℝ) : l1 (fun x => f x * g x) ≤ l1 f * l1 g := by
  unfold l1
  simp only [fourier_mul]
  calc ∑ ξ, |∑ η, QAlgorithms.boolFourier f η * QAlgorithms.boolFourier g (ξ + η)|
      ≤ ∑ ξ, ∑ η, |QAlgorithms.boolFourier f η| * |QAlgorithms.boolFourier g (ξ + η)| := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ η, |QAlgorithms.boolFourier f η| * ∑ ξ, |QAlgorithms.boolFourier g (ξ + η)| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ = ∑ η, |QAlgorithms.boolFourier f η| * ∑ ξ, |QAlgorithms.boolFourier g ξ| := by
        refine Finset.sum_congr rfl fun η _ => ?_
        congr 1
        exact Equiv.sum_comp (Equiv.addRight η) (fun ξ => |QAlgorithms.boolFourier g ξ|)
    _ = _ := by rw [Finset.sum_mul]

lemma fourier_translate (f : (Fin n → ZMod 2) → ℝ) (a ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f (x + a)) ξ = sg (ξ ⬝ᵥ a) * QAlgorithms.boolFourier f ξ := by
  rw [boolFourier_eq, boolFourier_eq]
  have hre : ∑ x, f x * sg (ξ ⬝ᵥ x) = ∑ x, f (x + a) * sg (ξ ⬝ᵥ (x + a)) :=
    (Equiv.sum_comp (Equiv.addRight a) (fun x => f x * sg (ξ ⬝ᵥ x))).symm
  rw [hre, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_right, sg_add]
  have := sg_mul_self (ξ ⬝ᵥ a)
  calc ((2:ℝ) ^ n)⁻¹ * (f (x + a) * sg (ξ ⬝ᵥ x))
      = ((2:ℝ) ^ n)⁻¹ * (f (x + a) * sg (ξ ⬝ᵥ x)) * (sg (ξ ⬝ᵥ a) * sg (ξ ⬝ᵥ a)) := by
        rw [this, mul_one]
    _ = _ := by ring

lemma l1_translate (f : (Fin n → ZMod 2) → ℝ) (a : Fin n → ZMod 2) :
    l1 (fun x => f (x + a)) = l1 f := by
  unfold l1; simp [fourier_translate, abs_mul, abs_sg]

lemma fourier_mul_char (f : (Fin n → ZMod 2) → ℝ) (a ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f x * sg (a ⬝ᵥ x)) ξ =
      QAlgorithms.boolFourier f (ξ + a) := by
  rw [boolFourier_eq, boolFourier_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_left, sg_add]; ring

lemma l1_mul_char (f : (Fin n → ZMod 2) → ℝ) (a : Fin n → ZMod 2) :
    l1 (fun x => f x * sg (a ⬝ᵥ x)) = l1 f := by
  unfold l1; simp only [fourier_mul_char]
  exact Equiv.sum_comp (Equiv.addRight a) (fun ξ => |QAlgorithms.boolFourier f ξ|)

end P2MFourier

end


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
noncomputable section

namespace P2MANF

open P2MDiff

variable {n : ℕ}

/-- the ANF coefficient as in the source statement -/
def coeffZ (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

def ind (B : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ B then 1 else 0

lemma natCast_zmod2 (k : ℕ) : (k : ZMod 2) = if Odd k then 1 else 0 := by
  split_ifs with h
  · exact ZMod.natCast_eq_one_iff_odd.mpr h
  · rw [ZMod.natCast_eq_zero_iff_even]; exact Nat.not_odd_iff_even.mp h

lemma coeffZ_eq (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    coeffZ p S = ∑ B ∈ S.powerset, p (ind B) := by
  classical
  have h01 : ∀ z : ZMod 2, (if z ≠ 0 then (1 : ZMod 2) else 0) = z := by decide
  rw [← Finset.sum_congr rfl (fun B _ => h01 (p (ind B))), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one, natCast_zmod2]
  unfold coeffZ ParityCubes.anfCoeff
  have : ∀ B : Finset (Fin n), (fun i => if decide (i ∈ B) = true then (1 : ZMod 2) else 0) = ind B := by
    intro B; funext i; simp [ind]
  simp only [this, decide_eq_true_eq]
  congr

/-- affine phases have no ANF coefficients of size `≥ 2` -/
lemma coeffZ_affine (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) : coeffZ p S = 0 := by
  classical
  rw [coeffZ_eq]
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set T := S.erase a
  have hS' : S = insert a T := (Finset.insert_erase ha).symm
  have haT : a ∉ T := Finset.notMem_erase a S
  have hT : T.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  rw [hS', Finset.sum_powerset_insert haT]
  rw [← Finset.sum_add_distrib]
  have hc : ∀ B ∈ T.powerset, p (ind B) + p (ind (insert a B)) = p (Pi.single a 1) + p 0 := by
    intro B hB
    have haB : a ∉ B := fun h => haT (Finset.mem_powerset.mp hB h)
    have hind : ind (insert a B) = ind B + Pi.single a 1 := by
      funext i; by_cases hi : i = a
      · subst hi; simp [ind, haB]
      · simp [ind, hi, Pi.single_apply]
    rw [hind]
    have := hp 0 (ind B) (Pi.single a 1)
    simp only [zero_add] at this
    have e : ∀ w x y z : ZMod 2, w + x + y + z = 0 → x + w = y + z := by decide
    exact e _ _ _ _ this
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  have : ((2 ^ T.card : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_pow (Finset.card_pos.mpr hT).ne']
  rw [this, zero_mul]

end P2MANF

namespace P2MANF

open P2MDiff

variable {n : ℕ}

lemma degLe_iff_succ (k : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe (k+1) f ↔ ∀ u, DegLe k (dl u f) := by
  constructor
  · intro hf u; exact degLe_dl hf u
  · intro H h x
    rw [diffs_succ]; exact H (h 0) (Fin.tail h) x

lemma degLe_zero_iff (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe 0 f ↔ ∀ u x, f (x + u) = f x := by
  have e : ∀ h : Fin 1 → Fin n → ZMod 2, diffs f h = dl (h 0) f := by
    intro h; rw [diffs_succ, diffs_zero]
  constructor
  · intro hf u x
    have := hf (fun _ => u) x
    rw [e] at this
    simp only [dl] at this
    have e2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact e2 _ _ this
  · intro H h x
    rw [e]; simp only [dl, H]
    exact CharTwo.add_self_eq_zero _

lemma diffs_add {k : ℕ} (f g : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) (x : Fin n → ZMod 2) :
    diffs (fun y => f y + g y) h x = diffs f h x + diffs g h x := by
  simp only [diffs_closed, Finset.sum_add_distrib]

lemma degLe_add {k : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (hg : DegLe k g) :
    DegLe k (fun y => f y + g y) := by
  intro h x; rw [diffs_add, hf, hg, add_zero]

lemma degLe_zerofun (k : ℕ) : DegLe k (fun _ : Fin n → ZMod 2 => (0 : ZMod 2)) := by
  intro h x; simp [diffs_closed]

lemma degLe_smul {k : ℕ} (c : ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k (fun y => c * f y) := by
  intro h x
  simp only [diffs_closed, ← Finset.mul_sum]
  rw [← diffs_closed, hf, mul_zero]

lemma degLe_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ i ∈ s, DegLe k (f i)) : DegLe k (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLe_zerofun k
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact degLe_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma degLe_translate {k : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (u : Fin n → ZMod 2) :
    DegLe k (fun x => f (x + u)) := by
  intro h x
  have := hf h (x + u)
  rw [diffs_closed] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1; abel

lemma degLe_mono {k k' : ℕ} (hkk : k ≤ k') {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k' f := by
  induction hkk with
  | refl => exact hf
  | step _ ih => exact degLe_succ ih

lemma dl_mul (u : Fin n → ZMod 2) (g h : (Fin n → ZMod 2) → ZMod 2) :
    dl u (fun x => g x * h x) = fun x => dl u g x * h (x + u) + g x * dl u h x := by
  funext x
  simp only [dl]
  have h2 := CharTwo.add_self_eq_zero (g x * h (x + u))
  linear_combination (-1 : ZMod 2) * h2

lemma degLe_mul : ∀ (N a b : ℕ) (g h : (Fin n → ZMod 2) → ZMod 2), a + b = N → DegLe a g →
    DegLe b h → DegLe N (fun x => g x * h x) := by
  intro N
  induction N with
  | zero =>
    intro a b g h hab hg hh
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    rw [degLe_zero_iff] at *
    intro u x
    rw [hg, hh]
  | succ N ih =>
    intro a b g h hab hg hh
    rw [degLe_iff_succ]
    intro u
    rw [dl_mul]
    apply degLe_add
    · cases a with
      | zero =>
        have : ∀ x, dl u g x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff g).mp hg u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, zero_mul]
        exact degLe_zerofun N
      | succ a =>
        exact ih a b (dl u g) (fun x => h (x + u)) (by omega) (degLe_dl hg u) (degLe_translate hh u)
    · cases b with
      | zero =>
        have : ∀ x, dl u h x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff h).mp hh u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, mul_zero]
        exact degLe_zerofun N
      | succ b =>
        exact ih a b g (dl u h) (by omega) hg (degLe_dl hh u)

def mon (S : Finset (Fin n)) : (Fin n → ZMod 2) → ZMod 2 := fun x => ∏ i ∈ S, x i

lemma degLe_mon (S : Finset (Fin n)) : DegLe S.card (mon S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [mon, Finset.prod_empty, Finset.card_empty]
    rw [degLe_zero_iff]; intro u x; rfl
  | insert a S ha ih =>
    have hcoord : DegLe 1 (fun x : Fin n → ZMod 2 => x a) := by
      rw [degLe_iff_succ]; intro u
      rw [degLe_zero_iff]; intro v x
      simp only [dl, Pi.add_apply]
      linear_combination CharTwo.add_self_eq_zero (v a)
    have := degLe_mul (1 + S.card) 1 S.card _ _ rfl hcoord ih
    rw [Finset.card_insert_of_notMem ha, add_comm]
    convert this using 1
    funext x
    simp [mon, Finset.prod_insert ha]

lemma mobius (T : Finset (Fin n)) : ∀ g : Finset (Fin n) → ZMod 2,
    ∑ S ∈ T.powerset, ∑ B ∈ S.powerset, g B = g T := by
  classical
  induction T using Finset.induction_on with
  | empty => intro g; simp
  | insert a T ha ih =>
    intro g
    rw [Finset.sum_powerset_insert ha]
    have h1 : ∀ S ∈ T.powerset, ∑ B ∈ (insert a S).powerset, g B =
        ∑ B ∈ S.powerset, g B + ∑ B ∈ S.powerset, g (insert a B) := by
      intro S hS
      have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
      rw [Finset.sum_powerset_insert haS]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih (fun B => g (insert a B))]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

lemma inversion (p : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    p x = ∑ S, coeffZ p S * mon S x := by
  classical
  set T := Finset.univ.filter fun i => x i ≠ 0
  have hx : x = ind T := by
    funext i
    simp only [ind, T, Finset.mem_filter, Finset.mem_univ, true_and]
    have h01 : ∀ z : ZMod 2, z = if z ≠ 0 then 1 else 0 := by decide
    exact h01 (x i)
  have hmon : ∀ S, mon S x = if S ⊆ T then 1 else 0 := by
    intro S
    rw [hx]
    simp only [mon, ind]
    split_ifs with h
    · exact Finset.prod_eq_one fun i hi => by simp [h hi]
    · rw [Finset.not_subset] at h
      obtain ⟨i, hiS, hiT⟩ := h
      exact Finset.prod_eq_zero hiS (by simp [hiT])
  simp only [hmon, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ T) = T.powerset := by
    ext S; simp
  rw [this]
  simp only [coeffZ_eq]
  rw [mobius T (fun B => p (ind B)), ← hx]

/-- ANF degree at most `d` implies vanishing `(d+1)`-fold differences -/
theorem degLe_of_coeffZ {d : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (h : ∀ S : Finset (Fin n), d < S.card → coeffZ p S = 0) : DegLe d p := by
  have hp : p = fun x => ∑ S, coeffZ p S * mon S x := funext (inversion p)
  rw [hp]
  apply degLe_sum
  intro S _
  by_cases hS : d < S.card
  · simp only [h S hS, zero_mul]; exact degLe_zerofun d
  · exact degLe_smul _ (degLe_mono (by omega) (degLe_mon S))

end P2MANF

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

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

private def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

private def IsSymmetric {F : Type} {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) x, T (x ∘ σ) = T x

private def IsAlternating {F : Type} [Zero F] {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ x i j, i ≠ j → x i = x j → T x = 0



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


private lemma dl_dl_self {n : ℕ} (u : Vec n (ZMod 2)) (q : Vec n (ZMod 2) → ZMod 2) :
    P2MDiff.dl u (P2MDiff.dl u q) = fun _ => 0 := by
  funext x
  simp only [P2MDiff.dl, add_assoc, P2MFourier.pself, add_zero]
  have h := CharTwo.add_self_eq_zero (q (x + u))
  have h' := CharTwo.add_self_eq_zero (q x)
  linear_combination h + h'

private lemma diffs_rep {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (h : Fin (k+2) → Vec n (ZMod 2))
    (h01 : h 0 = h 1) (x : Vec n (ZMod 2)) : P2MDiff.diffs p h x = 0 := by
  rw [P2MDiff.diffs_succ, P2MDiff.diffs_succ]
  have : Fin.tail h 0 = h 0 := by show h 1 = h 0; exact h01.symm
  rw [this, dl_dl_self, P2MDiff.diffs_closed]
  simp

private lemma coeff_eq_top {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (ind : Fin d → Fin n)
    (hind : Function.Injective ind) :
    P2MDiff.diffs p (fun i => Pi.single (ind i) 1) 0 = coefficient p (Finset.univ.image ind) := by
  classical
  rw [show coefficient p (Finset.univ.image ind) = P2MANF.coeffZ p (Finset.univ.image ind) from rfl,
    P2MANF.coeffZ_eq, P2MDiff.diffs_closed]
  simp only [zero_add]
  refine Finset.sum_nbij' (fun ε => (Finset.univ.filter fun l => ε l = 1).image ind)
    (fun B l => if ind l ∈ B then 1 else 0) ?_ ?_ ?_ ?_ ?_
  · intro ε _
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  · intro B _; simp
  · intro ε _
    funext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    by_cases hl : ε l = 1
    · rw [if_pos ⟨l, hl, rfl⟩, hl]
    · rw [if_neg]
      · rcases h01 (ε l) with h | h
        · exact h.symm
        · exact absurd h hl
      · rintro ⟨l', hl', he⟩
        exact hl (hind he ▸ hl')
  · intro B hB
    simp only [Finset.mem_coe, Finset.mem_powerset] at hB
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left_iff,
      zero_ne_one, imp_false, not_not]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro hv
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp (hB hv)
      exact ⟨l, hv, rfl⟩
  · intro ε _
    congr 1
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, P2MANF.ind, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : ∃ l, ε l = 1 ∧ ind l = v
    · obtain ⟨l, hl, rfl⟩ := hv
      rw [if_pos ⟨l, hl, rfl⟩, Finset.sum_eq_single l]
      · simp [hl]
      · intro b _ hb; rw [if_neg (fun h => hb (hind h.symm))]
      · simp
    · rw [if_neg hv]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs with h
      · have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases h01 (ε l) with h' | h'
        · exact h'
        · exact absurd ⟨l, h', h.symm⟩ hv
      · rfl

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 2 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 1 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    (∀ h x, differences p h x = topForm p d h) ∧
    (∃ h, topForm p d h ≠ 0) ∧
    IsSymmetric (topForm p d) ∧ IsMultilinear (topForm p d) ∧
    IsAlternating (topForm p d) ∧
    (∀ (indices : Fin d → Fin n), Function.Injective indices →
      topForm p d (fun i => Pi.single (indices i) 1) =
        coefficient p (Finset.univ.image indices)) := by
  classical
  have hdeg := degLe_of_anf p hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    exact P2MDiff.diffs_const hdeg h x
  · obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Fin n)))
      Finset.univ_nonempty (fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ))
    have h1 : anfDegree p = if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ) := hS
    rw [hp] at h1
    split_ifs at h1 with hc
    · exact absurd h1 (WithBot.natCast_ne_bot d)
    · have hcard : S.card = d := by exact_mod_cast h1.symm
      let e := S.equivFin
      let ind : Fin d → Fin n := fun i => (e.symm (Fin.cast hcard.symm i) : Fin n)
      have hind : Function.Injective ind := by
        intro a b hab
        have := Subtype.ext hab
        have := e.symm.injective this
        exact Fin.cast_injective _ this
      have himg : Finset.univ.image ind = S := by
        ext v; constructor
        · intro hv; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv; exact (e.symm _).2
        · intro hv
          refine Finset.mem_image.mpr ⟨Fin.cast hcard (e ⟨v, hv⟩), Finset.mem_univ _, ?_⟩
          simp [ind]
      refine ⟨fun i => Pi.single (ind i) 1, ?_⟩
      show P2MDiff.diffs p _ 0 ≠ 0
      rw [coeff_eq_top p ind hind, himg]
      exact hc
  · intro σ x
    exact congrFun (P2MDiff.diffs_perm p x σ) 0
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    refine ⟨?_, ?_⟩
    · intro x i u v
      show P2MDiff.diffs p _ 0 = P2MDiff.diffs p _ 0 + P2MDiff.diffs p _ 0
      rw [P2MDiff.top_eq_tensorEval _ p hdeg, P2MDiff.top_eq_tensorEval _ p hdeg,
        P2MDiff.top_eq_tensorEval _ p hdeg]
      exact L37aux.ev_update_add _ x i u v
    · intro x i c u
      show P2MDiff.diffs p _ 0 = c * P2MDiff.diffs p _ 0
      rw [P2MDiff.top_eq_tensorEval _ p hdeg, P2MDiff.top_eq_tensorEval _ p hdeg]
      exact L37aux.ev_update_smul _ x i c u
  · intro x i j hij hx
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by
      have := i.isLt; have := j.isLt
      rcases Nat.lt_or_ge d 2 with h | h
      · interval_cases d <;> simp_all [Fin.ext_iff] <;> omega
      · omega⟩
    let τ1 := Equiv.swap (0 : Fin (k+2)) i
    let τ2 := Equiv.swap (1 : Fin (k+2)) (τ1 j)
    let σ := τ1 * τ2
    have hτ1j : τ1 j ≠ 0 := by
      intro h
      apply hij
      have : j = τ1 0 := by rw [← h, Equiv.swap_apply_self]
      rw [this, Equiv.swap_apply_left]
    have hσ0 : σ 0 = i := by
      show τ1 (τ2 0) = i
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (Ne.symm hτ1j), Equiv.swap_apply_left]
    have hσ1 : σ 1 = j := by
      show τ1 (τ2 1) = j
      rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
    show P2MDiff.diffs p x 0 = 0
    rw [← P2MDiff.diffs_perm p x σ]
    apply diffs_rep
    simp only [Function.comp, hσ0, hσ1, hx]
  · intro indices hinj
    exact coeff_eq_top p indices hinj



