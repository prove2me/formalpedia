-- Prove2me | solution 1 for ParityDegreeDepth.Main.Ctx.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:25:27.527738+00:00
-- url     : https://prove2.me/submissions/05ca48d8-f0b8-4652-a98d-389e383a8a2f

import Mathlib
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Main_Context
import Definitions.Def_ParityDegreeDepth_Main_Supplement_ThresholdWeight

-- ===== T35a =====
section

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

end

-- ===== T35b =====
section

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

end

-- ===== T35c =====
section

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

end

-- ===== T35d =====
section

open MvPolynomial ParityDegreeDepth.Core Matrix

namespace T35aux

noncomputable section

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2)

abbrev PP (m n : ℕ) := MvPolynomial (Fin (m+1) × Fin n) (ZMod 2)
abbrev QQ (m n : ℕ) := MvPolynomial (Fin (m+1)) (PP m n)

def tv : Fin (m+1) → Fin n → PP m n := fun l v => X (l, v)
def AA : Matrix (Fin n) (Fin n) (PP m n) := Matrix.of fun i j => con c tv (ee i) (ee j)
def pert (w : Fin (m+1) → Fin n → PP m n) : Fin (m+1) → Fin n → QQ m n :=
  fun l v => C (X (l, v)) + X l * C (w l v)
def bsel (w : Fin (m+1) → Fin n → PP m n) (J : Finset (Fin (m+1))) :
    Fin (m+1) → Fin n → PP m n := fun l => if l ∈ J then w l else tv l
def cv (x : Fin n → PP m n) : Fin n → QQ m n := fun v => C (x v)

lemma bsel_empty (w : Fin (m+1) → Fin n → PP m n) : bsel w ∅ = tv := by
  funext l; simp [bsel]

lemma coeff_pert (w : Fin (m+1) → Fin n → PP m n) (J : Finset (Fin (m+1)))
    (x y : Fin n → PP m n) :
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

def phiw (w : Fin (m+1) → Fin n → PP m n) : PP m n →ₐ[ZMod 2] QQ m n :=
  aeval fun p : Fin (m+1) × Fin n => C (X p) + X p.1 * C (w p.1 p.2)

lemma con_map {S T : Type*} [CommRing S] [Algebra (ZMod 2) S] [CommRing T] [Algebra (ZMod 2) T]
    (φ : S →ₐ[ZMod 2] T) (w : Fin (m+1) → Fin n → S) (x y : Fin n → S) :
    φ (con c w x y) = con c (fun l v => φ (w l v)) (fun v => φ (x v)) (fun v => φ (y v)) := by
  unfold con
  rw [ev_map]
  congr 1
  funext j v
  refine Fin.addCases (fun l => ?_) (fun t => ?_) j
  · simp [Fin.append_left]
  · fin_cases t <;> simp [Fin.append_right]

lemma ee_cv (i : Fin n) : (ee i : Fin n → QQ m n) = cv (ee i) := by
  funext v; by_cases h : v = i
  · subst h; simp [ee, cv]
  · simp [ee, cv, Pi.single_apply, h]

lemma phiw_ee (w : Fin (m+1) → Fin n → PP m n) (i : Fin n) :
    (fun v => phiw w ((ee i : Fin n → PP m n) v)) = ee i := by
  funext v; by_cases h : v = i
  · subst h; simp [ee]
  · simp [ee, Pi.single_apply, h]

lemma phiw_tv (w : Fin (m+1) → Fin n → PP m n) :
    (fun l v => phiw w (tv l v)) = pert w := by
  funext l v; simp [phiw, tv, pert]

lemma map_AA (w : Fin (m+1) → Fin n → PP m n) :
    (AA c).map (phiw w) = Matrix.of fun i j => con c (pert w) (ee i) (ee j) := by
  ext i j
  simp only [AA, Matrix.map_apply, Matrix.of_apply]
  rw [con_map, phiw_ee, phiw_ee, phiw_tv]

lemma constantCoeff_phiw (w : Fin (m+1) → Fin n → PP m n) (p : PP m n) :
    constantCoeff (phiw w p) = p := by
  have : (constantCoeff : QQ m n →+* PP m n).comp (phiw w).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [phiw, MvPolynomial.algebraMap_apply]
    · intro p; simp [phiw]
  exact congrArg (fun f => f p) this

def InKer (u : Fin n → PP m n) : Prop := ∀ i, con c tv (ee i) u = 0

def AtMostOne (w : Fin (m+1) → Fin n → PP m n) (I : Finset (Fin (m+1))) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ¬ InKer c (w i) → ¬ InKer c (w j) → i = j

variable (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a)

lemma con_tv_left (u : Fin n → PP m n) (hu : InKer c u) (v : Fin n → PP m n) :
    con c tv v u = 0 := by
  rw [con_bilin]
  simp only [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mulVec_con, hu i, mul_zero]

include hc in
lemma con_tv_right (u : Fin n → PP m n) (hu : InKer c u) (v : Fin n → PP m n) :
    con c tv u v = 0 := by
  rw [con_symm c hc]; exact con_tv_left c u hu v

lemma rank_map_le {R : ℕ}
    (hrank : ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).rank ≤ R)
    (w : Fin (m+1) → Fin n → PP m n) :
    (((AA c).map (phiw w)).map (algebraMap (QQ m n) (FractionRing (QQ m n)))).rank ≤ R := by
  apply rank_le_of_minors
  intro r c'
  rw [show ((AA c).map (phiw w)).submatrix r c' = ((AA c).submatrix r c').map (phiw w) from rfl]
  rw [show (((AA c).submatrix r c').map (phiw w)).det =
    (((AA c).submatrix r c').map (phiw w).toRingHom).det from rfl, det_map_hom,
    minors_zero_of_rank_le (AA c) hrank r c', map_zero]

include hc in
theorem claims {R : ℕ}
    (hrank : ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).rank ≤ R)
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
      rw [show (constantCoeff : QQ m n →+* PP m n) (M.submatrix r c').det =
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

end T35aux

end

-- ===== T35e =====
section

open MvPolynomial ParityDegreeDepth.Core Matrix

namespace T35aux

noncomputable section

variable {n m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2)

lemma mulVec_ee (M : Matrix (Fin n) (Fin n) (PP m n)) (i k : Fin n) :
    (M *ᵥ (ee k : Fin n → PP m n)) i = M i k := by
  simp [ee, mulVec, dotProduct, Pi.single_apply]

lemma AA_mulVec (y : Fin n → PP m n) (i : Fin n) : (AA c *ᵥ y) i = con c tv (ee i) y := by
  rw [AA, mulVec_con]

theorem main_T35 (hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a) :
    ∃ (r : ℕ) (Λ : Matrix (Fin n) (Fin r) (PP m n)),
      r + ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).rank = n ∧
      (∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) ∧
      ∀ x : Fin (m+1+2) → Fin n → PP m n, (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ i l) →
        tensorEval c x = 0 := by
  classical
  set R := ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).rank with hR
  obtain ⟨I0, I0', hmin⟩ := exists_minor_of_le_rank
    ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))) (k := R) le_rfl
  have hδ : ((AA c).submatrix I0 I0').det ≠ 0 := by
    intro h; apply hmin
    rw [show ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).submatrix I0 I0' =
      ((AA c).submatrix I0 I0').map (algebraMap (PP m n) (FractionRing (PP m n))) from rfl,
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
  let β : Fin r → Fin R → PP m n := fun j b => AA c (I0 b) (J' j)
  let col : Fin r → Fin n → PP m n := fun j =>
    δ • (ee (J' j) : Fin n → PP m n) - ∑ a, (P0.adjugate *ᵥ β j) a • (ee (I0' a) : Fin n → PP m n)
  have hrank : ((AA c).map (algebraMap (PP m n) (FractionRing (PP m n)))).rank ≤ R := le_rfl
  have hker : ∀ j, InKer c (col j) := by
    intro j i
    rw [← AA_mulVec]
    simp only [col, mulVec_sub, mulVec_smul, mulVec_sum, Pi.sub_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, mulVec_ee]
    have key := bordered_identity (AA c) hrank I0 I0' hδ (ee i) (ee (J' j))
    have e1 : (ee i : Fin n → PP m n) ⬝ᵥ (AA c *ᵥ ee (J' j)) = AA c i (J' j) := by
      simp [ee, dotProduct, mulVec, Pi.single_apply]
    have e2 : ∀ k, ((ee i : Fin n → PP m n) ᵥ* AA c) k = AA c i k := by
      intro k; simp [ee, vecMul, dotProduct, Pi.single_apply]
    rw [e1] at key
    simp only [e2, mulVec_ee] at key
    rw [← hδdef, ← hP0] at key
    rw [key]
    simp only [dotProduct, β]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  let Λ : Matrix (Fin n) (Fin r) (PP m n) := Matrix.of fun v j => col j v
  refine ⟨r, Λ, by rw [hR] at hcard; exact hcard, ⟨J', ?_⟩, ?_⟩
  · have hsub : Λ.submatrix J' id = δ • (1 : Matrix (Fin r) (Fin r) (PP m n)) := by
      ext j' j
      simp only [Λ, col, Matrix.submatrix_apply, Matrix.of_apply, id, Pi.sub_apply,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
      have hz : ∀ a, (ee (I0' a) : Fin n → PP m n) (J' j') = 0 := by
        intro a; simp [ee, Pi.single_apply, hJ'ne j' a]
      simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero]
      by_cases hjj : j' = j
      · subst hjj; simp [ee]
      · have : J' j' ≠ J' j := fun h => hjj (hJ'inj h)
        simp [ee, Pi.single_apply, this, hjj]
    rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hδ
  · intro x hx
    let w : Fin (m+1) → Fin n → PP m n := fun l => x (Fin.castAdd 2 l)
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

end T35aux


end

-- ===== L37 =====
section

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

end

-- ===== L37b =====
section

open ParityDegreeDepth.Core Matrix

namespace L37aux

noncomputable section

open T35aux

variable {d n : ℕ} (c : (Fin (d+1) → Fin n) → ZMod 2)

lemma mul_adj_eq_det_update {R : Type*} [CommRing R] {r : ℕ}
    (Λ : Matrix (Fin n) (Fin r) R) (ρ : Fin r → Fin n) (i : Fin n) (k : Fin r) :
    (Λ * (Λ.submatrix ρ id).adjugate) i k = (Λ.submatrix (Function.update ρ k i) id).det := by
  classical
  have h1 : (Λ * (Λ.submatrix ρ id).adjugate) i k =
      ((Λ.submatrix ρ id)ᵀ.adjugate *ᵥ (fun j => Λ i j)) k := by
    rw [← Matrix.adjugate_transpose]
    simp [Matrix.mul_apply, mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply, ← Matrix.det_transpose]
  congr 1
  ext a b
  by_cases hak : a = k
  · subst hak; simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, hak, Function.update_of_ne hak]

theorem step {D : Type*} [CommRing D] [IsDomain D] [Algebra (ZMod 2) D] {r : ℕ}
    (Λ : Matrix (Fin n) (Fin r) (Polynomial D))
    (hΛ : ∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) (hv : SV c Λ) :
    ∃ Λ0 : Matrix (Fin n) (Fin r) D, (∃ ρ : Fin r → Fin n, (Λ0.submatrix ρ id).det ≠ 0) ∧
      SV c Λ0 := by
  classical
  have hne : (Finset.univ.filter fun ρ : Fin r → Fin n => (Λ.submatrix ρ id).det ≠ 0).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hΛ
    exact ⟨ρ, by simp [hρ]⟩
  obtain ⟨ρ, hρmem, hρmin⟩ := Finset.exists_min_image _
    (fun ρ : Fin r → Fin n => ((Λ.submatrix ρ id).det).natTrailingDegree) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρmem hρmin
  set δ := (Λ.submatrix ρ id).det with hδ
  set v := δ.natTrailingDegree with hv'
  set W := Λ * (Λ.submatrix ρ id).adjugate with hW
  have hdvd : ∀ i k, (Polynomial.X : Polynomial D) ^ v ∣ W i k := by
    intro i k
    rw [hW, mul_adj_eq_det_update]
    by_cases h0 : (Λ.submatrix (Function.update ρ k i) id).det = 0
    · rw [h0]; exact dvd_zero _
    · rw [Polynomial.X_pow_dvd_iff]
      intro e he
      apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      exact lt_of_lt_of_le he (hρmin _ h0)
  choose W' hW' using hdvd
  have hWeq : W = (Polynomial.X : Polynomial D) ^ v • (Matrix.of W') := by
    ext i k; simp [hW']
  have hsvW : SV c W := sv_mul c Λ _ hv
  have hXv : (Polynomial.X : Polynomial D) ^ v ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hsvW' : SV c (Matrix.of W') := sv_smul c _ _ hXv (by rw [← hWeq]; exact hsvW)
  let ev0 : Polynomial D →ₐ[ZMod 2] D := (Polynomial.aeval (0 : D)).restrictScalars (ZMod 2)
  have hev0 : Function.Surjective ev0 := by
    intro a; exact ⟨Polynomial.C a, by simp [ev0]⟩
  refine ⟨(Matrix.of W').map ev0, ?_, sv_map c ev0 hev0 _ hsvW'⟩
  -- the minor at ρ
  have hδdvd : (Polynomial.X : Polynomial D) ^ v ∣ δ := by
    rw [Polynomial.X_pow_dvd_iff]
    intro e he
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree he
  obtain ⟨q, hq⟩ := hδdvd
  have hq0 : q.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    have : δ.coeff v = q.coeff 0 := by
      rw [hq, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [← this, hv']
    exact mt Polynomial.trailingCoeff_eq_zero.mp hρmem
  refine ⟨ρ, ?_⟩
  have hrow : ∀ k' k, W (ρ k') k = δ * (1 : Matrix (Fin r) (Fin r) (Polynomial D)) k' k := by
    intro k' k
    have : W (ρ k') k = ((Λ.submatrix ρ id) * (Λ.submatrix ρ id).adjugate) k' k := by
      simp [hW, Matrix.mul_apply]
    rw [this, Matrix.mul_adjugate, Matrix.smul_apply, smul_eq_mul]
  have hsub : ((Matrix.of W').map ev0).submatrix ρ id =
      q.eval 0 • (1 : Matrix (Fin r) (Fin r) D) := by
    ext k' k
    have h1 := hrow k' k
    rw [hW' (ρ k') k, hq, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hXv h1
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, id, h2,
      Matrix.smul_apply, smul_eq_mul]
    by_cases hkk : k' = k
    · subst hkk; simp [ev0]
    · simp [ev0, Matrix.one_apply_ne hkk]
  rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ hq0

theorem descent_fin (L : ℕ) : ∀ {r : ℕ} (Λ : Matrix (Fin n) (Fin r) (MvPolynomial (Fin L) (ZMod 2))),
    (∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) → SV c Λ →
    ∃ Λ0 : Matrix (Fin n) (Fin r) (ZMod 2), (∃ ρ : Fin r → Fin n, (Λ0.submatrix ρ id).det ≠ 0) ∧
      SV c Λ0 := by
  induction L with
  | zero =>
    intro r Λ hΛ hv
    let φ := MvPolynomial.isEmptyAlgEquiv (ZMod 2) (Fin 0)
    refine ⟨Λ.map φ, ?_, sv_map c φ.toAlgHom φ.surjective Λ hv⟩
    obtain ⟨ρ, hρ⟩ := hΛ
    refine ⟨ρ, ?_⟩
    rw [show (Λ.map φ).submatrix ρ id = (Λ.submatrix ρ id).map (φ : MvPolynomial (Fin 0) (ZMod 2) →+* ZMod 2)
      from rfl, det_map_hom]
    exact (map_ne_zero_iff _ φ.injective).mpr hρ
  | succ L ih =>
    intro r Λ hΛ hv
    let ψ := MvPolynomial.finSuccEquiv (ZMod 2) L
    have hΛ' : ∃ ρ : Fin r → Fin n, ((Λ.map ψ).submatrix ρ id).det ≠ 0 := by
      obtain ⟨ρ, hρ⟩ := hΛ
      refine ⟨ρ, ?_⟩
      rw [show (Λ.map ψ).submatrix ρ id = (Λ.submatrix ρ id).map
        (ψ : MvPolynomial (Fin (L+1)) (ZMod 2) →+* Polynomial (MvPolynomial (Fin L) (ZMod 2)))
        from rfl, det_map_hom]
      exact (map_ne_zero_iff _ ψ.injective).mpr hρ
    obtain ⟨Λ1, h1, h2⟩ := step c (Λ.map ψ) hΛ' (sv_map c ψ.toAlgHom ψ.surjective Λ hv)
    exact ih Λ1 h1 h2

theorem descent {σ : Type*} [Fintype σ] {r : ℕ}
    (Λ : Matrix (Fin n) (Fin r) (MvPolynomial σ (ZMod 2)))
    (hΛ : ∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) (hv : SV c Λ) :
    ∃ Λ0 : Matrix (Fin n) (Fin r) (ZMod 2), (∃ ρ : Fin r → Fin n, (Λ0.submatrix ρ id).det ≠ 0) ∧
      SV c Λ0 := by
  let e := MvPolynomial.renameEquiv (ZMod 2) (Fintype.equivFin σ)
  apply descent_fin c (Fintype.card σ) (Λ.map e)
  · obtain ⟨ρ, hρ⟩ := hΛ
    refine ⟨ρ, ?_⟩
    rw [show (Λ.map e).submatrix ρ id = (Λ.submatrix ρ id).map
      (e : MvPolynomial σ (ZMod 2) →+* MvPolynomial (Fin (Fintype.card σ)) (ZMod 2)) from rfl,
      det_map_hom]
    exact (map_ne_zero_iff _ e.injective).mpr hρ
  · exact sv_map c e.toAlgHom e.surjective Λ hv

end

end L37aux

end

-- ===== GridSZ =====
section

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

end

-- ===== L33a =====
section

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

end

-- ===== L33b =====
section

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

end

-- ===== L33c =====
section

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

end

-- ===== L33d =====
section

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

end

-- ===== Four =====
section

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

end

-- ===== Four2 =====
section

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MFourier

variable {n : ℕ}

lemma parseval (f : (Fin n → ZMod 2) → ℝ) :
    ∑ ξ, QAlgorithms.boolFourier f ξ ^ 2 = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x ^ 2 := by
  calc ∑ ξ, QAlgorithms.boolFourier f ξ ^ 2
      = ∑ ξ, QAlgorithms.boolFourier f ξ * (((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * sg (ξ ⬝ᵥ x)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [sq]; congr 1
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ξ _ => ?_
        ring
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← fourier_inversion f x, sq]

lemma fourier_char (η ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => sg (η ⬝ᵥ y)) ζ = if η = ζ then 1 else 0 := by
  rw [boolFourier_eq]
  have : ∀ y : Fin n → ZMod 2, sg (η ⬝ᵥ y) * sg (ζ ⬝ᵥ y) = sg ((η + ζ) ⬝ᵥ y) := by
    intro y; rw [dot_add_left, sg_add]
  simp only [this, sum_sg_dot]
  by_cases h : η = ζ
  · subst h; simp [pself]
  · have : η + ζ ≠ 0 := fun h' => h (eq_of_add_eq_zero' h')
    simp [this, h]

lemma fourier_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ZMod 2) → ℝ) (ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => ∑ i ∈ s, g i y) ζ = ∑ i ∈ s, QAlgorithms.boolFourier (g i) ζ := by
  simp only [boolFourier_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma fourier_const_mul (c : ℝ) (g : (Fin n → ZMod 2) → ℝ) (ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => c * g y) ζ = c * QAlgorithms.boolFourier g ζ := by
  simp only [boolFourier_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => by ring

/-- restriction to an affine subspace (image of an affine map) does not increase the spectral norm -/
theorem l1_affine {m : ℕ} (f : (Fin n → ZMod 2) → ℝ)
    (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    l1 (fun y => f (a + B y)) ≤ l1 f := by
  classical
  let Bt : (Fin n → ZMod 2) → (Fin m → ZMod 2) := fun ξ => ξ ᵥ* LinearMap.toMatrix' B
  have hBt : ∀ ξ y, ξ ⬝ᵥ B y = Bt ξ ⬝ᵥ y := by
    intro ξ y
    rw [← LinearMap.toMatrix'_mulVec B y, Matrix.dotProduct_mulVec]
  have hexp : (fun y => f (a + B y)) = fun y => ∑ ξ, (QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a)) *
      sg (Bt ξ ⬝ᵥ y) := by
    funext y
    rw [fourier_inversion f (a + B y)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [dot_add_right, sg_add, hBt]; ring
  have hF : ∀ ζ, QAlgorithms.boolFourier (fun y => f (a + B y)) ζ =
      ∑ ξ, (QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a)) * (if Bt ξ = ζ then 1 else 0) := by
    intro ζ
    rw [hexp, fourier_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [fourier_const_mul, fourier_char]
  unfold l1
  simp only [hF]
  calc ∑ ζ, |∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a) * (if Bt ξ = ζ then (1:ℝ) else 0)|
      ≤ ∑ ζ, ∑ ξ, |QAlgorithms.boolFourier f ξ| * (if Bt ξ = ζ then (1:ℝ) else 0) := by
        refine Finset.sum_le_sum fun ζ _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [abs_mul, abs_mul, abs_sg, mul_one]
        split_ifs <;> simp
    _ = ∑ ξ, |QAlgorithms.boolFourier f ξ| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← Finset.mul_sum]
        simp

/-- the sign function of `p` -/
def phase (p : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ℝ := fun x => sg (p x)

lemma phase_sq (p : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) : phase p x ^ 2 = 1 := by
  unfold phase; rw [sq, sg_mul_self]

lemma parseval_phase (p : (Fin n → ZMod 2) → ZMod 2) :
    ∑ ξ, QAlgorithms.boolFourier (phase p) ξ ^ 2 = 1 := by
  rw [parseval]; simp [phase_sq, Finset.card_univ, ZMod.card]

lemma one_le_l1_phase (p : (Fin n → ZMod 2) → ZMod 2) : 1 ≤ l1 (phase p) := by
  have h := fourier_inversion (phase p) 0
  have h0 : |phase p 0| = 1 := abs_sg _
  rw [← h0, h]
  unfold l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [abs_mul, abs_sg, mul_one]

def sparsity' (f : (Fin n → ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

lemma sum_eq_sum_filter_ne (F g : (Fin n → ZMod 2) → ℝ) (hg : ∀ ξ, F ξ = 0 → g ξ = 0) :
    ∑ ξ, g ξ = ∑ ξ ∈ Finset.univ.filter (fun a => F a ≠ 0), g ξ := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  split_ifs with h
  · rfl
  · exact hg ξ (not_not.mp h)

lemma l1_sq_le_sparsity (p : (Fin n → ZMod 2) → ZMod 2) :
    l1 (phase p) ^ 2 ≤ sparsity' (phase p) := by
  classical
  have h1 : l1 (phase p) = ∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
      |QAlgorithms.boolFourier (phase p) ξ| * 1 := by
    unfold l1
    rw [sum_eq_sum_filter_ne (QAlgorithms.boolFourier (phase p)) _ (fun ξ h => by simp [h])]
    simp
  rw [h1]
  calc (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
        |QAlgorithms.boolFourier (phase p) ξ| * 1) ^ 2
      ≤ (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
          |QAlgorithms.boolFourier (phase p) ξ| ^ 2) *
        (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0), (1:ℝ) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ 1 * (Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0)).card := by
        apply mul_le_mul _ (by simp) (by positivity) (by norm_num)
        rw [← parseval_phase p]
        rw [sum_eq_sum_filter_ne (QAlgorithms.boolFourier (phase p))
          (fun ξ => QAlgorithms.boolFourier (phase p) ξ ^ 2) (fun ξ h => by simp [h])]
        exact le_of_eq (Finset.sum_congr rfl fun ξ _ => by rw [sq_abs])
    _ = sparsity' (phase p) := by simp [sparsity']

/-- a phase with at most one nonzero Fourier coefficient is affine -/
lemma affine_of_sparsity_le_one (p : (Fin n → ZMod 2) → ZMod 2) (h : sparsity' (phase p) ≤ 1) :
    ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0 := by
  classical
  have hsupp : ∃ ξ0, ∀ ξ, ξ ≠ ξ0 → QAlgorithms.boolFourier (phase p) ξ = 0 := by
    by_cases he : (Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0) = ∅
    · refine ⟨0, fun ξ _ => ?_⟩
      by_contra hne
      have : ξ ∈ Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0 := by simp [hne]
      rw [he] at this; simp at this
    · obtain ⟨ξ0, hξ0⟩ := Finset.nonempty_iff_ne_empty.mpr he
      refine ⟨ξ0, fun ξ hξ => ?_⟩
      by_contra hne
      have h2 : ({ξ, ξ0} : Finset _) ⊆
          Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0 := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simp [hne]
        · rw [Finset.mem_singleton] at hy; subst hy; exact hξ0
      have := Finset.card_le_card h2
      rw [Finset.card_pair hξ] at this
      unfold sparsity' at h
      omega
  obtain ⟨ξ0, hξ0⟩ := hsupp
  have hval : ∀ x, phase p x = QAlgorithms.boolFourier (phase p) ξ0 * sg (ξ0 ⬝ᵥ x) := by
    intro x
    rw [fourier_inversion (phase p) x, Finset.sum_eq_single ξ0]
    · intro ξ _ hξ; rw [hξ0 ξ hξ, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hp : ∀ x, p x = p 0 + ξ0 ⬝ᵥ x := by
    intro x
    have h1 := hval x
    have h2 := hval 0
    simp only [dotProduct_zero, sg_zero, mul_one] at h2
    rw [← h2] at h1
    unfold phase at h1
    have h3 : sg (p x) = sg (p 0 + ξ0 ⬝ᵥ x) := by rw [sg_add]; exact h1
    have key : ∀ a b : ZMod 2, sg a = sg b → a = b := by
      intro a b hab
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
        first | rfl | (simp only [sg_zero, sg_one] at hab; norm_num at hab)
    exact key _ _ h3
  intro x u v
  rw [hp (x + u + v), hp (x + u), hp (x + v), hp x]
  simp only [dotProduct_add]
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  linear_combination 2 * h2 (p 0) + 2 * h2 (ξ0 ⬝ᵥ x) + h2 (ξ0 ⬝ᵥ u) + h2 (ξ0 ⬝ᵥ v)

end P2MFourier

end
end

-- ===== Diffs =====
section

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

end
end

-- ===== Diffs2 =====
section

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

end
end

-- ===== Qspec =====
section

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MQ

open P2MFourier P2MDiff

variable {n : ℕ}

/-- polar form -/
def pol (q : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) : ZMod 2 :=
  q (u + v) + q u + q v + q 0

def polM (q : (Fin n → ZMod 2) → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun a b => pol q (Pi.single a 1) (Pi.single b 1)

variable (q : (Fin n → ZMod 2) → ZMod 2)
  (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
    q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0)

include hq in
lemma pol_add_right (u v w : Fin n → ZMod 2) : pol q u (v + w) = pol q u v + pol q u w := by
  unfold pol
  have h := hq 0 u v w
  simp only [zero_add] at h
  have e : ∀ a b c d e f g h' : ZMod 2,
      a + b + c + d + e + f + g + h' = 0 → a + e + d + h' = (b + e + f + h') + (c + e + g + h') := by
    decide
  rw [show u + (v + w) = u + v + w by abel]
  exact e _ _ _ _ _ _ _ _ h

lemma pol_symm (u v : Fin n → ZMod 2) : pol q u v = pol q v u := by
  unfold pol; rw [add_comm u v]; ring

include hq in
lemma pol_bilin (u v : Fin n → ZMod 2) : pol q u v = u ⬝ᵥ (polM q *ᵥ v) := by
  have h1 : ∀ u, pol q u v = ∑ b, v b * pol q u (Pi.single b 1) := fun u =>
    additive_expand (fun v => pol q u v) (pol_add_right q hq u) v
  have h2 : ∀ b, pol q u (Pi.single b 1) = ∑ a, u a * pol q (Pi.single a 1) (Pi.single b 1) := by
    intro b
    rw [pol_symm]
    rw [additive_expand (fun u => pol q (Pi.single b 1) u) (pol_add_right q hq _) u]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pol_symm]
  rw [h1]
  simp only [h2, dotProduct, mulVec, polM, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- the radical -/
def radF (q : (Fin n → ZMod 2) → ZMod 2) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun h => polM q *ᵥ h = 0

include hq in
lemma fourier_sq (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (phase q) ξ ^ 2 =
      ((2 : ℝ) ^ n)⁻¹ * ∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) := by
  classical
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹
  have hterm : ∀ x h : Fin n → ZMod 2,
      (phase q x * sg (ξ ⬝ᵥ x)) * (phase q (x + h) * sg (ξ ⬝ᵥ (x + h))) =
        sg (ξ ⬝ᵥ h + q h + q 0) * sg ((polM q *ᵥ h) ⬝ᵥ x) := by
    intro x h
    unfold phase
    rw [← sg_add, ← sg_add, ← sg_add, ← sg_add]
    congr 1
    have hpol : (polM q *ᵥ h) ⬝ᵥ x = q (x + h) + q x + q h + q 0 := by
      rw [dotProduct_comm, ← pol_bilin q hq]; rfl
    rw [hpol, dot_add_right]
    linear_combination h2 (ξ ⬝ᵥ x) - h2 (q h) - h2 (q 0)
  calc QAlgorithms.boolFourier (phase q) ξ ^ 2
      = c * c * ∑ x, ∑ y, (phase q x * sg (ξ ⬝ᵥ x)) * (phase q y * sg (ξ ⬝ᵥ y)) := by
        rw [sq, boolFourier_eq, mul_mul_mul_comm, Finset.sum_mul_sum]
    _ = c * c * ∑ x, ∑ h, (phase q x * sg (ξ ⬝ᵥ x)) * (phase q (x + h) * sg (ξ ⬝ᵥ (x + h))) := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Equiv.sum_comp (Equiv.addLeft x)
          (fun y => (phase q x * sg (ξ ⬝ᵥ x)) * (phase q y * sg (ξ ⬝ᵥ y)))).symm
    _ = c * c * ∑ h, sg (ξ ⬝ᵥ h + q h + q 0) * ∑ x, sg ((polM q *ᵥ h) ⬝ᵥ x) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hterm x h
    _ = c * c * ∑ h, (if polM q *ᵥ h = 0 then sg (ξ ⬝ᵥ h + q h + q 0) * (2 : ℝ) ^ n else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [sum_sg_dot]
        split_ifs <;> simp
    _ = c * ∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) := by
        rw [radF, Finset.sum_filter]
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs
        · simp only [c]; field_simp
        · simp

lemma mem_radF (h : Fin n → ZMod 2) : h ∈ radF q ↔ polM q *ᵥ h = 0 := by
  simp [radF]

lemma radF_add {h h' : Fin n → ZMod 2} (hh : h ∈ radF q) (hh' : h' ∈ radF q) : h + h' ∈ radF q := by
  rw [mem_radF] at *
  rw [mulVec_add, hh, hh', add_zero]

include hq in
lemma char_sum_rad (ξ : Fin n → ZMod 2) :
    (∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) = 0) ∨
      (∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) = (radF q).card) := by
  classical
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  set ψ : (Fin n → ZMod 2) → ZMod 2 := fun h => ξ ⬝ᵥ h + q h + q 0
  have hadd : ∀ h ∈ radF q, ∀ h' ∈ radF q, ψ (h + h') = ψ h + ψ h' := by
    intro h hh h' hh'
    have hp : pol q h h' = 0 := by
      rw [pol_bilin q hq, (mem_radF q h').mp hh', dotProduct_zero]
    unfold pol at hp
    simp only [ψ, dot_add_right]
    linear_combination hp - h2 (q h) - h2 (q h') - h2 (q 0)
  by_cases hall : ∀ h ∈ radF q, ψ h = 0
  · right
    rw [Finset.sum_congr rfl (fun h hh => by rw [show ξ ⬝ᵥ h + q h + q 0 = ψ h from rfl, hall h hh])]
    simp [sg_zero]
  · left
    push Not at hall
    obtain ⟨h0, hh0, hψ⟩ := hall
    have hψ1 : ψ h0 = 1 := zmod2_eq_one _ hψ
    set S := ∑ h ∈ radF q, sg (ψ h)
    have hS : S = -S := by
      have : S = ∑ h ∈ radF q, sg (ψ (h + h0)) := by
        refine Finset.sum_nbij' (· + h0) (· + h0) ?_ ?_ ?_ ?_ ?_
        · intro h hh; exact radF_add q hh hh0
        · intro h hh; exact radF_add q hh hh0
        · intro h _; simp [add_assoc, pself]
        · intro h _; simp [add_assoc, pself]
        · intro h _; simp [add_assoc, pself]
      conv_lhs => rw [this]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hadd h hh h0 hh0, sg_add, hψ1, sg_one]; ring
    have : S = 0 := by linarith
    exact this

lemma card_radF : ((radF q).card : ℝ) * 2 ^ (polM q).rank = 2 ^ n := by
  classical
  have hk : (radF q).card = Fintype.card (LinearMap.ker (polM q).mulVecLin) := by
    rw [radF, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun h => by simp [LinearMap.mem_ker, Matrix.mulVecLin_apply])
  have hc : Fintype.card (LinearMap.ker (polM q).mulVecLin) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (polM q).mulVecLin) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]; simp [ZMod.card]
  have hr : (polM q).rank + Module.finrank (ZMod 2) (LinearMap.ker (polM q).mulVecLin) = n := by
    rw [Matrix.rank]
    rw [LinearMap.finrank_range_add_finrank_ker]
    simp
  rw [hk, hc]
  push_cast
  rw [← pow_add, add_comm, hr]

include hq in
theorem qspec : l1 (phase q) ^ 2 = 2 ^ (polM q).rank := by
  classical
  set F := QAlgorithms.boolFourier (phase q) with hF
  set C : ℝ := ((radF q).card : ℝ) with hC
  have hCpos : 0 < C := by
    have : (0 : Fin n → ZMod 2) ∈ radF q := by simp [radF]
    have := Finset.card_pos.mpr ⟨_, this⟩
    rw [hC]; exact_mod_cast this
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹ * C with hcdef
  have hcpos : 0 < c := by positivity
  have hsq : ∀ ξ, F ξ ^ 2 = 0 ∨ F ξ ^ 2 = c := by
    intro ξ
    rw [hF, fourier_sq q hq ξ]
    rcases char_sum_rad q hq ξ with h | h
    · left; rw [h, mul_zero]
    · right; rw [h]
  have hpars : ∑ ξ, F ξ ^ 2 = 1 := parseval_phase q
  set N : ℕ := (Finset.univ.filter fun ξ => F ξ ≠ 0).card with hN
  have hsum2 : ∑ ξ, F ξ ^ 2 = N * c := by
    rw [sum_eq_sum_filter_ne F (fun ξ => F ξ ^ 2) (fun ξ h => by simp [h])]
    rw [Finset.sum_congr rfl (fun ξ hξ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      rcases hsq ξ with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hξ
      · exact h)]
    simp [hN]
  have hsum1 : l1 (phase q) = N * Real.sqrt c := by
    unfold l1
    rw [← hF]
    rw [sum_eq_sum_filter_ne F (fun ξ => |F ξ|) (fun ξ h => by simp [h])]
    rw [Finset.sum_congr rfl (fun ξ hξ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      rcases hsq ξ with h | h
      · exact absurd ((pow_eq_zero_iff (two_ne_zero)).mp h) hξ
      · rw [← Real.sqrt_sq_eq_abs, h])]
    simp [hN]
  have hNc : (N : ℝ) * c = 1 := by rw [← hsum2, hpars]
  have hcard := card_radF q
  rw [hsum1, mul_pow, Real.sq_sqrt hcpos.le, sq, mul_assoc, hNc, mul_one]
  have hc2 : c * 2 ^ (polM q).rank = 1 := by
    rw [hcdef, mul_assoc, hcard]; field_simp
  calc (N : ℝ) = N * (c * 2 ^ (polM q).rank) := by rw [hc2, mul_one]
    _ = (N * c) * 2 ^ (polM q).rank := by ring
    _ = 2 ^ (polM q).rank := by rw [hNc, one_mul]

end P2MQ

end
end

-- ===== L32 =====
section

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MQ

open P2MFourier P2MDiff

variable {n : ℕ}

lemma diffs_append {k l : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (h' : Fin l → Fin n → ZMod 2) : diffs p (Fin.append h h') = diffs (diffs p h) h' := by
  unfold diffs
  rw [List.ofFn_fin_append, List.foldl_append]

lemma diffs_three (q : (Fin n → ZMod 2) → ZMod 2) (u v w x : Fin n → ZMod 2) :
    diffs q ![u, v, w] x = q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
  rw [show x + w + v + u = x + u + v + w by abel, show x + w + v = x + v + w by abel,
    show x + w + u = x + u + w by abel, show x + v + u = x + u + v by abel]
  ring

lemma diffs_two (q : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs q ![u, v] 0 = pol q u v := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, pol, zero_add]
  rw [show v + u = u + v by abel]
  ring

lemma phase_dl (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2) :
    phase (dl u p) = fun x => phase p (x + u) * phase p x := by
  funext x; simp [phase, dl, sg_add]

lemma l1_phase_diffs : ∀ (k : ℕ) (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2),
    l1 (phase (diffs p h)) ≤ l1 (phase p) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro p h; rw [diffs_zero]; simp
  | succ k ih =>
    intro p h
    rw [diffs_succ]
    refine (ih _ _).trans ?_
    have h1 : l1 (phase (dl (h 0) p)) ≤ l1 (phase p) ^ 2 := by
      rw [phase_dl]
      refine (l1_mul_le _ _).trans ?_
      rw [l1_translate (phase p) (h 0), sq]
    calc l1 (phase (dl (h 0) p)) ^ 2 ^ k ≤ (l1 (phase p) ^ 2) ^ 2 ^ k :=
          pow_le_pow_left₀ (l1_nonneg _) h1 _
      _ = l1 (phase p) ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ, mul_comm]

/-- Lemma 3.2: the binary contraction ranks of the top form are bounded by the spectral norm -/
theorem contraction_rank_bound {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (hp : DegLe (k+2) p)
    (h : Fin k → Fin n → ZMod 2) :
    ((Matrix.of fun a b : Fin n => diffs p (Fin.append h ![Pi.single a 1, Pi.single b 1]) 0).rank : ℝ)
      ≤ 2 ^ (k+1) * Real.logb 2 (l1 (phase p)) := by
  set q := diffs p h with hqdef
  have hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0 := by
    intro x u v w
    rw [← diffs_three, hqdef, ← diffs_append]
    exact hp _ x
  have hM : (Matrix.of fun a b : Fin n => diffs p (Fin.append h ![Pi.single a 1, Pi.single b 1]) 0)
      = polM q := by
    ext a b
    simp only [Matrix.of_apply, polM]
    rw [diffs_append, diffs_two]
  rw [hM]
  have hspec := qspec q hq
  have hl1 := l1_phase_diffs k p h
  have hpos : 0 < l1 (phase q) := lt_of_lt_of_le one_pos (one_le_l1_phase q)
  have hlog : ((polM q).rank : ℝ) = 2 * Real.logb 2 (l1 (phase q)) := by
    have := congrArg (Real.logb 2) hspec
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    push_cast at this
    linarith
  rw [hlog]
  have h2 : Real.logb 2 (l1 (phase q)) ≤ Real.logb 2 (l1 (phase p) ^ 2 ^ k) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hl1
  rw [Real.logb_pow] at h2
  push_cast at h2
  calc 2 * Real.logb 2 (l1 (phase q)) ≤ 2 * (2 ^ k * Real.logb 2 (l1 (phase p))) := by linarith
    _ = 2 ^ (k+1) * Real.logb 2 (l1 (phase p)) := by ring

end P2MQ

end
end

-- ===== K3 =====
section

open scoped BigOperators
open Matrix MvPolynomial ParityDegreeDepth.Core
noncomputable section

namespace P2MK3

open P2MFourier P2MDiff P2MQ

variable {n : ℕ}

lemma rk_field {m r : ℕ} (N : Matrix (Fin m) (Fin r) (ZMod 2)) : L33aux.rk N = N.rank := by
  apply le_antisymm
  · obtain ⟨r', c', h⟩ := T35aux.exists_minor_of_le_rank
      (N.map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))) (le_refl (L33aux.rk N))
    apply T35aux.le_rank_of_minor N r' c'
    intro h0; apply h
    rw [show (N.map (algebraMap (ZMod 2) (FractionRing (ZMod 2)))).submatrix r' c' =
      (N.submatrix r' c').map (algebraMap (ZMod 2) (FractionRing (ZMod 2))) from rfl,
      T35aux.det_map_hom, h0, map_zero]
  · obtain ⟨r', c', h⟩ := T35aux.exists_minor_of_le_rank N le_rfl
    exact T35aux.le_rank_of_minor' N r' c' h

/-- the generic contraction matrix in the block form used by Lemma 3.3 -/
lemma AA_eq_gen {m : ℕ} (c : (Fin (m+1+2) → Fin n) → ZMod 2) :
    T35aux.AA c = L33aux.gen (fun g : Fin (m+1) → Fin n =>
      Matrix.of fun i j => c (Fin.append g ![i, j])) := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [T35aux.AA, Matrix.of_apply, L33aux.gen, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul]
  rw [T35aux.con_explicit]
  rw [← Fintype.sum_equiv (Fin.appendEquiv (m+1) 2)
    (fun z => algebraMap (ZMod 2) (T35aux.PP m n) (c (Fin.append z.1 z.2)) *
      ((∏ l : Fin (m+1), T35aux.tv l ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) (Fin.castAdd 2 l))) *
        ((T35aux.ee i : Fin n → T35aux.PP m n) ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n)
          (Fin.natAdd (m+1) 0)) * (T35aux.ee j : Fin n → T35aux.PP m n)
          ((Fin.append z.1 z.2 : Fin (m+1+2) → Fin n) (Fin.natAdd (m+1) 1))))) _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Fin.append_left, Fin.append_right]
  rw [← Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n).symm
    (fun z => algebraMap (ZMod 2) (T35aux.PP m n) (c (Fin.append g ((piFinTwoEquiv fun _ => Fin n).symm z))) *
      ((∏ l : Fin (m+1), T35aux.tv l (g l)) *
        ((T35aux.ee i : Fin n → T35aux.PP m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 0) *
          (T35aux.ee j : Fin n → T35aux.PP m n) (((piFinTwoEquiv fun _ => Fin n).symm z) 1))))
    _ (fun z => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, T35aux.ee, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [Fin.cons_zero, Fin.cons_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [T35aux.tv, MvPolynomial.algebraMap_eq]
  rw [mul_comm]; rfl

lemma gen_map_eval {m r k : ℕ} (Ng : (Fin k → Fin n) → Matrix (Fin m) (Fin r) (ZMod 2))
    (a : Fin k × Fin n → ZMod 2) :
    (L33aux.gen Ng).map (MvPolynomial.aeval a : MvPolynomial (Fin k × Fin n) (ZMod 2) →ₐ[ZMod 2] ZMod 2)
      = L33aux.spec Ng a := by
  refine Matrix.ext fun i j => ?_
  simp [L33aux.gen, L33aux.spec, Matrix.sum_apply, map_sum, map_prod]

/-- eq. (7): for `deg p ≤ j`, `j ≥ 3`, the top form vanishes on a subspace of codimension
`≤ 2^{2j-3} log₂ ‖p̂‖₁` -/
theorem eq7 {j : ℕ} (hj : 3 ≤ j) (p : (Fin n → ZMod 2) → ZMod 2) (hp : DegLe j p) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin j → Fin n → ZMod 2, (∀ i, h i ∈ U) → diffs p h 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤ 2 ^ (2 * j - 3) * Real.logb 2 (l1 (phase p)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 + 2 := ⟨j - 3, by omega⟩
  set c := cT p (m+1+2) with hcdef
  have hc : ∀ (σ : Equiv.Perm (Fin (m+1+2))) a, c (a ∘ σ) = c a := cT_symm p _
  obtain ⟨r, Λ, hrR, hmin, hSV⟩ := T35aux.main_T35 c hc
  obtain ⟨Λ0, hmin0, hSV0⟩ := L37aux.descent c Λ hmin hSV
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
  · set R := ((T35aux.AA c).map (algebraMap (T35aux.PP m n)
      (FractionRing (T35aux.PP m n)))).rank with hRdef
    have hcod : (n : ℝ) - Module.finrank (ZMod 2) U = R := by
      rw [hfr]; have : (n : ℝ) = r + R := by exact_mod_cast hrR.symm
      linarith
    rw [hcod]
    let Ng : (Fin (m+1) → Fin n) → Matrix (Fin n) (Fin n) (ZMod 2) :=
      fun g => Matrix.of fun i j => c (Fin.append g ![i, j])
    obtain ⟨a, -, hblk⟩ := L33aux.blocks (m+1) (ZMod 2) n n Ng
    rw [← AA_eq_gen] at hblk
    let h : Fin (m+1) → Fin n → ZMod 2 := fun l v => a (l, v)
    have hspec : L33aux.spec Ng a =
        Matrix.of fun i j : Fin n => diffs p (Fin.append h ![Pi.single i 1, Pi.single j 1]) 0 := by
      rw [← gen_map_eval, ← AA_eq_gen]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, T35aux.AA, Matrix.of_apply]
      rw [T35aux.con_map, top_eq_tensorEval _ p hp]
      have e1 : (fun l v => (MvPolynomial.aeval a) (T35aux.tv l v)) = h := by
        funext l v; simp [T35aux.tv, h]
      have e2 : ∀ i, (fun v => (MvPolynomial.aeval a) ((T35aux.ee i : Fin n → T35aux.PP m n) v)) =
          (Pi.single i 1 : Fin n → ZMod 2) := by
        intro i; funext v; by_cases hv : v = i
        · subst hv; simp [T35aux.ee]
        · simp [T35aux.ee, Pi.single_apply, hv]
      rw [e1, e2, e2]
      rfl
    have hbin := contraction_rank_bound (k := m+1) p hp h
    rw [← hspec, ← rk_field] at hbin
    have hlog : 0 ≤ Real.logb 2 (l1 (phase p)) :=
      Real.logb_nonneg (by norm_num) (one_le_l1_phase p)
    have hR : (R : ℝ) ≤ 2 ^ (m+1) * (L33aux.rk (L33aux.spec Ng a) : ℝ) := by exact_mod_cast hblk
    calc (R : ℝ) ≤ 2 ^ (m+1) * (L33aux.rk (L33aux.spec Ng a) : ℝ) := hR
      _ ≤ 2 ^ (m+1) * (2 ^ (m+1+1) * Real.logb 2 (l1 (phase p))) := by gcongr
      _ = 2 ^ (2 * (m+1+2) - 3) * Real.logb 2 (l1 (phase p)) := by
        rw [show 2 * (m+1+2) - 3 = (m+1) + (m+1+1) by omega, pow_add]; ring

end P2MK3

end
end

-- ===== K2 =====
section

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MQ

open P2MFourier P2MDiff

variable {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2)
  (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
    q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0)

lemma pol_self (u : Fin n → ZMod 2) : pol q u u = 0 := by
  unfold pol
  rw [pself]
  have h2 : ∀ a b : ZMod 2, a + b + b + a = 0 := by decide
  exact h2 _ _

include hq in
theorem isotropic_codim :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2), (∀ u ∈ U, ∀ v ∈ U, pol q u v = 0) ∧
      2 * (n - Module.finrank (ZMod 2) U) ≤ (polM q).rank := by
  classical
  set Bf : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) := Matrix.toBilin' (polM q) with hBf
  have hB : ∀ u v, Bf u v = pol q u v := by
    intro u v
    rw [hBf, Matrix.toBilin'_apply', pol_bilin q hq]
  have hrefl : Bf.IsRefl := by
    intro u v h
    rw [hB] at h ⊢; rw [pol_symm]; exact h
  let Iso : Submodule (ZMod 2) (Fin n → ZMod 2) → Prop := fun U => ∀ u ∈ U, ∀ v ∈ U, pol q u v = 0
  let P : ℕ → Prop := fun k => ∃ U, Iso U ∧ Module.finrank (ZMod 2) U = k
  have hP0 : P 0 := by
    refine ⟨⊥, ?_, by simp⟩
    intro u hu v _
    rw [Submodule.mem_bot] at hu
    subst hu
    simp only [pol, zero_add]
    have h2 : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
    exact h2 _ _
  set k₀ := Nat.findGreatest P n
  obtain ⟨U, hUiso, hUk⟩ : P k₀ := Nat.findGreatest_spec (Nat.zero_le n) hP0
  have hmax : ∀ U', Iso U' → Module.finrank (ZMod 2) U' ≤ Module.finrank (ZMod 2) U := by
    intro U' hU'
    rw [hUk]
    apply Nat.le_findGreatest
    · calc Module.finrank (ZMod 2) U' ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) :=
            Submodule.finrank_le U'
        _ = n := by simp
    · exact ⟨U', hU', rfl⟩
  refine ⟨U, hUiso, ?_⟩
  -- the orthogonal of U is U
  have horth_le : Bf.orthogonal U ≤ U := by
    intro x hx
    by_contra hxU
    have hiso' : Iso (U ⊔ Submodule.span (ZMod 2) {x}) := by
      intro u hu v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      rw [← hB, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h1 : Bf a a' = 0 := by rw [hB]; exact hUiso a ha a' ha'
      have h2 : Bf a x = 0 := hx a ha
      have h3 : Bf x a' = 0 := by
        have := hx a' ha'
        rw [hB] at this ⊢; rw [pol_symm]; exact this
      have h4 : Bf x x = 0 := by rw [hB]; exact pol_self q x
      rw [h1, h2, h3, h4]; ring
    have hlt : U < U ⊔ Submodule.span (ZMod 2) {x} := by
      refine lt_of_le_of_ne le_sup_left fun h => hxU ?_
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    have := hmax _ hiso'
    omega
  have hle_orth : U ≤ Bf.orthogonal U := by
    intro x hx u hu
    show Bf u x = 0
    rw [hB]; exact hUiso u hu x hx
  have horth : Bf.orthogonal U = U := le_antisymm horth_le hle_orth
  have htop : Bf.orthogonal ⊤ = LinearMap.ker (polM q).mulVecLin := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_top, true_implies,
      LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext i
      have := h (Pi.single i 1)
      rw [hB, pol_bilin q hq] at this
      simpa [dotProduct, Pi.single_apply] using this
    · intro h y
      rw [hB, pol_bilin q hq, h, dotProduct_zero]
  have hrad_le : Bf.orthogonal ⊤ ≤ U := by
    rw [← horth]; exact LinearMap.BilinForm.orthogonal_le (le_top)
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl U
  rw [horth, inf_eq_right.mpr hrad_le, htop] at hdim
  have hr : (polM q).rank + Module.finrank (ZMod 2) (LinearMap.ker (polM q).mulVecLin) = n := by
    rw [Matrix.rank, LinearMap.finrank_range_add_finrank_ker]; simp
  simp only [Module.finrank_fin_fun] at hdim
  omega

end P2MQ

end
end

-- ===== ANF =====
section

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

end
end

-- ===== MainP =====
section

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

open Matrix

section trees

variable {n : ℕ}

lemma treeEval_query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (l r : ParityTree n)
    (x : Vec n (ZMod 2)) :
    treeEval (ParityTree.query a ha l r) x = if a ⬝ᵥ x = 0 then treeEval l x else treeEval r x := rfl

lemma treeDepth_query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (l r : ParityTree n) :
    treeDepth (ParityTree.query a ha l r) = 1 + max (treeDepth l) (treeDepth r) := rfl

/-- transport of a tree along an injective affine map -/
lemma transport {m : ℕ} (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hB : Function.Injective B) (a : Fin n → ZMod 2) :
    ∀ t : ParityTree m, ∃ t' : ParityTree n, treeDepth t' = treeDepth t ∧
      ∀ y, treeEval t' (a + B y) = treeEval t y := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective B (LinearMap.ker_eq_bot.mpr hB)
  intro t
  induction t with
  | leaf b => exact ⟨ParityTree.leaf b, rfl, fun y => rfl⟩
  | query b hb l r ihl ihr =>
    obtain ⟨l', hl'd, hl'⟩ := ihl
    obtain ⟨r', hr'd, hr'⟩ := ihr
    let c : Fin n → ZMod 2 := fun j => b ⬝ᵥ L (Pi.single j 1)
    have hc : ∀ x, c ⬝ᵥ x = b ⬝ᵥ L x := by
      intro x
      have hx : x = ∑ j, x j • (Pi.single j 1 : Fin n → ZMod 2) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hx]
      rw [map_sum, dotProduct_sum]
      simp only [map_smul, c, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hcB : ∀ y, c ⬝ᵥ B y = b ⬝ᵥ y := by
      intro y; rw [hc]
      have := congrArg (fun f => f y) hL
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this]
    have hc0 : c ≠ 0 := by
      intro h0
      apply hb
      funext i
      have := hcB (Pi.single i 1)
      rw [h0, zero_dotProduct] at this
      simpa [dotProduct_single] using this.symm
    by_cases hca : c ⬝ᵥ a = 0
    · refine ⟨ParityTree.query c hc0 l' r', ?_, ?_⟩
      · rw [treeDepth_query, treeDepth_query, hl'd, hr'd]
      · intro y
        rw [treeEval_query, treeEval_query, dotProduct_add, hca, zero_add, hcB, hl', hr']
    · have hca1 : c ⬝ᵥ a = 1 := P2MFourier.zmod2_eq_one _ hca
      refine ⟨ParityTree.query c hc0 r' l', ?_, ?_⟩
      · rw [treeDepth_query, treeDepth_query, hl'd, hr'd, max_comm]
      · intro y
        rw [treeEval_query, treeEval_query, dotProduct_add, hca1, hcB, hl', hr']
        have h01 : ∀ z : ZMod 2, (1 + z = 0) ↔ ¬ (z = 0) := by decide
        by_cases hz : b ⬝ᵥ y = 0
        · rw [if_neg ((h01 _).not.mpr (not_not.mpr hz)), if_pos hz]
        · rw [if_pos ((h01 _).mpr hz), if_neg hz]

/-- querying a list of parity checks, then using trees on the cells -/
lemma coset_tree (f : Vec n (ZMod 2) → ℝ) (D : ℕ) (tf : Vec n (ZMod 2) → ParityTree n) :
    ∀ (cs : List (Vec n (ZMod 2))) (S : Set (Vec n (ZMod 2))),
      (∀ a ∈ S, treeDepth (tf a) ≤ D ∧
        ∀ x ∈ S, (∀ c ∈ cs, c ⬝ᵥ x = c ⬝ᵥ a) → treeEval (tf a) x = f x) →
      ∃ t : ParityTree n, treeDepth t ≤ cs.length + D ∧ ∀ x ∈ S, treeEval t x = f x := by
  classical
  intro cs
  induction cs with
  | nil =>
    intro S hS
    by_cases hne : S.Nonempty
    · obtain ⟨a, ha⟩ := hne
      refine ⟨tf a, by simpa using (hS a ha).1, fun x hx => (hS a ha).2 x hx (by simp)⟩
    · refine ⟨ParityTree.leaf true, by simp [treeDepth], fun x hx => absurd ⟨x, hx⟩ hne⟩
  | cons c cs ih =>
    intro S hS
    by_cases hc : c = 0
    · obtain ⟨t, ht, htS⟩ := ih S (fun a ha => ⟨(hS a ha).1, fun x hx hcs =>
        (hS a ha).2 x hx (by
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · rw [hc, zero_dotProduct, zero_dotProduct]
          · exact hcs c' hc')⟩)
      exact ⟨t, by simp; omega, htS⟩
    · have hsub : ∀ b : ZMod 2, ∃ t : ParityTree n, treeDepth t ≤ cs.length + D ∧
          ∀ x ∈ {x | x ∈ S ∧ c ⬝ᵥ x = b}, treeEval t x = f x := by
        intro b
        apply ih
        rintro a ⟨haS, hab⟩
        refine ⟨(hS a haS).1, fun x ⟨hxS, hxb⟩ hcs => (hS a haS).2 x hxS ?_⟩
        intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [hxb, hab]
        · exact hcs c' hc'
      obtain ⟨t0, ht0, ht0S⟩ := hsub 0
      obtain ⟨t1, ht1, ht1S⟩ := hsub 1
      refine ⟨ParityTree.query c hc t0 t1, ?_, ?_⟩
      · rw [treeDepth_query]; simp only [List.length_cons]; omega
      · intro x hx
        rw [treeEval_query]
        split_ifs with h
        · exact ht0S x ⟨hx, h⟩
        · exact ht1S x ⟨hx, P2MFourier.zmod2_eq_one _ h⟩

lemma treeEval_leaf (b : Bool) (x : Vec n (ZMod 2)) :
    treeEval (ParityTree.leaf b : ParityTree n) x = if b then -1 else 1 := rfl

lemma sg_eq_leaf (v : ZMod 2) : P2MFourier.sg v = if decide (v = 1) then -1 else 1 := by
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 v with rfl | rfl
  · simp [P2MFourier.sg_zero]
  · simp [P2MFourier.sg_one]

/-- affine phases have parity depth at most one -/
lemma affine_tree (p : Vec n (ZMod 2) → ZMod 2) (hp : P2MDiff.DegLe 1 p) :
    ∃ t : ParityTree n, treeDepth t ≤ 1 ∧ ∀ x, treeEval t x = phase p x := by
  classical
  have hpol : ∀ u v, p (u + v) + p u + p v + p 0 = 0 := by
    intro u v
    have := hp ![u, v] 0
    rw [show (![u, v] : Fin 2 → Fin n → ZMod 2) = ![u, v] from rfl, P2MQ.diffs_two] at this
    exact this
  let L : Vec n (ZMod 2) → ZMod 2 := fun x => p x + p 0
  have hL : ∀ u v, L (u + v) = L u + L v := by
    intro u v
    simp only [L]
    have := hpol u v
    linear_combination this - CharTwo.add_self_eq_zero (p u) - CharTwo.add_self_eq_zero (p v) -
      CharTwo.add_self_eq_zero (p 0)
  let ℓ : Vec n (ZMod 2) := fun i => L (Pi.single i 1)
  have hℓ : ∀ x, p x = p 0 + ℓ ⬝ᵥ x := by
    intro x
    have := P2MDiff.additive_expand L hL x
    have hdot : ℓ ⬝ᵥ x = p x + p 0 := by
      rw [dotProduct]
      simp only [L] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 := CharTwo.add_self_eq_zero (p 0)
    linear_combination -hdot - h2
  have hph : ∀ x, phase p x = P2MFourier.sg (p 0 + ℓ ⬝ᵥ x) := by
    intro x; rw [← hℓ]; rfl
  by_cases hℓ0 : ℓ = 0
  · refine ⟨ParityTree.leaf (decide (p 0 = 1)), by simp [treeDepth], fun x => ?_⟩
    rw [hph, hℓ0, zero_dotProduct, add_zero, treeEval_leaf, sg_eq_leaf]
  · refine ⟨ParityTree.query ℓ hℓ0 (ParityTree.leaf (decide (p 0 = 1)))
      (ParityTree.leaf (decide (p 0 + 1 = 1))), by simp [treeDepth], fun x => ?_⟩
    rw [treeEval_query, hph]
    split_ifs with h
    · rw [h, add_zero, treeEval_leaf, sg_eq_leaf]
    · rw [P2MFourier.zmod2_eq_one _ h, treeEval_leaf, sg_eq_leaf]

end trees

section rec

def Gam (j : ℕ) : ℝ := if j = 2 then 1 else 2 ^ (2 * j - 3)
def Gs (d : ℕ) : ℝ := ∑ j ∈ Finset.Icc 2 d, Gam j

lemma Gam_nonneg (j : ℕ) : 0 ≤ Gam j := by unfold Gam; split_ifs <;> positivity

lemma Gs_nonneg (d : ℕ) : 0 ≤ Gs d := Finset.sum_nonneg fun j _ => Gam_nonneg j

lemma Gs_succ {d : ℕ} (hd : 1 ≤ d) : Gs (d+1) = Gs d + Gam (d+1) := by
  unfold Gs
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma Gs_one : Gs 1 = 0 := by simp [Gs]

lemma Gs_closed : ∀ d, 2 ≤ d → Gs d = ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simp [Gs, Gam]; norm_num
  | succ d hd ih =>
    rw [Gs_succ (by omega), ih]
    unfold Gam
    rw [if_neg (by omega)]
    rw [show 2 * (d+1) - 1 = (2 * d - 1) + 2 by omega, show 2 * (d+1) - 3 = 2 * d - 1 by omega,
      pow_add]
    ring

variable {n : ℕ}

lemma l1_pos (p : Vec n (ZMod 2) → ZMod 2) : 0 < P2MFourier.l1 (P2MFourier.phase p) :=
  lt_of_lt_of_le one_pos (P2MFourier.one_le_l1_phase p)

/-- one level of the recursion: a subspace on which the top form vanishes -/
lemma codim_step (j : ℕ) (hj : 2 ≤ j) (p : Vec n (ZMod 2) → ZMod 2)
    (hp : P2MDiff.DegLe j p) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin j → Fin n → ZMod 2, (∀ i, h i ∈ U) → P2MDiff.diffs p h 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤
        Gam j * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
  by_cases hj2 : j = 2
  · subst hj2
    have hq : ∀ x u v w : Fin n → ZMod 2, p (x + u + v + w) + p (x + u + v) + p (x + u + w) +
        p (x + v + w) + p (x + u) + p (x + v) + p (x + w) + p x = 0 := by
      intro x u v w; rw [← P2MQ.diffs_three]; exact hp _ x
    obtain ⟨U, hUiso, hUc⟩ := P2MQ.isotropic_codim p hq
    refine ⟨U, ?_, ?_⟩
    · intro h hh
      have : h = ![h 0, h 1] := by
        funext i; fin_cases i <;> rfl
      rw [this, P2MQ.diffs_two]
      exact hUiso _ (hh 0) _ (hh 1)
    · have hspec := P2MQ.qspec p hq
      have hlog : Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) = (P2MQ.polM p).rank / 2 := by
        have := congrArg (Real.logb 2) hspec
        rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
        push_cast at this
        linarith
      rw [hlog]
      simp only [Gam, if_true, one_mul]
      have hle : Module.finrank (ZMod 2) U ≤ n := by
        have := Submodule.finrank_le U; simpa using this
      have : ((2 * (n - Module.finrank (ZMod 2) U) : ℕ) : ℝ) ≤ (P2MQ.polM p).rank := by
        exact_mod_cast hUc
      push_cast [Nat.cast_sub hle] at this
      linarith
  · obtain ⟨U, h1, h2⟩ := P2MK3.eq7 (j := j) (by omega) p hp
    refine ⟨U, h1, ?_⟩
    unfold Gam; rw [if_neg hj2]; exact h2

/-- the recursion over the degree (Lemma 3.1 with `Γ(2) = log‖f̂‖₁`, `Γ(j) = 2^{2j-3} log‖f̂‖₁`) -/
theorem rec_tree : ∀ d, 1 ≤ d → ∀ (n : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    P2MDiff.DegLe d p → ∃ t : ParityTree n, (∀ x, treeEval t x = phase p x) ∧
      (treeDepth t : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro n p hp
    obtain ⟨t, ht, htf⟩ := affine_tree p hp
    refine ⟨t, htf, ?_⟩
    rw [Gs_one, zero_mul, add_zero]
    exact_mod_cast ht
  | succ d hd ih =>
    intro n p hp
    classical
    obtain ⟨U, hUv, hUc⟩ := codim_step (d+1) (by omega) p hp
    set m := Module.finrank (ZMod 2) U
    let bU := Module.finBasis (ZMod 2) U
    let B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
    have hBinj : Function.Injective B := by
      intro y y' h
      have := Subtype.ext h
      exact bU.equivFun.symm.injective this
    have hBU : ∀ y, B y ∈ U := fun y => (bU.equivFun.symm y).2
    have hUB : ∀ u ∈ U, ∃ y, B y = u := by
      intro u hu
      exact ⟨bU.equivFun ⟨u, hu⟩, by simp [B]⟩
    -- trees on the cosets
    have hcell : ∀ a : Fin n → ZMod 2, ∃ t' : ParityTree n,
        (∀ y, treeEval t' (a + B y) = phase p (a + B y)) ∧
        (treeDepth t' : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
      intro a
      let q : Vec m (ZMod 2) → ZMod 2 := fun y => p (a + B y)
      have hq : P2MDiff.DegLe d q := by
        intro h y
        show P2MDiff.diffs (fun y => p (a + B y)) h y = 0
        rw [P2MDiff.diffs_comp, P2MDiff.diffs_const hp]
        exact hUv _ (fun i => hBU _)
      obtain ⟨t, htf, htd⟩ := ih m q hq
      obtain ⟨t', ht'd, ht'⟩ := transport B hBinj a t
      refine ⟨t', fun y => by rw [ht', htf]; rfl, ?_⟩
      rw [ht'd]
      refine htd.trans ?_
      have hl1 : P2MFourier.l1 (P2MFourier.phase q) ≤ P2MFourier.l1 (P2MFourier.phase p) :=
        P2MFourier.l1_affine (P2MFourier.phase p) B a
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (l1_pos q) hl1
      have := Gs_nonneg d
      nlinarith
    choose tf htf htfd using hcell
    -- parity checks cutting out the cosets of U
    let Q := (Fin n → ZMod 2) ⧸ U
    let bQ := Module.finBasis (ZMod 2) Q
    set k := Module.finrank (ZMod 2) Q
    let φ : Fin k → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      fun i => (LinearMap.proj i) ∘ₗ bQ.equivFun.toLinearMap ∘ₗ U.mkQ
    let cs : Fin k → Fin n → ZMod 2 := fun i j => φ i (Pi.single j 1)
    have hcs : ∀ i x, cs i ⬝ᵥ x = φ i x := by
      intro i x
      have := P2MDiff.additive_expand (φ i) (fun u v => map_add _ u v) x
      rw [this, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hmemU : ∀ x, (∀ i, cs i ⬝ᵥ x = 0) → x ∈ U := by
      intro x hx
      have h0 : bQ.equivFun (U.mkQ x) = 0 := by
        funext i; have := hx i; rw [hcs] at this; exact this
      have : U.mkQ x = 0 := bQ.equivFun.injective (by rw [h0, map_zero])
      exact (Submodule.Quotient.mk_eq_zero U).mp this
    have hk : (k : ℝ) = (n : ℝ) - m := by
      have := Submodule.finrank_quotient_add_finrank U
      simp only [Module.finrank_fin_fun] at this
      have : (k : ℝ) + m = n := by exact_mod_cast this
      linarith
    set D := Finset.univ.sup fun a => treeDepth (tf a)
    obtain ⟨t, htd, htS⟩ := coset_tree (phase p) D tf (List.ofFn cs) Set.univ (by
      intro a _
      refine ⟨Finset.le_sup (f := fun a => treeDepth (tf a)) (Finset.mem_univ a), ?_⟩
      intro x _ hx
      have hxa : x + a ∈ U := by
        apply hmemU
        intro i
        have := hx (cs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
        rw [dotProduct_add, this]
        exact CharTwo.add_self_eq_zero _
      obtain ⟨y, hy⟩ := hUB _ hxa
      have hx' : x = a + B y := by
        rw [hy, add_comm x a, ← add_assoc, P2MFourier.pself a, zero_add]
      rw [hx']; exact htf a y)
    refine ⟨t, fun x => htS x (Set.mem_univ x), ?_⟩
    have hD : (D : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun a => treeDepth (tf a))
      rw [show D = treeDepth (tf a) from ha]
      exact htfd a
    have hlen : ((List.ofFn cs).length : ℝ) = k := by simp
    have : (treeDepth t : ℝ) ≤ (List.ofFn cs).length + D := by exact_mod_cast htd
    rw [Gs_succ hd]
    calc (treeDepth t : ℝ) ≤ (List.ofFn cs).length + D := this
      _ ≤ Gam (d+1) * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) +
          (1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p))) := by
          rw [hlen, hk]; exact add_le_add hUc hD
      _ = _ := by ring

end rec

section final

variable {n : ℕ}

def sim : ParityTree n → DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2))
  | .leaf b => .leaf b
  | .query a _ l r => .alice (fun x => decide (a ⬝ᵥ x = 1))
      (.bob (fun y => decide (a ⬝ᵥ y = 1)) (sim l) (sim r))
      (.bob (fun y => decide (a ⬝ᵥ y = 1)) (sim r) (sim l))

lemma sim_sign : ∀ (t : ParityTree n) (x y : Vec n (ZMod 2)),
    protocolSign (sim t) x y = treeEval t (x + y) := by
  intro t
  induction t with
  | leaf b => intro x y; rfl
  | query a ha l r ihl ihr =>
    intro x y
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    simp only [protocolSign, sim, DetCCHard.Protocol.eval] at ihl ihr ⊢
    rw [treeEval_query, dotProduct_add]
    rcases h01 (a ⬝ᵥ x) with hx | hx <;> rcases h01 (a ⬝ᵥ y) with hy | hy <;>
      simp only [hx, hy, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        zero_ne_one, one_ne_zero, ihl, ihr] <;> first | rfl | (simp; done) | skip
    all_goals
      first
      | (rw [if_pos (by decide)]; exact ihl x y)
      | (rw [if_neg (by decide)]; exact ihr x y)

lemma sim_depth : ∀ t : ParityTree n, (sim t).depth = 2 * treeDepth t := by
  intro t
  induction t with
  | leaf b => rfl
  | query a ha l r ihl ihr =>
    simp only [sim, DetCCHard.Protocol.depth, treeDepth, ihl, ihr]
    omega

theorem main_result_pub :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    2 ≤ d → anfDegree p = (d : WithBot ℕ) →
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ∧
    1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    communicationDepth (phase p) ≤ 2 * parityDepth (phase p) ∧
    (parityDepth (phase p) : ℝ) ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) := by
  refine ⟨1, one_pos, ?_⟩
  intro n d p hd hp
  classical
  -- degree information
  have hcoef : ∀ S : Finset (Fin n), d < S.card → P2MANF.coeffZ p S = 0 := by
    intro S hS
    by_contra hne
    have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
      unfold anfDegree
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
      simp only [show coefficient p S = P2MANF.coeffZ p S from rfl, if_neg hne]
    rw [hp] at this
    have : S.card ≤ d := by exact_mod_cast this
    omega
  have hdeg : P2MDiff.DegLe d p := P2MANF.degLe_of_coeffZ p hcoef
  have hnaff : ¬ ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0 := by
    intro haff
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Fin n)))
      Finset.univ_nonempty (fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ))
    have h1 : anfDegree p = if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ) :=
      hS
    rw [hp] at h1
    split_ifs at h1 with hc
    · exact WithBot.natCast_ne_bot d h1
    · have hcard : d = S.card := by exact_mod_cast h1
      exact hc (P2MANF.coeffZ_affine p haff S (by omega))
  have hsp : 2 ≤ sparsity (phase p) := by
    by_contra hlt
    exact hnaff (P2MFourier.affine_of_sparsity_le_one p (by
      show P2MFourier.sparsity' (P2MFourier.phase p) ≤ 1
      exact Nat.lt_succ_iff.mp (not_le.mp hlt)))
  -- the tree
  obtain ⟨t, ht, htd⟩ := rec_tree d (by omega) n p hdeg
  have hPD : parityDepth (phase p) ≤ treeDepth t := Nat.sInf_le ⟨t, rfl, ht⟩
  set L1 := spectralNorm (phase p) with hL1
  set sp := sparsity (phase p) with hsp_def
  have hL1eq : L1 = P2MFourier.l1 (P2MFourier.phase p) := rfl
  have hL1pos : 0 < L1 := l1_pos p
  set a : ℝ := (2 : ℝ) ^ (2 * d - 1) - 5 with ha
  have ha0 : 0 ≤ a := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ (2 * d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  have hlogT : ∀ x, logTwo x = Real.logb 2 x := fun x => rfl
  have h1 : (parityDepth (phase p) : ℝ) ≤ 1 + a / 3 * logTwo L1 := by
    rw [hlogT]
    have := Gs_closed d hd
    calc (parityDepth (phase p) : ℝ) ≤ treeDepth t := by exact_mod_cast hPD
      _ ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := htd
      _ = 1 + a / 3 * Real.logb 2 L1 := by rw [this, hL1eq]
  have hsq : L1 ^ 2 ≤ sp := P2MFourier.l1_sq_le_sparsity p
  have hsppos : (0 : ℝ) < sp := by
    have : (2 : ℝ) ≤ sp := by exact_mod_cast hsp
    linarith
  have hlogL : 2 * logTwo L1 ≤ logTwo sp := by
    rw [hlogT, hlogT]
    calc 2 * Real.logb 2 L1 = Real.logb 2 (L1 ^ 2) := by rw [Real.logb_pow]; push_cast; ring
      _ ≤ Real.logb 2 sp := Real.logb_le_logb_of_le (by norm_num) (by positivity) hsq
  have h2 : 1 + a / 3 * logTwo L1 ≤ 1 + a / 6 * logTwo sp := by
    have : a / 3 * logTwo L1 ≤ a / 6 * logTwo sp := by
      have := mul_le_mul_of_nonneg_left hlogL ha0
      linarith
    linarith
  -- communication
  obtain ⟨t0, ht0d, ht0⟩ : ∃ t0 : ParityTree n, treeDepth t0 = parityDepth (phase p) ∧
      ∀ x, treeEval t0 x = phase p x :=
    Nat.sInf_mem (s := {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = phase p x})
      ⟨_, t, rfl, ht⟩
  have h4 : communicationDepth (phase p) ≤ 2 * parityDepth (phase p) := by
    rw [← ht0d, ← sim_depth]
    exact Nat.sInf_le ⟨sim t0, rfl, fun x y => by rw [sim_sign, ht0]⟩
  have h4r : (communicationDepth (phase p) : ℝ) / 2 ≤ parityDepth (phase p) := by
    have : (communicationDepth (phase p) : ℝ) ≤ 2 * parityDepth (phase p) := by exact_mod_cast h4
    linarith
  -- uniform constant
  have hlogs : 1 ≤ logTwo sp := by
    rw [hlogT]
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 2)
      (show (2:ℝ) ≤ sp by exact_mod_cast hsp)
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have h5 : (parityDepth (phase p) : ℝ) ≤ 1 * (4 : ℝ) ^ d * logTwo sp := by
    have h4d : (4 : ℝ) ^ d = 2 * 2 ^ (2 * d - 1) := by
      have e : (2:ℝ) ^ (2 * d) = 2 ^ (2 * d - 1 + 1) := by congr 1; omega
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, e, pow_succ]; ring
    have h16 : (16 : ℝ) ≤ 4 ^ d := by
      have : (4 : ℝ) ^ 2 ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) hd
      norm_num at this; linarith
    have hpow : (8 : ℝ) ≤ 2 ^ (2 * d - 1) := by
      have : (2 : ℝ) ^ 3 ≤ 2 ^ (2 * d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    calc (parityDepth (phase p) : ℝ) ≤ 1 + a / 6 * logTwo sp := h1.trans h2
      _ ≤ 1 * (4 : ℝ) ^ d * logTwo sp := by
        rw [h4d, ha]
        nlinarith
  refine ⟨h1, h2, ?_, h4, h5, ?_⟩
  · exact h4r.trans (h1.trans h2)
  · exact h4r.trans h5

end final

end ParityDegreeDepth.Main


end
end

-- ===== LC2a =====
section

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement P2MFourier

variable {n : ℕ}

lemma spectralNorm_eq (f : Vec n (ZMod 2) → ℝ) : spectralNorm f = l1 f := rfl

lemma spectralNorm_nonneg (f : Vec n (ZMod 2) → ℝ) : 0 ≤ spectralNorm f := l1_nonneg f

/-- polarised Parseval -/
lemma plancherel (f g : (Fin n → ZMod 2) → ℝ) :
    ∑ ξ, QAlgorithms.boolFourier f ξ * QAlgorithms.boolFourier g ξ =
      ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
  calc ∑ ξ, QAlgorithms.boolFourier f ξ * QAlgorithms.boolFourier g ξ
      = ∑ ξ, QAlgorithms.boolFourier f ξ * (((2 : ℝ) ^ n)⁻¹ * ∑ x, g x * sg (ξ ⬝ᵥ x)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [boolFourier_eq g ξ]
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, g x * ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ξ _ => ?_
        ring
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← fourier_inversion f x, mul_comm]

/-- `‖ĝ‖₁ ≥ 1 / max|f̂|` for a margin-one witness: if all `|f̂| ≤ M` then `1 ≤ M ‖ĝ‖₁` -/
lemma witness_bound (f g : Vec n (ZMod 2) → ℝ) (hfg : IsSignWitness f g) (M : ℝ)
    (hM : ∀ ξ, |QAlgorithms.boolFourier f ξ| ≤ M) : 1 ≤ M * spectralNorm g := by
  have h1 : 1 ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
    have : ∑ _x : Vec n (ZMod 2), (1 : ℝ) ≤ ∑ x, f x * g x := Finset.sum_le_sum fun x _ => hfg x
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one] at this
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_inv_mul_iff₀ h2]
    push_cast at this
    linarith
  rw [← plancherel] at h1
  refine h1.trans ?_
  rw [spectralNorm_eq]
  unfold l1
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun ξ _ => le_abs_self _).trans ?_
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM ξ) (abs_nonneg _)

lemma witness_set_nonempty (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) :
    {w : ℝ | ∃ g : Vec n (ZMod 2) → ℝ, IsSignWitness f g ∧ spectralNorm g = w}.Nonempty := by
  refine ⟨_, f, fun x => ?_, rfl⟩
  rcases hf x with h | h <;> rw [h] <;> norm_num

lemma witness_set_bdd (f : Vec n (ZMod 2) → ℝ) :
    BddBelow {w : ℝ | ∃ g : Vec n (ZMod 2) → ℝ, IsSignWitness f g ∧ spectralNorm g = w} := by
  refine ⟨0, ?_⟩
  rintro w ⟨g, -, rfl⟩
  exact spectralNorm_nonneg g

lemma W_le (f g : Vec n (ZMod 2) → ℝ) (hfg : IsSignWitness f g) :
    thresholdWeight f ≤ spectralNorm g :=
  csInf_le (witness_set_bdd f) ⟨g, hfg, rfl⟩

lemma le_W (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (c : ℝ)
    (h : ∀ g, IsSignWitness f g → c ≤ spectralNorm g) : c ≤ thresholdWeight f := by
  apply le_csInf (witness_set_nonempty f hf)
  rintro w ⟨g, hg, rfl⟩
  exact h g hg

lemma W_nonneg (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) : 0 ≤ thresholdWeight f :=
  le_W f hf 0 fun g _ => spectralNorm_nonneg g

lemma self_witness (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) : IsSignWitness f f := by
  intro x; rcases hf x with h | h <;> rw [h] <;> norm_num

end P2MLC2

end
end

-- ===== LC2b =====
section

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement P2MFourier

variable {n : ℕ}

lemma sd_succ {k : ℕ} (f : Vec n (ZMod 2) → ℝ) (h : Fin (k+1) → Vec n (ZMod 2)) :
    signDerivatives f h = signDerivatives (fun x => f x * f (x + h 0)) (Fin.tail h) := by
  simp only [signDerivatives, List.ofFn_succ, List.foldl_cons]; rfl

lemma sd_witness : ∀ (k : ℕ) (f g : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
    IsSignWitness f g → IsSignWitness (signDerivatives f h) (signDerivatives g h) := by
  intro k
  induction k with
  | zero => intro f g h hfg; simpa [signDerivatives] using hfg
  | succ k ih =>
    intro f g h hfg
    rw [sd_succ, sd_succ]
    apply ih
    intro x
    have h1 := hfg x
    have h2 := hfg (x + h 0)
    calc (1 : ℝ) ≤ (f x * g x) * (f (x + h 0) * g (x + h 0)) := by nlinarith
      _ = _ := by ring

lemma sd_norm : ∀ (k : ℕ) (g : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
    spectralNorm (signDerivatives g h) ≤ spectralNorm g ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro g h; simp [signDerivatives]
  | succ k ih =>
    intro g h
    rw [sd_succ]
    refine (ih _ _).trans ?_
    have h1 : spectralNorm (fun x => g x * g (x + h 0)) ≤ spectralNorm g ^ 2 := by
      refine (l1_mul_le _ _).trans ?_
      rw [show l1 (fun x => g (x + h 0)) = l1 g from l1_translate g (h 0), sq]; rfl
    calc spectralNorm (fun x => g x * g (x + h 0)) ^ 2 ^ k ≤ (spectralNorm g ^ 2) ^ 2 ^ k :=
          pow_le_pow_left₀ (l1_nonneg _) h1 _
      _ = spectralNorm g ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ, mul_comm]

lemma W_nonneg' (f : Vec n (ZMod 2) → ℝ) : 0 ≤ thresholdWeight f := by
  apply Real.sInf_nonneg
  rintro w ⟨g, -, rfl⟩
  exact spectralNorm_nonneg g

lemma W_sd {k : ℕ} (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (h : Fin k → Vec n (ZMod 2)) :
    thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k) := by
  set a := thresholdWeight (signDerivatives f h)
  set N := 2 ^ k with hN
  have hN0 : N ≠ 0 := by positivity
  have ha0 : 0 ≤ a := W_nonneg' _
  have hroot : a ^ ((N : ℝ)⁻¹) ≤ thresholdWeight f := by
    apply le_W f hf
    intro g hg
    have h1 : a ≤ spectralNorm g ^ N :=
      (W_le _ _ (sd_witness k f g h hg)).trans (sd_norm k g h)
    calc a ^ ((N : ℝ)⁻¹) ≤ (spectralNorm g ^ N) ^ ((N : ℝ)⁻¹) :=
          Real.rpow_le_rpow ha0 h1 (by positivity)
      _ = spectralNorm g := Real.pow_rpow_inv_natCast (spectralNorm_nonneg g) hN0
  calc a = (a ^ ((N : ℝ)⁻¹)) ^ N := (Real.rpow_inv_natCast_pow ha0 hN0).symm
    _ ≤ thresholdWeight f ^ N := pow_le_pow_left₀ (by positivity) hroot _

/-- quadratic phases: all coefficients are at most `2^{-rank/2}` -/
lemma quad_coeff_bound (q : (Fin n → ZMod 2) → ZMod 2)
    (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (P2MFourier.phase q) ξ ^ 2 * 2 ^ (P2MQ.polM q).rank ≤ 1 := by
  rw [P2MQ.fourier_sq q hq ξ]
  have hcard := P2MQ.card_radF q
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rcases P2MQ.char_sum_rad q hq ξ with h | h
  · rw [h]; simp
  · rw [h]
    apply le_of_eq
    calc ((2 : ℝ) ^ n)⁻¹ * ((P2MQ.radF q).card : ℝ) * 2 ^ (P2MQ.polM q).rank
        = ((2 : ℝ) ^ n)⁻¹ * (((P2MQ.radF q).card : ℝ) * 2 ^ (P2MQ.polM q).rank) := by ring
      _ = 1 := by rw [hcard]; field_simp

end P2MLC2

end
end

-- ===== LC2c =====
section

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement

variable {n : ℕ}

lemma phase_pm (p : Vec n (ZMod 2) → ZMod 2) :
    ∀ x, ParityDegreeDepth.Main.phase p x = -1 ∨ ParityDegreeDepth.Main.phase p x = 1 := by
  intro x
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  unfold ParityDegreeDepth.Main.phase
  rcases h01 (p x) with h | h <;> rw [h] <;> simp [ZMod.val_one]

lemma sd_phase : ∀ (k : ℕ) (p : Vec n (ZMod 2) → ZMod 2) (h : Fin k → Vec n (ZMod 2)),
    signDerivatives (ParityDegreeDepth.Main.phase p) h = ParityDegreeDepth.Main.phase (P2MDiff.diffs p h) := by
  intro k
  induction k with
  | zero => intro p h; simp [signDerivatives, P2MDiff.diffs]
  | succ k ih =>
    intro p h
    rw [sd_succ, P2MDiff.diffs_succ, ← ih]
    congr 1
    funext x
    show P2MFourier.sg (p x) * P2MFourier.sg (p (x + h 0)) = P2MFourier.sg (p (x + h 0) + p x)
    rw [P2MFourier.sg_add, mul_comm]

lemma degLe_of_anf_le {k : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : anfDegree p ≤ (k : WithBot ℕ)) :
    P2MDiff.DegLe k p := by
  classical
  apply P2MANF.degLe_of_coeffZ p
  intro S hS
  by_contra hne
  have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
    unfold anfDegree
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
      if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
    simp only [show coefficient p S = P2MANF.coeffZ p S from rfl, if_neg hne]
  have := this.trans hp
  have : S.card ≤ k := by exact_mod_cast this
  omega

lemma hq_of_degLe2 (q : Vec n (ZMod 2) → ZMod 2) (hq : P2MDiff.DegLe 2 q) :
    ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0 := by
  intro x u v w; rw [← P2MQ.diffs_three]; exact hq _ x

/-- for a quadratic phase with polar rank `ρ`, every witness has norm at least `√(2^ρ)` -/
lemma quad_witness (q : Vec n (ZMod 2) → ZMod 2) (hq : P2MDiff.DegLe 2 q) (g : Vec n (ZMod 2) → ℝ)
    (hg : IsSignWitness (ParityDegreeDepth.Main.phase q) g) :
    Real.sqrt (2 ^ (P2MQ.polM q).rank) ≤ spectralNorm g := by
  have hq' := hq_of_degLe2 q hq
  have hpos : (0 : ℝ) < Real.sqrt (2 ^ (P2MQ.polM q).rank) := Real.sqrt_pos.mpr (by positivity)
  have hb := witness_bound _ g hg (Real.sqrt (2 ^ (P2MQ.polM q).rank))⁻¹ (by
    intro ξ
    have h1 := quad_coeff_bound q hq' ξ
    have hc : (0 : ℝ) < 2 ^ (P2MQ.polM q).rank := by positivity
    have h2 : QAlgorithms.boolFourier (ParityDegreeDepth.Main.phase q) ξ ^ 2 ≤
        ((Real.sqrt (2 ^ (P2MQ.polM q).rank))⁻¹) ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (by positivity), show ((2 : ℝ) ^ (P2MQ.polM q).rank)⁻¹ =
        1 / 2 ^ (P2MQ.polM q).rank by ring, le_div_iff₀ hc]
      exact h1
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_pos (inv_pos.mpr hpos)] at h3)
  rw [le_inv_mul_iff₀ hpos, mul_one] at hb
  exact hb

lemma polM_eq_contraction (p : Vec n (ZMod 2) → ZMod 2) :
    P2MQ.polM p = contraction (topForm p 2) (fun i => Fin.elim0 i) := by
  ext a b
  simp only [P2MQ.polM, contraction, topForm, Matrix.of_apply]
  rw [← P2MQ.diffs_two]
  show _ = P2MDiff.diffs p _ 0
  congr 1
  funext s
  fin_cases s <;> simp

lemma coeff_eq_top {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (ind : Fin d → Fin n)
    (hind : Function.Injective ind) :
    P2MDiff.diffs p (fun i => Pi.single (ind i) 1) 0 = ParityDegreeDepth.Main.coefficient p (Finset.univ.image ind) := by
  classical
  rw [show ParityDegreeDepth.Main.coefficient p (Finset.univ.image ind) = P2MANF.coeffZ p (Finset.univ.image ind) from rfl,
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


theorem lc2 :
    -- (a)
    (∀ (n m : ℕ) (f g : Vec n (ZMod 2) → ℝ)
        (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2)) (a : Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) → Function.Injective B →
        (IsSignWitness f g →
          IsSignWitness (f ∘ affineMap B a) (g ∘ affineMap B a) ∧
          spectralNorm (g ∘ affineMap B a) ≤ spectralNorm g) ∧
        thresholdWeight (f ∘ affineMap B a) ≤ thresholdWeight f) ∧
    -- (b)
    (∀ (n : ℕ) (f₁ f₂ g₁ g₂ : Vec n (ZMod 2) → ℝ),
        (∀ x, f₁ x = -1 ∨ f₁ x = 1) → (∀ x, f₂ x = -1 ∨ f₂ x = 1) →
        IsSignWitness f₁ g₁ → IsSignWitness f₂ g₂ →
        IsSignWitness (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) ∧
        spectralNorm (fun x => g₁ x * g₂ x) ≤ spectralNorm g₁ * spectralNorm g₂) ∧
    (∀ (n k : ℕ) (f : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) →
        thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k)) ∧
    -- (c)
    (∀ (n r : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        anfDegree p ≤ (2 : WithBot ℕ) →
        (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r →
        (∀ g, IsSignWitness (phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g) ∧
        thresholdWeight (phase p) = (2 : ℝ) ^ r) ∧
    -- (d)
    (∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        2 ≤ d → anfDegree p = (d : WithBot ℕ) →
        1 < thresholdWeight (phase p)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n m f g B a hf hB
    refine ⟨fun hfg => ⟨fun x => hfg _, P2MFourier.l1_affine g B a⟩, ?_⟩
    apply le_W f hf
    intro g hg
    exact (W_le _ (g ∘ affineMap B a) (fun x => hg _)).trans (P2MFourier.l1_affine g B a)
  · intro n f₁ f₂ g₁ g₂ _ _ h₁ h₂
    refine ⟨fun x => ?_, P2MFourier.l1_mul_le g₁ g₂⟩
    have a1 := h₁ x
    have a2 := h₂ x
    calc (1 : ℝ) ≤ (f₁ x * g₁ x) * (f₂ x * g₂ x) := by nlinarith
      _ = _ := by ring
  · intro n k f h hf
    exact W_sd f hf h
  · intro n r p hp hr
    have hdeg := degLe_of_anf_le (k := 2) p hp
    have hrank : (P2MQ.polM p).rank = 2 * r := by rw [polM_eq_contraction]; exact hr
    have hspec := P2MQ.qspec p (hq_of_degLe2 p hdeg)
    rw [hrank] at hspec
    have hl1 : spectralNorm (ParityDegreeDepth.Main.phase p) = 2 ^ r := by
      have h0 : 0 ≤ spectralNorm (ParityDegreeDepth.Main.phase p) := spectralNorm_nonneg _
      have : spectralNorm (ParityDegreeDepth.Main.phase p) ^ 2 = ((2 : ℝ) ^ r) ^ 2 := by
        rw [← pow_mul, mul_comm]; exact hspec
      exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).mp this
    have hsqrt : Real.sqrt (2 ^ (P2MQ.polM p).rank) = (2 : ℝ) ^ r := by
      rw [hrank, pow_mul', Real.sqrt_sq (by positivity)]
    have hwit : ∀ g, IsSignWitness (ParityDegreeDepth.Main.phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g := by
      intro g hg; rw [← hsqrt]; exact quad_witness p hdeg g hg
    refine ⟨hwit, le_antisymm ?_ (le_W _ (phase_pm p) _ hwit)⟩
    rw [← hl1]
    exact W_le _ _ (self_witness _ (phase_pm p))
  · intro n d p hd hp
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    have hdeg : P2MDiff.DegLe (k + 2) p := degLe_of_anf_le p (le_of_eq hp)
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Fin n)))
      Finset.univ_nonempty (fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ))
    have h1 : anfDegree p = if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ) := hS
    rw [hp] at h1
    split_ifs at h1 with hc
    · exact absurd h1 (WithBot.natCast_ne_bot _)
    have hcard : S.card = k + 2 := by exact_mod_cast h1.symm
    let e := S.equivFin
    let ind : Fin (k + 2) → Fin n := fun i => (e.symm (Fin.cast hcard.symm i) : Fin n)
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
    set h : Fin (k + 2) → Vec n (ZMod 2) := fun i => Pi.single (ind i) 1 with hh
    have hT : P2MDiff.diffs p h 0 ≠ 0 := by
      rw [coeff_eq_top p ind hind, himg]; exact hc
    let hk : Fin k → Vec n (ZMod 2) := fun l => h (Fin.castAdd 2 l)
    set q := P2MDiff.diffs p hk with hqdef
    have hsplit : h = Fin.append hk ![h (Fin.natAdd k 0), h (Fin.natAdd k 1)] := by
      funext i
      refine Fin.addCases (fun l => ?_) (fun t => ?_) i
      · simp [hk, Fin.append_left]
      · fin_cases t <;> simp [Fin.append_right]
    have hpol : P2MQ.pol q (h (Fin.natAdd k 0)) (h (Fin.natAdd k 1)) ≠ 0 := by
      rw [← P2MQ.diffs_two, hqdef, ← P2MQ.diffs_append, ← hsplit]; exact hT
    have hrank : 1 ≤ (P2MQ.polM q).rank := by
      apply T35aux.le_rank_of_minor (P2MQ.polM q) (fun _ => ind (Fin.natAdd k 0))
        (fun _ => ind (Fin.natAdd k 1))
      rw [Matrix.det_unique]
      exact hpol
    have hq2 : P2MDiff.DegLe 2 q := by
      intro h' x
      rw [hqdef, ← P2MQ.diffs_append]
      exact hdeg _ x
    have hWq : Real.sqrt 2 ≤ thresholdWeight (ParityDegreeDepth.Main.phase q) := by
      apply le_W _ (phase_pm q)
      intro g hg
      refine le_trans ?_ (quad_witness q hq2 g hg)
      apply Real.sqrt_le_sqrt
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (P2MQ.polM q).rank := pow_le_pow_right₀ (by norm_num) hrank
    have hsd := W_sd (ParityDegreeDepth.Main.phase p) (phase_pm p) hk
    rw [sd_phase] at hsd
    have hsqrt : 1 < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    by_contra hle
    push Not at hle
    have hW0 := W_nonneg' (ParityDegreeDepth.Main.phase p)
    have := pow_le_one₀ hW0 hle (n := 2 ^ k)
    linarith

end P2MLC2

end
end

-- ===== L31 =====
section

open scoped BigOperators
noncomputable section

namespace P2ML31

open ParityDegreeDepth.Main Matrix

variable {n : ℕ}

lemma anf_le_of_degLe {k : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : P2MDiff.DegLe k p) :
    anfDegree p ≤ (k : WithBot ℕ) := by
  classical
  unfold anfDegree
  apply Finset.sup_le
  intro S _
  split_ifs with hc
  · exact bot_le
  · by_contra hlt
    have hk : k < S.card := by
      rw [not_le] at hlt; exact_mod_cast hlt
    apply hc
    obtain ⟨c, hc'⟩ : ∃ c, S.card = c + 1 := ⟨S.card - 1, by omega⟩
    have hmono : P2MDiff.DegLe c p := P2MANF.degLe_mono (by omega) hp
    let ind : Fin (c+1) → Fin n := fun i => (S.equivFin.symm (Fin.cast hc'.symm i) : Fin n)
    have hind : Function.Injective ind := by
      intro x y hxy
      have := Subtype.ext hxy
      have := S.equivFin.symm.injective this
      exact Fin.cast_injective _ this
    have himg : Finset.univ.image ind = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact (S.equivFin.symm _).2
      · intro hx
        refine ⟨Fin.cast hc' (S.equivFin ⟨x, hx⟩), ?_⟩
        simp [ind]
    rw [← himg, ← P2MLC2.coeff_eq_top p ind hind]
    exact hmono _ 0

lemma diffs_zero_vec {j : ℕ} (q : Vec n (ZMod 2) → ZMod 2) :
    P2MDiff.diffs q (fun _ : Fin (j+1) => (0 : Vec n (ZMod 2))) 0 = 0 := by
  rw [P2MDiff.diffs_closed]
  simp only [smul_zero, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ, show (2 : ZMod 2) = 0 from rfl, mul_zero, zero_mul]

lemma glue {m : ℕ} (f : Vec m (ZMod 2) → ℝ) (U : Submodule (ZMod 2) (Fin m → ZMod 2)) (D0 : ℝ)
    (hcell : ∀ a : Fin m → ZMod 2, ∃ t' : ParityTree m,
      (∀ u ∈ U, treeEval t' (a + u) = f (a + u)) ∧ (treeDepth t' : ℝ) ≤ D0) :
    ∃ t : ParityTree m, (∀ x, treeEval t x = f x) ∧
      (treeDepth t : ℝ) ≤ ((m : ℝ) - Module.finrank (ZMod 2) U) + D0 := by
  classical
  choose tf htf htfd using hcell
  let Q := (Fin m → ZMod 2) ⧸ U
  let bQ := Module.finBasis (ZMod 2) Q
  set k := Module.finrank (ZMod 2) Q
  let φ : Fin k → (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    fun i => (LinearMap.proj i) ∘ₗ bQ.equivFun.toLinearMap ∘ₗ U.mkQ
  let cs : Fin k → Fin m → ZMod 2 := fun i j => φ i (Pi.single j 1)
  have hcs : ∀ i x, cs i ⬝ᵥ x = φ i x := by
    intro i x
    have := P2MDiff.additive_expand (φ i) (fun u v => map_add _ u v) x
    rw [this, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hmemU : ∀ x, (∀ i, cs i ⬝ᵥ x = 0) → x ∈ U := by
    intro x hx
    have h0 : bQ.equivFun (U.mkQ x) = 0 := by
      funext i; have := hx i; rw [hcs] at this; exact this
    have : U.mkQ x = 0 := bQ.equivFun.injective (by rw [h0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero U).mp this
  have hk : (k : ℝ) = (m : ℝ) - Module.finrank (ZMod 2) U := by
    have := Submodule.finrank_quotient_add_finrank U
    simp only [Module.finrank_fin_fun] at this
    have : (k : ℝ) + Module.finrank (ZMod 2) U = m := by exact_mod_cast this
    linarith
  set D := Finset.univ.sup fun a => treeDepth (tf a)
  obtain ⟨t, htd, htS⟩ := coset_tree f D tf (List.ofFn cs) Set.univ (by
    intro a _
    refine ⟨Finset.le_sup (f := fun a => treeDepth (tf a)) (Finset.mem_univ a), ?_⟩
    intro x _ hx
    have hxa : x + a ∈ U := by
      apply hmemU
      intro i
      have := hx (cs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
      rw [dotProduct_add, this]
      exact CharTwo.add_self_eq_zero _
    have hx' : x = a + (x + a) := by
      rw [add_comm x a, ← add_assoc, P2MFourier.pself, zero_add]
    rw [hx']; exact htf a _ hxa)
  refine ⟨t, fun x => htS x (Set.mem_univ x), ?_⟩
  have hD : (D : ℝ) ≤ D0 := by
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun a => treeDepth (tf a))
    rw [show D = treeDepth (tf a) from ha]
    exact htfd a
  have hlen : ((List.ofFn cs).length : ℝ) = k := by simp
  have : (treeDepth t : ℝ) ≤ (List.ofFn cs).length + D := by exact_mod_cast htd
  rw [hlen, hk] at this
  linarith

theorem lemma_3_1 {d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) (Γ : ℕ → ℝ)
    (hΓ : ∀ j ∈ Finset.Icc 2 d, 0 ≤ Γ j)
    (hhigh : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B → ∀ j, 3 ≤ j → j ≤ d →
      anfDegree (p ∘ affineMap B a) = (j : WithBot ℕ) →
      (vanishingCodim (topForm (p ∘ affineMap B a) j) : ℝ) ≤ Γ j)
    (hquad : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      anfDegree (p ∘ affineMap B a) = (2 : WithBot ℕ) →
      (parityDepth (phase (p ∘ affineMap B a)) : ℝ) ≤ 1 + Γ 2) :
    (parityDepth (phase p) : ℝ) ≤ 1 + ∑ j ∈ Finset.Icc 2 d, Γ j := by
  classical
  have claim : ∀ j, 1 ≤ j → j ≤ d → ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      anfDegree (p ∘ affineMap B a) ≤ (j : WithBot ℕ) →
      ∃ t : ParityTree m, (∀ y, treeEval t y = phase (p ∘ affineMap B a) y) ∧
        (treeDepth t : ℝ) ≤ 1 + ∑ i ∈ Finset.Icc 2 j, Γ i := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _ m B a _ hdeg
      obtain ⟨t, ht, htf⟩ := affine_tree _ (P2MLC2.degLe_of_anf_le _ hdeg)
      refine ⟨t, htf, ?_⟩
      have : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
      rw [this, Finset.sum_empty, add_zero]
      exact_mod_cast ht
    | succ j hj ih =>
      intro hjd m B a hB hdeg
      set q := p ∘ affineMap B a with hq
      have hstep : ∑ i ∈ Finset.Icc 2 (j+1), Γ i = ∑ i ∈ Finset.Icc 2 j, Γ i + Γ (j+1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hΓj : 0 ≤ Γ (j+1) := hΓ (j+1) (by simp only [Finset.mem_Icc]; omega)
      by_cases hlow : anfDegree q ≤ (j : WithBot ℕ)
      · obtain ⟨t, htf, htd⟩ := ih (by omega) m B a hB hlow
        exact ⟨t, htf, by rw [hstep]; linarith⟩
      have hexact : anfDegree q = ((j+1 : ℕ) : WithBot ℕ) := by
        have hle : anfDegree q ≤ ((j+1 : ℕ) : WithBot ℕ) := hdeg
        revert hle hlow
        generalize anfDegree q = x
        intro hlow hle
        induction x using WithBot.recBotCoe with
        | bot => exact absurd bot_le hlow
        | coe v =>
          have h1 : v ≤ j + 1 := WithBot.coe_le_coe.mp hle
          have h2 : ¬ v ≤ j := fun h => hlow (WithBot.coe_le_coe.mpr h)
          have : v = j + 1 := by omega
          rw [this]; rfl
      have hqdeg : P2MDiff.DegLe (j+1) q := P2MLC2.degLe_of_anf_le q (le_of_eq hexact)
      by_cases hj1 : j + 1 = 2
      · have h2 : anfDegree (p ∘ affineMap B a) = (2 : WithBot ℕ) := by
          rw [← hq, hexact, hj1]; rfl
        have hqd := hquad m B a hB h2
        have hne : {k | ∃ t : ParityTree m, treeDepth t = k ∧
            ∀ x, treeEval t x = phase q x}.Nonempty := by
          obtain ⟨t, ht, -⟩ := rec_tree (j+1) (by omega) m q hqdeg
          exact ⟨_, t, rfl, ht⟩
        obtain ⟨t, htd, ht⟩ := Nat.sInf_mem hne
        refine ⟨t, ht, ?_⟩
        have hpd : (treeDepth t : ℝ) = parityDepth (phase q) := by
          rw [htd]; rfl
        rw [hpd, hj1]
        have : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
        rw [this, Finset.sum_singleton]
        exact hqd
      · have hj3 : 3 ≤ j + 1 := by omega
        have hcod := hhigh m B a hB (j+1) hj3 hjd hexact
        have hne : {r | ∃ U : Submodule (ZMod 2) (Vec m (ZMod 2)),
            m - Module.finrank (ZMod 2) U = r ∧ Vanishes (topForm q (j+1)) U}.Nonempty := by
          refine ⟨_, ⊥, rfl, ?_⟩
          intro x hx
          have hx0 : x = fun _ => 0 := funext fun i => (Submodule.mem_bot _).mp (hx i)
          rw [hx0]
          exact diffs_zero_vec (j := j) q
        obtain ⟨U, hUr, hUv⟩ := Nat.sInf_mem hne
        have hcodU : (m : ℝ) - Module.finrank (ZMod 2) U ≤ Γ (j+1) := by
          have hle : Module.finrank (ZMod 2) U ≤ m := by
            have := Submodule.finrank_le U; simpa using this
          have : ((m - Module.finrank (ZMod 2) U : ℕ) : ℝ) ≤ Γ (j+1) := by
            rw [hUr]; exact hcod
          push_cast [Nat.cast_sub hle] at this; exact this
        let bU := Module.finBasis (ZMod 2) U
        set k := Module.finrank (ZMod 2) U
        let C : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
          U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
        have hCinj : Function.Injective C := by
          intro y y' h
          have := Subtype.ext h
          exact bU.equivFun.symm.injective this
        have hCU : ∀ y, C y ∈ U := fun y => (bU.equivFun.symm y).2
        have hUC : ∀ u ∈ U, ∃ y, C y = u := by
          intro u hu
          exact ⟨bU.equivFun ⟨u, hu⟩, by simp [C]⟩
        obtain ⟨t, ht, htd⟩ := glue (phase q) U (1 + ∑ i ∈ Finset.Icc 2 j, Γ i) (fun a' => by
          have e : (p ∘ affineMap (B ∘ₗ C) (a + B a')) = fun y => q (a' + C y) := by
            funext y
            simp only [Function.comp_apply, affineMap, LinearMap.coe_comp, q, map_add, add_assoc]
          have hr : anfDegree (p ∘ affineMap (B ∘ₗ C) (a + B a')) ≤ (j : WithBot ℕ) := by
            apply anf_le_of_degLe
            intro h y
            rw [e, P2MDiff.diffs_comp q C a' h y, P2MDiff.diffs_const hqdeg]
            exact hUv (fun i => C (h i)) (fun i => hCU _)
          obtain ⟨t'', ht'', htd''⟩ := ih (by omega) k (B ∘ₗ C) (a + B a') (hB.comp hCinj) hr
          obtain ⟨t', ht'd, ht'⟩ := transport C hCinj a' t''
          refine ⟨t', fun u hu => ?_, by rw [ht'd]; exact htd''⟩
          obtain ⟨y, rfl⟩ := hUC u hu
          rw [ht', ht'', e]; rfl)
        refine ⟨t, ht, ?_⟩
        rw [hstep]
        linarith
  have hid : p ∘ affineMap (LinearMap.id : Vec n (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2)) 0 = p := by
    funext x; simp [affineMap]
  obtain ⟨t, ht, htd⟩ := claim d (by omega) le_rfl n LinearMap.id 0 Function.injective_id
    (by rw [hid, hp])
  rw [hid] at ht
  have hPD : parityDepth (phase p) ≤ treeDepth t := Nat.sInf_le ⟨t, rfl, ht⟩
  calc (parityDepth (phase p) : ℝ) ≤ treeDepth t := by exact_mod_cast hPD
    _ ≤ _ := htd

end P2ML31

end
end

-- ===== adapter =====
open ParityDegreeDepth.Main in
theorem solution {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) (Γ : ℕ → ℝ)
    (hΓ : ∀ j ∈ Finset.Icc 2 d, 0 ≤ Γ j)
    (hhigh : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B → ∀ j, 3 ≤ j → j ≤ d →
      anfDegree (p ∘ affineMap B a) = (j : WithBot ℕ) →
      (vanishingCodim (topForm (p ∘ affineMap B a) j) : ℝ) ≤ Γ j)
    (hquad : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      anfDegree (p ∘ affineMap B a) = (2 : WithBot ℕ) →
      (parityDepth (phase (p ∘ affineMap B a)) : ℝ) ≤ 1 + Γ 2) :
    (parityDepth (phase p) : ℝ) ≤ 1 + ∑ j ∈ Finset.Icc 2 d, Γ j := P2ML31.lemma_3_1 p hd hp Γ hΓ hhigh hquad

