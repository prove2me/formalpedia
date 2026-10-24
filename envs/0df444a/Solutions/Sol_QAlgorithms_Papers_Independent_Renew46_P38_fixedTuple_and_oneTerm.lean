-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.fixedTuple_and_oneTerm
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:23:31.218985+00:00
-- url     : https://prove2.me/submissions/d2078860-5873-4a88-836b-f1d6f005a200

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38


/- Direct helper source: JENS2_Blocks.lean -/

noncomputable section

open scoped BigOperators ComplexOrder CStarAlgebra
open ContinuousLinearMap

namespace QAlgorithms.Papers.Independent.Renew46.P38.BlockProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite operator matrix acting on the Hilbert direct sum. -/
def blockRaw (A : Matrix ι ι (Operators H)) :
    Operators (PiLp 2 (fun _ : ι => H)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j, (A i j).comp (PiLp.proj 2 (fun _ : ι => H) j))

omit [DecidableEq ι] [CompleteSpace H] in
@[simp] lemma blockRaw_apply (A : Matrix ι ι (Operators H))
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    blockRaw A z i = ∑ j, A i j (z j) := by
  simp [blockRaw]

omit [DecidableEq ι] in
lemma blockRaw_star (A : Matrix ι ι (Operators H)) :
    blockRaw (star A) = star (blockRaw A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  simp only [PiLp.inner_apply, blockRaw_apply, Matrix.star_apply, sum_inner,
    inner_sum, ContinuousLinearMap.star_eq_adjoint, adjoint_inner_left]
  rw [Finset.sum_comm]

/-- Faithful unital star-algebra realization; the domain needs no C*-matrix norm. -/
def block : Matrix ι ι (Operators H) →⋆ₐ[ℂ]
    Operators (PiLp 2 (fun _ : ι => H)) where
  toFun := blockRaw
  map_zero' := by
    ext z i
    simp
  map_add' A B := by
    ext z i
    simp [Finset.sum_add_distrib]
  map_one' := by
    ext z i
    simp only [blockRaw_apply, Matrix.one_apply, one_apply_eq_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_mul' A B := by
    ext z i
    simp only [blockRaw_apply, Matrix.mul_apply, sum_apply,
      mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    ext z i
    simp only [blockRaw_apply, Matrix.algebraMap_matrix_apply, ContinuousLinearMap.algebraMap_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_star' := blockRaw_star

@[simp] lemma block_apply (A : Matrix ι ι (Operators H))
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (block (ι := ι) (H := H)) A z i = ∑ j, A i j (z j) := blockRaw_apply A z i

@[simp] lemma block_single (A : Matrix ι ι (Operators H)) (j i : ι) (u : H) :
    (block (ι := ι) (H := H)) A (PiLp.single 2 j u) i = A i j u := by
  simp [block_apply, PiLp.single_apply, apply_ite]

theorem block_injective : Function.Injective
    (block : Matrix ι ι (Operators H) →⋆ₐ[ℂ] Operators (PiLp 2 (fun _ : ι => H))) := by
  intro A B h
  ext i j u
  simpa only [block_single] using congrArg (fun T : Operators (PiLp 2 (fun _ : ι => H)) =>
    T (PiLp.single 2 j u) i) h

/-- The diagonal realization from the finite product C*-algebra. -/
def diagonalHom : (ι → Operators H) →⋆ₐ[ℂ]
    Operators (PiLp 2 (fun _ : ι => H)) :=
  (block (ι := ι) (H := H)).comp { Matrix.diagonalAlgHom ℂ (n := ι) (α := Operators H) with
    map_star' := by
      intro x
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j; simp [Matrix.star_apply]
      · simp [Matrix.star_apply, hij, Ne.symm hij] }

@[simp] lemma diagonalHom_apply (x : ι → Operators H) :
    (diagonalHom (ι := ι) (H := H)) x = (block (ι := ι) (H := H)) (Matrix.diagonal x) := rfl

@[simp] lemma block_diagonal_apply (x : ι → Operators H)
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (block (ι := ι) (H := H)) (Matrix.diagonal x) z i = x i (z i) := by
  simp only [block_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Spectrum containment, valid also when the index type or Hilbert space is trivial. -/
theorem diagonal_spectrum_subset (x : ι → Operators H) :
    spectrum ℝ ((block (ι := ι) (H := H)) (Matrix.diagonal x)) ⊆ ⋃ i, spectrum ℝ (x i) := by
  have h := AlgHom.spectrum_apply_subset ((diagonalHom (ι := ι) (H := H)).restrictScalars ℝ) x
  change spectrum ℝ ((diagonalHom (ι := ι) (H := H)) x) ⊆ spectrum ℝ x at h
  simpa only [Pi.spectrum_eq, diagonalHom_apply] using h

theorem diagonal_isSelfAdjoint (x : ι → Operators H) (hx : ∀ i, IsSelfAdjoint (x i)) :
    IsSelfAdjoint ((block (ι := ι) (H := H)) (Matrix.diagonal x)) := by
  have h : IsSelfAdjoint x := by
    change star x = x
    funext i
    exact (hx i).star_eq
  exact h.map (diagonalHom (ι := ι) (H := H))

theorem InInterval_diagonal {I : Set ℝ} (x : ι → Operators H)
    (hx : ∀ i, InInterval I (x i)) : InInterval I ((block (ι := ι) (H := H)) (Matrix.diagonal x)) := by
  refine ⟨diagonal_isSelfAdjoint x (fun i => (hx i).1), ?_⟩
  exact (diagonal_spectrum_subset x).trans (Set.iUnion_subset (fun i => (hx i).2))

set_option backward.isDefEq.respectTransparency false in
/-- Continuous functional calculus acts coordinatewise on diagonal blocks. -/
theorem diagonal_cfc (f : ℝ → ℝ) (x : ι → Operators H)
    (hx : ∀ i, IsSelfAdjoint (x i))
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (x i))) :
    cfc f ((block (ι := ι) (H := H)) (Matrix.diagonal x)) =
      (block (ι := ι) (H := H)) (Matrix.diagonal (fun i => cfc f (x i))) := by
  have : ContinuousFunctionalCalculus ℝ (ι → Operators H) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := ι → Operators H)).toContinuousFunctionalCalculus
  have hsa : IsSelfAdjoint x := by
    change star x = x
    funext i
    exact (hx i).star_eq
  have hfc : ContinuousOn f (spectrum ℝ x) := by simpa only [Pi.spectrum_eq] using hf
  have h := (diagonalHom (ι := ι) (H := H)).map_cfc f x hfc
    (by fun_prop) hsa (diagonal_isSelfAdjoint x hx)
  rw [cfc_map_pi (S := ℂ) f x hf hsa hx] at h
  exact h.symm

/-- Positive operators remain positive under coordinate compression. -/
theorem diagonal_le_of_block_le {A B : Matrix ι ι (Operators H)}
    (h : (block (ι := ι) (H := H)) A ≤ (block (ι := ι) (H := H)) B) (i : ι) : A i i ≤ B i i := by
  have hp : ((block (ι := ι) (H := H)) (B - A)).IsPositive := by
    simpa only [map_sub] using (ContinuousLinearMap.le_def _ _).mp h
  have hs : star (B - A) = B - A := block_injective (by
    rw [map_star, hp.isSelfAdjoint.star_eq])
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · have hh := congrArg (fun C : Matrix ι ι (Operators H) => C i i) hs
    change star (B i i - A i i) = B i i - A i i
    simpa only [Matrix.star_apply, Matrix.sub_apply] using hh
  · intro u
    have hh := hp.re_inner_nonneg_left (PiLp.single 2 i u)
    simp only [PiLp.inner_apply, block_single] at hh
    simpa [ContinuousLinearMap.reApplyInnerSelf, PiLp.single_apply,
      apply_ite] using hh

end QAlgorithms.Papers.Independent.Renew46.P38.BlockProof


/- Direct helper source: JENS8_Doubling.lean -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P38.FixedSpaceProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma eq_zero_of_inner_hilbertBasis {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H)
    (h : ∀ i, inner ℂ (b i) x = 0) : x = 0 := by
  apply b.repr.injective
  ext i
  simpa [HilbertBasis.repr_apply_apply] using h i

def doubleFamily {ι : Type*} (b : HilbertBasis ι ℂ H) : ι ⊕ ι → HilbertPower H 2 :=
  Sum.elim (fun i => PiLp.single 2 (0 : Fin 2) (b i))
    (fun i => PiLp.single 2 (1 : Fin 2) (b i))

omit [CompleteSpace H] in
lemma doubleFamily_orthonormal {ι : Type*} (b : HilbertBasis ι ℂ H) :
    Orthonormal ℂ (doubleFamily b) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i <;> cases j <;>
    simp [doubleFamily, PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply,
      orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace H] in
lemma doubleFamily_total {ι : Type*} (b : HilbertBasis ι ℂ H) :
    (Submodule.span ℂ (Set.range (doubleFamily b)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  ext j
  fin_cases j
  · apply eq_zero_of_inner_hilbertBasis b
    intro i
    have hm : doubleFamily b (Sum.inl i) ∈
        Submodule.span ℂ (Set.range (doubleFamily b)) := Submodule.subset_span ⟨_, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal hm hz
    simpa [doubleFamily, PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply] using h
  · apply eq_zero_of_inner_hilbertBasis b
    intro i
    have hm : doubleFamily b (Sum.inr i) ∈
        Submodule.span ℂ (Set.range (doubleFamily b)) := Submodule.subset_span ⟨_, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal hm hz
    simpa [doubleFamily, PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply] using h

def doubleBasis {ι : Type*} (b : HilbertBasis ι ℂ H) :
    HilbertBasis (ι ⊕ ι) ℂ (HilbertPower H 2) :=
  HilbertBasis.mkOfOrthogonalEqBot (doubleFamily_orthonormal b) (doubleFamily_total b)

lemma exists_double_equiv (hH : ¬ FiniteDimensional ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] HilbertPower H 2) := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  have hi : Infinite ι := by
    apply not_finite_iff_infinite.mp
    intro hfin
    let := Fintype.ofFinite ι
    exact hH b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  let := hi
  have hcard : Cardinal.mk (ι ⊕ ι) = Cardinal.mk ι := by
    simpa only [Cardinal.mk_sum, Cardinal.lift_id] using
      Cardinal.add_eq_self (Cardinal.aleph0_le_mk ι)
  let e : (ι ⊕ ι) ≃ ι := Classical.choice (Cardinal.eq.mp hcard)
  have hr : Set.range ((b : ι → H) ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by simp⟩
  let b' : HilbertBasis (ι ⊕ ι) ℂ H :=
    HilbertBasis.mk (b.orthonormal.comp e e.injective) (by rw [hr, b.dense_span])
  exact ⟨b'.repr.trans (doubleBasis b).repr.symm⟩

end QAlgorithms.Papers.Independent.Renew46.P38.FixedSpaceProof


/- Direct helper source: JENS8_Elementary.lean -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace QAlgorithms.Papers.Independent.Renew46.P38.FixedTupleProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma unital_of_le (I : Set ℝ) (f : ℝ → ℝ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hJ : UnitalJensenOn H I f n) : UnitalJensenOn H I f m := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro x a hx ha
  let xx : Fin (m+r) → Operators H := Fin.addCases x (fun _ => x ⟨0, hm⟩)
  let aa : Fin (m+r) → Operators H := Fin.addCases a (fun _ => 0)
  have hxx : ∀ i, InInterval I (xx i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [xx] using hx j
    · simpa [xx] using hx ⟨0, hm⟩
  have haa : columnSquares aa = 1 := by
    simpa [columnSquares, aa, Fin.sum_univ_add] using ha
  have h := hJ xx aa hxx haa
  simpa [combination, xx, aa, Fin.sum_univ_add] using h

lemma scalar_sandwich (t : ℝ) (ht : 0 ≤ t) (x : Operators H) :
    star (Real.sqrt t • (1 : Operators H)) * x * (Real.sqrt t • 1) = t • x := by
  simp [star_smul, smul_smul, Real.mul_self_sqrt ht]

lemma scalar_square (t : ℝ) (ht : 0 ≤ t) :
    star (Real.sqrt t • (1 : Operators H)) * (Real.sqrt t • 1) = t • 1 := by
  simpa using scalar_sandwich (H := H) t ht 1

lemma unital_two_convex (I : Set ℝ) (f : ℝ → ℝ)
    (hJ : UnitalJensenOn H I f 2) : ConvexOnOperators H I f := by
  intro x y hx hy t ht ht1
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have ha : columnSquares ![Real.sqrt t • (1 : Operators H), Real.sqrt (1-t) • 1] = 1 := by
    simp only [columnSquares, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      scalar_square t ht, scalar_square (1-t) h1t]
    rw [← add_smul]
    simp
  have h := hJ ![x,y] ![Real.sqrt t • 1,Real.sqrt (1-t) • 1]
    (by intro i; fin_cases i <;> assumption) ha
  simpa only [combination, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, scalar_sandwich t ht, scalar_sandwich (1-t) h1t] using h

end QAlgorithms.Papers.Independent.Renew46.P38.FixedTupleProof


/- Direct helper source: JENS8_Compression.lean -/

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
open ContinuousLinearMap
set_option backward.isDefEq.respectTransparency false

namespace QAlgorithms.Papers.Independent.Renew46.P38.FixedSpaceProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A two-entry column, with real coefficients acting on the original Hilbert space. -/
def twoColumn (r s : ℝ) : H →L[ℂ] HilbertPower H 2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![r • (1 : Operators H), s • 1])

omit [CompleteSpace H] in
@[simp] lemma twoColumn_apply_zero (r s : ℝ) (x : H) : twoColumn r s x 0 = r • x := by
  simp [twoColumn]

omit [CompleteSpace H] in
@[simp] lemma twoColumn_apply_one (r s : ℝ) (x : H) : twoColumn r s x 1 = s • x := by
  simp [twoColumn]

lemma twoColumn_adjoint_apply (r s : ℝ) (z : HilbertPower H 2) :
    (twoColumn r s).adjoint z = r • z 0 + s • z 1 := by
  apply ext_inner_right ℂ
  intro x
  rw [adjoint_inner_left]
  simp [PiLp.inner_apply, Fin.sum_univ_two, inner_add_left]

lemma twoColumn_isometry (r s : ℝ) (hrs : r*r+s*s=1) :
    (twoColumn (H := H) r s).adjoint.comp (twoColumn r s) = 1 := by
  ext x
  simp only [comp_apply, twoColumn_adjoint_apply, twoColumn_apply_zero, twoColumn_apply_one,
    smul_smul, ← add_smul, hrs, one_smul, one_apply_eq_self]

lemma twoColumn_diagonal (r s : ℝ) (x y : Operators H) :
    (twoColumn (H := H) r s).adjoint.comp
      (((BlockProof.block (ι := Fin 2) (H := H)) (Matrix.diagonal ![x,y])).comp
        (twoColumn r s)) = (r*r) • x + (s*s) • y := by
  ext z
  simp [twoColumn_adjoint_apply, smul_smul]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma pulled_column_square (e : H ≃ₗᵢ[ℂ] K) (C : H →L[ℂ] K) :
    star ((e.symm : K →L[ℂ] H).comp C) * ((e.symm : K →L[ℂ] H).comp C) =
      C.adjoint.comp C := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  ext z
  simp

lemma pulled_column_compression (e : H ≃ₗᵢ[ℂ] K) (C : H →L[ℂ] K) (D : Operators K) :
    star ((e.symm : K →L[ℂ] H).comp C) * e.symm.conjStarAlgEquiv D *
      ((e.symm : K →L[ℂ] H).comp C) = C.adjoint.comp (D.comp C) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  ext z
  simp

lemma conj_inInterval (e : K ≃ₗᵢ[ℂ] H) (I : Set ℝ) (D : Operators K)
    (hD : InInterval I D) : InInterval I (e.conjStarAlgEquiv D) := by
  refine ⟨hD.1.map e.conjStarAlgEquiv, ?_⟩
  exact (AlgHom.spectrum_apply_subset
    (e.conjStarAlgEquiv.toAlgEquiv.toAlgHom.restrictScalars ℝ) D).trans hD.2

lemma conj_cfc (e : K ≃ₗᵢ[ℂ] H) (D : Operators K) (hD : IsSelfAdjoint D)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ D)) :
    cfc f (e.conjStarAlgEquiv D) = e.conjStarAlgEquiv (cfc f D) := by
  exact (StarAlgHomClass.map_cfc e.conjStarAlgEquiv f D hf (by fun_prop)
    hD (hD.map e.conjStarAlgEquiv)).symm

lemma one_term_convex (I : Set ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f I)
    (hH : ¬ FiniteDimensional ℂ H) (hJ : UnitalJensenOn H I f 1) :
    ConvexOnOperators H I f := by
  obtain ⟨e⟩ := exists_double_equiv hH
  intro x y hx hy t ht ht1
  let r := Real.sqrt t
  let s := Real.sqrt (1-t)
  have h1t : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hrr : r*r=t := Real.mul_self_sqrt ht
  have hss : s*s=1-t := Real.mul_self_sqrt h1t
  have hrs : r*r+s*s=1 := by rw [hrr,hss]; ring
  let D := (BlockProof.block (ι := Fin 2) (H := H)) (Matrix.diagonal ![x,y])
  have hD : InInterval I D := BlockProof.InInterval_diagonal ![x,y]
    (by intro i; fin_cases i <;> assumption)
  let v : Operators H := (e.symm : HilbertPower H 2 →L[ℂ] H).comp (twoColumn r s)
  let A : Operators H := e.symm.conjStarAlgEquiv D
  have hv : star v * v = 1 := by
    dsimp only [v]
    rw [pulled_column_square, twoColumn_isometry r s hrs]
  have hA : InInterval I A := conj_inInterval e.symm I D hD
  have h := hJ (fun _ => A) (fun _ => v) (fun _ => hA)
    (by simpa [columnSquares] using hv)
  have hleft : star v * A * v = t • x+(1-t) • y := by
    dsimp only [v,A]
    rw [pulled_column_compression]
    simpa only [D,hrr,hss] using twoColumn_diagonal r s x y
  have hfcD : cfc f D =
      (BlockProof.block (ι := Fin 2) (H := H)) (Matrix.diagonal ![cfc f x,cfc f y]) := by
    have hc := BlockProof.diagonal_cfc f ![x,y]
      (by intro i; fin_cases i; exact hx.1; exact hy.1)
      (hf.mono (Set.iUnion_subset fun i => by fin_cases i; exact hx.2; exact hy.2))
    have hvec : (fun i : Fin 2 => cfc f (![x,y] i)) = ![cfc f x,cfc f y] := by
      ext i; fin_cases i <;> rfl
    simpa only [D,hvec] using hc
  have hright : star v * cfc f A * v = t • cfc f x+(1-t) • cfc f y := by
    dsimp only [A,v]
    rw [conj_cfc e.symm D hD.1 f (hf.mono hD.2),pulled_column_compression,hfcD]
    simpa only [hrr,hss] using twoColumn_diagonal r s (cfc f x) (cfc f y)
  simpa only [combination, Fin.sum_univ_one, hleft, hright] using h

end QAlgorithms.Papers.Independent.Renew46.P38.FixedSpaceProof


open QAlgorithms.Papers.Independent.Renew46.P38
universe u

/-- Hansen–Pedersen, Remark 2.2: fixed-tuple and fixed-space one-term Jensen implications. -/
theorem solution (I : Set ℝ) (f : ℝ → ℝ)
    (_hI : Set.OrdConnected I) (hf : ContinuousOn f I)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    (∀ n : ℕ, 2 ≤ n → UnitalJensenOn H I f n → ConvexOnOperators H I f) ∧
    ((¬ FiniteDimensional ℂ H) → UnitalJensenOn H I f 1 → ConvexOnOperators H I f) ∧
    (∀ n : ℕ, 1 ≤ n → UnitalJensenOn H I f n → UnitalJensenOn H I f 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hJ
    exact FixedTupleProof.unital_two_convex I f
      (FixedTupleProof.unital_of_le I f (by decide : 1 ≤ 2) hn hJ)
  · intro hH hJ
    exact FixedSpaceProof.one_term_convex I f hf hH hJ
  · intro n hn hJ
    exact FixedTupleProof.unital_of_le I f (by decide : 1 ≤ 1) hn hJ
