-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_smooth_mixed_flag_family
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T00:00:49.851251+00:00
-- url     : https://prove2.me/submissions/81cfcc5a-5c4c-46d6-8f97-c52b81846780

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_smooth_mixed_zero_locus
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedKernels

theorem surjective_mulVec_of_minor
    {K m n : Type*} [Field K] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n K) (e : m → n)
    (h : (A.submatrix id e).det ≠ 0) : Function.Surjective A.mulVec := by
  let B : Matrix n m K := fun k j => (Pi.single (e j) (1 : K) : n → K) k
  have hB : A * B = A.submatrix id e := by
    ext i j
    change (∑ k, A i k * B k j) = A i (e j)
    simp [B, Pi.single_apply]
  have hs : Function.Surjective (A * B).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hB]; exact isUnit_iff_ne_zero.mpr h))
  intro y
  obtain ⟨z,hz⟩ := hs y
  exact ⟨B.mulVec z, by simpa only [Matrix.mulVec_mulVec] using hz⟩

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

abbrev Rows (l : List M.FactorIndex) (i : M.FactorIndex) :=
  {j : Fin l.length // l[j] = i}

theorem card_rows (l : List M.FactorIndex) (i : M.FactorIndex) :
    Fintype.card (Rows M l i) = l.count i := by
  classical
  rw [Fintype.card_subtype]
  convert Fin.card_filter_univ_eq_vector_get_eq_count i
    (⟨l,rfl⟩ : List.Vector M.FactorIndex l.length) using 1
  · apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.Vector.get,
      List.get_eq_getElem, Fin.cast_refl, id_eq, Fin.getElem_fin]
  · rfl

def pivot (l : List M.FactorIndex)
    (h : ∀ i, l.count i ≤ M.ambientDimension i + 1) (i : M.FactorIndex) :
    Rows M l i ↪ Fin (M.ambientDimension i + 1) :=
  (Fintype.equivFin _).toEmbedding.trans
    (Fin.castLEEmb (by simpa only [card_rows] using h i))

def coeffMatrix (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (i : M.FactorIndex) :
    Matrix (Rows M l i) (Fin (M.ambientDimension i + 1)) K :=
  fun j k => c j.val ⟨i,k⟩

def minorPolynomial (l : List M.FactorIndex)
    (h : ∀ i, l.count i ≤ M.ambientDimension i + 1) (i : M.FactorIndex) :
    MvPolynomial (Fin l.length × M.Variable) K :=
  MvPolynomial.rename (fun jk : Rows M l i × Rows M l i =>
    (jk.1.val, ⟨i,pivot M l h i jk.2⟩))
    (Matrix.mvPolynomialX (Rows M l i) (Rows M l i) K).det

theorem minorPolynomial_ne_zero (l : List M.FactorIndex)
    (h : ∀ i, l.count i ≤ M.ambientDimension i + 1) (i : M.FactorIndex) :
    minorPolynomial M l h i ≠ 0 := by
  classical
  have hi : Function.Injective (fun jk : Rows M l i × Rows M l i =>
      (jk.1.val, (⟨i,pivot M l h i jk.2⟩ : M.Variable))) := by
    intro a b hab
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hab)
    · apply (pivot M l h i).injective
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hab)).2
  exact fun heq => Matrix.det_mvPolynomialX_ne_zero (Rows M l i) K
    ((MvPolynomial.rename_eq_zero_iff_of_injective _ hi).mp heq)

theorem eval_minorPolynomial (l : List M.FactorIndex)
    (h : ∀ i, l.count i ≤ M.ambientDimension i + 1) (i : M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    MvPolynomial.eval (Function.uncurry c) (minorPolynomial M l h i) =
      ((coeffMatrix M l c i).submatrix id (pivot M l h i)).det := by
  simp only [minorPolynomial, MvPolynomial.eval_rename]
  rw [Matrix.eval_det_mvPolynomialX]
  rfl

def blockKernel (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (i : M.FactorIndex) :
    Submodule K (Fin (M.ambientDimension i + 1) → K) :=
  (coeffMatrix M l c i).mulVecLin.ker

theorem exists_principal_open_kernel_dimensions (l : List M.FactorIndex)
    (h : ∀ i, l.count i ≤ M.ambientDimension i + 1) :
    ∃ H : MvPolynomial (Fin l.length × M.Variable) K, H ≠ 0 ∧
      ∀ c : Fin l.length → M.Variable → K,
        MvPolynomial.eval (Function.uncurry c) H ≠ 0 →
        ∀ i, Module.finrank K (blockKernel M l c i) + l.count i =
          M.ambientDimension i + 1 := by
  classical
  refine ⟨∏ i, minorPolynomial M l h i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => minorPolynomial_ne_zero M l h i)
  · intro c hc i
    have hm : MvPolynomial.eval (Function.uncurry c) (minorPolynomial M l h i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hc) i (Finset.mem_univ i)
    rw [eval_minorPolynomial] at hm
    have hs : Function.Surjective (coeffMatrix M l c i).mulVecLin :=
      surjective_mulVec_of_minor _ _ hm
    have hd := (coeffMatrix M l c i).mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi,
      Module.finrank_pi, Fintype.card_fin, card_rows] at hd
    exact (Nat.add_comm _ _).trans hd

theorem row_at_representative (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (i : M.FactorIndex)
    (j : Rows M l i) (x : M.Point) :
    ((coeffMatrix M l c i).mulVecLin (x i).rep) j =
      M.eval (MixedFlag.polynomial M l c j.val) x := by
  rcases j with ⟨j,hj⟩
  subst i
  simp [coeffMatrix, Matrix.mulVec, dotProduct, MultiProjectiveSpace.eval,
    MultiProjectiveSpace.coordinate, MixedFlag.polynomial, MixedFlag.rowForm,
    map_sum]

theorem linearSlice_blockKernel (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (W : Set M.Point) :
    linearSlice M W (blockKernel M l c) =
      {x : M.Point | x ∈ W ∧ ∀ j : Fin l.length,
        M.eval (MixedFlag.polynomial M l c j) x = 0} := by
  ext x
  change (x ∈ W ∧ ∀ i, (x i).rep ∈ blockKernel M l c i) ↔ _
  apply and_congr_right
  intro _
  constructor
  · intro hx j
    have hj := congrFun (hx l[j]) (⟨j,rfl⟩ : Rows M l l[j])
    simpa only [row_at_representative, Pi.zero_apply] using hj
  · intro hx i
    apply funext
    intro j
    simpa only [row_at_representative, Pi.zero_apply] using hx j.val

theorem exists_block_list (α : M.FactorIndex → ℕ) :
    ∃ l : List M.FactorIndex, ∀ i, l.count i = α i := by
  classical
  let s : Multiset M.FactorIndex := ∑ i, Multiset.replicate (α i) i
  refine ⟨s.toList, ?_⟩
  intro i
  rw [← Multiset.coe_count, Multiset.coe_toList]
  simp [s, Multiset.count_sum', Multiset.count_replicate]

end PhilipponMultiplicity.MixedKernels

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem smooth_family_of_mixed_zero_locus
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hzero : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ l : List M.FactorIndex, (∀ i, l.count i = α i) ∧
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
              (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
              (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
              (∀ x : M.Point, x ∈ linearSlice M W L ↔ x ∈ W ∧
                ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0) ∧
              (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by
  classical
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨l,hcount⟩ := MixedKernels.exists_block_list M α
  have hbound : ∀ i, l.count i ≤ M.ambientDimension i + 1 := by
    intro i
    rw [hcount]
    exact Nat.le_succ_of_le (hα i)
  obtain ⟨F,hF,hgeom⟩ := hzero M W hW hirr α hα hdim B hB hBW hnonempty l hcount
  obtain ⟨H,hH,hker⟩ := MixedKernels.exists_principal_open_kernel_dimensions M l hbound
  refine ⟨l,hcount,F*H,mul_ne_zero hF hH,?_⟩
  intro c hc
  have hFH : MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      MvPolynomial.eval (Function.uncurry c) H ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hc
  obtain ⟨hfinite,hdisjoint,hsmooth⟩ := hgeom c hFH.1
  refine ⟨MixedKernels.blockKernel M l c,?_,?_,?_,?_,hsmooth⟩
  · intro i
    simpa only [hcount] using hker c hFH.2 i
  · simpa only [MixedKernels.linearSlice_blockKernel] using hfinite
  · simpa only [MixedKernels.linearSlice_blockKernel] using hdisjoint
  · intro x
    rw [MixedKernels.linearSlice_blockKernel]
    rfl

end PhilipponMultiplicity

end

end

set_option maxHeartbeats 1000000
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ l : List M.FactorIndex, (∀ i, l.count i = α i) ∧
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
              (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
              (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
              (∀ x : M.Point, x ∈ linearSlice M W L ↔ x ∈ W ∧
                ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0) ∧
              (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by
  exact smooth_family_of_mixed_zero_locus K hK
    (exists_principal_open_smooth_mixed_zero_locus K hK)
