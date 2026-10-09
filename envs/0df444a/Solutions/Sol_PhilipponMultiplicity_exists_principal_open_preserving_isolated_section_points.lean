-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_preserving_isolated_section_points
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T15:06:39.157981+00:00
-- url     : https://prove2.me/submissions/b80cf344-7f56-43b2-ab86-9b1bd48737af

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_isolated_equation_points
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedKernels

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

def coeffMatrix (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (i : M.FactorIndex) :
    Matrix (Rows M l i) (Fin (M.ambientDimension i + 1)) K :=
  fun j k => c j.val ⟨i,k⟩

def blockKernel (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (i : M.FactorIndex) :
    Submodule K (Fin (M.ambientDimension i + 1) → K) :=
  (coeffMatrix M l c i).mulVecLin.ker

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

end MixedKernels
end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.SectionEquations

/-- A codimension-m subspace is the kernel of a surjective m-row matrix,
including the case in which there are no rows. -/
theorem exists_matrix_with_kernel
    {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (L : Submodule K (n → K))
    (hdim : Module.finrank K L + Fintype.card m = Fintype.card n) :
    ∃ A : Matrix m n K, Function.Surjective A.mulVecLin ∧ A.mulVecLin.ker = L := by
  classical
  have hq : Module.finrank K ((n → K) ⧸ L) = Module.finrank K (m → K) := by
    have h := L.finrank_quotient_add_finrank
    simp only [Module.finrank_pi] at h ⊢
    omega
  let e : ((n → K) ⧸ L) ≃ₗ[K] (m → K) := LinearEquiv.ofFinrankEq _ _ hq
  let f := e.toLinearMap.comp L.mkQ
  have hf : (LinearMap.toMatrix' f).mulVecLin = f := by
    apply LinearMap.ext
    intro v
    exact LinearMap.toMatrix'_mulVec f v
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · rw [hf]
    exact e.surjective.comp L.mkQ_surjective
  · rw [hf]
    ext v
    change e (L.mkQ v) = 0 ↔ v ∈ L
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero L

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Pack independent block matrices into one coefficient array, respecting
every repeated occurrence in an arbitrarily ordered block list. -/
theorem exists_coefficients_of_matrices (l : List M.FactorIndex)
    (A : ∀ i : M.FactorIndex,
      Matrix (MixedKernels.Rows M l i) (Fin (M.ambientDimension i + 1)) K) :
    ∃ c : Fin l.length → M.Variable → K,
      ∀ i, MixedKernels.coeffMatrix M l c i = A i := by
  classical
  let c : Fin l.length → M.Variable → K := fun j w =>
    if h : l[j] = w.1 then A w.1 ⟨j,h⟩ w.2 else 0
  refine ⟨c, ?_⟩
  intro i
  ext j k
  simp only [MixedKernels.coeffMatrix, c, dif_pos j.property]

/-- Every prescribed collection of subspaces can be recovered as the block
kernels of a coefficient array with the prescribed row ordering. -/
theorem exists_coefficients_with_block_kernels
    (l : List M.FactorIndex)
    (L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K))
    (hL : ∀ i, Module.finrank K (L i) + l.count i = M.ambientDimension i + 1) :
    ∃ c : Fin l.length → M.Variable → K,
      (∀ i, Function.Surjective (MixedKernels.coeffMatrix M l c i).mulVecLin) ∧
      MixedKernels.blockKernel M l c = L := by
  classical
  have hmat (i : M.FactorIndex) :
      ∃ A : Matrix (MixedKernels.Rows M l i) (Fin (M.ambientDimension i + 1)) K,
        Function.Surjective A.mulVecLin ∧ A.mulVecLin.ker = L i := by
    apply exists_matrix_with_kernel (L i)
    simpa only [MixedKernels.card_rows, Fintype.card_fin] using hL i
  choose A hsurj hker using hmat
  obtain ⟨c, hc⟩ := exists_coefficients_of_matrices M l A
  refine ⟨c, ?_, ?_⟩
  · intro i
    rw [hc]
    exact hsurj i
  · funext i
    change (MixedKernels.coeffMatrix M l c i).mulVecLin.ker = L i
    rw [hc]
    exact hker i

/-- The set-theoretic linear section agrees exactly with the common zero
locus of the constructed ordered equations. -/
theorem exists_equations_for_linear_slice
    (l : List M.FactorIndex)
    (L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K))
    (hL : ∀ i, Module.finrank K (L i) + l.count i = M.ambientDimension i + 1) :
    ∃ c : Fin l.length → M.Variable → K,
      ∀ W : Set M.Point,
        linearSlice M W L = {x : M.Point | x ∈ W ∧
          ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} := by
  obtain ⟨c, _, hc⟩ := exists_coefficients_with_block_kernels M l L hL
  refine ⟨c, fun W => ?_⟩
  rw [← hc]
  exact MixedKernels.linearSlice_blockKernel M l c W

/-- Any Zariski-open neighborhood of a coefficient point contains a principal
open whose polynomial is nonzero at that very point. -/
theorem exists_principal_neighborhood
    {σ : Type*} (a : σ → K)
    (U : Set (PrimeSpectrum (MvPolynomial σ K))) (hU : IsOpen U)
    (ha : (⟨MvPolynomial.vanishingIdeal K {a}, inferInstance⟩ :
      PrimeSpectrum (MvPolynomial σ K)) ∈ U) :
    ∃ F : MvPolynomial σ K, MvPolynomial.eval a F ≠ 0 ∧
      ∀ b : σ → K, MvPolynomial.eval b F ≠ 0 →
        (⟨MvPolynomial.vanishingIdeal K {b}, inferInstance⟩ :
          PrimeSpectrum (MvPolynomial σ K)) ∈ U := by
  obtain ⟨_, ⟨_, ⟨F, rfl⟩, rfl⟩, haF, hFU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open ha hU
  refine ⟨F, ?_, ?_⟩
  · simpa [PrimeSpectrum.mem_basicOpen, MvPolynomial.vanishingIdeal] using haF
  · intro b hb
    apply hFU
    simpa [PrimeSpectrum.mem_basicOpen, MvPolynomial.vanishingIdeal] using hb

end PhilipponMultiplicity.SectionEquations

end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem isolated_section_persistence_of_open_equation_persistence
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S, ∃ V : Set M.Point, @IsOpen _ M.zariskiTopology V ∧ x ∈ V ∧
        V ∩ {x : M.Point | x ∈ W ∧
          ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} ⊆ S) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0})) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  intro M W hW hirr α hα hdim L hL S hfinite hS hisolated l hl
  have hL' : ∀ i, Module.finrank K (L i) + l.count i = M.ambientDimension i + 1 := by
    intro i
    simpa only [hl] using hL i
  obtain ⟨c₀, hzero⟩ := SectionEquations.exists_equations_for_linear_slice M l L hL'
  have hS' : S ⊆ {x : M.Point | x ∈ W ∧
      ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} := by
    simpa only [hzero W] using hS
  have hisolated' : ∀ x ∈ S, ∃ V : Set M.Point,
      @IsOpen _ M.zariskiTopology V ∧ x ∈ V ∧
      V ∩ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} ⊆ S := by
    simpa only [hzero W] using hisolated
  obtain ⟨U, hU, hc₀, hgood⟩ :=
    hgeometry M W hW hirr α hα hdim l hl c₀ S hfinite hS' hisolated'
  obtain ⟨F, hF, hFU⟩ := SectionEquations.exists_principal_neighborhood
    (Function.uncurry c₀) U hU hc₀
  refine ⟨F, ?_, fun c hc => hgood c (hFU (Function.uncurry c) hc)⟩
  intro hz
  exact hF (by rw [hz, map_zero])

end PhilipponMultiplicity

end

end

set_option maxHeartbeats 1000000
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact isolated_section_persistence_of_open_equation_persistence K hK
    (exists_open_preserving_isolated_equation_points K hK)
