-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.comp_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:18.545627+00:00
-- url     : https://prove2.me/submissions/70601c49-a9ac-4b31-bcee-db89a6b016e2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_closure_fromSpec_mem_compsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_of_mem_compsH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
section Br
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}
private lemma fromSpec_mem_zeroLocus_iff_subset {V : W.Opens} (hV : IsAffineOpen V) (s : Set Γ(W, V))
    (P : PrimeSpectrum Γ(W, V)) : hV.fromSpec P ∈ W.zeroLocus s ↔ s ⊆ P.asIdeal := by
  show P ∈ hV.fromSpec ⁻¹' W.zeroLocus s ↔ _
  rw [hV.fromSpec_preimage_zeroLocus]
  exact Iff.rfl
private lemma fromSpec_specializes_iff_le {V : W.Opens} (hV : IsAffineOpen V) (P Q : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ⤳ hV.fromSpec Q ↔ P ≤ Q := by
  exact hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes P Q).symm
private lemma fromSpec_mem_of_isAffineOpen' {V : W.Opens} (hV : IsAffineOpen V) (P : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ∈ V := by
  show _ ∈ (V : Set W)
  rw [← hV.range_fromSpec]
  exact Set.mem_range_self P
private lemma exists_fromSpec_eq_of_mem {V : W.Opens} (hV : IsAffineOpen V) {z : W} (hz : z ∈ V) :
    ∃ P : PrimeSpectrum Γ(W, V), hV.fromSpec P = z := by
  rw [← SetLike.mem_coe, ← hV.range_fromSpec] at hz
  exact hz
private lemma supp_lemma_5 (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i})
    (P : PrimeSpectrum Γ(W, U)) :
    hU.fromSpec P ∈ (Z.support : Set W) ↔ ∃ i ∈ J, f i ∈ P.asIdeal := by
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) (fromSpec_mem_of_isAffineOpen' hU P),
    hZU, fromSpec_mem_zeroLocus_iff_subset, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
  haveI := P.isPrime
  exact Ideal.IsPrime.prod_mem_iff
end Br
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (hq : ParPrimes hU hy f q)
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {C : Set W}
    (hC : C ∈ compsH (Z.support : Set W)) (hyC : y ∈ C) :
    ∃ i ∈ J, C = closure {hU.fromSpec (q i)} := by
  have hCcl := isClosed_of_mem_compsH Z.support.isClosed hC
  have hK := hC.1.1.isGenericPoint_genericPoint hCcl
  generalize hC.1.1.genericPoint = η at hK
  have hηy : η ⤳ y := hK.specializes hyC
  obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem hU (hηy.mem_open U.isOpen hy)
  have hPy : P ≤ hU.primeIdealOf ⟨y, hy⟩ := by
    rw [← fromSpec_specializes_iff_le hU, hP, hU.fromSpec_primeIdealOf]
    exact hηy
  have hηs : hU.fromSpec P ∈ (Z.support : Set W) := by
    rw [hP]
    exact hC.1.2 hK.mem
  obtain ⟨i, hi, hfi⟩ := (supp_lemma_5 hZU P).1 hηs
  have hqi : q i ≤ P := (hq.2.2.1 i P hPy).1 hfi
  refine ⟨i, hi, ?_⟩
  have hmem := closure_fromSpec_mem_compsH hq hZU hi
  have hsub : C ⊆ closure {hU.fromSpec (q i)} := by
    have hK' : closure {η} = C := hK
    rw [← hK']
    refine closure_minimal ?_ isClosed_closure
    rw [Set.singleton_subset_iff, ← hP, ← specializes_iff_mem_closure]
    exact (fromSpec_specializes_iff_le hU _ _).2 hqi
  exact le_antisymm hsub (hC.2 hmem.1 hsub)
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
