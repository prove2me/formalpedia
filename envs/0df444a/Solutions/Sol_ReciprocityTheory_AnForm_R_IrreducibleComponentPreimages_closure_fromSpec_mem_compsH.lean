-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.closure_fromSpec_mem_compsH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:42.317866+00:00
-- url     : https://prove2.me/submissions/afb46b06-4fe6-4a59-8513-f9d50f49b597

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
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
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {i : Fin n} (hi : i ∈ J) :
    closure {hU.fromSpec (q i)} ∈ compsH (Z.support : Set W) := by
  have hxs : hU.fromSpec (q i) ∈ (Z.support : Set W) := (supp_lemma_5 hZU (q i)).2 ⟨i, hi, hq.2.1 i⟩
  have hsub : closure {hU.fromSpec (q i)} ⊆ (Z.support : Set W) :=
    Z.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hxs)
  refine ⟨⟨isIrreducible_singleton.closure, hsub⟩, fun C hC hle => ?_⟩
  obtain ⟨hCirr, hCsub⟩ := hC
  have hK := hCirr.closure.isGenericPoint_genericPoint isClosed_closure
  generalize hCirr.closure.genericPoint = η at hK
  have hxK : hU.fromSpec (q i) ∈ closure C := subset_closure (hle (subset_closure (Set.mem_singleton _)))
  have hηx : η ⤳ hU.fromSpec (q i) := hK.specializes hxK
  obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem hU (hηx.mem_open U.isOpen (fromSpec_mem_of_isAffineOpen' hU (q i)))
  have hPq : P ≤ q i := by
    rw [← fromSpec_specializes_iff_le hU, hP]
    exact hηx

  have hηs : hU.fromSpec P ∈ (Z.support : Set W) := by
    rw [hP]
    exact Z.support.isClosed.closure_subset_iff.2 hCsub hK.mem
  obtain ⟨j, hj, hfj⟩ := (supp_lemma_5 hZU P).1 hηs
  have hqj : q j ≤ P := (hq.2.2.1 j P (le_trans hPq (hq.1 i))).1 hfj
  have hji : j = i := hq.2.2.2 i j ((hqj.trans hPq) (hq.2.1 j))
  rw [hji] at hqj
  have hPe : P = q i := le_antisymm hPq hqj
  have hK' : closure {η} = closure C := hK
  rw [← hP, hPe] at hK'
  rw [hK']
  exact subset_closure
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
