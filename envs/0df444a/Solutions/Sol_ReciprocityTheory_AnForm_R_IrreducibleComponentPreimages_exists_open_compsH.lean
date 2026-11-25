-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_open_compsH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:17.621921+00:00
-- url     : https://prove2.me/submissions/9fb98356-0ee2-4390-af04-3ed9889a59f7

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_parPrimes
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_fromSpec_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_comp_eq_closure
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isBranch_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_sUnion_compsH_not
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_of_mem_compsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_sUnion_compsH

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
private lemma exists_fromSpec_eq_of_mem {V : W.Opens} (hV : IsAffineOpen V) {z : W} (hz : z ∈ V) :
    ∃ P : PrimeSpectrum Γ(W, V), hV.fromSpec P = z := by
  rw [← SetLike.mem_coe, ← hV.range_fromSpec] at hz
  exact hz
end Br
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ compsH (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranchH (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp

  have hB : IsClosed (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D}) :=
    isClosed_sUnion_compsH_not Z.support.isClosed y
  have hBf : IsClosed (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D}) :=
    isClosed_iUnion_of_finite (fun i => isClosed_sUnion_compsH_not (W.zeroLocus_isClosed _) y)
  let O : W.Opens := ⟨(U.1 : Set W) ∩ (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D})ᶜ ∩
      (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D})ᶜ,
    (U.1.isOpen.inter hB.isOpen_compl).inter hBf.isOpen_compl⟩
  have hyB : y ∉ ⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D} := by
    rintro ⟨D, ⟨-, hyD⟩, hyD'⟩
    exact hyD hyD'
  have hyBf : y ∉ ⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D} := by
    rw [Set.mem_iUnion]
    rintro ⟨i, D, ⟨-, hyD⟩, hyD'⟩
    exact hyD hyD'
  refine ⟨O, ⟨⟨hy, hyB⟩, hyBf⟩, fun z hz => hz.1.1, ?_⟩
  intro C hC
  ext z
  constructor
  · rintro ⟨hzC, hzO⟩
    have hyC : y ∈ C := by
      by_contra hyC
      exact hzO.1.2 ⟨C, ⟨hC, hyC⟩, hzC⟩
    obtain ⟨i, hi, rfl⟩ := comp_eq_closure hq hZU hC hyC
    refine ⟨hzO, i, hi, (isBranch_iff hq hZU hi _).2 rfl, ?_⟩
    exact closure_minimal (Set.singleton_subset_iff.2 (fromSpec_mem_zeroLocus hq i))
      (W.zeroLocus_isClosed _) hzC
  · rintro ⟨hzO, i, hi, hbr, hzf⟩
    refine ⟨?_, hzO⟩
    rw [(isBranch_iff hq hZU hi C).1 hbr]
    have hzE : z ∈ ⋃₀ compsH (W.zeroLocus {f i}) := by
      rw [sUnion_compsH]
      exact hzf
    obtain ⟨E, hE, hzE⟩ := hzE
    have hyE : y ∈ E := by
      by_contra hyE
      exact hzO.2 (Set.mem_iUnion.2 ⟨i, E, ⟨hE, hyE⟩, hzE⟩)
    have hK := hE.1.1.isGenericPoint_genericPoint (isClosed_of_mem_compsH (W.zeroLocus_isClosed _) hE)
    generalize hE.1.1.genericPoint = ζ at hK
    have hζy : ζ ⤳ y := hK.specializes hyE
    obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem U.2 (hζy.mem_open U.1.isOpen hy)
    have hPy : P ≤ U.2.primeIdealOf ⟨y, hy⟩ := by
      rw [← fromSpec_specializes_iff_le U.2, hP, U.2.fromSpec_primeIdealOf]
      exact hζy
    have hζf : U.2.fromSpec P ∈ W.zeroLocus {f i} := by
      rw [hP]
      exact hE.1.2 hK.mem
    have hfP : f i ∈ P.asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f i} P).1 hζf)
    have h1 : U.2.fromSpec (q i) ⤳ ζ := by
      rw [← hP]
      exact (fromSpec_specializes_iff_le U.2 _ _).2 ((hq.2.2.1 i P hPy).1 hfP)
    exact specializes_iff_mem_closure.1 (h1.trans (hK.specializes hzE))
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
