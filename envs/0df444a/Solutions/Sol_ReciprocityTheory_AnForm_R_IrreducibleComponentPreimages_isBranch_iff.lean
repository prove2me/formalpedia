-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isBranch_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:40.727574+00:00
-- url     : https://prove2.me/submissions/f00581e3-d8a6-4e3f-a1d3-752051987376

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_gp_closure_singleton
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_fromSpec_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_fromSpec_specializes
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_closure_fromSpec_mem_compsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_comp_eq_closure
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
private lemma fromSpec_mem_of_isAffineOpen' {V : W.Opens} (hV : IsAffineOpen V) (P : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ∈ V := by
  show _ ∈ (V : Set W)
  rw [← hV.range_fromSpec]
  exact Set.mem_range_self P
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
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {i : Fin n} (hi : i ∈ J) (C : Set W) :
    IsBranchH (Z.support : Set W) (f i) y C ↔ C = closure {hU.fromSpec (q i)} := by
  constructor
  · rintro ⟨hC, hyC, hirr, -, hgz⟩
    obtain ⟨j, -, rfl⟩ := comp_eq_closure hq hZU hC hyC
    rw [gp_closure_singleton hirr] at hgz
    have hfi : f i ∈ (q j).asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset hU {f i} (q j)).1 hgz)
    rw [hq.2.2.2 j i hfi]
  · rintro rfl
    refine ⟨closure_fromSpec_mem_compsH hq hZU hi,
      specializes_iff_mem_closure.1 (fromSpec_specializes hq i), isIrreducible_singleton.closure, ?_, ?_⟩
    · rw [gp_closure_singleton]
      exact fromSpec_mem_of_isAffineOpen' hU _
    · rw [gp_closure_singleton]
      exact fromSpec_mem_zeroLocus hq i
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
