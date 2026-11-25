-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.branch_neH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:23.699731+00:00
-- url     : https://prove2.me/submissions/dfd3ee47-4d53-4e96-bdfe-b50b714c4bb6

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_eq_of_closure_singleton_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_parPrimes
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_fromSpec_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isBranch_iff
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
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hij : i ≠ j) {C C' : Set W} (hC : IsBranchH (Z.support : Set W) (f i) y C)
    (hC' : IsBranchH (Z.support : Set W) (f j) y C') : C ≠ C' := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp
  rw [(isBranch_iff hq hZU hi C).1 hC, (isBranch_iff hq hZU hj C').1 hC']
  intro heq
  have hx := eq_of_closure_singleton_eq heq
  have h2 := fromSpec_mem_zeroLocus hq j
  rw [← hx] at h2
  have hfj : f j ∈ (q i).asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f j} (q i)).1 h2)
  exact hij (hq.2.2.2 i j hfj).symm
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
