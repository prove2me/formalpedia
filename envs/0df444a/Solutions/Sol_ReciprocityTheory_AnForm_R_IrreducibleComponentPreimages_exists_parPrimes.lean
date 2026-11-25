-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_parPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:47.834744+00:00
-- url     : https://prove2.me/submissions/32f22989-e7ab-42d1-a892-02963cfee76a

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_eq_of_mem_parPrime
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_mem_iff_parPrime_le
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_parPrime_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {U : W.Opens} (hU : IsAffineOpen U) {y : W} (hy : y ∈ U) {n : ℕ}
    (f : Fin n → Γ(W, U)) [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U y hy (f i))) :
    ∃ q, ParPrimes hU hy f q := by
  letI : Algebra Γ(W, U) (W.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨y, hy⟩
  haveI : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  have hrsp' : FinalTheorems.Rsp (W.presheaf.stalk y) n
      (fun i => algebraMap Γ(W, U) (W.presheaf.stalk y) (f i)) := hrsp
  have hsp := fun i => parPrime_spec (A := Γ(W, U)) (S := W.presheaf.stalk y)
    (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i
  refine ⟨fun i => ⟨parPrime (S := W.presheaf.stalk y) f i, (hsp i).1⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hsp i).2.1
  · intro i
    exact (hsp i).2.2
  · intro i Q hQ
    haveI := Q.isPrime
    exact mem_iff_parPrime_le (A := Γ(W, U)) (S := W.presheaf.stalk y)
      (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i hQ
  · intro i j h
    exact eq_of_mem_parPrime (A := Γ(W, U)) (S := W.presheaf.stalk y) hrsp' h
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
