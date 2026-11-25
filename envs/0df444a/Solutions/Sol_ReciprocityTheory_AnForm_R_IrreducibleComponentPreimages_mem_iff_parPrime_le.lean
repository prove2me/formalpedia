-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.mem_iff_parPrime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:36.129474+00:00
-- url     : https://prove2.me/submissions/bb7a1441-f978-479d-912b-102d81ac4c2f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
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
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}
variable (S)
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n)
    {Q : Ideal A} [Q.IsPrime] (hQ : Q ≤ p) : f i ∈ Q ↔ parPrime (S := S) f i ≤ Q := by
  refine ⟨fun h => ?_, fun h => h (parPrime_spec (p := p) S hrsp i).2.2⟩
  have hdisj : Disjoint (p.primeCompl : Set A) Q := by
    rw [Set.disjoint_left]
    intro a ha haQ
    exact ha (hQ haQ)
  have hQ' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹Q.IsPrime› hdisj
  intro a ha
  rw [← hQ']
  show algebraMap A S a ∈ Q.map (algebraMap A S)
  have h1 : Ideal.span {algebraMap A S (f i)} ≤ Q.map (algebraMap A S) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ h
  exact h1 (Ideal.mem_comap.mp ha)
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
