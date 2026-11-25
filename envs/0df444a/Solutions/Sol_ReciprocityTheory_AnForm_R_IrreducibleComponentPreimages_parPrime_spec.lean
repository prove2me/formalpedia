-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.parPrime_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:19.98068+00:00
-- url     : https://prove2.me/submissions/bc7e9cb5-c482-48b5-bae3-d246563984ad

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params


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
theorem _root_.solution (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n) :
    (parPrime (S := S) f i).IsPrime ∧ parPrime (S := S) f i ≤ p ∧ f i ∈ parPrime (S := S) f i := by
  have hp := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hP : (Ideal.span {algebraMap A S (f i)}).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨Ideal.comap_isPrime _ _, ?_, Ideal.mem_comap.mpr (Ideal.subset_span rfl)⟩
  intro a ha
  have hle : Ideal.span {algebraMap A S (f i)} ≤ maximalIdeal S := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hrsp.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  have := hle (Ideal.mem_comap.mp ha)
  have h2 : (maximalIdeal S).comap (algebraMap A S) = p :=
    IsLocalization.AtPrime.under_maximalIdeal S p
  rw [← Ideal.mem_comap, h2] at this
  exact this
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
