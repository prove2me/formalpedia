-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_countableColimit
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:12:19.570313+00:00
-- url     : https://prove2.me/submissions/5967fd4c-5e9d-48c2-90f6-ff0bd7a00957

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Proposition C.5, PDF p. 38: countable colimits in Top are k-omega
when every object is k-omega. Countability concerns both objects and morphisms;
finite and empty diagrams are included. -/
theorem solution
    (J : Type u) [SmallCategory J] [Countable J]
    [Countable (Σ i : J, Σ j : J, (i ⟶ j))] (F : J ⥤ TopCat.{u})
    (hF : ∀ j, IsKOmega (F.obj j)) :
    IsKOmega (Limits.colimit F : TopCat.{u}) := by
  classical
  unfold IsKOmega at hF ⊢
  choose I hI K f hcov hopen using hF
  letI : ∀ j, Countable (I j) := hI
  refine ⟨(Σ j, I j), inferInstance, (fun a => K a.1 a.2),
    (fun a => (Limits.colimit.ι F a.1).hom.comp (f a.1 a.2)), ?_, ?_⟩
  · intro x
    obtain ⟨j,y,hy⟩ := Limits.Types.jointly_surjective_of_isColimit
      (Limits.isColimitOfPreserves (CategoryTheory.forget TopCat) (Limits.colimit.isColimit F)) x
    obtain ⟨i,z,hz⟩ := hcov j y
    refine ⟨⟨j,i⟩,z,?_⟩
    change (Limits.colimit.ι F j) (f j i z) = x
    rw [hz]
    exact hy
  · intro A
    constructor
    · intro h a
      exact h.preimage ((Limits.colimit.ι F a.1).hom.comp (f a.1 a.2)).continuous
    · intro h
      apply (TopCat.colimit_isOpen_iff F A).mpr
      intro j
      apply (hopen j _).mpr
      intro i
      exact h ⟨j,i⟩
