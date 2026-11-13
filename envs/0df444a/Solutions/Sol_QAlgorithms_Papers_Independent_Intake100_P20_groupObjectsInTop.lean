-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInTop
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:21:18.279922+00:00
-- url     : https://prove2.me/submissions/c33866e1-3628-44a3-bd52-f56f4bb33f34

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 3: group objects in Top are precisely topological groups, with
identical topology and operations. No separation axiom is imposed. -/
theorem solution {G : Type u} [TopologicalSpace G] (D : GroupMaps G) :
    GroupObjectInTop D ↔
      ∃ h : GroupDiagrams D,
        letI : Group G := groupOfMaps D h
        IsTopologicalGroup G := by
  constructor
  · rintro ⟨h,hm,he,hi⟩
    refine ⟨h,?_⟩
    letI : Group G := groupOfMaps D h
    exact { continuous_mul := hm, continuous_inv := hi }
  · rintro ⟨h,hT⟩
    letI : Group G := groupOfMaps D h
    letI : IsTopologicalGroup G := hT
    exact ⟨h,continuous_mul,continuous_const,continuous_inv⟩
