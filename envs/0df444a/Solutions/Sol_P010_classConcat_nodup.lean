-- Prove2me | solution 1 for P010.classConcat_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:25.840792+00:00
-- url     : https://prove2.me/submissions/7d33d9b5-8711-4dc1-b768-a4fc604f872e

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_primeClass_toList_disjoint

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (ps : List ℕ) (hps : ps.Nodup) :
    (classConcat n ps).Nodup := by
  classical
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro p hp
    exact Finset.nodup_toList _
  · exact hps.imp (fun {_ _} hpq => primeClass_toList_disjoint n _ _ hpq)
end P010
