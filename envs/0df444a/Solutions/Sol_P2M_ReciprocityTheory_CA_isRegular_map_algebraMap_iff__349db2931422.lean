-- Prove2me | solution 1 for P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:00.70401+00:00
-- url     : https://prove2.me/submissions/11f6a30a-14ff-4c98-a7bd-e2993513e409

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution {S M : Type*} [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (rs : List R) :
    IsRegular M (rs.map (algebraMap R S)) ↔ IsRegular M rs := by
  open Pointwise in
  have key : ∀ l : List R,
      ((Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M)).restrictScalars R
        = Ideal.ofList l • (⊤ : Submodule R M) := by
    intro l
    induction l with
    | nil => simp
    | cons r l ih =>
      have ih' : ∀ y : M, y ∈ (Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M) ↔
          y ∈ Ideal.ofList l • (⊤ : Submodule R M) :=
        fun y => by rw [← ih, Submodule.restrictScalars_mem]
      have hr : ∀ y : M, y ∈ (algebraMap R S r) • (⊤ : Submodule S M) ↔
          y ∈ r • (⊤ : Submodule R M) := fun y => by
        simp [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]
      ext m
      simp only [List.map_cons, Ideal.ofList_cons, Submodule.sup_smul,
        Submodule.ideal_span_singleton_smul, Submodule.restrictScalars_mem, Submodule.mem_sup, ih', hr]
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h h'
    apply h
    apply Submodule.restrictScalars_injective R S M
    rw [key, Submodule.restrictScalars_top]
    exact h'
  · intro h h'
    apply h
    rw [← key, ← h', Submodule.restrictScalars_top]
end ReciprocityTheory.CA
