-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.length_ker_eq_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:59.590343+00:00
-- url     : https://prove2.me/submissions/3234b665-6c1d-4da1-bbec-ca097400a9b4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_KilledHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemCoboundariesOfCocycleProcyclic
import Definitions.Def_ReciprocityTheory_GroupCohomology_LengthKerEqCoker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Function
universe u
open ReciprocityTheory.Coh.ProcyclicCohomology
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] V) (h : IsFiniteLength R V) :
    Module.length R (LinearMap.ker f) = Module.length R (V ⧸ LinearMap.range f) := by
  have h1 : Module.length R V = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.injective_subtype _)
      f.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R V = Module.length R (LinearMap.range f) + Module.length R (V ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have hVt : Module.length R V ≠ ⊤ := Module.length_ne_top_iff.2 h
  have hL : Module.length R (LinearMap.range f) ≠ ⊤ := fun h' => hVt (by rw [h1, h', add_top])
  rw [h1, add_comm (Module.length R (LinearMap.range f))] at h2
  exact (WithTop.add_right_cancel hL h2)
end ReciprocityTheory.Coh.ProcyclicCohomology
