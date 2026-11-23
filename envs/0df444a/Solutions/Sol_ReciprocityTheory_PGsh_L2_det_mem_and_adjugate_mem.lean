-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.det_mem_and_adjugate_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:20.381383+00:00
-- url     : https://prove2.me/submissions/4845d95c-7fd2-443f-82cd-757e0b10f6eb

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) {X : Type} [Fintype X] [DecidableEq X]
    (F : Matrix X X (N → C)) (hF : ∀ i j, F i j ∈ AA.carrier) :
    (fun x => (F.map fun g => g x).det) ∈ AA.carrier ∧
      ∀ i j, (fun x => (F.map fun g => g x).adjugate i j) ∈ AA.carrier := by
  let F' : Matrix X X (hopfOrderSubgroup AA) := Matrix.of fun i j => ⟨F i j, hF i j⟩
  have hF' : F = (hopfOrderSubgroup AA).subtype.mapMatrix F' := Matrix.ext fun i j => rfl
  refine ⟨?_, fun i j => ?_⟩
  · have e : (fun x => (F.map fun g => g x).det) = F.det := by
      funext x
      exact ((Pi.evalRingHom (fun _ : N => C) x).map_det F).symm
    rw [e, hF', ← RingHom.map_det]
    exact (F'.det).2
  · have e : (fun x => (F.map fun g => g x).adjugate i j) = F.adjugate i j := by
      funext x
      have := (Pi.evalRingHom (fun _ : N => C) x).map_adjugate F
      exact (congrFun (congrFun this i) j).symm
    rw [e, hF', ← RingHom.map_adjugate]
    exact (F'.adjugate i j).2
end ReciprocityTheory.PGsh.L2
