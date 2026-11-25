-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.hopfOrder_translate_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:19:14.330815+00:00
-- url     : https://prove2.me/submissions/37701194-0114-4951-8c22-10f448ed50d8

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
theorem _root_.solution (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (y : N) :
    (fun x => f (x + y)) ∈ AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      AA.carrier.comap (LinearMap.funLeft R C (fun x : N => (x, y))) := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := AA.le_int hh y
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : LinearMap.funLeft R C (fun x : N => (x, y)) (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x; simp [Algebra.smul_def, hr, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)
end ReciprocityTheory.PGsh.L2
