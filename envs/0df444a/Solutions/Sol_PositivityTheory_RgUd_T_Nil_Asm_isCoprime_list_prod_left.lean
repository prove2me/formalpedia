-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.isCoprime_list_prod_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:50.252094+00:00
-- url     : https://prove2.me/submissions/45fac55d-66cf-48d8-b1d7-28af0d567c22

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.RgUd.T.Nil.Asm
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) :
    ∀ l : List ι, (∀ x ∈ l, IsCoprime (f x) z) → IsCoprime (l.map f).prod z := by
  intro l
  induction l with
  | nil => intro _; simpa using isCoprime_one_left
  | cons x t ih =>
    intro h
    rw [List.map_cons, List.prod_cons]
    exact (h x (List.mem_cons_self)).mul_left (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
end PositivityTheory.RgUd.T.Nil.Asm
