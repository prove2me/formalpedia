-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.pow_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:50.089871+00:00
-- url     : https://prove2.me/submissions/e4e466f4-6f64-416b-b9d0-e7a5ab767c39

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
theorem _root_.solution (R R' : Module.End ℂ M) (hRR : R * R' = 1) (hR'R : R' * R = 1) (β : ℂ) (γ : ℝ → ℂ) :
    ∀ l : List ℝ, R ^ l.length * ((l.map fun x => β • R' - γ x • (1 : Module.End ℂ M)).prod) =
      (l.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod := by
  have hc : Commute R R' := hRR.trans hR'R.symm
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.length_cons, pow_succ', mul_assoc]
    have hcm : Commute (R ^ t.length) (β • R' - γ x • (1 : Module.End ℂ M)) :=
      ((hc.pow_left _).smul_right β).sub_right ((Commute.one_right _).smul_right _)
    rw [← mul_assoc (R ^ t.length), hcm.eq, mul_assoc, ih, ← mul_assoc]
    congr 1
    rw [mul_sub, mul_smul_comm, hRR, mul_smul_comm, mul_one]
end PositivityTheory.RgUd.T.Nil.Asm
