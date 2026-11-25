-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.dList_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:23.122442+00:00
-- url     : https://prove2.me/submissions/35db2d5e-7d5e-474c-ab1c-6026a1802c76

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dc_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (β : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (l : List (Fin n × Fin n)) (c : ℂ) (x : Vr n),
      dList l (fun y => c * Complex.exp (ell β (herm y))) x =
        c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod * Complex.exp (ell β (herm x))
  | [], c, x => by simp [dList]
  | a :: l, c, x => by
    have h : dList l (fun y => c * Complex.exp (ell β (herm y))) =
        fun y => (c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod) * Complex.exp (ell β (herm y)) := by
      funext y; rw [solution β l c y]
    simp only [dList]
    rw [h]
    set c' := c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod
    have hd : HasFDerivAt (fun H => c' * Complex.exp (ell β H))
        (c' • (Complex.exp (ell β (herm x)) • ell β)) (herm x) :=
      ((ell β).hasFDerivAt.cexp).const_mul c'
    rw [dc_comp hd.differentiableAt, hd.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul, List.map_cons, List.prod_cons, c']
    ring
end PositivityTheory.Rg.Sw.LVs.STD
