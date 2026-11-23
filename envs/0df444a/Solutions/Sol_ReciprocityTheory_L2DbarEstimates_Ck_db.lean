-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.db
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:15.890491+00:00
-- url     : https://prove2.me/submissions/b40b0404-26f8-42af-8604-3eaa2b2b808a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
private theorem contDiffOn_wd_wdb_of_contDiffOn_succ {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ} (k : ℕ)
    (hg : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g U) (j : Fin n) :
    ContDiffOn ℝ k (wd n j g) U ∧ ContDiffOn ℝ k (wdb n j g) U := by
  have hF : ∀ v : V n, ContDiffOn ℝ k (fun y => fderiv ℝ g y v) U := fun v =>
    (hg.fderiv_of_isOpen hU (Nat.cast_succ k).ge).clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (j : Fin n)
    (f : M → ℂ) (hf : Ck n z (k + 1) f) : Ck n z k (db n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_succ e.open_target k (hf e he) j).2.congr fun y hy => db_comp_symm n z e he j f y hy
end Ck
end ReciprocityTheory.L2DbarEstimates
