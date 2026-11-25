-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:38.72313+00:00
-- url     : https://prove2.me/submissions/8da7f014-ca7c-4a06-b1af-354ff41bc96d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hH, -⟩ := hyperbolic_at_place h v hp w
  rw [← hForm_conj hH, Complex.conj_re]
end GroundTheory.Heights₂.Heights.FiniteCovolume
