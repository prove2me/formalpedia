-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sg_prod_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:48.527838+00:00
-- url     : https://prove2.me/submissions/ff8a8174-391d-4baa-8743-9862cbbc5f51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_cp_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) (l : List (Fin n × Fin n)) :
    sgE ε cpFock cmFock c c (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
      (((l.map fun x => modeWt ε x c).sum : ℝ) : ℂ) •
        (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod := by
  induction l with
  | nil => simp [sgE_one]
  | cons x l ih =>
    obtain ⟨i, y⟩ := x
    have h := LinearMap.congr_fun (sg_cp_comm isCAR_fock ε c i y)
      ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, ih, map_smul] at h
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [show ExteriorAlgebra.ι ℂ (Pi.single (i, y) (1 : ℂ)) *
        (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
        cpFock i y ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod) from rfl, h,
      ← add_smul]
    congr 1
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.DS
