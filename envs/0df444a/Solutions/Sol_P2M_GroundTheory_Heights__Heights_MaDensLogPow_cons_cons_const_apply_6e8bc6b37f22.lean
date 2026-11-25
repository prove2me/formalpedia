-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:50.243555+00:00
-- url     : https://prove2.me/submissions/5f0d53c7-eb4d-4936-8c02-38fadaa7d88c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (k : Fin (n + 1 + 1)) :
    (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) k =
      if k = 0 then G else if k = 1 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · refine Fin.cases ?_ (fun l => ?_) i
    · simp
    · have h1 : (l.succ.succ : Fin (n + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]; exact fun h => Fin.succ_ne_zero l (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, h1]
end GroundTheory.Heights₂.Heights.MaDensLogPow
