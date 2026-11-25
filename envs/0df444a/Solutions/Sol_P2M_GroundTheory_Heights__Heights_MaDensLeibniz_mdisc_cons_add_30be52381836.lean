-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:19.67932+00:00
-- url     : https://prove2.me/submissions/017b0261-19ab-421e-a1dc-7870dce5800c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLeibniz
theorem _root_.solution {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simpa using mdisc_cons_smul_add 1 1 A A' B
end GroundTheory.Heights₂.Heights.MaDensLeibniz
