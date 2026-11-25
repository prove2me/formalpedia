-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_proof_683f795c1327
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:39.893888+00:00
-- url     : https://prove2.me/submissions/ce02ec97-7f11-4bcc-ada3-af4ebc882028

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst


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
theorem _root_.solution : MaDensLeibniz.Statement := by
  intro D φ f g z hf hg
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_mul f g z hf hg]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_add, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_sq_half f z hf]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_smul_fst]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
end GroundTheory.Heights₂.Heights.MaDensLeibniz
