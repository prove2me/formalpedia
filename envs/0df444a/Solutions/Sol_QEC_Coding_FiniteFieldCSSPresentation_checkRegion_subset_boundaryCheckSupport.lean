-- Prove2me | solution 1 for QEC.Coding.FiniteFieldCSSPresentation.checkRegion_subset_boundaryCheckSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:10:47.018808+00:00
-- url     : https://prove2.me/submissions/c16a70b9-0182-4d1a-969f-bdd7abc58faf

import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_incident_baseCheckIndex_of_incident
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldCSSPresentation
open QEC.Coding.FiniteFieldPauli
universe u
variable {F ι κ₀ κ₂ : Type u}
variable [Field F] [Fintype F]
variable [Fintype ι] [Fintype κ₀] [Fintype κ₂]
attribute [local instance] QEC.Coding.FiniteFieldCSSPresentation._p2m_local_instance_10414ac4d3_24
namespace QEC.Coding.FiniteFieldCSSPresentation
theorem _root_.solution
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) :
    ((presentation K).checks c).region.selected ⊆
      (QLDPC.chainComplexBoundaryIncidence K).checkSupport
        (baseCheckIndex c) := by
  intro q hq
  rw [QLDPC.CheckIncidence.mem_checkSupport]
  apply incident_baseCheckIndex_of_incident K c q
  exact hq
end QEC.Coding.FiniteFieldCSSPresentation
