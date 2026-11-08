-- Prove2me | solution 1 for QEC.Coding.FiniteFieldCSSPresentation.variableSupport_map_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:10:48.591003+00:00
-- url     : https://prove2.me/submissions/3511b971-3bb9-4b08-bc79-6d28c8a3b3e6

import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_incident_baseCheckIndex_of_incident
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport



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
    (q : ι) :
    ((presentation K).incidence.variableSupport q).map
        checkIndexEquiv.toEmbedding ⊆
      (QLDPC.chainComplexBoundaryIncidence K).variableSupport q ×ˢ
        (Finset.univ : Finset F) := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  rw [Finset.mem_product]
  constructor
  · rw [QLDPC.CheckIncidence.mem_variableSupport] at hc ⊢
    exact incident_baseCheckIndex_of_incident K c q hc
  · exact Finset.mem_univ _
end QEC.Coding.FiniteFieldCSSPresentation
