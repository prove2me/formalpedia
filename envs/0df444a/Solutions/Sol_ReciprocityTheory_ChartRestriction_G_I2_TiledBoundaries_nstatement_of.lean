-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:29.766428+00:00
-- url     : https://prove2.me/submissions/212763bf-3f11-4c8a-91ca-566ae158e340

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_norm_part
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_orth_part
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_span_part
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pullbackSection_mem_thetaSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (hT : StepT) (hI : StepI) (hF : StepF) (hP : StepP) (hPos : StepPos)
    (hDual : StepDual) (hKc : StepK) (hD : StepD) : NStatement := by
  intro E _ _ _ X q n π hq hπ s hs hs0 K hK
  have hS := pullbackSection_mem_thetaSpace X (n := n) hπ hs
  have h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n := fun b hb => nA_U_mem X hS (hK.1 b hb)
  have h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' →
      X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0 :=
    fun b hb b' hb' hne => orth_part hT hDual X hq hπ hs hK hb hb' hne
  have h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n :=
    fun b _ => norm_part hT hF hP X hq hπ hs b
  exact ⟨h1, h2, h3, span_part hI hPos hKc hD X hq hπ hs hs0 hK h1 h2 h3⟩
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
