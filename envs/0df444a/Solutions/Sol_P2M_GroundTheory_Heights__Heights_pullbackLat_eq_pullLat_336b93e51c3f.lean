-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pullbackLat_eq_pullLat_336b93e51c3f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:42:05.962797+00:00
-- url     : https://prove2.me/submissions/f76a0902-9bb4-4aa6-b29c-a3e03da4b97e

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Mathlib




-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}
theorem _root_.solution {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {x : ι → Ω}
    (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    pullbackLat B z q = IndefiniteRowSideFullHecke.Antisym.pullLat x z B.lat q := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_77_4"



end 
