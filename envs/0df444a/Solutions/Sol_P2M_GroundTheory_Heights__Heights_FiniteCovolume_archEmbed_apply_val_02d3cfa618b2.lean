-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:53.490112+00:00
-- url     : https://prove2.me/submissions/62fed1e0-4354-4769-8f97-6a3c21346c63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Theorems.Thm_GroundTheory_Automorphic_unitaryGroupEquivMatrix_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (g : h.unitaryGroup)
    (w : InfinitePlace E) :
    ((((archEmbed h v g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) :
        Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
