-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_gramAt_line_6c50ef986e6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:31.244921+00:00
-- url     : https://prove2.me/submissions/645d23c1-5d58-40fe-b5cf-68d8c53c1be0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}
variable {z : (Σ _ : Unit, Fin 2) → ℂ}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    gramAt lineMetric b z =
      (Matrix.of fun p q => valAt yLine (b q p) z)ᴴ * Matrix.of fun p q => valAt yLine (b q p) z := by
  classical
  obtain ⟨i, hi⟩ := hz
  have hl : ∃ l, InFrameDomain yLine (lineMetric.chart l) (lineMetric.fr l) z := ⟨i, inFrameDomain_line hi⟩
  have hS : ∃ S : Matrix (Fin 2) (Fin 2) Ω, ∀ q, b q = ∑ p, S p q • lineMetric.b hl.choose p :=
    ⟨Matrix.of fun p q => b q p, fun q => by
      funext r
      simp [lineMetric, Finset.sum_apply, Pi.single_apply]⟩
  have hSe : hS.choose = Matrix.of fun p q => b q p := by
    refine Matrix.ext fun p q => ?_
    have := congrFun (hS.choose_spec q) p
    simp [lineMetric, Finset.sum_apply, Pi.single_apply] at this
    exact this.symm
  unfold gramAt
  rw [dif_pos hl, dif_pos hS, hSe]
  show _ * (1 : Matrix (Fin 2) (Fin 2) ℂ) * _ = _
  rw [Matrix.mul_one]
  rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
