-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:18.309132+00:00
-- url     : https://prove2.me/submissions/684105e7-bc47-47ef-8939-58058ed097d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    (∀ z' ∈ Heights.conePoints (P.projIdeal k₀) ℂ,
        ‖evalCone z' (rename (blockCoordEquiv (n := n) k₀) f)‖ ≤ B * l2Norm (z' ()) ^ N) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by
  have hev : ∀ z' : Cone (fun _ : Unit ↦ n k₀) ℂ,
      evalCone z' (rename (blockCoordEquiv (n := n) k₀) f) = eval₂ (Int.castRingHom ℂ) (z' ()) f := by
    intro z'
    rw [evalCone, eval₂_rename]
    rfl
  constructor
  · intro h w hw
    have := h _ ((mem_oneBlockPoints_iff P k₀ w).mp hw)
    rwa [hev] at this
  · intro h z' hz'
    have hz : z' = fun _ : Unit ↦ z' () := funext fun u ↦ by cases u; rfl
    rw [hev]
    rw [hz] at hz'
    exact h _ ((mem_oneBlockPoints_iff P k₀ (z' ())).mpr hz')
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
