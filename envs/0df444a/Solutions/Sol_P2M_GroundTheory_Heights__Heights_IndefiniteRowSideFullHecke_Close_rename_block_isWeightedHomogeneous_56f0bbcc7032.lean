-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:34.824897+00:00
-- url     : https://prove2.me/submissions/3f92945d-28bc-4251-a765-7199e57b193e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (k₀ : ι) {N : ℕ} {g : MvPolynomial (Fin (n k₀ + 1)) ℤ}
    (hg : g.IsHomogeneous N) :
    IsWeightedHomogeneous (coordDeg n) (rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g) (N • Pi.single k₀ 1) := by
  classical
  intro d hd
  rw [← mem_support_iff, support_rename_of_injective (blockInj_injective k₀), Finset.mem_image] at hd
  obtain ⟨d', hd', rfl⟩ := hd
  have hN : ∑ i, d' i = N := by rw [← weight_one_fin]; exact hg (mem_support_iff.mp hd')
  funext k
  rw [weight_coordDeg_apply]
  by_cases hk : k = k₀
  · subst hk
    simp only [Finsupp.mapDomain_apply (blockInj_injective k), hN]
    simp
  · have h0 : ∀ i, Finsupp.mapDomain (fun i ↦ (⟨k₀, i⟩ : Coord n)) d' ⟨k, i⟩ = 0 := fun i ↦
      Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; exact hk (congrArg Sigma.fst hj).symm)
    simp [h0, hk]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
