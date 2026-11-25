-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:22.029948+00:00
-- url     : https://prove2.me/submissions/9c59f2c9-2592-4cd0-b71c-8f8a025e8c34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSupSmall
theorem _root_.solution {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ))
    (G : Coord D.extSizes → MvPolynomial (Coord n) ℤ) (e : ι → ℕ)
    (hG : ∀ v, IsWeightedHomogeneous (coordDeg n) (G v) e) :
    IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) := by
  rw [aeval_def, eval₂_eq']
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun v ↦ G v ^ m v) (fun v ↦ m v • e)
    fun v _ ↦ (hG v).pow (m v)
  have hs : ∑ v, m v • e = τ • e := by
    obtain ⟨h0, hτ⟩ := exps D hf hm
    rw [← Finset.sum_smul, Fintype.sum_sigma, Fintype.sum_option]
    simp [h0, hτ]
  rw [hs] at hp
  have hC : IsWeightedHomogeneous (coordDeg n) (algebraMap ℤ (MvPolynomial (Coord n) ℤ) (coeff m f)) 0 := by
    rw [algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  simpa using hC.mul hp
end GroundTheory.Heights₂.Heights.YPlusSupSmall
