-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:23.057969+00:00
-- url     : https://prove2.me/submissions/6a21dd70-1382-4d2e-8a34-708c125b2341

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3


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
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.VerticalPartGauss
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    {u : Fin n → ℤ} (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    linForm (fun j => (u j : ℚ)) ∉ genericIdeal P := by
  intro h
  have hmap : linForm (fun j => (u j : ℚ)) = map (Int.castRingHom ℚ) (linForm u) := by
    simp [linForm, map_sum]
  rw [hmap, map_mem_genericIdeal_iff hP, ObjectsChow.linForm_mem_finIdeal] at h
  exact hu h
end GroundTheory.Heights₂.Heights.VerticalPartGauss
