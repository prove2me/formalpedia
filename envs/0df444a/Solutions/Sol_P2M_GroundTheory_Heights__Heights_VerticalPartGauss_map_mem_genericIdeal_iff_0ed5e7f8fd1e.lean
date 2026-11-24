-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:54.5898+00:00
-- url     : https://prove2.me/submissions/f831524d-d0f6-4d8c-94e0-572d6a85d2ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_algebraMap_eq_3bee6135e2df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_disjoint_constUnits_690a47693f08

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
    (x : MvPolynomial (Fin n) ℤ) :
    map (Int.castRingHom ℚ) x ∈ genericIdeal P ↔ x ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
  have h := IsLocalization.under_map_of_isPrime_disjoint (constUnits n) (MvPolynomial (Fin n) ℚ)
    (finIdeal_isPrime hP) (disjoint_constUnits hP)
  rw [genericIdeal_eq, ← algebraMap_eq]
  constructor
  · intro hx
    rw [← h]
    exact hx
  · exact Ideal.mem_map_of_mem _
end GroundTheory.Heights₂.Heights.VerticalPartGauss
