-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_disjoint_constUnits_690a47693f08
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:46.062944+00:00
-- url     : https://prove2.me/submissions/5d6ba310-c229-439c-ac51-9de3efdfd452

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm

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
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    Disjoint (constUnits n : Set (MvPolynomial (Fin n) ℤ)) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ hmem
  have hk0 : k ≠ 0 := nonZeroDivisors.ne_zero hk
  have h1 : (C k : MRing (PBlk n)) ∈ P := by
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C] using hmem
  have h2 : k ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
  rw [hP.2.2.1] at h2
  exact hk0 ((Submodule.mem_bot ℤ).mp h2)
end GroundTheory.Heights₂.Heights.VerticalPartGauss
