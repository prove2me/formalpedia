-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:26.162798+00:00
-- url     : https://prove2.me/submissions/becb3015-5721-43c5-8479-8f59cb04a879

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution {d d' : ℕ} {XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    {XT : InfinitePlace K → Matrix (Fin d') (Fin d') ℂ} {v : InfinitePlace K} {φ : Matrix (Fin d') (Fin d) K}
    {A : Submodule K (Fin d → K)} {E : Submodule K (Fin d' → K)} {s : ℝ} (hφ : Function.Bijective φ.mulVec)
    (hmap : A.map φ.mulVecLin = E) (h : IsScalarOn XS XT v φ A s) :
    IsScalarOn XS XT v φ (E.comap φ.mulVecLin) s := by
  have hA : E.comap φ.mulVecLin = A := by
    rw [← hmap]
    exact Submodule.comap_map_eq_of_injective (f := φ.mulVecLin) (by exact hφ.1) A
  rw [hA]
  exact h
end Formalism.L2.Indef.Examples₂
