-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:35.045933+00:00
-- url     : https://prove2.me/submissions/1861ee45-3470-46b8-85ce-f1e9463a5d76

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_StepBAux_span_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K (matLat P M) := by
  refine ⟨(Submodule.IsLattice.fg (self := hM)).map _, ?_⟩
  have : ((matLat P M : Submodule (𝓞 K) (Fin D → K)) : Set (Fin D → K)) =
      (Matrix.mulVecLin P) '' (M : Set (Fin n → K)) := by
    rw [matLat, Submodule.map_coe]
    rfl
  rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hM), Submodule.map_top,
    LinearMap.range_eq_top]
  exact hP
end Formalism.DivisionValues.GluingInclusion
