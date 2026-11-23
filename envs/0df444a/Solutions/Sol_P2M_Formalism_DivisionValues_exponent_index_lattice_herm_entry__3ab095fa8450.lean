-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:40.193339+00:00
-- url     : https://prove2.me/submissions/9b61f55a-b4ed-45e9-9ee8-100a0fe56749

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H) (i j : Fin n) :
    H j i = star (H i j) := by
  have h := congrFun (congrFun hH j) i
  rw [Matrix.conjTranspose_apply] at h
  exact h.symm
end Formalism.DivisionValues.exponent_index_lattice
