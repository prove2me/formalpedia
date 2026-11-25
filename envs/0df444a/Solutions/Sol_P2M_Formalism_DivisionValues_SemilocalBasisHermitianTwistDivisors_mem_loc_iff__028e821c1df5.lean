-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:05.49033+00:00
-- url     : https://prove2.me/submissions/67ed3620-8753-4e3d-81d9-fed28402b86e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔
      ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal, s • x ∈ M :=
  Iff.rfl
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
