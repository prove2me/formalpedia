-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:36.038509+00:00
-- url     : https://prove2.me/submissions/5a8a526c-a2c4-4d9a-828e-7330c86710bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {e : ℕ} (R : AnLogRes P J e) (x₀ : R.X) {x : R.X} (hx : x ∈ R.U x₀) :
    ∃ c : ℂ, c ≠ 0 ∧ segre (R.lift x x) = c • (segre (R.lift x₀ x) : ((k : K) → ι k) → ℂ) :=
  segre_of_sameOrbit (R.compat x x₀ x ⟨R.mem_U x, hx⟩)
end GroundTheory.Heights₂.Heights.Targets
