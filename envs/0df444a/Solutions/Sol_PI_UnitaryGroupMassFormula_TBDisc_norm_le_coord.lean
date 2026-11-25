-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.norm_le_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:04.830979+00:00
-- url     : https://prove2.me/submissions/0ecadf78-8300-41ea-86f3-0a342572b5dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_normFam_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution (Nf : NormFam K V) (σ : K →+* ℂ) (v : V) :
    Nf.N σ v ≤ ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by
  have hv : v = ∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i :=
    ((Module.finBasis K V).sum_repr v).symm
  have hle : ∀ i, ‖σ ((Module.finBasis K V).repr v i)‖ ≤ ‖coordMap (K := K) v‖ := fun i =>
    (norm_le_pi_norm (coordMap (K := K) v σ) i).trans (norm_le_pi_norm (coordMap (K := K) v) σ)
  calc Nf.N σ v = Nf.N σ (∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i) := by
        conv_lhs => rw [hv]
    _ ≤ ∑ i, Nf.N σ ((Module.finBasis K V).repr v i • Module.finBasis K V i) := normFam_sum_le Nf σ _ _
    _ = ∑ i, ‖σ ((Module.finBasis K V).repr v i)‖ * Nf.N σ (Module.finBasis K V i) := by
        simp only [Nf.smul]
    _ ≤ ∑ i, ‖coordMap (K := K) v‖ * Nf.N σ (Module.finBasis K V i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (Nf.nonneg _ _)
    _ = ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by rw [Finset.mul_sum]
end PI.UnitaryGroupMassFormula.TBDisc
