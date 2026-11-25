-- Prove2me | solution 1 for PI.Residue.fib_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:00.996147+00:00
-- url     : https://prove2.me/submissions/86c87044-61bd-4aa6-952f-2ce5599609ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_P2M_PI_Residue_measurableSet_shell__efd4227c586e
import Theorems.Thm_P2M_PI_Residue_measurableSet_hit__413fd930b60e
import Theorems.Thm_PI_Residue_mem_hit_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (hUP : UnitPreserving) (ρ : ℝ) (x1 : mixedSpace K) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K, Fv ρ (urep g • x1) ≤
      volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x1) := by
  let A : (𝓞 K)ˣ ⧸ torsion K → Set (mixedSpace K) := fun g =>
    (fun z : mixedSpace K => (urep g)⁻¹ • z) ⁻¹' shell K ∩ hit K ρ x1
  have hAm : ∀ g, MeasurableSet (A g) := fun g =>
    ((hUP K (urep g)⁻¹).measurable measurableSet_shell').inter (measurableSet_hit' _ _)
  have hFA : ∀ g, Fv ρ (urep g • x1) = volume (A g) := by
    intro g
    have e : shell K ∩ hit K ρ (urep g • x1) = (fun y : mixedSpace K => urep g • y) ⁻¹' A g := by
      ext y
      simp only [A, Set.mem_inter_iff, Set.mem_preimage, mem_hit_smul, inv_smul_smul]
    rw [Fv, e, (hUP K (urep g)).measure_preimage (hAm g).nullMeasurableSet]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro g g' hgg
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨hz, _⟩ ⟨hz', _⟩
    apply hgg
    have h1 : (urep g)⁻¹ • z ∈ fundamentalCone K := hz.1
    have h2 : (urep g')⁻¹ • z ∈ fundamentalCone K := hz'.1
    have h3 : ((urep g')⁻¹ * urep g) • ((urep g)⁻¹ • z) ∈ fundamentalCone K := by
      rw [← mul_smul]; simpa using h2
    have h4 := (unit_smul_mem_iff_mem_torsion h1 _).1 h3
    have h5 : (QuotientGroup.mk (urep g') : (𝓞 K)ˣ ⧸ torsion K) = QuotientGroup.mk (urep g) :=
      QuotientGroup.eq.2 h4
    rw [urep, urep, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h5
    exact h5.symm
  calc ∑' g, Fv ρ (urep g • x1) = ∑' g, volume (A g) := tsum_congr hFA
    _ ≤ volume (⋃ g, A g) := tsum_meas_le_meas_iUnion_of_disjoint volume hAm hdisj
    _ ≤ _ := by
        refine measure_mono (Set.iUnion_subset fun g => ?_)
        rintro z ⟨hz, hz'⟩
        refine ⟨?_, hz'⟩
        have : 1 / 2 < mixedEmbedding.norm ((urep g)⁻¹ • z) := hz.2.1
        rwa [norm_unit_smul] at this
end PI.Residue
