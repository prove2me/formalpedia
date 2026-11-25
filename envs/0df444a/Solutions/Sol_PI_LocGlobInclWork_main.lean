-- Prove2me | solution 1 for PI.LocGlobInclWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:45.486511+00:00
-- url     : https://prove2.me/submissions/ce176182-4b75-4c69-9819-d083678e34a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Theorems.Thm_PI_LocGlobInclWork_mem_localization_iff
import Theorems.Thm_PI_LocGlobInclWork_self_le_locP
import Theorems.Thm_PI_LocGlobInclWork_mem_of_local
import Theorems.Thm_PI_LocGlobInclWork_exists_unit_at
import Theorems.Thm_PI_LocGlobInclWork_smul_mem_idealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]
namespace PI.LocGlobInclWork
theorem _root_.solution : PI.LocGlobIncl := by
  intro K W _ _ _ _ _ _ _ M B T a hT hnT x hx
  classical
  unfold Formalism.AtG.denIdeal
  apply mem_of_local
  intro w
  haveI : w.asIdeal.IsPrime := w.isPrime
  by_cases hw : w ∈ T
  · obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w.asIdeal _ x).mp (hT w hw ((self_le_locP w.asIdeal M) hx))
    obtain ⟨t, ht, htJ⟩ := exists_unit_at w (T.erase w) (by simp) (fun v => -(a v))
    have htJ' : algebraMap (𝓞 K) K t ∈
        ∏ v ∈ T.erase w, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) := htJ
    refine ⟨t * s, fun hmem => (w.isPrime.mem_or_mem hmem).elim ht hs, ?_⟩
    rw [mul_smul]
    have e : (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w)) *
        ∏ v ∈ T.erase w, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) =
        ∏ v ∈ T, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) :=
      Finset.mul_prod_erase T (fun v => (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v))) hw
    have hm := smul_mem_idealSmul _ _ B t htJ' hsx
    rw [e] at hm
    exact hm
  · obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w.asIdeal _ x).mp (hnT w hw ((self_le_locP w.asIdeal M) hx))
    obtain ⟨t, ht, htJ⟩ := exists_unit_at w T hw (fun v => -(a v))
    have htJ' : algebraMap (𝓞 K) K t ∈
        ∏ v ∈ T, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) := htJ
    refine ⟨t * s, fun hmem => (w.isPrime.mem_or_mem hmem).elim ht hs, ?_⟩
    rw [mul_smul]
    have hB : s • x ∈ Formalism.HermitianLatticesTheory.idealSmul
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) B := by
      apply Submodule.subset_span
      refine ⟨1, ?_, s • x, hsx, (one_smul K _).symm⟩
      rw [FractionalIdeal.coe_one]
      exact Submodule.one_le.mp le_rfl
    have hm := smul_mem_idealSmul 1 _ B t htJ' hB
    rw [one_mul] at hm
    exact hm
end PI.LocGlobInclWork
