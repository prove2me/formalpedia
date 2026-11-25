-- Prove2me | solution 1 for PI.LatIdxDetW.lidx_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:36.064387+00:00
-- url     : https://prove2.me/submissions/a61f56d7-7da1-4d9f-8ae5-230d1f89007c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_PI_LatIdxDetW_locLen_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
namespace PI.LatIdxDetW
section Gen
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
private theorem mem_localization_iff_exists_smul_mem (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl
private theorem localization_inf' (p : Ideal R) [p.IsPrime] (X Y : Submodule R W) :
    localization₂ p (X ⊓ Y) = localization₂ p X ⊓ localization₂ p Y := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨⟨s, hs, (Submodule.mem_inf.1 hx).1⟩, ⟨s, hs, (Submodule.mem_inf.1 hx).2⟩⟩
  · rintro ⟨⟨s, hs, hx⟩, ⟨t, ht, hy⟩⟩
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]
      exact X.smul_mem t hx
    · rw [mul_smul]
      exact Y.smul_mem s hy
end Gen
section Lat
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [FiniteDimensional K V]
end Lat
end PI.LatIdxDetW
end
end

set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace PI.LatIdxDetW
theorem _root_.solution (p : Ideal R) [p.IsPrime] {A A' B B' : Submodule R W}
    (hA : localization₂ p A = localization₂ p A') (hB : localization₂ p B = localization₂ p B') : lidx p A B = lidx p A' B' := by
  unfold lidx
  have hAB : localization₂ p (A ⊓ B) = localization₂ p (A' ⊓ B') := by
    rw [localization_inf', localization_inf', hA, hB]
  rw [locLen_congr p hA hAB, locLen_congr p hB hAB]
end PI.LatIdxDetW
