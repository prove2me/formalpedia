-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_quot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:51.698798+00:00
-- url     : https://prove2.me/submissions/d12c996d-8fd8-49b1-a00c-fd3451325ed8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (q P : Ideal R) [P.IsPrime] (h : ¬ q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨s, hsq, hsP⟩ := SetLike.not_le_iff_exists.mp h
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  induction z using LocalizedModule.induction_on with
  | h m t =>
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
    refine ⟨⟨s, hsP⟩, ?_⟩
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact q.mul_mem_right _ hsq
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
