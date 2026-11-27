-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCF.classGroup_mulEquiv_mk0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:24.773491+00:00
-- url     : https://prove2.me/submissions/06b0fa02-1cb2-413a-8acc-9db5e7ca3d4c

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCF
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
namespace ReciprocityTheory.Neutral.Bridge.HCF
theorem _root_.solution (g : R ≃+* R') (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨(I : Ideal R).map g, map_mem_nzd g I⟩ := by
  apply (ClassGroup.equiv (FractionRing R')).injective
  rw [ClassGroup.mulEquiv_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk0, ClassGroup.equiv_mk0]
  simp only [QuotientGroup.mk'_apply]
  erw [QuotientGroup.congr_mk]
  congr 1
  apply Units.ext
  simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, FractionalIdeal.coe_mk0]
  apply Subtype.ext
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨g z, Ideal.mem_map_of_mem _ hz, ?_⟩
    simp [IsFractionRing.semilinearEquivOfRingEquiv]
  · rintro ⟨y, hy, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨algebraMap R (FractionRing R) z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · simp [IsFractionRing.semilinearEquivOfRingEquiv]
end ReciprocityTheory.Neutral.Bridge.HCF
