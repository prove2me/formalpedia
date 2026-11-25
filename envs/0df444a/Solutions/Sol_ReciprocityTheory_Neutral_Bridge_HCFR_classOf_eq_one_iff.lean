-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:44:11.782234+00:00
-- url     : https://prove2.me/submissions/0ded06e2-a003-4f87-8253-1734e9aebf48

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_rayUnits_top_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_count_idealFI
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_eq_of_count
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_count_spanSingleton
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_diag
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (a : Ideles K) :
    classOf K a = 1 ↔ ∃ k : Kˣ, ∃ u ∈ rayUnits K ⊤ ∅, a = diagUnits K k * u := by
  have key : ∀ k : Kˣ, idealFI K (diagUnits K k) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
    intro k
    apply eq_of_count K (idealFI_ne_zero K _) (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact k.ne_zero)
    intro v
    rw [count_idealFI, ordAt_diag, count_spanSingleton K v k.ne_zero]
  have hone : ∀ u ∈ rayUnits K ⊤ ∅, idealFI K u = 1 := by
    intro u hu
    rw [rayUnits_top_iff] at hu
    apply eq_of_count K (idealFI_ne_zero K _) one_ne_zero
    intro v
    rw [count_idealFI, FractionalIdeal.count_one, (ordAt_eq_zero_iff K v u).mpr (hu v)]
  constructor
  · intro h
    rw [classOf, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff] at h
    obtain ⟨x, hx⟩ := h.principal
    have hI : idealFI K a = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      show ((idealFI K a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
        ((FractionalIdeal.spanSingleton (𝓞 K)⁰ x : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply idealFI_ne_zero K a
      rw [hI, FractionalIdeal.spanSingleton_zero]
    refine ⟨Units.mk0 x hx0, (diagUnits K (Units.mk0 x hx0))⁻¹ * a, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [rayUnits_top_iff]
    intro v
    rw [← ordAt_eq_zero_iff, ordAt_mul, ordAt_inv, ordAt_diag, Units.val_mk0, ← count_spanSingleton K v hx0,
      ← hI, count_idealFI]
    ring
  · rintro ⟨k, u, hu', rfl⟩
    rw [classOf, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff]
    have h2 : ((idealOf K (diagUnits K k * u) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
      show idealFI K _ = _
      rw [idealFI_mul, key, hone u hu', mul_one]
    rw [h2, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨k, rfl⟩⟩
end ReciprocityTheory.Neutral.Bridge.HCFR
