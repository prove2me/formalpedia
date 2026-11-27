-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:30.166814+00:00
-- url     : https://prove2.me/submissions/06519fdb-0922-427a-a1fe-28de54f04c40

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
variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
namespace ReciprocityTheory.Neutral.Bridge.HCF
theorem _root_.solution (A : ValuationSubring L) (g : L ≃ₐ[K] L) :
    g ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      g • A = A ∧ ∀ x ∈ A, g x - x ∈ A.nonunits := by
  have key : ∀ (hg : g ∈ A.decompositionSubgroup K), (⟨g, hg⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K ↔
      ∀ x ∈ A, g x - x ∈ A.nonunits := by
    intro hg
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker, RingEquiv.ext_iff]
    simp only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply, RingAut.one_apply]
    constructor
    · intro h x hx
      have h1 := h (IsLocalRing.residue A ⟨x, hx⟩)
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨_, h1⟩
    · intro h r
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective r
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      obtain ⟨_, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (h x hx)
      exact h2
  constructor
  · rintro ⟨⟨g', hg'⟩, hin, rfl⟩
    exact ⟨hg', (key hg').mp hin⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, (key hg).mpr hx, rfl⟩
end ReciprocityTheory.Neutral.Bridge.HCF
