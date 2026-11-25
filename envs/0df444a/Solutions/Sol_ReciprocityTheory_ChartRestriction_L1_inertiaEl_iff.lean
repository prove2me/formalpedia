-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inertiaEl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:36.479127+00:00
-- url     : https://prove2.me/submissions/c82e6f16-164c-4ddd-9a28-44914bc9a148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) :
    InertiaEl A g ↔ g ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype := by
  constructor
  · rintro ⟨hd, hx⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hd⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    refine RingEquiv.ext fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ((⟨g, hd⟩ : A.decompositionSubgroup E) • a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a
    rw [Ideal.Quotient.eq]
    obtain ⟨h1, h2⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).1 (hx a a.2)
    exact h2
  · intro hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨g'.2, fun x hx => ?_⟩
    have key : (g' • (⟨x, hx⟩ : A)) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal A := by
      rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hg'
      have h3 := congrArg (fun f : RingAut (IsLocalRing.ResidueField A) =>
        f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ⟨x, hx⟩)) hg'
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (g' • (⟨x, hx⟩ : A)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ at h3
      exact Ideal.Quotient.eq.1 h3
    have e : ((A.decompositionSubgroup E).subtype g') x - x =
        ((g' • (⟨x, hx⟩ : A) - (⟨x, hx⟩ : A) : A) : Ω) := rfl
    rw [e, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)]
    exact ⟨(g' • (⟨x, hx⟩ : A) - (⟨x, hx⟩ : A)).2, key⟩
end ReciprocityTheory.ChartRestriction.L1
