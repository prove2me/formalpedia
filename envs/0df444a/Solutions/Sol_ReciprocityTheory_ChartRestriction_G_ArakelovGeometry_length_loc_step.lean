-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:45.735823+00:00
-- url     : https://prove2.me/submissions/a3f2a49f-091c-42c8-8613-13be9adc6fa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_add

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
theorem _root_.solution (I q : Ideal R) (f : R) (hq : ∀ g, g ∈ q ↔ g * f ∈ I) (P : Ideal R)
    [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) +
        Module.length (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (R ⧸ (I ⊔ Ideal.span {f}))) := by
  let g : (R ⧸ q) →ₗ[R] (R ⧸ I) :=
    Submodule.mapQ q I (LinearMap.mulRight R f) (by intro x hx; exact (hq x).mp hx)
  let π : (R ⧸ I) →ₗ[R] (R ⧸ (I ⊔ Ideal.span {f})) :=
    Submodule.mapQ I (I ⊔ Ideal.span {f}) LinearMap.id (by intro x hx; exact Ideal.mem_sup_left hx)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (p := I) (x * f) = 0 at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change Submodule.Quotient.mk (p := q) x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hq x).mpr hz
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact g π := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (p := I ⊔ Ideal.span {f}) y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      change Submodule.Quotient.mk (p := I) (r * f) = Submodule.Quotient.mk (a + r * f)
      rw [Submodule.Quotient.eq]
      simpa using I.neg_mem ha
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (p := I) (x * f) = Submodule.Quotient.mk y at hx
      rw [Submodule.Quotient.eq] at hx
      have e : y = x * f - (x * f - y) := by ring
      rw [e]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩))
        (Ideal.mem_sup_left hx)
  exact length_loc_add g π hg hπ hex P
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
