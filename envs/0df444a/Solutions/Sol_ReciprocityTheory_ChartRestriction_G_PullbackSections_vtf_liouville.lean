-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_liouville
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:21.626879+00:00
-- url     : https://prove2.me/submissions/43f5cade-8558-47bf-9571-5534a294cb9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (lat : AddSubgroup (Fin g → ℂ)) (hspan : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤)
    (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hper : ∀ z, ∀ a ∈ lat, ‖f (z + a)‖ = ‖f z‖)
    (z w : Fin g → ℂ) : f z = f w := by
  classical
  obtain ⟨s, hsl, hss, hli⟩ := exists_linearIndependent ℝ (lat : Set (Fin g → ℂ))
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : s → Fin g → ℂ)) :=
    le_of_eq (by rw [Subtype.range_coe, hss, hspan])
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let b : Module.Basis s ℝ (Fin g → ℂ) := Module.Basis.mk hli hsp
  have hb : ∀ i, b i ∈ lat := fun i => by
    simp only [b, Module.Basis.mk_apply]
    exact hsl i.2
  have hfl : ∀ x : Fin g → ℂ, (ZSpan.floor b x : Fin g → ℂ) ∈ lat := by
    intro x
    have h1 : Submodule.span ℤ (Set.range b) ≤ lat.toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb i
    exact h1 (ZSpan.floor b x).2
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := (hK.image hf.continuous).isBounded.exists_norm_le
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx : ZSpan.fract b x + (ZSpan.floor b x : Fin g → ℂ) = x := by
      rw [ZSpan.fract_apply, sub_add_cancel]
    calc ‖f x‖ = ‖f (ZSpan.fract b x + (ZSpan.floor b x : Fin g → ℂ))‖ := by rw [hx]
      _ = ‖f (ZSpan.fract b x)‖ := hper _ _ (hfl x)
      _ ≤ C := hC _ ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b x), rfl⟩
  exact hf.apply_eq_apply_of_bounded hbd z w
end ReciprocityTheory.ChartRestriction.G.PullbackSections
