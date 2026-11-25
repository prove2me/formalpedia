-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.basis_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:55:41.09978+00:00
-- url     : https://prove2.me/submissions/c41e0eb0-b35a-4142-968b-fba224ac5f46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (e' : Fin g ≃ Lt1 Dw) (v : Fin g → ℂ) :
    ∃! a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = v j := by
  have key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j) := by
    intro a j
    rw [Fintype.sum_eq_single (e' j)]
    · simp
    · intro ℓ hℓ
      have hne : j ≠ e'.symm ℓ := by
        intro h
        apply hℓ
        rw [h, Equiv.apply_symm_apply]
      simp [hne]
  refine ⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp
  · funext ℓ
    have h1 := ha (e'.symm ℓ)
    rw [key, Equiv.apply_symm_apply] at h1
    exact h1
end ReciprocityTheory.ChartRestriction.G.PullbackSections
