-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.inj_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:45.702834+00:00
-- url     : https://prove2.me/submissions/b4aa7265-3c96-44da-b005-9529e0f33dc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_cm_nat_apply

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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
include hnat
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
theorem _root_.solution {V : B.Opens} (h : V ≤ W) {ι : Type} (U : ι → B.Opens) (hU : ∀ i, U i ≤ V)
    (hcov : V ≤ iSup U) (hinj : ∀ i, Function.Injective (cm q φ (U i) ((hU i).trans h))) :
    Function.Injective (cm q φ V h) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom p = 0 := by
    intro i
    apply hinj i
    rw [cm_nat_apply q φ hnat ((hU i).trans h) h (hU i), hp, map_zero, map_zero]
  ext x
  apply B.sheaf.eq_of_locally_eq' U V (fun i => homOfLE (hU i)) hcov
  intro i
  have h2 := congrArg (fun r => r.coeff x) (h1 i)
  have h3 : (B.presheaf.map (homOfLE (hU i)).op).hom (p.coeff x) = 0 := by simpa using h2
  refine h3.trans ?_
  exact (map_zero _).symm
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
