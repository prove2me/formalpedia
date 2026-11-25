-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_closure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:04.569911+00:00
-- url     : https://prove2.me/submissions/30e62bed-b4e5-4dc5-91a3-6c548f4531c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol

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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) = ⊤ := by
  set R := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) with hR
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inl.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inr.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let i : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ i = 𝟙 P := by
    apply h.hom_ext
    · ext b
      simp [l, i]
    · ext c
      simp [r, i]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [i] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2
end ReciprocityTheory.ChartRestriction.G.PullbackSections
