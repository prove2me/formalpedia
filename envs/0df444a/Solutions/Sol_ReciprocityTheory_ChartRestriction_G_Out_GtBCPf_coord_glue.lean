-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:40.516843+00:00
-- url     : https://prove2.me/submissions/a8943167-d4cb-4abc-9b08-e1be582845d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_inj_of_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_surj_of_cover

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
open GluingInclusion
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
    (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
    (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) (x : Multiplicative X),
      φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
    (hgood : ∀ x ∈ W, ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, x ∈ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀),
      IsAffineOpen V₁ → Function.Bijective
        (AddMonoidAlgebra.liftNCRingHom (q.app V₁).hom (φ V₁ (h₁.trans hV₀))
          (fun _ _ => Commute.all _ _)))
    (V : B.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)) := by
  classical
  have hbasis := AlgebraicGeometry.Scheme.isBasis_affineOpens B
  have hloc : ∀ x ∈ W, ∀ O : B.Opens, x ∈ O → ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ O ∧
      ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
        Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := by
    intro x hx O hxO
    obtain ⟨V₀, hV₀, hxV₀, hb⟩ := hgood x hx
    obtain ⟨A, hA, hxA, hAle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis) (show x ∈ O ⊓ V₀ from ⟨hxO, hxV₀⟩)
    exact ⟨A, hA, hxA, hAle.trans inf_le_left, V₀, hV₀, hAle.trans inf_le_right, hb⟩
  have hinj : ∀ (O : B.Opens) (hO : O ≤ W), Function.Injective (cm q φ O hO) := by
    intro O hO
    let ι := {A : B.Opens // IsAffineOpen A ∧ A ≤ O ∧ ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧
      ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ → Function.Bijective (cm q φ V₁ (h₁.trans hV₀))}
    refine inj_of_cover q φ hnat hO (fun a : ι => a.1) (fun a => a.2.2.1) ?_ ?_
    · intro x hx
      obtain ⟨A, hA, hxA, hAO, rest⟩ := hloc x (hO hx) O hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, hA, hAO, rest⟩, hxA⟩
    · intro a
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := a.2.2.2
      exact (hb a.1 hAV₀ a.2.1).1
  constructor
  · exact hinj V h
  · have hx : ∀ x ∈ V, ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ V ∧
        ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
          Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := fun x hxV => hloc x (h hxV) V hxV
    choose A hA using hx
    obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (A x.1 x.2 : Set B))
      (fun x => (A x.1 x.2).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hA y hy).2.1⟩)
    refine surj_of_cover q φ hnat h (fun i : t => A i.1.1 i.1.2) (fun i => (hA _ _).2.2.1) ?_ ?_
      (fun i j => hinj _ _)
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
    · intro i
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := (hA _ _).2.2.2
      exact (hb _ hAV₀ (hA _ _).1).2
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
