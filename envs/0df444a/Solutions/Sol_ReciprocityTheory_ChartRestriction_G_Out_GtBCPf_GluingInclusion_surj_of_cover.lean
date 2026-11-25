-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.surj_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:49.361836+00:00
-- url     : https://prove2.me/submissions/4816aa91-9d75-4aed-bc41-c6fc5119e1d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_res_res
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
theorem _root_.solution {V : B.Opens} (h : V ≤ W) {ι : Type} [Finite ι] (U : ι → B.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ iSup U)
    (hsurj : ∀ i, Function.Surjective (cm q φ (U i) ((hU i).trans h)))
    (hinj2 : ∀ i j, Function.Injective (cm q φ (U i ⊓ U j) (inf_le_left.trans ((hU i).trans h)))) :
    Function.Surjective (cm q φ V h) := by
  classical
  intro s
  haveI := Fintype.ofFinite ι
  have hloc : ∀ i, ∃ p : AddMonoidAlgebra Γ(B, U i) X, cm q φ (U i) ((hU i).trans h) p =
      (G.presheaf.map (homOfLE (q.preimage_mono (hU i))).op).hom s := fun i => hsurj i _
  choose p hp using hloc
  have hcompat : ∀ i j,
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (p i) =
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (p j) := by
    intro i j
    apply hinj2 i j
    rw [cm_nat_apply q φ hnat _ ((hU i).trans h) inf_le_left,
      cm_nat_apply q φ hnat _ ((hU j).trans h) inf_le_right, hp i, hp j, res_res, res_res]
  have hcx : ∀ x : X, TopCat.Presheaf.IsCompatible B.sheaf.1 U (fun i => (p i).coeff x) := by
    intro x i j
    have e := congrArg (fun r => r.coeff x) (hcompat i j)
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at e
    exact e
  have hglue : ∀ x : X, ∃ c : Γ(B, V), ∀ i, (B.presheaf.map (homOfLE (hU i)).op).hom c = (p i).coeff x := by
    intro x
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' B.sheaf U V (fun i => homOfLE (hU i)) hcov
      (fun i => (p i).coeff x) (hcx x)
    exact ⟨c, hc⟩
  choose c hc using hglue
  let S : Finset X := Finset.univ.biUnion (fun i => (p i).coeff.support)
  let F : X →₀ Γ(B, V) := ∑ x ∈ S, Finsupp.single x (c x)
  have hF : ∀ x, F x = if x ∈ S then c x else 0 := by
    intro x
    simp [F, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hres : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom
      (AddMonoidAlgebra.ofCoeff F) = p i := by
    intro i
    apply AddMonoidAlgebra.coeff_injective
    ext x
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff, hF]
    split_ifs with hx
    · exact hc x i
    · rw [map_zero]
      symm
      by_contra hne
      exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩)
  refine ⟨AddMonoidAlgebra.ofCoeff F, ?_⟩
  have hcovG : q ⁻¹ᵁ V ≤ iSup (fun i => q ⁻¹ᵁ U i) := by
    have e := q.preimage_mono hcov
    rw [Scheme.Hom.preimage_iSup] at e
    exact e
  apply TopCat.Sheaf.eq_of_locally_eq' G.sheaf (fun i => q ⁻¹ᵁ U i) (q ⁻¹ᵁ V)
    (fun i => homOfLE (q.preimage_mono (hU i))) hcovG
  intro i
  have e1 := cm_nat_apply q φ hnat ((hU i).trans h) h (hU i) (AddMonoidAlgebra.ofCoeff F)
  rw [hres i, hp i] at e1
  exact e1.symm
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
