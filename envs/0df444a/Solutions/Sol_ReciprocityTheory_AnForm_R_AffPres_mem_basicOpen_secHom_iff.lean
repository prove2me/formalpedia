-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.mem_basicOpen_secHom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:01.77786+00:00
-- url     : https://prove2.me/submissions/fca3d01c-86df-4c31-9b8b-e6eae8618cb6

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemBasicOpenSecHomIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution (x : W) (hx : x ∈ P.V) (f : MvPolynomial (Fin P.n) ℂ) :
    x ∈ W.basicOpen (P.secHom f) ↔ f ∉ P.ptOf x hx := by
  set g := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv
    (Ideal.Quotient.mk P.K f) with hg
  have h1 : x ∈ W.basicOpen (P.secHom f) ↔
      (⟨x, hx⟩ : P.V.toScheme) ∈ P.V.toScheme.basicOpen (P.iso.hom.app ⊤ g) := by
    rw [Scheme.Opens.mem_basicOpen_toScheme]
    have e : P.secHom f = W.presheaf.map (eqToHom P.V.ι_image_top.symm).op (P.iso.hom.app ⊤ g) := rfl
    have e' := Scheme.basicOpen_res W (i := (eqToHom P.V.ι_image_top.symm).op)
      (f := (P.iso.hom.app ⊤ g : Γ(W, P.V.ι ''ᵁ ⊤)))
    rw [e]
    refine (Iff.of_eq (congrArg (fun O => x ∈ O) e')).trans ?_
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have e2 := Scheme.preimage_basicOpen P.iso.hom g
  refine h1.trans (Iff.trans (Iff.of_eq (congrArg (fun O => (⟨x, hx⟩ : P.V.toScheme) ∈ O) e2.symm)) ?_)
  show P.iso.hom.base ⟨x, hx⟩ ∈ (Spec _).basicOpen g ↔ _
  have e4 := AlgebraicGeometry.basicOpen_eq_of_affine
    (R := .of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) (Ideal.Quotient.mk P.K f)
  rw [hg, e4]
  exact Iff.rfl
end ReciprocityTheory.AnForm.R.AffPres
