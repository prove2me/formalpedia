-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.isUnit_germ_secH_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:33.628809+00:00
-- url     : https://prove2.me/submissions/d354da2c-8a8f-4669-ba0c-3910a04d4f26

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB

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
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution (v : V) (f : MvPolynomial (Fin n) ℂ) :
    IsUnit (W.presheaf.germ V v.1 v.2 (secH V K iso f)) ↔
      Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal := by

  have hSpec : IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))) ↔
      Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal := by
    have key := Scheme.mem_basicOpen (Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f)) (iso.hom.base v) trivial
    rw [basicOpen_eq_of_affine] at key
    exact key.symm.trans (PrimeSpectrum.mem_basicOpen _ _)

  have hMap : ∀ ρ, IsUnit (V.toScheme.presheaf.germ ⊤ v trivial (iso.hom.appTop ρ)) ↔
      IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial ρ) := by
    intro ρ
    change IsUnit (V.toScheme.presheaf.germ ((TopologicalSpace.Opens.map iso.hom.base).obj ⊤) v trivial
      (iso.hom.app ⊤ ρ)) ↔ _
    rw [← Scheme.Hom.germ_stalkMap_apply iso.hom ⊤ v trivial ρ]
    haveI : IsLocalHom (iso.hom.stalkMap v).hom := iso.hom.toLRSHom.prop v
    exact isUnit_map_iff (iso.hom.stalkMap v).hom _

  have hOpen : ∀ τ, IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom τ)) ↔
      IsUnit (V.toScheme.presheaf.germ ⊤ v trivial τ) := by
    intro τ
    rw [Scheme.Opens.topIso_hom]
    erw [TopCat.Presheaf.germ_res_apply]
    have h := congrArg (fun g => CommRingCat.Hom.hom g τ)
      (Scheme.Opens.germ_stalkIso_hom V (V := ⊤) v trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    refine Iff.trans ?_ (MulEquiv.isUnit_map (V.stalkIso v).commRingCatIsoToRingEquiv.toMulEquiv)
    exact iff_of_eq (congrArg IsUnit h.symm)
  show IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom (iso.hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))))) ↔ _
  rw [hOpen, hMap, hSpec]
end ReciprocityTheory.AnForm.R.StalkLocB
