-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.val_secHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:44.755831+00:00
-- url     : https://prove2.me/submissions/7275bb2f-5930-435d-9391-8f4c43e489c4

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
import Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_secHom_C
import Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_map_maximalIdeal_stalk
import Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_stalkEquiv_germ
import Theorems.Thm_ReciprocityTheory_AnForm_R_val_const
import Theorems.Thm_ReciprocityTheory_AnForm_R_val_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_val_ringHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]
end ReciprocityTheory.AnForm.R.AffPres
