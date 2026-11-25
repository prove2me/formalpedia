-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:39.892929+00:00
-- url     : https://prove2.me/submissions/3b5a7f96-99e1-4f75-be44-bc87a8051980

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetZero_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precomp


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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (u : Sp ℂ ⟶ Y) (m : ℕ) :
    spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u = jetPt (fun _ => u) (isHolFam_const u) m := by
  have hl : IsLocalHom ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m) (fun _ => 0) (fun _ => Ideal.zero_mem _)
  have h1 := jetPt_precomp (fun _ => u) (fun _ => u) (isHolFam_const u) (isHolFam_const u) rfl m
    ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)
    (fun U _ f => by simp only [jetOf_const, AlgHom.coe_toRingHom, AlgHom.commutes])
  rw [← h1]
  have h2 : ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    exact RingHom.ext fun a => jetZero_eq m a
  have h3 : spMap ((algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫
        spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    first
    | rfl
    | (simp only [spMap]; rw [← Spec.map_comp]; rfl)
    | (unfold spMap; rw [← Spec.map_comp]; rfl)
  rw [h2, h3, Category.assoc, jetPt_aug]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
