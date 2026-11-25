-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:45.029115+00:00
-- url     : https://prove2.me/submissions/ac7a0ed6-4a22-45f8-8f05-e7341a49dda5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isUnit_eq_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_bijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution [TwoUniqueSums X] {w : Γ((splitTorus (Spec (.of K)) X).left, ⊤)} (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a : X), IsUnit c ∧
      w = (splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a := by
  obtain ⟨a, c, hc, he⟩ := isUnit_eq_single (hw.map (torusGamma K X).hom)
  refine ⟨(Scheme.ΓSpecIso (.of K)).inv.hom c, a, hc.map _, (torusGamma_bijective K X).1 ?_⟩
  rw [he, map_mul, torusGamma_const, torusGamma_chi, single_mul_single, zero_add, mul_one]
  have hinv : (Scheme.ΓSpecIso (.of K)).hom.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c) = c := by
    first
    | exact congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (.of K)).inv_hom_id
    | (simp; done)
  rw [hinv]
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
