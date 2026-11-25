-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus_const_mul_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:38.783107+00:00
-- url     : https://prove2.me/submissions/22af81a2-4e72-4ad4-a1ec-a7698cdb2cb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
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
theorem _root_.solution {c₁ c₂ : Γ(Spec (.of K), ⊤)} (h1 : IsUnit c₁) {a : X}
    (h : (splitTorus (Spec (.of K)) X).hom.appTop.hom c₁ * chi X a =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom c₂) : a = 0 := by
  have h' := congrArg (torusGamma K X).hom h
  rw [map_mul, torusGamma_const, torusGamma_chi, torusGamma_const, single_mul_single, zero_add,
    mul_one] at h'
  have hc : (Scheme.ΓSpecIso (.of K)).hom.hom c₁ ≠ 0 :=
    (h1.map (Scheme.ΓSpecIso (.of K)).hom.hom).ne_zero
  first
  | exact (((AddMonoidAlgebra.single_eq_single_iff _ _ _ _).1 h').resolve_right (fun h => hc h.1)).1
  | exact ((AddMonoidAlgebra.single_eq_single_iff.1 h').resolve_right (fun h => hc h.1)).1
  | (simp [AddMonoidAlgebra.single_eq_single_iff, hc] at h'; exact h'.1)
  | (simp [hc] at h'; exact h'.1)
  | (simp [hc] at h'; exact h')
  | (by_contra ha
     have h2 := congrArg (fun p => AddMonoidAlgebra.coeff p a) h'
     simp [Ne.symm ha] at h2
     exact hc h2)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
