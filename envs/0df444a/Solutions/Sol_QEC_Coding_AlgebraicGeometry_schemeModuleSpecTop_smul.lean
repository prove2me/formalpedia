-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModuleSpecTop_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:35.726971+00:00
-- url     : https://prove2.me/submissions/6a78bbdd-a51f-4b99-9385-4bcfc32fe706

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (A : CommRingCat.{u}) (M : (Spec A).Modules)
    (a : A) (s : Γ(M, ⊤)) : a • s = (Scheme.ΓSpecIso A).inv a • s := by
  rw [Scheme.Modules.smul_Spec_def]
  simp only [show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl, op_id]
  exact congrArg (fun t : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤) => t ((Scheme.ΓSpecIso A).inv a) • s)
    ((Spec A).presheaf.map_id _)
end QEC.Coding.AlgebraicGeometry
