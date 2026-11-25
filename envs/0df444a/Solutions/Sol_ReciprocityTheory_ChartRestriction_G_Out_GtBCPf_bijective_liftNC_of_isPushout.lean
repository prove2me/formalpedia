-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bijective_liftNC_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:17.971987+00:00
-- url     : https://prove2.me/submissions/4aaf4208-8a08-4919-a3e0-7f8ea76ef7a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
universe u
variable {R A R' A' : CommRingCat.{u}} {qa : R ⟶ A} {ba : R ⟶ R'} {ga : A ⟶ A'} {qa' : R' ⟶ A'}
  {X : Type u} [AddCommMonoid X]
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (hP : IsPushout qa ba ga qa')
    (φ : Multiplicative X →* A) (φ' : Multiplicative X →* A') (hφ' : ∀ x, φ' x = ga (φ x))
    (hφ : Function.Bijective (AddMonoidAlgebra.liftNCRingHom qa.hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom qa'.hom φ' (fun _ _ => Commute.all _ _)) := by
  classical
  let F : AddMonoidAlgebra R' X →+* A' := AddMonoidAlgebra.liftNCRingHom qa'.hom φ' (fun _ _ => Commute.all _ _)
  let e : AddMonoidAlgebra R X ≃+* A := RingEquiv.ofBijective _ hφ
  let Mp : AddMonoidAlgebra R X →+* AddMonoidAlgebra R' X := AddMonoidAlgebra.mapRingHom X ba.hom
  have he : ∀ (x : X) (r : R), e (AddMonoidAlgebra.single x r) = qa.hom r * φ (Multiplicative.ofAdd x) := by
    intro x r
    simp [e, AddMonoidAlgebra.liftNC_single]
  have hF : ∀ (x : X) (r : R'), F (AddMonoidAlgebra.single x r) = qa'.hom r * φ' (Multiplicative.ofAdd x) := by
    intro x r
    simp [F, AddMonoidAlgebra.liftNC_single]
  have hM : ∀ (x : X) (r : R), Mp (AddMonoidAlgebra.single x r) = AddMonoidAlgebra.single x (ba.hom r) := by
    intro x r
    simp [Mp]
  have hw : ∀ r : R, ga.hom (qa.hom r) = qa'.hom (ba.hom r) := fun r => congrArg (fun f => f.hom r) hP.w
  have hes0 : ∀ r : R, e.symm (qa.hom r) = AddMonoidAlgebra.single 0 r := by
    intro r
    rw [RingEquiv.symm_apply_eq, he]
    simp
  have hes1 : ∀ x : X, e.symm (φ (Multiplicative.ofAdd x)) = AddMonoidAlgebra.single x 1 := by
    intro x
    rw [RingEquiv.symm_apply_eq, he]
    simp
  let u : A ⟶ CommRingCat.of (AddMonoidAlgebra R' X) := CommRingCat.ofHom (Mp.comp (e.symm : A →+* AddMonoidAlgebra R X))
  let v : R' ⟶ CommRingCat.of (AddMonoidAlgebra R' X) := CommRingCat.ofHom (algebraMap R' (AddMonoidAlgebra R' X))
  have hcond : qa ≫ u = ba ≫ v := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    show Mp (e.symm (qa.hom r)) = algebraMap R' (AddMonoidAlgebra R' X) (ba.hom r)
    rw [hes0, hM]
    rfl
  let G := hP.desc u v hcond
  have hG1 : ∀ a : A, G.hom (ga.hom a) = Mp (e.symm a) := fun a => congrArg (fun f => f.hom a) (hP.inl_desc u v hcond)
  have hG2 : ∀ r : R', G.hom (qa'.hom r) = AddMonoidAlgebra.single 0 r := fun r => congrArg (fun f => f.hom r) (hP.inr_desc u v hcond)
  have hleft : (G.hom).comp F = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, hF]
      simp [hG2]
    · intro x
      rw [RingHom.comp_apply, hF, map_one, one_mul, hφ', hG1, hes1, hM, map_one]
      rfl
  have hright : ∀ a : A', F (G.hom a) = a := by
    have h3 : G ≫ CommRingCat.ofHom F = 𝟙 A' := by
      apply hP.hom_ext
      · ext a
        show F (G.hom (ga.hom a)) = ga.hom a
        rw [hG1]
        obtain ⟨p, rfl⟩ := e.surjective a
        rw [RingEquiv.symm_apply_apply]
        have h4 : F.comp Mp = ga.hom.comp (e : AddMonoidAlgebra R X →+* A) := by
          apply AddMonoidAlgebra.ringHom_ext
          · intro r
            rw [RingHom.comp_apply, RingHom.comp_apply, hM, hF]
            simp [he, hw]
          · intro x
            rw [RingHom.comp_apply, RingHom.comp_apply, hM, hF, map_one, map_one, one_mul, hφ']
            simp [he]
        exact congrArg (fun f => f p) h4
      · ext r
        show F (G.hom (qa'.hom r)) = qa'.hom r
        rw [hG2, hF]
        simp
    intro a
    exact congrArg (fun f => f.hom a) h3
  exact Function.bijective_iff_has_inverse.mpr ⟨G.hom, fun p => congrArg (fun f => f p) hleft, hright⟩
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
