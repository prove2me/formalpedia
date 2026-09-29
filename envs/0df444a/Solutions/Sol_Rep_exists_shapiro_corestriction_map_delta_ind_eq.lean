-- Prove2me | solution 1 for Rep.exists_shapiro_corestriction_map_delta_ind_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c8373f9a-3ed2-5f5e-a37f-c087658e9258

import Mathlib
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Theorems.Thm_groupCohomology_map_delta_eq_delta_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_shapiro_corestriction_map_delta_ind_eq
set_option autoImplicit false
open CategoryTheory

namespace Pen5Exf

section Norm
variable {k G : Type} [CommRing k] [Group G] (S : Subgroup G) {R C : Rep k G}

noncomputable def normTerm (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (g : G) : R →ₗ[k] C :=
  (C.ρ g) ∘ₗ ψ.hom.toLinearMap ∘ₗ (R.ρ g⁻¹)

theorem normTerm_apply (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (g : G) (x : R) :
    normTerm S ψ g x = C.ρ g (ψ.hom (R.ρ g⁻¹ x)) := rfl

theorem hom_res_comm (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (s : S) (y : R) :
    ψ.hom (R.ρ s y) = C.ρ s (ψ.hom y) := Rep.hom_comm_apply ψ s y

theorem normTerm_mul_of_mem (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (g t : G) (ht : t ∈ S) :
    normTerm S ψ (g * t) = normTerm S ψ g := by
  refine LinearMap.ext fun x => ?_
  simp only [normTerm_apply, map_mul, mul_inv_rev, Module.End.mul_apply]
  have h := hom_res_comm S ψ ⟨t, ht⟩⁻¹ (R.ρ g⁻¹ x)
  simp only [Subgroup.coe_inv] at h
  rw [h, ← Module.End.mul_apply (f := C.ρ t), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem normTerm_out (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (g : G) :
    normTerm S ψ ((QuotientGroup.mk g : G ⧸ S).out) = normTerm S ψ g := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul S g
  rw [ht]
  exact normTerm_mul_of_mem S ψ g t t.2

variable [Fintype (G ⧸ S)]

noncomputable def normLin (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) : R →ₗ[k] C :=
  ∑ q : G ⧸ S, normTerm S ψ q.out

theorem normLin_apply (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (x : R) :
    normLin S ψ x = ∑ q : G ⧸ S, C.ρ q.out (ψ.hom (R.ρ q.out⁻¹ x)) := by
  simp [normLin, LinearMap.sum_apply, normTerm_apply]

omit [Fintype (G ⧸ S)] in
theorem normTerm_out_apply_rho (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (s : G) (q : G ⧸ S) (x : R) :
    normTerm S ψ q.out (R.ρ s x) = C.ρ s (normTerm S ψ (s⁻¹ • q).out x) := by
  have hq : (QuotientGroup.mk (s⁻¹ * q.out) : G ⧸ S) = s⁻¹ • q := by
    rw [← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  rw [← hq, normTerm_out]
  simp only [normTerm_apply, map_mul, mul_inv_rev, inv_inv, Module.End.mul_apply,
    Representation.self_inv_apply]

theorem normLin_comm (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (s : G) :
    normLin S ψ ∘ₗ R.ρ s = C.ρ s ∘ₗ normLin S ψ := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, normLin, LinearMap.sum_apply, map_sum, normTerm_out_apply_rho]
  exact Equiv.sum_comp (MulAction.toPerm (s⁻¹ : G)) (fun q : G ⧸ S => C.ρ s (normTerm S ψ q.out x))

noncomputable def normHom (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) : R ⟶ C :=
  Rep.ofHom ⟨normLin S ψ, normLin_comm S ψ⟩

theorem normHom_hom_apply (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (x : R) :
    (normHom S ψ).hom x = ∑ q : G ⧸ S, C.ρ q.out (ψ.hom (R.ρ q.out⁻¹ x)) := normLin_apply S ψ x

theorem normHom_comp_right (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) {C' : Rep k G} (χ : C ⟶ C') :
    normHom S (ψ ≫ (Rep.resFunctor S.subtype).map χ) = normHom S ψ ≫ χ := by
  refine Rep.hom_ext (DFunLike.ext _ _ fun x => ?_)
  have h1 : ∀ y, (ψ ≫ (Rep.resFunctor S.subtype).map χ).hom y = χ.hom (ψ.hom y) := fun y => rfl
  have h2 : (normHom S ψ ≫ χ).hom x = χ.hom ((normHom S ψ).hom x) := rfl
  change (normHom S (ψ ≫ (Rep.resFunctor S.subtype).map χ)).hom x = (normHom S ψ ≫ χ).hom x
  rw [h2, normHom_hom_apply, normHom_hom_apply, map_sum]
  simp only [h1]
  exact Finset.sum_congr rfl fun q _ => (Rep.hom_comm_apply χ _ _).symm

theorem normHom_comp_left {R' : Rep k G} (α : R' ⟶ R) (ψ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) :
    normHom S ((Rep.resFunctor S.subtype).map α ≫ ψ) = α ≫ normHom S ψ := by
  refine Rep.hom_ext (DFunLike.ext _ _ fun x => ?_)
  have h1 : ∀ y, ((Rep.resFunctor S.subtype).map α ≫ ψ).hom y = ψ.hom (α.hom y) := fun y => rfl
  have h2 : (α ≫ normHom S ψ).hom x = (normHom S ψ).hom (α.hom x) := rfl
  change (normHom S ((Rep.resFunctor S.subtype).map α ≫ ψ)).hom x = (α ≫ normHom S ψ).hom x
  rw [h2, normHom_hom_apply, normHom_hom_apply]
  simp only [h1]
  exact Finset.sum_congr rfl fun q _ => by rw [Rep.hom_comm_apply α]

theorem normHom_id_hom_apply (C : Rep k G) (x : C) :
    (normHom S (𝟙 (Rep.res S.subtype C))).hom x = (Fintype.card (G ⧸ S)) • x := by
  rw [normHom_hom_apply]
  simp [Representation.self_inv_apply, Finset.sum_const, Finset.card_univ]

end Norm

section Theta
variable {k G : Type} [CommRing k] [Group G] (S : Subgroup G) [Fintype (G ⧸ S)]

noncomputable abbrev ev (X : Rep k S) : Rep.res S.subtype ((Rep.coindFunctor k S.subtype).obj X) ⟶ X :=
  (Rep.resCoindAdjunction k S.subtype).counit.app X

noncomputable abbrev un (X : Rep k S) : X ⟶ Rep.res S.subtype ((Rep.indFunctor k S.subtype).obj X) :=
  (Rep.indResAdjunction k S.subtype).unit.app X

noncomputable def theta (X : Rep k S) : (Rep.coindFunctor k S.subtype).obj X ⟶ (Rep.indFunctor k S.subtype).obj X :=
  normHom S (ev S X ≫ un S X)

theorem theta_natural {X Y : Rep k S} (f : X ⟶ Y) :
    (Rep.coindFunctor k S.subtype).map f ≫ theta S Y = theta S X ≫ (Rep.indFunctor k S.subtype).map f := by
  have h1 : (Rep.resFunctor S.subtype).map ((Rep.coindFunctor k S.subtype).map f) ≫ ev S Y = ev S X ≫ f :=
    (Rep.resCoindAdjunction k S.subtype).counit.naturality f
  have h2 : un S X ≫ (Rep.resFunctor S.subtype).map ((Rep.indFunctor k S.subtype).map f) = f ≫ un S Y :=
    ((Rep.indResAdjunction k S.subtype).unit.naturality f).symm
  have e1 := normHom_comp_left S ((Rep.coindFunctor k S.subtype).map f) (ev S Y ≫ un S Y)
  have e2 := normHom_comp_right S (ev S X ≫ un S X) ((Rep.indFunctor k S.subtype).map f)
  unfold theta
  refine (e1.symm.trans ?_).trans e2
  congr 1

end Theta

section MapAdd
variable {k G : Type} [CommRing k] [Group G]

theorem map_id_add {A B : Rep k G} (f g : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (f + g) n =
      groupCohomology.map (MonoidHom.id G) f n + groupCohomology.map (MonoidHom.id G) g n := by
  show HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor k G).map (f + g)) n = _
  rw [(groupCohomology.cochainsFunctor k G).map_add, HomologicalComplex.homologyMap_add]
  rfl

theorem map_id_nsmul_hom_apply {A B : Rep k G} (c : ℕ) (f : A ⟶ B) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map (MonoidHom.id G) (c • f) n).hom x = c • (groupCohomology.map (MonoidHom.id G) f n).hom x := by
  induction c with
  | zero =>
    have h0 : groupCohomology.map (MonoidHom.id G) (0 : A ⟶ B) n = 0 := (groupCohomology.functor k G n).map_zero A B
    simp [h0]
  | succ c ih =>
    rw [succ_nsmul, map_id_add, succ_nsmul]
    simp [ih]

end MapAdd

end Pen5Exf

set_option maxHeartbeats 1600000 in
theorem solution
    {G : Type} [Group G] [Fintype G] (H : Subgroup G)
    {T₀ : ShortComplex (Rep ℤ ↥H)} (hT₀ : T₀.ShortExact)
    (hT : (T₀.map (Rep.indFunctor ℤ H.subtype)).ShortExact) (C : Rep ℤ G) :
    ∃ (Sh : groupCohomology T₀.X₃ 1 →+ groupCohomology ((Rep.indFunctor ℤ H.subtype).obj T₀.X₃) 1)
      (cor : groupCohomology (Rep.res H.subtype C) 2 →+ groupCohomology C 2),
      (∀ x : groupCohomology C 2,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom x) = H.index • x) ∧
      ∀ (φ : (Rep.indFunctor ℤ H.subtype).obj T₀.X₁ ⟶ C) (y₀ : groupCohomology T₀.X₃ 1),
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT 1 2 rfl).hom (Sh y₀)) =
          cor ((groupCohomology.map (MonoidHom.id ↥H) ((Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ) 2).hom
            ((groupCohomology.δ hT₀ 1 2 rfl).hom y₀)) := by
  classical

  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_map_map_res_eq_map_norm H C 2

  have hTc : (T₀.map (Rep.coindFunctor ℤ H.subtype)).ShortExact :=
    ShortComplex.shortExact_of_iso (T₀.mapNatIso (Rep.indCoindNatIso ℤ H)) hT

  have capp : ∀ {X Y Z : ModuleCat ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun f g x => rfl

  have hsh : ∀ (X : Rep ℤ ↥H) (n : ℕ), (groupCohomology.coindIso X n).hom =
      groupCohomology.map H.subtype (Pen5Exf.ev H X) n := fun X n => by
    rw [groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one X n (Pen5Exf.ev H X) (fun f => rfl)]
    exact (groupCohomology.map_comp H.subtype (MonoidHom.id ↥H) (𝟙 (Rep.res H.subtype ((Rep.coindFunctor ℤ H.subtype).obj X)))
      (Pen5Exf.ev H X) n).symm
  refine ⟨((groupCohomology.map (MonoidHom.id G) (Pen5Exf.theta H T₀.X₃) 1).hom.toAddMonoidHom).comp
      (groupCohomology.coindIso T₀.X₃ 1).inv.hom.toAddMonoidHom, cor, fun x => ?_, fun φ y₀ => ?_⟩
  ·
    have h := hcor C (𝟙 _) (Pen5Exf.normHom H (𝟙 _)) (fun y => Pen5Exf.normHom_hom_apply H (𝟙 _) y) x
    have hN : Pen5Exf.normHom H (𝟙 (Rep.res H.subtype C)) = (Fintype.card (G ⧸ H)) • 𝟙 C :=
      Rep.hom_ext (DFunLike.ext _ _ fun y => by rw [Pen5Exf.normHom_id_hom_apply]; rfl)
    rw [groupCohomology.map_id, hN, Pen5Exf.map_id_nsmul_hom_apply, groupCohomology.map_id] at h
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact h
  ·

    set u := (groupCohomology.coindIso T₀.X₃ 1).inv.hom y₀ with hu_def
    have hy : (groupCohomology.map H.subtype (Pen5Exf.ev H T₀.X₃) 1).hom u = y₀ := by
      rw [← hsh]
      show ((groupCohomology.coindIso T₀.X₃ 1).inv ≫ (groupCohomology.coindIso T₀.X₃ 1).hom).hom y₀ = y₀
      rw [Iso.inv_hom_id]
      rfl

    have ha := groupCohomology.map_delta_eq_delta_map (MonoidHom.id G) hTc hT
      (Pen5Exf.theta H T₀.X₁) (Pen5Exf.theta H T₀.X₂) (Pen5Exf.theta H T₀.X₃)
      (Pen5Exf.theta_natural H T₀.f) (Pen5Exf.theta_natural H T₀.g) 1 2 rfl u

    have hb := groupCohomology.map_delta_eq_delta_map H.subtype hTc hT₀
      (Pen5Exf.ev H T₀.X₁) (Pen5Exf.ev H T₀.X₂) (Pen5Exf.ev H T₀.X₃)
      ((Rep.resCoindAdjunction ℤ H.subtype).counit.naturality T₀.f)
      ((Rep.resCoindAdjunction ℤ H.subtype).counit.naturality T₀.g) 1 2 rfl u

    have hc := hcor ((Rep.coindFunctor ℤ H.subtype).obj T₀.X₁)
      (Pen5Exf.ev H T₀.X₁ ≫ (Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ)
      (Pen5Exf.normHom H (Pen5Exf.ev H T₀.X₁ ≫ (Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ))
      (fun y => Pen5Exf.normHom_hom_apply H _ y) ((groupCohomology.δ hTc 1 2 rfl).hom u)

    have hN : Pen5Exf.normHom H (Pen5Exf.ev H T₀.X₁ ≫ (Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ) =
        Pen5Exf.theta H T₀.X₁ ≫ φ := by
      rw [Adjunction.homEquiv_unit, ← Category.assoc]
      exact Pen5Exf.normHom_comp_right H _ φ
    rw [hN] at hc

    have hmc : groupCohomology.map H.subtype (Pen5Exf.ev H T₀.X₁) 2 =
        groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype ((Rep.coindFunctor ℤ H.subtype).obj T₀.X₁))) 2 ≫
          groupCohomology.map (MonoidHom.id ↥H) (Pen5Exf.ev H T₀.X₁) 2 :=
      groupCohomology.map_comp H.subtype (MonoidHom.id ↥H) (𝟙 (Rep.res H.subtype ((Rep.coindFunctor ℤ H.subtype).obj T₀.X₁)))
        (Pen5Exf.ev H T₀.X₁) 2

    have haX : (groupCohomology.map (MonoidHom.id G) (Pen5Exf.theta H T₀.X₁) 2).hom ((groupCohomology.δ hTc 1 2 rfl).hom u) =
        (groupCohomology.δ hT 1 2 rfl).hom ((groupCohomology.map (MonoidHom.id G) (Pen5Exf.theta H T₀.X₃) 1).hom u) := by
      exact ha
    have hbX : (groupCohomology.map H.subtype (Pen5Exf.ev H T₀.X₁) 2).hom ((groupCohomology.δ hTc 1 2 rfl).hom u) =
        (groupCohomology.δ hT₀ 1 2 rfl).hom ((groupCohomology.map H.subtype (Pen5Exf.ev H T₀.X₃) 1).hom u) := by
      exact hb
    have hcX : cor ((groupCohomology.map (MonoidHom.id ↥H)
            (Pen5Exf.ev H T₀.X₁ ≫ (Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ) 2).hom
          ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype ((Rep.coindFunctor ℤ H.subtype).obj T₀.X₁))) 2).hom
            ((groupCohomology.δ hTc 1 2 rfl).hom u))) =
        (groupCohomology.map (MonoidHom.id G) (Pen5Exf.theta H T₀.X₁ ≫ φ) 2).hom ((groupCohomology.δ hTc 1 2 rfl).hom u) := by
      exact hc
    rw [groupCohomology.map_id_comp, capp] at hcX

    show (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT 1 2 rfl).hom
      ((groupCohomology.map (MonoidHom.id G) (Pen5Exf.theta H T₀.X₃) 1).hom u)) = _
    rw [← haX, ← hy, ← hbX, hmc, capp, hcX, groupCohomology.map_id_comp]
    rfl

end S_Rep_exists_shapiro_corestriction_map_delta_ind_eq
end P2MW
export P2MW.S_Rep_exists_shapiro_corestriction_map_delta_ind_eq (solution)
