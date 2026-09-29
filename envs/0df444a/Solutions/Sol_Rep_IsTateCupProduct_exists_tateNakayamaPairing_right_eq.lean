-- Prove2me | solution 1 for Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d70bcefd-5269-5b52-a56e-90a420d54600

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_tateMap_id
import Theorems.Thm_Rep_tateMap_comp
import Theorems.Thm_Rep_IsTateCupProduct_cup_assoc
import Theorems.Thm_Rep_IsTateCupProduct_cup_comm
import Theorems.Thm_Rep_IsTateCupProduct_bijective_cup_of_h1_h2
import Theorems.Thm_Rep_IsTateCupProduct_exists_cupEv_dual_right_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq
p2m_attr_erase "simp" "Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"
universe u

namespace P2mS26TnREa

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

def ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : (M : Type u) →ₗ[k] W := f

def toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : (ihom M).obj W := f

@[scoped simp] lemma ofD_toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : ofD M W (toD M W f) = f := rfl
@[scoped simp] lemma toD_ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : toD M W (ofD M W f) = f := rfl

lemma ofD_ρ (M W : Rep.{u} k G) (g : G) (f : (ihom M).obj W) :
    ofD M W (((ihom M).obj W).ρ g f) = W.ρ g ∘ₗ ofD M W f ∘ₗ M.ρ g⁻¹ :=
  Rep.ihom_obj_ρ_apply (A := M) (B := W) g (ofD M W f)

lemma ev_tmul (M W : Rep.{u} k G) (m : M) (f : (ihom M).obj W) :
    ((ihom.ev M).app W).hom (m ⊗ₜ[k] f : (M ⊗ (ihom M).obj W : Rep.{u} k G)) = ofD M W f m := by
  change ((ihom.ev M).app W).hom.toLinearMap (m ⊗ₜ[k] f) = ofD M W f m
  rw [Rep.ihom_ev_app_hom]
  rfl

lemma whiskerRight_tmul {P Q : Rep.{u} k G} (ψ : P ⟶ Q) (C : Rep.{u} k G) (x : P) (c : C) :
    (ψ ▷ C).hom (x ⊗ₜ[k] c : (P ⊗ C : Rep.{u} k G)) = (ψ.hom x ⊗ₜ[k] c : (Q ⊗ C : Rep.{u} k G)) := by
  change (ψ ▷ C).hom.toLinearMap (x ⊗ₜ[k] c) = _
  rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor, LinearMap.rTensor_tmul]
  rfl

lemma whiskerLeft_tmul (C : Rep.{u} k G) {P Q : Rep.{u} k G} (ψ : P ⟶ Q) (c : C) (x : P) :
    (C ◁ ψ).hom (c ⊗ₜ[k] x : (C ⊗ P : Rep.{u} k G)) = (c ⊗ₜ[k] ψ.hom x : (C ⊗ Q : Rep.{u} k G)) := by
  change (C ◁ ψ).hom.toLinearMap (c ⊗ₜ[k] x) = _
  rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.toLinearMap_lTensor, LinearMap.lTensor_tmul]
  rfl

lemma braiding_tmul (A B : Rep.{u} k G) (a : A) (b : B) :
    (β_ A B).hom.hom (a ⊗ₜ[k] b : (A ⊗ B : Rep.{u} k G)) = (b ⊗ₜ[k] a : (B ⊗ A : Rep.{u} k G)) := rfl

lemma associator_tmul (A B C : Rep.{u} k G) (a : A) (b : B) (c : C) :
    (α_ A B C).hom.hom ((a ⊗ₜ[k] b) ⊗ₜ[k] c : ((A ⊗ B) ⊗ C : Rep.{u} k G))
      = (a ⊗ₜ[k] (b ⊗ₜ[k] c) : (A ⊗ (B ⊗ C) : Rep.{u} k G)) := rfl

lemma tensorUnit_eq : (𝟙_ (Rep.{u} k G)) = Rep.trivial k G k := rfl

lemma rightUnitor_tmul (C : Rep.{u} k G) (c : C) (r : k) :
    (ρ_ C).hom.hom (c ⊗ₜ[k] r : (C ⊗ Rep.trivial k G k : Rep.{u} k G)) = r • c := rfl

def thetaLin (M C : Rep.{u} k G) :
    ((C ⊗ (ihom M).obj (Rep.trivial k G k) : Rep.{u} k G) : Type u) →ₗ[k] (ihom M).obj C :=
  (dualTensorHom k M C) ∘ₗ (TensorProduct.comm k C (Module.Dual k M)).toLinearMap

lemma thetaLin_tmul (M C : Rep.{u} k G) (c : C) (f : (ihom M).obj (Rep.trivial k G k)) (m : M) :
    ofD M C (thetaLin M C (c ⊗ₜ[k] f)) m = ofD M _ f m • c := rfl

lemma thetaLin_equivariant (M C : Rep.{u} k G) (g : G) :
    thetaLin M C ∘ₗ (C ⊗ (ihom M).obj (Rep.trivial k G k)).ρ g = ((ihom M).obj C).ρ g ∘ₗ thetaLin M C := by
  refine TensorProduct.ext' fun c f => ?_
  change thetaLin M C ((C ⊗ (ihom M).obj (Rep.trivial k G k)).ρ g (c ⊗ₜ[k] f))
    = ((ihom M).obj C).ρ g (thetaLin M C (c ⊗ₜ[k] f))
  have h1 : (C ⊗ (ihom M).obj (Rep.trivial k G k)).ρ g (c ⊗ₜ[k] f)
      = (C.ρ g c ⊗ₜ[k] ((ihom M).obj (Rep.trivial k G k)).ρ g f) := by
    change (C.ρ.tprod ((ihom M).obj (Rep.trivial k G k)).ρ) g (c ⊗ₜ[k] f) = _
    rw [Representation.tprod_apply, TensorProduct.map_tmul]
  rw [h1]
  apply congrArg (toD M C) (?_ : ofD M C _ = ofD M C _)
  rw [ofD_ρ]
  refine LinearMap.ext fun m => ?_
  change ofD M _ (((ihom M).obj (Rep.trivial k G k)).ρ g f) m • C.ρ g c
    = C.ρ g (ofD M C (thetaLin M C (c ⊗ₜ[k] f)) (M.ρ g⁻¹ m))
  rw [ofD_ρ, thetaLin_tmul, map_smul]
  rfl

def theta (M C : Rep.{u} k G) : C ⊗ (ihom M).obj (Rep.trivial k G k) ⟶ (ihom M).obj C :=
  Rep.ofHom ⟨thetaLin M C, thetaLin_equivariant M C⟩

lemma theta_hom_apply (M C : Rep.{u} k G) (z : (C ⊗ (ihom M).obj (Rep.trivial k G k) : Rep.{u} k G)) :
    (theta M C).hom z = thetaLin M C z := rfl

lemma ofD_theta_tmul (M C : Rep.{u} k G) (c : C) (f : (ihom M).obj (Rep.trivial k G k)) (m : M) :
    ofD M C ((theta M C).hom (c ⊗ₜ[k] f)) m = ofD M _ f m • c := rfl

theorem ev_compat (M C : Rep.{u} k G) :
    (β_ C M).hom ▷ ((ihom M).obj (Rep.trivial k G k)) ≫ (α_ M C ((ihom M).obj (Rep.trivial k G k))).hom
        ≫ M ◁ theta M C ≫ (ihom.ev M).app C
      = (α_ C M ((ihom M).obj (Rep.trivial k G k))).hom ≫ C ◁ (ihom.ev M).app (Rep.trivial k G k) ≫ (ρ_ C).hom := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext_threefold fun c m f => ?_))
  change ((ihom.ev M).app C).hom ((M ◁ theta M C).hom ((α_ M C ((ihom M).obj (Rep.trivial k G k))).hom.hom
      (((β_ C M).hom ▷ ((ihom M).obj (Rep.trivial k G k))).hom ((c ⊗ₜ[k] m) ⊗ₜ[k] f))))
    = (ρ_ C).hom.hom ((C ◁ (ihom.ev M).app (Rep.trivial k G k)).hom
        ((α_ C M ((ihom M).obj (Rep.trivial k G k))).hom.hom ((c ⊗ₜ[k] m) ⊗ₜ[k] f)))
  refine (?_ : _ = ofD M _ f m • c).trans (?_ : ofD M _ f m • c = _)
  · rw [whiskerRight_tmul, braiding_tmul, associator_tmul, whiskerLeft_tmul, ev_tmul, ofD_theta_tmul]
  · symm
    refine (congrArg (fun t => (ρ_ C).hom.hom ((C ◁ (ihom.ev M).app (Rep.trivial k G k)).hom t))
      (associator_tmul C M _ c m f)).trans ?_
    refine (congrArg (fun t => (ρ_ C).hom.hom t)
      (whiskerLeft_tmul C ((ihom.ev M).app (Rep.trivial k G k)) c (m ⊗ₜ[k] f))).trans ?_
    refine (congrArg (fun t => (ρ_ C).hom.hom (c ⊗ₜ[k] t : (C ⊗ Rep.trivial k G k : Rep.{u} k G)))
      (ev_tmul M (Rep.trivial k G k) m f)).trans ?_
    exact rightUnitor_tmul C c _

section iso
variable (M C : Rep.{u} k G) [Module.Free k M] [Module.Finite k M]

def thetaEquiv : ((C ⊗ (ihom M).obj (Rep.trivial k G k) : Rep.{u} k G) : Type u) ≃ₗ[k] (ihom M).obj C :=
  (TensorProduct.comm k C (Module.Dual k M)).trans (dualTensorHomEquiv k M C)

lemma thetaEquiv_apply (z : (C ⊗ (ihom M).obj (Rep.trivial k G k) : Rep.{u} k G)) :
    thetaEquiv M C z = thetaLin M C z := by
  change dualTensorHomEquivOfBasis (Module.Free.chooseBasis k M) (TensorProduct.comm k C (Module.Dual k M) z) = _
  exact LinearMap.congr_fun (dualTensorHomEquivOfBasis_toLinearMap (N := C) (Module.Free.chooseBasis k M)) _

lemma bijective_theta : Function.Bijective (theta M C).hom := by
  have h : ⇑(theta M C).hom = ⇑(thetaEquiv M C) := funext fun z => (thetaEquiv_apply M C z).symm
  rw [h]
  exact (thetaEquiv M C).bijective

def thetaRepEquiv : (C ⊗ (ihom M).obj (Rep.trivial k G k)).ρ.Equiv ((ihom M).obj C).ρ :=
  Representation.Equiv.mk' ⟨thetaLin M C, thetaLin_equivariant M C⟩ (thetaEquiv M C).symm
    (fun z => by
      change (thetaEquiv M C).symm (thetaLin M C z) = z
      rw [← thetaEquiv_apply, LinearEquiv.symm_apply_apply])
    (fun h => by
      change thetaLin M C ((thetaEquiv M C).symm h) = h
      rw [← thetaEquiv_apply, LinearEquiv.apply_symm_apply])

def thetaIso : C ⊗ (ihom M).obj (Rep.trivial k G k) ≅ (ihom M).obj C :=
  Rep.mkIso (thetaRepEquiv M C)

lemma thetaIso_hom : (thetaIso M C).hom = theta M C := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  change (Rep.mkIso (thetaRepEquiv M C)).hom.hom z = thetaLin M C z
  rw [Rep.mkIso_hom_hom]
  rfl

end iso

section tate
variable [Fintype G]

lemma bijective_tateMap_of_iso {A B : Rep.{u} k G} (e : A ≅ B) (n : ℤ) :
    Function.Bijective (Rep.tateMap e.hom n).hom := by
  have h1 : ∀ x, (Rep.tateMap e.inv n).hom ((Rep.tateMap e.hom n).hom x) = x := fun x => by
    have := congrArg (fun φ => (Rep.tateMap φ n).hom x) e.hom_inv_id
    rwa [Rep.tateMap_comp, Rep.tateMap_id] at this
  have h2 : ∀ y, (Rep.tateMap e.hom n).hom ((Rep.tateMap e.inv n).hom y) = y := fun y => by
    have := congrArg (fun φ => (Rep.tateMap φ n).hom y) e.inv_hom_id
    rwa [Rep.tateMap_comp, Rep.tateMap_id] at this
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

lemma bijective_tateMap_theta (M C : Rep.{u} k G) [Module.Free k M] [Module.Finite k M] (n : ℤ) :
    Function.Bijective (Rep.tateMap (theta M C) n).hom := by
  rw [← thetaIso_hom]
  exact bijective_tateMap_of_iso (thetaIso M C) n

end tate

section dual

theorem bijective_cup_dual {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (j : ℤ) :
    Function.Bijective (fun b : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.trivial ℤ S ℤ)).tateCohomology j =>
      (cup (Rep.res S.subtype C) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.trivial ℤ S ℤ)) 2 j (j + 2) (add_comm 2 j)
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) b :
          (Rep.res S.subtype C ⊗ (ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.trivial ℤ S ℤ)).tateCohomology (j + 2))) :=
  Rep.IsTateCupProduct.bijective_cup_of_h1_h2 C u h1 h2card h2gen (V →ₗ[ℤ] ℤ)
    ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).ρ S cup hcup j

end dual

end

end P2mS26TnREa
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

namespace P2mS26TnREb

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem comp_apply' {A B C : Rep.{u} k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) (y : A.tateCohomology n) :
    (Rep.tateMap g n).hom ((Rep.tateMap f n).hom y) = (Rep.tateMap (f ≫ g) n).hom y := by
  rw [Rep.tateMap_comp]; rfl

theorem id_apply' (A : Rep.{u} k G) (n : ℤ) (y : A.tateCohomology n) : (Rep.tateMap (𝟙 A) n).hom y = y := by
  rw [Rep.tateMap_id]; rfl

theorem hom_inv_apply' {A B : Rep.{u} k G} (i : A ≅ B) (n : ℤ) (y : B.tateCohomology n) :
    (Rep.tateMap i.hom n).hom ((Rep.tateMap i.inv n).hom y) = y := by
  rw [comp_apply', Iso.inv_hom_id, id_apply']

theorem heart {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup)
    {M C P H T D : Rep.{u} k G} (θ : C ⊗ P ⟶ H) (e : M ⊗ H ⟶ D) (e' : M ⊗ P ⟶ T) (lam : C ⊗ T ⟶ D)
    (hθ : (β_ C M).hom ▷ P ≫ (α_ M C P).hom ≫ M ◁ θ ≫ e = (α_ C M P).hom ≫ C ◁ e' ≫ lam)
    (s p j r_sj r_pj r : ℤ) (hsj : s + j = r_sj) (hpj : p + j = r_pj) (h : p + r_sj = r)
    (u : C.tateCohomology s) (x : M.tateCohomology p) (b : P.tateCohomology j) :
    (Rep.tateMap e r).hom (cup M H p r_sj r h x ((Rep.tateMap θ r_sj).hom (cup C P s j r_sj hsj u b)))
      = (((s * p).negOnePow : ℤ) : k) •
        (Rep.tateMap lam r).hom (cup C T s r_pj r (by omega) u ((Rep.tateMap e' r_pj).hom (cup M P p j r_pj hpj x b))) := by

  have L1 : cup M H p r_sj r h x ((Rep.tateMap θ r_sj).hom (cup C P s j r_sj hsj u b))
      = (Rep.tateMap (M ◁ θ) r).hom (cup M (C ⊗ P) p r_sj r h x (cup C P s j r_sj hsj u b)) := by
    have t := hcup.map_cup (𝟙 M) θ p r_sj r h x (cup C P s j r_sj hsj u b)
    rw [id_apply', MonoidalCategory.id_tensorHom] at t
    exact t.symm

  have L2 : cup M (C ⊗ P) p r_sj r h x (cup C P s j r_sj hsj u b)
      = (Rep.tateMap (α_ M C P).hom r).hom (cup (M ⊗ C) P (p + s) j r (by omega) (cup M C p s (p + s) rfl x u) b) := by
    rw [hcup.cup_assoc M C P p s j (p + s) r_sj r rfl hsj (by omega) x u b, hom_inv_apply']

  have L3 : cup M C p s (p + s) rfl x u
      = (((s * p).negOnePow : ℤ) : k) • (Rep.tateMap (β_ C M).hom (p + s)).hom (cup C M s p (p + s) (by omega) u x) :=
    hcup.cup_comm C M s p (p + s) (by omega) u x

  have L4 : cup (M ⊗ C) P (p + s) j r (by omega)
        ((Rep.tateMap (β_ C M).hom (p + s)).hom (cup C M s p (p + s) (by omega) u x)) b
      = (Rep.tateMap ((β_ C M).hom ▷ P) r).hom (cup (C ⊗ M) P (p + s) j r (by omega) (cup C M s p (p + s) (by omega) u x) b) := by
    have t := hcup.map_cup (β_ C M).hom (𝟙 P) (p + s) j r (by omega) (cup C M s p (p + s) (by omega) u x) b
    rw [id_apply', MonoidalCategory.tensorHom_id] at t
    exact t.symm

  have R1 : cup C T s r_pj r (by omega) u ((Rep.tateMap e' r_pj).hom (cup M P p j r_pj hpj x b))
      = (Rep.tateMap (C ◁ e') r).hom (cup C (M ⊗ P) s r_pj r (by omega) u (cup M P p j r_pj hpj x b)) := by
    have t := hcup.map_cup (𝟙 C) e' s r_pj r (by omega) u (cup M P p j r_pj hpj x b)
    rw [id_apply', MonoidalCategory.id_tensorHom] at t
    exact t.symm

  have R2 : cup C (M ⊗ P) s r_pj r (by omega) u (cup M P p j r_pj hpj x b)
      = (Rep.tateMap (α_ C M P).hom r).hom (cup (C ⊗ M) P (p + s) j r (by omega) (cup C M s p (p + s) (by omega) u x) b) := by
    rw [hcup.cup_assoc C M P s p j (p + s) r_pj r (by omega) hpj (by omega) u x b, hom_inv_apply']
  rw [L1, L2, L3, LinearMap.map_smul₂, map_smul, map_smul, map_smul, L4,
    comp_apply' (M ◁ θ) e, comp_apply' (α_ M C P).hom, comp_apply' ((β_ C M).hom ▷ P), hθ,
    R1, R2, comp_apply' (C ◁ e') lam, comp_apply' (α_ C M P).hom]

end P2mS26TnREb
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

namespace P2mS26TnREb

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem inv_hom_apply' {A B : Rep.{u} k G} (i : A ≅ B) (n : ℤ) (y : A.tateCohomology n) :
    (Rep.tateMap i.inv n).hom ((Rep.tateMap i.hom n).hom y) = y := by
  rw [comp_apply', Iso.hom_inv_id, id_apply']

theorem bijective_tateMap_iso {A B : Rep.{u} k G} (i : A ≅ B) (n : ℤ) :
    Function.Bijective (Rep.tateMap i.hom n).hom :=
  ⟨fun y₁ y₂ hy => by rw [← inv_hom_apply' i n y₁, ← inv_hom_apply' i n y₂, hy],
    fun z => ⟨(Rep.tateMap i.inv n).hom z, hom_inv_apply' i n z⟩⟩

theorem heart_two {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup)
    {M C P H T D : Rep.{u} k G} (θ : C ⊗ P ⟶ H) (e : M ⊗ H ⟶ D) (e' : M ⊗ P ⟶ T) (lam : C ⊗ T ⟶ D)
    (hθ : (β_ C M).hom ▷ P ≫ (α_ M C P).hom ≫ M ◁ θ ≫ e = (α_ C M P).hom ≫ C ◁ e' ≫ lam)
    (p j r_sj r_pj r : ℤ) (hsj : 2 + j = r_sj) (hpj : p + j = r_pj) (h : p + r_sj = r) (h' : 2 + r_pj = r)
    (u : C.tateCohomology 2) (x : M.tateCohomology p) (b : P.tateCohomology j) :
    (Rep.tateMap e r).hom (cup M H p r_sj r h x ((Rep.tateMap θ r_sj).hom (cup C P 2 j r_sj hsj u b)))
      = (Rep.tateMap lam r).hom (cup C T 2 r_pj r h' u ((Rep.tateMap e' r_pj).hom (cup M P p j r_pj hpj x b))) := by
  rw [heart hcup θ e e' lam hθ 2 p j r_sj r_pj r hsj hpj h u x b, Int.negOnePow_two_mul, Units.val_one, Int.cast_one,
    one_smul]

section transfer

variable {cup : Rep.TateCupFamily k G} {M C P H T D : Rep.{u} k G}
  {θ : C ⊗ P ⟶ H} {e : M ⊗ H ⟶ D} {e' : M ⊗ P ⟶ T} {lam : C ⊗ T ⟶ D}
  {s p j r_sj r_pj r : ℤ} {hsj : s + j = r_sj} {hpj : p + j = r_pj} {h : p + r_sj = r} {h' : s + r_pj = r}
  {u : C.tateCohomology s}

theorem right_exists_transfer
    (compat : ∀ (x : M.tateCohomology p) (b : P.tateCohomology j),
      (Rep.tateMap e r).hom (cup M H p r_sj r h x ((Rep.tateMap θ r_sj).hom (cup C P s j r_sj hsj u b)))
        = (Rep.tateMap lam r).hom (cup C T s r_pj r h' u ((Rep.tateMap e' r_pj).hom (cup M P p j r_pj hpj x b))))
    (hΛ : Function.Bijective (fun z : T.tateCohomology r_pj => (Rep.tateMap lam r).hom (cup C T s r_pj r h' u z)))
    (hINT : ∀ φ : M.tateCohomology p →ₗ[k] T.tateCohomology r_pj, ∃ b : P.tateCohomology j,
      ∀ x : M.tateCohomology p, (Rep.tateMap e' r_pj).hom (cup M P p j r_pj hpj x b) = φ x)
    (ψ : M.tateCohomology p →ₗ[k] D.tateCohomology r) :
    ∃ a : H.tateCohomology r_sj,
      ∀ x : M.tateCohomology p, (Rep.tateMap e r).hom (cup M H p r_sj r h x a) = ψ x := by
  let Λ : T.tateCohomology r_pj ≃ₗ[k] D.tateCohomology r :=
    LinearEquiv.ofBijective ((Rep.tateMap lam r).hom ∘ₗ cup C T s r_pj r h' u) hΛ
  obtain ⟨b, hb⟩ := hINT (Λ.symm.toLinearMap ∘ₗ ψ)
  refine ⟨(Rep.tateMap θ r_sj).hom (cup C P s j r_sj hsj u b), fun x => ?_⟩
  rw [compat, hb]
  exact Λ.apply_symm_apply (ψ x)

end transfer
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

end P2mS26TnREb
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

namespace P2mS26TnREb

section trio

theorem bijective_cup_trivial {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) :
    Function.Bijective (fun z : (Rep.trivial ℤ S ℤ).tateCohomology 0 =>
      cup (Rep.res S.subtype C) (Rep.trivial ℤ S ℤ) 2 0 2 (by omega)
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) z) :=
  Rep.IsTateCupProduct.bijective_cup_of_h1_h2 C u h1 h2card h2gen ℤ (Representation.trivial ℤ G ℤ) S cup hcup 0

theorem tn_right_exists_of {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (C : Rep ℤ G) (u : C.tateCohomology 2)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (θ : C ⊗ ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) ⟶ ((ihom (Rep.of ρ)).obj C)) (hθb : ∀ n : ℤ, Function.Bijective (Rep.tateMap θ n).hom)
    (hθ : (β_ C (Rep.of ρ)).hom ▷ ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) ≫ (α_ (Rep.of ρ) C ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ))).hom ≫ (Rep.of ρ) ◁ θ ≫ ((ihom.ev (Rep.of ρ)).app C)
      = (α_ C (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ))).hom ≫ C ◁ ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) ≫ (ρ_ C).hom)
    (hdual : ∀ j : ℤ, Function.Bijective (fun b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology j =>
      cup C ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) 2 j (j + 2) (by omega) u b))
    (htriv : Function.Bijective (fun z : (Rep.trivial ℤ G ℤ).tateCohomology 0 => cup C (Rep.trivial ℤ G ℤ) 2 0 2 (by omega) u z))
    (q : ℤ)
    (φ : (Rep.of ρ).tateCohomology (2 - q) →ₗ[ℤ] C.tateCohomology 2) :
    ∃ a : ((ihom (Rep.of ρ)).obj C).tateCohomology q, ∀ x : (Rep.of ρ).tateCohomology (2 - q),
      (Rep.tateMap ((ihom.ev (Rep.of ρ)).app C) 2).hom (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj C) (2 - q) q 2 (by omega) x a) = φ x := by
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 2 := ⟨q - 2, by omega⟩
  have hB : Function.Bijective (fun b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology j =>
      (Rep.tateMap θ (j + 2)).hom (cup C ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) 2 j (j + 2) (by omega) u b)) :=
    (hθb (j + 2)).comp (hdual j)
  have hΛ : Function.Bijective (fun z : (Rep.trivial ℤ G ℤ).tateCohomology 0 =>
      (Rep.tateMap (ρ_ C).hom 2).hom (cup C (Rep.trivial ℤ G ℤ) 2 0 2 (by omega) u z)) :=
    (bijective_tateMap_iso (ρ_ C) 2).comp htriv
  have compat : ∀ (x : (Rep.of ρ).tateCohomology (2 - (j + 2))) (b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology j),
      (Rep.tateMap ((ihom.ev (Rep.of ρ)).app C) 2).hom (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj C) (2 - (j + 2)) (j + 2) 2 (by omega) x
        ((Rep.tateMap θ (j + 2)).hom (cup C ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) 2 j (j + 2) (by omega) u b)))
      = (Rep.tateMap (ρ_ C).hom 2).hom (cup C (Rep.trivial ℤ G ℤ) 2 0 2 (by omega) u
        ((Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) (2 - (j + 2)) j 0 (by omega) x b))) :=
    fun x b => heart_two hcup θ ((ihom.ev (Rep.of ρ)).app C) ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) (ρ_ C).hom hθ (2 - (j + 2)) j (j + 2) 0 2
      (by omega) (by omega) (by omega) (by omega) u x b
  exact right_exists_transfer (hsj := by omega) (hpj := by omega) (h := by omega) (h' := by omega) compat hΛ
    (Rep.IsTateCupProduct.exists_cupEv_dual_right_eq hcup V ρ (2 - (j + 2)) j (by omega)) φ

end trio
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

end P2mS26TnREb
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.P2mS26TnREa"

theorem solution {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (q : ℤ)
    (φ : (Rep.res S.subtype (Rep.of ρ)).tateCohomology (2 - q) →ₗ[ℤ] groupCohomology (Rep.res S.subtype C) 2) :
    ∃ a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q,
      ∀ x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology (2 - q),
        (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
          (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C))
            (2 - q) q 2 (by omega) x a) = φ x := by
  exact P2mS26TnREb.tn_right_exists_of hcup (Rep.res S.subtype C)
    ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) V (ρ.comp S.subtype)
    (P2mS26TnREa.theta (Rep.res S.subtype (Rep.of ρ)) (Rep.res S.subtype C)) (P2mS26TnREa.bijective_tateMap_theta (Rep.res S.subtype (Rep.of ρ)) (Rep.res S.subtype C))
    (P2mS26TnREa.ev_compat (Rep.res S.subtype (Rep.of ρ)) (Rep.res S.subtype C))
    (P2mS26TnREa.bijective_cup_dual C u h1 h2card h2gen V ρ S cup hcup)
    (P2mS26TnREb.bijective_cup_trivial C u h1 h2card h2gen S cup hcup) q φ

end S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq
end P2MW
export P2MW.S_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq (solution)
