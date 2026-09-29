-- Prove2me | solution 1 for Rep.exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/193bf567-ae4b-5eca-be8d-329fb5616645

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho

set_option autoImplicit false
open CategoryTheory

namespace Pen5BaseH

private noncomputable def mkHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (f : A → B)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : k) (a : A), f (c • a) = c • f a)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) : A ⟶ B :=
  Rep.ofHom ⟨⟨⟨f, hadd⟩, hsmul⟩, fun g => LinearMap.ext (hcomm g)⟩

private theorem map_smul_int {V W : Type} [AddCommGroup V] [AddCommGroup W] (iV : Module ℤ V) (iW : Module ℤ W)
    (f : V →+ W) (m : ℤ) (v : V) :
    f (@SMul.smul ℤ V iV.toSMul m v) = @SMul.smul ℤ W iW.toSMul m (f v) := by
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul]

private noncomputable def mkHomInt {G : Type} [Group G] (A B : Rep.{0} ℤ G) (f : A →+ B)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) : A ⟶ B :=
  mkHom A B f f.map_add (fun c a => map_smul_int _ _ f c a) hcomm

private theorem mkHomInt_hom_apply {G : Type} [Group G] (A B : Rep.{0} ℤ G) (f : A →+ B)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) (a : A) : (mkHomInt A B f hcomm).hom a = f a := rfl

section Norm
variable {G : Type} [Group G] [Fintype G]

private noncomputable def normFun (X C : Rep.{0} ℤ G) (η : X →+ C) : X →+ C where
  toFun x := ∑ g : G, C.ρ g (η (X.ρ g⁻¹ x))
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

private theorem normFun_apply (X C : Rep.{0} ℤ G) (η : X →+ C) (x : X) :
    normFun X C η x = ∑ g : G, C.ρ g (η (X.ρ g⁻¹ x)) := rfl

private theorem normFun_comm (X C : Rep.{0} ℤ G) (η : X →+ C) (s : G) (x : X) :
    normFun X C η (X.ρ s x) = C.ρ s (normFun X C η x) := by
  simp only [normFun_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s⁻¹) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply,
    Representation.self_inv_apply]

private noncomputable def normHom (X C : Rep.{0} ℤ G) (η : X →+ C) : X ⟶ C :=
  mkHomInt X C (normFun X C η) (normFun_comm X C η)

private theorem normHom_hom_apply (X C : Rep.{0} ℤ G) (η : X →+ C) (x : X) :
    (normHom X C η).hom x = ∑ g : G, C.ρ g (η (X.ρ g⁻¹ x)) := rfl

private noncomputable def grpNorm (C : Rep.{0} ℤ G) : C →+ C where
  toFun c := ∑ g : G, C.ρ g c
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

private theorem grpNorm_apply (C : Rep.{0} ℤ G) (c : C) : grpNorm C c = ∑ g : G, C.ρ g c := rfl

end Norm

end Pen5BaseH

namespace Pen5BaseH

section Coord
variable {G : Type} [Group G] (B₀ : Rep.{0} ℤ G) {ι : Type} (a : ι → B₀) (v : B₀ → (ι →₀ ℤ))

private noncomputable def tot : MonoidAlgebra ℤ G →+ ℤ :=
  (Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

omit [Group G] in
private theorem tot_single (h : G) (n : ℤ) : tot (G := G) (MonoidAlgebra.single h n) = n := by
  simp [tot, MonoidAlgebra.coeff_single]

private noncomputable def coord : (B₀ →₀ MonoidAlgebra ℤ G) →+ (ι →₀ ℤ) :=
  (Finsupp.liftAddHom fun b => zmultiplesHom (ι →₀ ℤ) (v b)).comp (Finsupp.mapRange.addMonoidHom tot)

private theorem coord_single_single (b : B₀) (h : G) (n : ℤ) :
    coord B₀ v (Finsupp.single b (MonoidAlgebra.single h n)) = n • v b := by
  simp [coord, tot_single]

private noncomputable def sec : (ι →₀ ℤ) →+ (B₀ →₀ MonoidAlgebra ℤ G) :=
  (Finsupp.mapRange.addMonoidHom (MonoidAlgebra.singleAddHom (1 : G))).comp (Finsupp.mapDomain.addMonoidHom a)

private theorem sec_single (i : ι) (n : ℤ) : sec B₀ a (Finsupp.single i n) = Finsupp.single (a i) (MonoidAlgebra.single 1 n) := by
  simp [sec, Finsupp.mapDomain_single]

private noncomputable def lin : (ι →₀ ℤ) →+ B₀ := Finsupp.liftAddHom fun i => zmultiplesHom B₀ (a i)

private theorem lin_single (i : ι) (n : ℤ) : lin B₀ a (Finsupp.single i n) = n • a i := by
  simp [lin]

private noncomputable def cov : (B₀ →₀ MonoidAlgebra ℤ G) →+ B₀ :=
  AddMonoidHom.mk' (fun x => (Rep.freeCover B₀).hom x) fun _ _ => map_add _ _ _

private theorem cov_apply (x : B₀ →₀ MonoidAlgebra ℤ G) : cov B₀ x = (Rep.freeCover B₀).hom x := rfl

private theorem cov_single_single (htriv : ∀ (g : G) (b : B₀), B₀.ρ g b = b) (b : B₀) (h : G) (n : ℤ) :
    cov B₀ (Finsupp.single b (MonoidAlgebra.single h n)) = n • b := by
  rw [cov_apply]
  simp only [Rep.freeCover, Rep.hom_ofHom, Representation.freeLift_single_single, htriv]
  exact int_smul_eq_zsmul _ n b

variable (hv : ∀ b : B₀, lin B₀ a (v b) = b)
include hv in

private theorem cov_eq_lin_coord (htriv : ∀ (g : G) (b : B₀), B₀.ρ g b = b) (x : B₀ →₀ MonoidAlgebra ℤ G) :
    cov B₀ x = lin B₀ a (coord B₀ v x) := by
  suffices h : cov B₀ = (lin B₀ a).comp (coord B₀ v) from DFunLike.congr_fun h x
  refine Finsupp.addHom_ext fun b m => ?_
  suffices h' : (cov B₀).comp (Finsupp.singleAddHom b) = ((lin B₀ a).comp (coord B₀ v)).comp (Finsupp.singleAddHom b) from
    DFunLike.congr_fun h' m
  refine MonoidAlgebra.addMonoidHom_ext fun h n => ?_
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, cov_single_single B₀ htriv, coord_single_single,
    map_zsmul, hv]

private theorem cov_sec (htriv : ∀ (g : G) (b : B₀), B₀.ρ g b = b) (y : ι →₀ ℤ) : cov B₀ (sec B₀ a y) = lin B₀ a y := by
  suffices h : (cov B₀).comp (sec B₀ a) = lin B₀ a from DFunLike.congr_fun h y
  refine Finsupp.addHom_ext fun i n => ?_
  simp only [AddMonoidHom.comp_apply, sec_single, cov_single_single B₀ htriv, lin_single]

private theorem coord_rho (g : G) (x : B₀ →₀ MonoidAlgebra ℤ G) : coord B₀ v ((Rep.free ℤ G B₀).ρ g x) = coord B₀ v x := by
  suffices h : (coord B₀ v).comp ((Rep.free ℤ G B₀).ρ g).toAddMonoidHom = coord B₀ v from DFunLike.congr_fun h x
  refine Finsupp.addHom_ext fun b m => ?_
  suffices h' : ((coord B₀ v).comp ((Rep.free ℤ G B₀).ρ g).toAddMonoidHom).comp (Finsupp.singleAddHom b) =
      (coord B₀ v).comp (Finsupp.singleAddHom b) from DFunLike.congr_fun h' m
  refine MonoidAlgebra.addMonoidHom_ext fun h n => ?_
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, LinearMap.toAddMonoidHom_coe,
    Representation.free_single_single, coord_single_single]

end Coord

end Pen5BaseH

namespace Pen5BaseH

section Rel
variable {G : Type} [Group G] (B₀ : Rep.{0} ℤ G)

private noncomputable def _root_.Pen5BaseH.val : Rep.relationCarrier B₀ →+ (B₀ →₀ MonoidAlgebra ℤ G) :=
  AddMonoidHom.mk' (fun r => (Rep.relationModuleInt.ι B₀).hom r) fun _ _ => map_add _ _ _

p2m_export "Pen5BaseH" "val"
private theorem val_apply (r : Rep.relationCarrier B₀) : val B₀ r = (Rep.relationModuleInt.ι B₀).hom r := rfl

private theorem val_injective : Function.Injective (val B₀) := fun _ _ h => Subtype.ext h

private theorem cov_val (r : Rep.relationCarrier B₀) : cov B₀ (val B₀ r) = 0 :=
  Rep.freeCover_hom_apply_ι B₀ (show Rep.relationModule B₀ from r)

private theorem val_rho (g : G) (r : Rep.relationCarrier B₀) :
    val B₀ (Rep.relationRepInt B₀ g r) = (Rep.free ℤ G B₀).ρ g (val B₀ r) :=
  Rep.hom_comm_apply (Rep.relationModuleInt.ι B₀) g r

private noncomputable def toRel (x : B₀ →₀ MonoidAlgebra ℤ G) (hx : cov B₀ x = 0) : Rep.relationCarrier B₀ :=
  show Rep.relationModule B₀ from ⟨x, hx⟩

private theorem val_toRel (x : B₀ →₀ MonoidAlgebra ℤ G) (hx : cov B₀ x = 0) : val B₀ (toRel B₀ x hx) = x := rfl

end Rel

section Construct
variable {G : Type} [Group G] [Fintype G]

private theorem exists_extension_of_coords (C : Rep.{0} ℤ G) (p : ℕ)
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : G, C.ρ g d = d) ∧ (∑ g : G, C.ρ g c) = p • d)
    (B₀ : Rep.{0} ℤ G) (hB₀ : ∀ b : B₀, p • b = 0) (htriv : ∀ (g : G) (b : B₀), B₀.ρ g b = b)
    {ι : Type} (a : ι → B₀) (v : B₀ → (ι →₀ ℤ)) (hv : ∀ b : B₀, lin B₀ a (v b) = b)
    (hindep : ∀ z : ι →₀ ℤ, lin B₀ a z = 0 → ∃ y : ι →₀ ℤ, z = p • y)
    (φ : Rep.relationModuleInt B₀ ⟶ C) (ψ : Rep.relationCarrier B₀ →+ C)
    (hφ : ∀ x : Rep.relationModuleInt B₀, φ.hom x = ∑ g : G, C.ρ g (ψ (Rep.relationRepInt B₀ g⁻¹ x))) :
    ∃ χ : Rep.free ℤ G B₀ ⟶ C, Rep.relationModuleInt.ι B₀ ≫ χ = φ := by

  have hsR : ∀ x : B₀ →₀ MonoidAlgebra ℤ G, cov B₀ (x - sec B₀ a (coord B₀ v x)) = 0 := fun x => by
    rw [map_sub, cov_sec B₀ a htriv, cov_eq_lin_coord B₀ a v hv htriv, sub_self]
  let sR : (B₀ →₀ MonoidAlgebra ℤ G) →+ Rep.relationCarrier B₀ :=
    AddMonoidHom.mk' (fun x => toRel B₀ _ (hsR x)) fun x y => val_injective B₀ (by
      simp only [map_add, val_toRel, map_add]; abel)
  have val_sR : ∀ x, val B₀ (sR x) = x - sec B₀ a (coord B₀ v x) := fun x => rfl

  have hsecR : ∀ y : ι →₀ ℤ, cov B₀ (sec B₀ a (p • y)) = 0 := fun y => by
    rw [map_nsmul, map_nsmul, cov_sec B₀ a htriv, hB₀]
  let secR : (ι →₀ ℤ) →+ Rep.relationCarrier B₀ :=
    AddMonoidHom.mk' (fun y => toRel B₀ _ (hsecR y)) fun x y => val_injective B₀ (by
      simp only [map_add, val_toRel, map_add, smul_add])
  have val_secR : ∀ y, val B₀ (secR y) = sec B₀ a (p • y) := fun y => rfl
  let ω : (ι →₀ ℤ) →+ C := ψ.comp secR

  choose d hd using fun i : ι => hnorm (ω (Finsupp.single i 1))
  let θ : (ι →₀ ℤ) →+ C := Finsupp.liftAddHom fun i => zmultiplesHom C (d i)
  have θ_single : ∀ i n, θ (Finsupp.single i n) = n • d i := fun i n => by
    simp [θ]
  have hθ1 : ∀ (g : G) (y : ι →₀ ℤ), C.ρ g (θ y) = θ y := fun g y => by
    suffices h : (C.ρ g).toAddMonoidHom.comp θ = θ from DFunLike.congr_fun h y
    refine Finsupp.addHom_ext fun i n => ?_
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, θ_single, map_zsmul, (hd i).1]
  have hθ2 : ∀ y : ι →₀ ℤ, p • θ y = grpNorm C (ω y) := fun y => by
    let np : C →+ C := AddMonoidHom.mk' (fun c : C => p • c) fun x y => nsmul_add x y p
    suffices h : np.comp θ = (grpNorm C).comp ω from DFunLike.congr_fun h y
    refine Finsupp.addHom_ext' fun i => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, θ_single, one_zsmul]
    exact ((hd i).2).symm

  let χ₁ : Rep.free ℤ G B₀ ⟶ C := normHom (Rep.free ℤ G B₀) C (ψ.comp sR)
  let χ₂ : Rep.free ℤ G B₀ ⟶ C := mkHomInt (Rep.free ℤ G B₀) C (θ.comp (coord B₀ v)) fun g x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, coord_rho, hθ1]
  refine ⟨χ₁ + χ₂, Rep.hom_ext (DFunLike.ext _ _ fun r => ?_)⟩

  obtain ⟨y, hy⟩ := hindep (coord B₀ v (val B₀ r)) (by rw [← cov_eq_lin_coord B₀ a v hv htriv, cov_val])
  have hsRr : ∀ g : G, sR ((Rep.free ℤ G B₀).ρ g⁻¹ (val B₀ r)) = Rep.relationRepInt B₀ g⁻¹ r - secR y := fun g =>
    val_injective B₀ (by rw [val_sR, map_sub, val_rho, val_secR, coord_rho, hy])
  have h1 : χ₁.hom (val B₀ r) = φ.hom r - grpNorm C (ω y) := by
    rw [hφ, normHom_hom_apply, grpNorm_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [AddMonoidHom.comp_apply, hsRr, map_sub, map_sub]
    rfl
  have h2 : χ₂.hom (val B₀ r) = grpNorm C (ω y) := by
    rw [mkHomInt_hom_apply, AddMonoidHom.comp_apply, hy, map_nsmul, hθ2]
  change χ₁.hom (val B₀ r) + χ₂.hom (val B₀ r) = φ.hom r
  rw [h1, h2, sub_add_cancel]

end Construct

end Pen5BaseH

namespace Pen5BaseH

private theorem exists_coords {G : Type} [Group G] (B₀ : Rep.{0} ℤ G) [Fintype B₀] (p : ℕ) [Fact p.Prime]
    (hB₀ : ∀ b : B₀, p • b = 0) :
    ∃ (ι : Type) (a : ι → B₀) (v : B₀ → (ι →₀ ℤ)),
      (∀ b : B₀, lin B₀ a (v b) = b) ∧ (∀ z : ι →₀ ℤ, lin B₀ a z = 0 → ∃ y : ι →₀ ℤ, z = p • y) := by
  haveI : Module (ZMod p) B₀ := AddCommGroup.zmodModule hB₀
  obtain ⟨bs⟩ : Nonempty (Module.Basis (Module.Basis.ofVectorSpaceIndex (ZMod p) B₀) (ZMod p) B₀) :=
    ⟨Module.Basis.ofVectorSpace (ZMod p) B₀⟩
  have hlin : ∀ z : Module.Basis.ofVectorSpaceIndex (ZMod p) B₀ →₀ ℤ,
      lin B₀ (⇑bs) z = Finsupp.linearCombination (ZMod p) (⇑bs) (z.mapRange (Int.cast : ℤ → ZMod p) (Int.cast_zero)) := by
    intro z
    rw [lin, Finsupp.liftAddHom_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => zero_smul (ZMod p) (bs i))]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zmultiplesHom_apply _ (bs i) (z i)
  refine ⟨Module.Basis.ofVectorSpaceIndex (ZMod p) B₀, ⇑bs, fun b => (bs.repr b).mapRange (fun c => (c.val : ℤ)) (by simp), ?_, ?_⟩
  · intro b
    have hmm : ((bs.repr b).mapRange (fun c => (c.val : ℤ)) (by simp)).mapRange (Int.cast : ℤ → ZMod p) Int.cast_zero =
        bs.repr b := by
      ext i
      simp
    rw [hlin, hmm, Module.Basis.linearCombination_repr]
  · intro z hz
    rw [hlin] at hz
    have hz' := linearIndependent_iff.1 bs.linearIndependent _ hz
    have hdvd : ∀ i, (p : ℤ) ∣ z i := fun i => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact DFunLike.congr_fun hz' i
    refine ⟨z.mapRange (fun n => n / p) (by simp), Finsupp.ext fun i => ?_⟩
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm

end Pen5BaseH

theorem solution
    {H : Type} [Group H] [Fintype H]
    (C : Rep ℤ H) (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : H, C.ρ g d = d) ∧ (∑ g : H, C.ρ g c) = p • d)
    (B₀ : Rep ℤ H) [Fintype B₀] (hB₀ : ∀ b : B₀, p • b = 0) (htriv : ∀ (g : H) (b : B₀), B₀.ρ g b = b)
    (φ : Rep.relationModuleInt B₀ ⟶ C) (ψ : Rep.relationCarrier B₀ →+ C)
    (hφ : ∀ x : Rep.relationModuleInt B₀, φ.hom x = ∑ g : H, C.ρ g (ψ (Rep.relationRepInt B₀ g⁻¹ x))) :
    ∃ χ : Rep.free ℤ H B₀ ⟶ C, Rep.relationModuleInt.ι B₀ ≫ χ = φ := by
  obtain ⟨ι, a, v, hv, hindep⟩ := Pen5BaseH.exists_coords B₀ p hB₀
  exact Pen5BaseH.exists_extension_of_coords C p hnorm B₀ hB₀ htriv a v hv hindep φ ψ hφ

end S_Rep_exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho
end P2MW
export P2MW.S_Rep_exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho (solution)
