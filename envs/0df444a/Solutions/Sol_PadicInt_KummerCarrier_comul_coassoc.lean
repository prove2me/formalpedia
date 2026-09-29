-- Prove2me | solution 1 for PadicInt.KummerCarrier.comul_coassoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/edcfac15-0393-5a66-9133-347180a8d960

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_KummerCarrier_comul_coassoc

open scoped TensorProduct
open PadicInt.KummerCarrier Polynomial

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u) := by
  have hp : (0:ℕ) < p := (Fact.out : p.Prime).pos

  have hlift_root : ∀ {T : Type} [CommRing T] [Algebra ℤ_[p] T] (j : ZMod p) (w : T) (hwj),
      AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] T) w hwj
        (AdjoinRoot.root (kpoly p u j)) = w := by
    intro T _ _ j w hwj
    rw [show AdjoinRoot.root (kpoly p u j) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]

  have hΔ_comp : ∀ (h : Carrier p u) (a b : ZMod p),
      piPiEquiv p u (Δ p u h) a b = μ p u a b h := fun h a b => by
    have hrfl : Δ p u h = (piPiEquiv p u).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl

  have hmap_eval : ∀ (a b : ZMod p) (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
        (Pi.evalAlgHom ℤ_[p] (A p u) b) y = piPiEquiv p u y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

  let E3 : Carrier p u ⊗[ℤ_[p]] (Carrier p u ⊗[ℤ_[p]] Carrier p u) ≃ₐ[ℤ_[p]]
      Π a : ZMod p, Π b : ZMod p, Π c : ZMod p,
        A p u a ⊗[ℤ_[p]] (A p u b ⊗[ℤ_[p]] A p u c) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl) (piPiEquiv p u)).trans <|
    (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
    (Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] _ (A p u)).trans <|
    AlgEquiv.piCongrRight fun a =>
      (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
      (Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (A p u a)
        (fun b => Π c : ZMod p, A p u b ⊗[ℤ_[p]] A p u c)).trans <|
      AlgEquiv.piCongrRight fun b =>
        Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (A p u a)
          (fun c => A p u b ⊗[ℤ_[p]] A p u c)

  have hE3_zero : E3 0 = 0 := map_zero E3
  have hE3_add : ∀ x y, E3 (x + y) = E3 x + E3 y := fun x y => map_add E3 x y

  have hcongr_tmul : ∀ (f : Carrier p u) (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℤ_[p]) (A₁ := Carrier p u))
        (piPiEquiv p u)) (f ⊗ₜ y) = f ⊗ₜ (piPiEquiv p u y) := fun f y => rfl

  have hE3_tmul : ∀ (f g k : Carrier p u) (a b c : ZMod p),
      E3 (f ⊗ₜ (g ⊗ₜ k)) a b c = (f a) ⊗ₜ ((g b) ⊗ₜ (k c)) := by
    intro f g k a b c
    simp only [E3, AlgEquiv.trans_apply, hcongr_tmul, piPiEquiv_tmul,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.piRight_tmul,
      AlgEquiv.piCongrRight_apply]

  have hE3 : ∀ (y : Carrier p u ⊗[ℤ_[p]] (Carrier p u ⊗[ℤ_[p]] Carrier p u)) (a b c : ZMod p),
      E3 y a b c = Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) b)
          (Pi.evalAlgHom ℤ_[p] (A p u) c)) y := by
    intro y a b c
    induction y using TensorProduct.induction_on with
    | zero => rw [hE3_zero]; simp only [Pi.zero_apply, map_zero]
    | tmul f yy =>
      induction yy using TensorProduct.induction_on with
      | zero =>
        rw [TensorProduct.tmul_zero, hE3_zero]
        simp only [Pi.zero_apply, map_zero]
      | tmul g k =>
        rw [hE3_tmul]
        simp only [Algebra.TensorProduct.map_tmul, Pi.evalAlgHom_apply]
      | add y1 y2 hy1 hy2 =>
        rw [TensorProduct.tmul_add, hE3_add]
        simp only [Pi.add_apply, hy1, hy2, map_add]
    | add y1 y2 hy1 hy2 =>
      rw [hE3_add]; simp only [Pi.add_apply, hy1, hy2, map_add]

  have hsum3 : ∀ (x y : ℕ), x/p + (x%p + y)/p = (x+y)/p := fun x y => by
    conv_rhs => rw [← Nat.div_add_mod x p, Nat.add_assoc, Nat.mul_add_div hp]
  have hcfac_2cocycle : ∀ (a b c : ZMod p),
      cfac p u (a+b) c * cfac p u a b = cfac p u a (b+c) * cfac p u b c := by
    intro a b c
    unfold PadicInt.KummerCarrier.cfac
    rw [← pow_add, ← pow_add]
    congr 1
    have eL : ((a+b).val + c.val)/p + (a.val+b.val)/p = (a.val+b.val+c.val)/p := by
      rw [ZMod.val_add, Nat.add_comm (((a.val+b.val)%p + c.val)/p), hsum3]
    have eR : (a.val + (b+c).val)/p + (b.val+c.val)/p = (a.val+b.val+c.val)/p := by
      rw [ZMod.val_add, Nat.add_comm a.val,
        Nat.add_comm (((b.val+c.val)%p + a.val)/p), hsum3,
        show b.val+c.val+a.val = a.val+b.val+c.val from by ring]
    rw [eL, eR]

  have hμ_at_j : ∀ (a' b' j : ZMod p) (hj : j.val = (a'+b').val) (h : Carrier p u),
      μ p u a' b' h = AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId _ _)
        (cfac p u a' b' • (z p u a' ⊗ₜ z p u b'))
        (by
          simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p, hj]
          rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a'),
            Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b'),
            TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl) (h j) := by
    intro a' b' j hj h
    obtain rfl : j = a'+b' := ZMod.val_injective p (hj.trans rfl)
    rfl

  apply AlgHom.ext; intro h
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  apply E3.injective
  funext a b c
  rw [hE3, hE3]
  show Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
      (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) b)
        (Pi.evalAlgHom ℤ_[p] (A p u) c))
      (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p] (Carrier p u) (Carrier p u) (Carrier p u)
        ((Algebra.TensorProduct.map (Δ p u) (AlgHom.id ℤ_[p] (Carrier p u))) (Δ p u h)))
    = Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
      (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) b)
        (Pi.evalAlgHom ℤ_[p] (A p u) c))
      ((Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (Carrier p u)) (Δ p u)) (Δ p u h))

  have hR1 : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) b)
          (Pi.evalAlgHom ℤ_[p] (A p u) c))
        (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (Carrier p u)) (Δ p u) y)
      = Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a) (μ p u b c) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Pi.evalAlgHom_apply]
      rw [hmap_eval, hΔ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  let μlift_bc : A p u (b+c) →ₐ[ℤ_[p]] A p u b ⊗[ℤ_[p]] A p u c :=
    AdjoinRoot.liftAlgHom (kpoly p u (b+c)) (Algebra.ofId _ _)
      (cfac p u b c • (z p u b ⊗ₜ z p u c))
      (by
        simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
          _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
        rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
          Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u c),
          TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
          ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
        rfl)
  have hR2 : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a) (μ p u b c) y
      = Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u a)) μlift_bc
          (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
            (Pi.evalAlgHom ℤ_[p] (A p u) (b+c)) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Pi.evalAlgHom_apply]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  have hL1 : ∀ (y : (Carrier p u ⊗[ℤ_[p]] Carrier p u) ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) b)
          (Pi.evalAlgHom ℤ_[p] (A p u) c))
        (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p] (Carrier p u) (Carrier p u) (Carrier p u) y)
      = Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p] (A p u a) (A p u b) (A p u c)
          (Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
              (Pi.evalAlgHom ℤ_[p] (A p u) b))
            (Pi.evalAlgHom ℤ_[p] (A p u) c) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul xy zz =>
      induction xy using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | tmul xx yy =>
        simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
          Pi.evalAlgHom_apply]
      | add x1 x2 hx1 hx2 =>
        simp only [TensorProduct.add_tmul, map_add, hx1, hx2]
    | add y1 y2 hy1 hy2 => simp only [map_add, hy1, hy2]
  have hL2 : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map
        (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a)
          (Pi.evalAlgHom ℤ_[p] (A p u) b))
        (Pi.evalAlgHom ℤ_[p] (A p u) c)
        (Algebra.TensorProduct.map (Δ p u) (AlgHom.id ℤ_[p] (Carrier p u)) y)
      = Algebra.TensorProduct.map (μ p u a b) (Pi.evalAlgHom ℤ_[p] (A p u) c) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Pi.evalAlgHom_apply]
      rw [hmap_eval, hΔ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  let μlift_ab : A p u (a+b) →ₐ[ℤ_[p]] A p u a ⊗[ℤ_[p]] A p u b :=
    AdjoinRoot.liftAlgHom (kpoly p u (a+b)) (Algebra.ofId _ _)
      (cfac p u a b • (z p u a ⊗ₜ z p u b))
      (by
        simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
          _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
        rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
          Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
          TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
          ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
        rfl)
  have hL3 : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (μ p u a b) (Pi.evalAlgHom ℤ_[p] (A p u) c) y
      = Algebra.TensorProduct.map μlift_ab (AlgHom.id ℤ_[p] (A p u c))
          (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) (a+b))
            (Pi.evalAlgHom ℤ_[p] (A p u) c) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Pi.evalAlgHom_apply]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  conv_rhs => rw [hR1, hR2, hmap_eval, hΔ_comp]
  conv_lhs => rw [hL1, hL2, hL3, hmap_eval, hΔ_comp]

  set j := a + (b + c) with hj_def
  have hj_L : j.val = ((a+b)+c).val := by rw [hj_def, add_assoc]
  have hj_R : j.val = (a+(b+c)).val := by rw [hj_def]
  let liftL : A p u j →ₐ[ℤ_[p]] A p u (a+b) ⊗[ℤ_[p]] A p u c :=
    AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId _ _)
      (cfac p u (a+b) c • (z p u (a+b) ⊗ₜ z p u c))
      (by
        simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
          _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p, hj_L]
        rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u (a+b)),
          Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u c),
          TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
          ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
        rfl)
  let liftR : A p u j →ₐ[ℤ_[p]] A p u a ⊗[ℤ_[p]] A p u (b+c) :=
    AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId _ _)
      (cfac p u a (b+c) • (z p u a ⊗ₜ z p u (b+c)))
      (by
        simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
          _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p, hj_R]
        rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
          Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u (b+c)),
          TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
          ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
        rfl)
  have hμL : μ p u (a+b) c h = liftL (h j) := hμ_at_j (a+b) c j hj_L h
  have hμR : μ p u a (b+c) h = liftR (h j) := hμ_at_j a (b+c) j hj_R h
  rw [hμL, hμR]

  have hliftL_root : liftL (AdjoinRoot.root (kpoly p u j))
      = cfac p u (a+b) c • (z p u (a+b) ⊗ₜ z p u c) := hlift_root j _ _
  have hliftR_root : liftR (AdjoinRoot.root (kpoly p u j))
      = cfac p u a (b+c) • (z p u a ⊗ₜ z p u (b+c)) := hlift_root j _ _
  have hμab_root : μlift_ab (z p u (a+b))
      = cfac p u a b • (z p u a ⊗ₜ z p u b) := hlift_root (a+b) _ _
  have hμbc_root : μlift_bc (z p u (b+c))
      = cfac p u b c • (z p u b ⊗ₜ z p u c) := hlift_root (b+c) _ _
  have key :
      (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (A p u a) (A p u b) (A p u c)).toAlgHom.comp
        ((Algebra.TensorProduct.map μlift_ab (AlgHom.id ℤ_[p] (A p u c))).comp liftL)
      = (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u a)) μlift_bc).comp liftR := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    show (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p] (A p u a) (A p u b) (A p u c))
        ((Algebra.TensorProduct.map μlift_ab (AlgHom.id ℤ_[p] (A p u c)))
          (liftL (AdjoinRoot.root (kpoly p u j))))
      = (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u a)) μlift_bc)
          (liftR (AdjoinRoot.root (kpoly p u j)))
    rw [hliftL_root, hliftR_root]

    rw [show (Algebra.TensorProduct.map μlift_ab (AlgHom.id ℤ_[p] (A p u c)))
          (cfac p u (a+b) c • (z p u (a+b) ⊗ₜ z p u c))
        = cfac p u (a+b) c • (μlift_ab (z p u (a+b)) ⊗ₜ z p u c) from by
          rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply],
      hμab_root]

    rw [show (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u a)) μlift_bc)
          (cfac p u a (b+c) • (z p u a ⊗ₜ z p u (b+c)))
        = cfac p u a (b+c) • (z p u a ⊗ₜ μlift_bc (z p u (b+c))) from by
          rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply],
      hμbc_root]

    rw [show ((cfac p u a b • (z p u a ⊗ₜ z p u b)) ⊗ₜ[ℤ_[p]] z p u c
          : (A p u a ⊗[ℤ_[p]] A p u b) ⊗[ℤ_[p]] A p u c)
        = cfac p u a b • ((z p u a ⊗ₜ z p u b) ⊗ₜ z p u c) from rfl,
      map_smul, map_smul, Algebra.TensorProduct.assoc_tmul, smul_smul]
    rw [show ((z p u a) ⊗ₜ[ℤ_[p]] (cfac p u b c • (z p u b ⊗ₜ z p u c))
          : A p u a ⊗[ℤ_[p]] (A p u b ⊗[ℤ_[p]] A p u c))
        = cfac p u b c • (z p u a ⊗ₜ (z p u b ⊗ₜ z p u c)) from
          TensorProduct.tmul_smul _ _ _,
      smul_smul]
    rw [hcfac_2cocycle a b c]
  exact DFunLike.congr_fun key (h j)

end S_PadicInt_KummerCarrier_comul_coassoc
end P2MW
export P2MW.S_PadicInt_KummerCarrier_comul_coassoc (solution)
