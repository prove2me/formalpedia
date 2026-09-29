-- Prove2me | solution 1 for PadicInt.KummerCarrier.bialgebra_axioms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/59f712ed-e5fd-583b-92e1-64265f132922

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import Theorems.Thm_PadicInt_KummerCarrier_comul_coassoc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_KummerCarrier_bialgebra_axioms

open scoped TensorProduct
open PadicInt.KummerCarrier Polynomial

set_option maxHeartbeats 6400000 in
theorem solution (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u)) ∧
    ((Algebra.TensorProduct.map (ε p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u)
      = (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).symm) ∧
    ((Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (ε p u)).comp (Δ p u)
      = (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).symm) ∧
    (∀ h, (TensorProduct.comm ℤ_[p] (Carrier p u) (Carrier p u)) (Δ p u h) = Δ p u h) := by
  have hp : (0:ℕ) < p := (Fact.out : p.Prime).pos

  have hΔ_comp : ∀ (h : Carrier p u) (a b : ZMod p),
      piPiEquiv p u (Δ p u h) a b = μ p u a b h := fun h a b => by
    have hrfl : Δ p u h = (piPiEquiv p u).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl

  have hmap_eval : ∀ (a b : ZMod p) (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a) (Pi.evalAlgHom ℤ_[p] (A p u) b) y
        = piPiEquiv p u y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

  have hcomm_piPi : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u) (a b : ZMod p),
      piPiEquiv p u (TensorProduct.comm ℤ_[p] (Carrier p u) (Carrier p u) y) a b
        = Algebra.TensorProduct.comm ℤ_[p] (A p u b) (A p u a) (piPiEquiv p u y b a) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul, piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

  have hcfac_zero : ∀ k : ZMod p, cfac p u 0 k = 1 ∧ cfac p u k 0 = 1 := fun k => by
    have h1 : ((0:ZMod p).val + k.val) / p = 0 := by
      rw [ZMod.val_zero, Nat.zero_add]; exact Nat.div_eq_of_lt k.val_lt
    have h2 : (k.val + (0:ZMod p).val) / p = 0 := by
      rw [ZMod.val_zero, Nat.add_zero]; exact Nat.div_eq_of_lt k.val_lt
    have h0 : k.val / p = 0 := Nat.div_eq_of_lt k.val_lt
    unfold PadicInt.KummerCarrier.cfac
    simp [h0, h1, h2]

  have hcfac_symm : ∀ a b : ZMod p, cfac p u a b = cfac p u b a := fun a b => by
    unfold PadicInt.KummerCarrier.cfac; rw [Nat.add_comm]

  have hμ_at_j : ∀ (a b j : ZMod p) (hj : j.val = (a+b).val) (h : Carrier p u),
      μ p u a b h = AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId _ _)
        (cfac p u a b • (z p u a ⊗ₜ z p u b))
        (by
          simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p, hj]
          rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
            Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
            TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl) (h j) := by
    intro a b j hj h
    obtain rfl : j = a+b := ZMod.val_injective p (hj.trans rfl)
    rfl

  have hlift_root : ∀ {T : Type} [CommRing T] [Algebra ℤ_[p] T] (j : ZMod p) (w : T) (hwj),
      AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] T) w hwj
        (AdjoinRoot.root (kpoly p u j)) = w := by
    intro T _ _ j w hwj
    rw [show AdjoinRoot.root (kpoly p u j) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  refine ⟨PadicInt.KummerCarrier.comul_coassoc p u, ?_, ?_, ?_⟩

  · apply AlgHom.ext; intro h
    apply (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).injective
    conv_rhs => rw [show (↑(Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).symm :
        Carrier p u →ₐ[ℤ_[p]] _) h = (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).symm h from rfl,
      AlgEquiv.apply_symm_apply]
    simp only [AlgHom.comp_apply]
    funext k
    let εlift₀ : A p u 0 →ₐ[ℤ_[p]] ℤ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u 0) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
        (by simp [kpoly, ZMod.val_zero])

    have hlid_k : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
        (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u) (Algebra.TensorProduct.map (ε p u)
          (AlgHom.id ℤ_[p] (Carrier p u)) y)) k
        = Algebra.TensorProduct.lmul' ℤ_[p]
            (Algebra.TensorProduct.map ((Algebra.ofId ℤ_[p] (A p u k)).comp εlift₀)
              (AlgHom.id ℤ_[p] (A p u k))
              (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) 0)
                (Pi.evalAlgHom ℤ_[p] (A p u) k) y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f g =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lid_tmul,
          Pi.smul_apply, AlgHom.comp_apply, Algebra.ofId_apply, Pi.evalAlgHom_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, Algebra.smul_def]
        rfl
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    rw [hlid_k, hmap_eval, hΔ_comp,
      hμ_at_j 0 k k (by rw [ZMod.val_add, ZMod.val_zero, Nat.zero_add,
        Nat.mod_eq_of_lt k.val_lt]) h]

    set x := h k
    let μlift0k : A p u k →ₐ[ℤ_[p]] A p u 0 ⊗[ℤ_[p]] A p u k :=
      AdjoinRoot.liftAlgHom (kpoly p u k) (Algebra.ofId _ _)
        (cfac p u 0 k • (z p u 0 ⊗ₜ z p u k))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u 0),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u k),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            congr 2
            rw [ZMod.val_add, ZMod.val_zero, Nat.zero_add, Nat.mod_eq_of_lt k.val_lt])
    have key : (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map ((Algebra.ofId ℤ_[p] (A p u k)).comp εlift₀)
          (AlgHom.id ℤ_[p] (A p u k))).comp μlift0k)
        = AlgHom.id ℤ_[p] (A p u k) := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [hlift_root, (hcfac_zero k).1, one_smul, Algebra.TensorProduct.map_tmul,
        AlgHom.comp_apply, hlift_root, map_one, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    exact DFunLike.congr_fun key x

  · apply AlgHom.ext; intro h
    apply (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).injective
    conv_rhs => rw [show (↑(Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).symm :
        Carrier p u →ₐ[ℤ_[p]] _) h = (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).symm h
        from rfl, AlgEquiv.apply_symm_apply]
    simp only [AlgHom.comp_apply]
    funext k
    let εlift₀ : A p u 0 →ₐ[ℤ_[p]] ℤ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u 0) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
        (by simp [kpoly, ZMod.val_zero])
    have hrid_k : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
        (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u) (Algebra.TensorProduct.map
          (AlgHom.id ℤ_[p] (Carrier p u)) (ε p u) y)) k
        = Algebra.TensorProduct.lmul' ℤ_[p]
            (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u k))
              ((Algebra.ofId ℤ_[p] (A p u k)).comp εlift₀)
              (Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) k)
                (Pi.evalAlgHom ℤ_[p] (A p u) 0) y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f g =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
          Pi.smul_apply, AlgHom.comp_apply, Algebra.ofId_apply, Pi.evalAlgHom_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, Algebra.smul_def, mul_comm]
        rfl
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    rw [hrid_k, hmap_eval, hΔ_comp,
      hμ_at_j k 0 k (by rw [ZMod.val_add, ZMod.val_zero, Nat.add_zero,
        Nat.mod_eq_of_lt k.val_lt]) h]
    set x := h k
    let μliftk0 : A p u k →ₐ[ℤ_[p]] A p u k ⊗[ℤ_[p]] A p u 0 :=
      AdjoinRoot.liftAlgHom (kpoly p u k) (Algebra.ofId _ _)
        (cfac p u k 0 • (z p u k ⊗ₜ z p u 0))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u k),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u 0),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            congr 2
            rw [ZMod.val_add, ZMod.val_zero, Nat.add_zero, Nat.mod_eq_of_lt k.val_lt])
    have key : (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u k))
          ((Algebra.ofId ℤ_[p] (A p u k)).comp εlift₀)).comp μliftk0)
        = AlgHom.id ℤ_[p] (A p u k) := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [hlift_root, (hcfac_zero k).2, one_smul, Algebra.TensorProduct.map_tmul,
        AlgHom.comp_apply, hlift_root, map_one, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
    exact DFunLike.congr_fun key x

  · intro h
    apply (piPiEquiv p u).injective
    funext a b
    rw [hcomm_piPi, hΔ_comp, hΔ_comp]

    have hvba : (b+a).val = (a+b : ZMod p).val := by rw [add_comm]
    let μliftba : A p u (b+a) →ₐ[ℤ_[p]] A p u b ⊗[ℤ_[p]] A p u a :=
      AdjoinRoot.liftAlgHom (kpoly p u (b+a)) (Algebra.ofId _ _)
        (cfac p u b a • (z p u b ⊗ₜ z p u a))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    let μliftab : A p u (b+a) →ₐ[ℤ_[p]] A p u a ⊗[ℤ_[p]] A p u b :=
      AdjoinRoot.liftAlgHom (kpoly p u (b+a)) (Algebra.ofId _ _)
        (cfac p u a b • (z p u a ⊗ₜ z p u b))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            congr 2
            rw [ZMod.val_add, ZMod.val_add, Nat.add_comm])
    have hμba : μ p u b a h = μliftba (h (b+a)) := hμ_at_j b a (b+a) rfl h
    have hμab : μ p u a b h = μliftab (h (b+a)) := hμ_at_j a b (b+a) hvba h
    rw [hμba, hμab]
    have key : (Algebra.TensorProduct.comm ℤ_[p] (A p u b) (A p u a)).toAlgHom.comp μliftba
        = μliftab := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
      rw [hlift_root, map_smul]
      show cfac p u b a • (z p u a ⊗ₜ[ℤ_[p]] z p u b) = μliftab (AdjoinRoot.root (kpoly p u (b+a)))
      rw [hlift_root, hcfac_symm]
    exact DFunLike.congr_fun key (h (b+a))

end S_PadicInt_KummerCarrier_bialgebra_axioms
end P2MW
export P2MW.S_PadicInt_KummerCarrier_bialgebra_axioms (solution)
