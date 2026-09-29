-- Prove2me | solution 1 for PadicInt.KummerCarrier.exists_antipode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/834aa8bc-d83c-53b1-87ef-835859307320

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_KummerCarrier_exists_antipode

open scoped TensorProduct
open PadicInt.KummerCarrier Polynomial

set_option maxHeartbeats 6400000 in
theorem solution (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ∃ S : Carrier p u →ₗ[ℤ_[p]] Carrier p u,
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.rTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) ∧
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.lTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) := by
  have hp : (0:ℕ) < p := (Fact.out : p.Prime).pos
  have hp' : p ≠ 0 := hp.ne'
  let sfac : ZMod p → ℤ_[p] := fun k =>
    (if k = 0 then 1 else (u : ℤ_[p])) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ k.val
  have hσobl : ∀ k : ZMod p, (sfac k • z p u k ^ (p-1)) ^ p
      = algebraMap ℤ_[p] (A p u k) ((u : ℤ_[p]) ^ (-k).val) := by
    intro k
    rw [_root_.smul_pow, ← pow_mul, Nat.mul_comm (p-1) p, pow_mul, z_pow_p,
      ← map_pow, ← pow_mul, Algebra.smul_def, ← map_mul]
    congr 1
    rcases eq_or_ne k 0 with rfl | hk
    · simp [sfac, ZMod.val_zero]
    · haveI : NeZero k := ⟨hk⟩
      have hkv : (-k).val = p - k.val := ZMod.val_neg_of_ne_zero k
      have hklt : k.val < p := k.val_lt
      have hkpos : 0 < k.val := Nat.pos_of_ne_zero
        (fun h => hk (ZMod.val_injective p (h.trans (ZMod.val_zero (n := p)).symm)))
      simp only [sfac, if_neg hk, mul_pow, ← pow_mul, hkv]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
        ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
        ← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      have hcast1 : ((p - k.val : ℕ) : ℤ) = (p : ℤ) - k.val := by
        exact_mod_cast Int.natCast_sub hklt.le
      have hcast2 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
        exact_mod_cast Int.natCast_sub hp
      push_cast [hcast1, hcast2]
      ring
  let σ : ∀ k : ZMod p, A p u (-k) →ₐ[ℤ_[p]] A p u k := fun k =>
    AdjoinRoot.liftAlgHom (kpoly p u (-k)) (Algebra.ofId ℤ_[p] (A p u k))
      (sfac k • z p u k ^ (p-1))
      (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
          exact (hσobl k).trans rfl)
  have hσ_root : ∀ k, σ k (z p u (-k)) = sfac k • z p u k ^ (p-1) := fun k => by
    show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
    rw [show AdjoinRoot.root (kpoly p u (-k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  let S : Carrier p u →ₐ[ℤ_[p]] Carrier p u :=
    Pi.algHom _ _ fun k => (σ k).comp (Pi.evalAlgHom ℤ_[p] (A p u) (-k))
  have hS_apply : ∀ (h : Carrier p u) (k : ZMod p), S h k = σ k (h (-k)) := fun _ _ => rfl
  have hcfac_symm : ∀ k : ZMod p, cfac p u (-k) k = cfac p u k (-k) := fun k => by
    unfold PadicInt.KummerCarrier.cfac; rw [Nat.add_comm]
  have hkey : ∀ k : ZMod p, cfac p u (-k) k * (sfac k * (u : ℤ_[p]) ^ k.val) = 1 := by
    intro k
    unfold PadicInt.KummerCarrier.cfac
    rcases eq_or_ne k 0 with rfl | hk
    · simp [sfac, ZMod.val_zero]
    · haveI : NeZero k := ⟨hk⟩
      have hkv : (-k).val = p - k.val := ZMod.val_neg_of_ne_zero k
      have hklt : k.val < p := k.val_lt
      have hdiv : ((-k).val + k.val) / p = 1 := by
        rw [hkv, Nat.sub_add_cancel hklt.le, Nat.div_self hp]
      simp only [sfac, if_neg hk, hdiv, pow_one]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
      congr 1; group
  have hΔ_comp : ∀ (h : Carrier p u) (a b : ZMod p),
      piPiEquiv p u (Δ p u h) a b = μ p u a b h := fun h a b => by
    have hrfl : Δ p u h = (piPiEquiv p u).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl
  have hSr_comp : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u) (a b : ZMod p),
      piPiEquiv p u (Algebra.TensorProduct.map S (AlgHom.id ℤ_[p] (Carrier p u)) y) a b
        = Algebra.TensorProduct.map (σ a) (AlgHom.id ℤ_[p] (A p u b)) (piPiEquiv p u y (-a) b) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, piPiEquiv_tmul, hS_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hSl_comp : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u) (a b : ZMod p),
      piPiEquiv p u (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (Carrier p u)) S y) a b
        = Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u a)) (σ b) (piPiEquiv p u y a (-b)) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, piPiEquiv_tmul, hS_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hmul'_comp : ∀ (y : Carrier p u ⊗[ℤ_[p]] Carrier p u) (k : ZMod p),
      Algebra.TensorProduct.lmul' ℤ_[p] y k
        = Algebra.TensorProduct.lmul' ℤ_[p] (piPiEquiv p u y k k) := by
    intro y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.lmul'_apply_tmul, piPiEquiv_tmul, Pi.mul_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

  have hnkval : ∀ k : ZMod p, (-k+k : ZMod p).val = 0 := fun k => by
    rw [neg_add_cancel, ZMod.val_zero]

  have hε_at_j : ∀ (j : ZMod p) (hj : j.val = 0) (h : Carrier p u),
      ε p u h = AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
        (by simp [kpoly, hj]) (h j) := by
    intro j hj h
    obtain rfl : j = 0 := ZMod.val_injective p (hj.trans (ZMod.val_zero (n := p)).symm)
    rfl
  have hnkval' : ∀ k : ZMod p, (k + -k : ZMod p).val = 0 := fun k => by
    rw [add_neg_cancel, ZMod.val_zero]
  have hpercomp_r : ∀ k : ZMod p,
      (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map (σ k) (AlgHom.id ℤ_[p] (A p u k))).comp (μ p u (-k) k))
      = (Algebra.ofId ℤ_[p] (A p u k)).comp (ε p u) := by
    intro k
    let εlift' : A p u (-k+k) →ₐ[ℤ_[p]] ℤ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u (-k+k)) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
        (by simp [kpoly, hnkval k])
    let μlift : A p u (-k+k) →ₐ[ℤ_[p]] A p u (-k) ⊗[ℤ_[p]] A p u k :=
      AdjoinRoot.liftAlgHom (kpoly p u (-k+k)) (Algebra.ofId _ _)
        (cfac p u (-k) k • (z p u (-k) ⊗ₜ z p u k))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u (-k)),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u k),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have hμ_apply : ∀ h, μ p u (-k) k h = μlift (h (-k+k)) := fun _ => rfl
    have hGR : (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map (σ k) (AlgHom.id ℤ_[p] (A p u k))).comp μlift)
      = (Algebra.ofId ℤ_[p] (A p u k)).comp εlift' := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      have hμlift_root : μlift (AdjoinRoot.root (kpoly p u (-k+k)))
          = cfac p u (-k) k • (z p u (-k) ⊗ₜ z p u k) := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (kpoly p u (-k+k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      have hεlift'_root : εlift' (AdjoinRoot.root (kpoly p u (-k+k))) = 1 := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (kpoly p u (-k+k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hσ_root, AlgHom.id_apply,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, smul_mul_assoc, ← pow_succ,
        Nat.sub_add_cancel hp, z_pow_p, Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul,
        mul_assoc, hkey, one_smul, hεlift'_root, map_one]
    apply AlgHom.ext; intro h
    simp only [AlgHom.comp_apply, Algebra.ofId_apply]
    rw [hμ_apply, hε_at_j (-k+k) (hnkval k) h]
    exact DFunLike.congr_fun hGR (h (-k+k))
  have hpercomp_l : ∀ k : ZMod p,
      (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u k)) (σ k)).comp (μ p u k (-k)))
      = (Algebra.ofId ℤ_[p] (A p u k)).comp (ε p u) := by
    intro k
    let εlift' : A p u (k+(-k)) →ₐ[ℤ_[p]] ℤ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u (k+(-k))) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
        (by simp [kpoly, hnkval' k])
    let μlift : A p u (k+(-k)) →ₐ[ℤ_[p]] A p u k ⊗[ℤ_[p]] A p u (-k) :=
      AdjoinRoot.liftAlgHom (kpoly p u (k+(-k))) (Algebra.ofId _ _)
        (cfac p u k (-k) • (z p u k ⊗ₜ z p u (-k)))
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
            rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u k),
              Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u (-k)),
              TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have hμ_apply : ∀ h, μ p u k (-k) h = μlift (h (k+(-k))) := fun _ => rfl
    have hGR : (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (A p u k)) (σ k)).comp μlift)
      = (Algebra.ofId ℤ_[p] (A p u k)).comp εlift' := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      have hμlift_root : μlift (AdjoinRoot.root (kpoly p u (k+(-k))))
          = cfac p u k (-k) • (z p u k ⊗ₜ z p u (-k)) := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (kpoly p u (k+(-k))) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      have hεlift'_root : εlift' (AdjoinRoot.root (kpoly p u (k+(-k)))) = 1 := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (kpoly p u (k+(-k))) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hσ_root, AlgHom.id_apply,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, mul_smul_comm, ← pow_succ',
        Nat.sub_add_cancel hp, z_pow_p, Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul,
        ← hcfac_symm, mul_assoc, hkey, one_smul, hεlift'_root, map_one]
    apply AlgHom.ext; intro h
    simp only [AlgHom.comp_apply, Algebra.ofId_apply]
    rw [hμ_apply, hε_at_j (k+(-k)) (hnkval' k) h]
    exact DFunLike.congr_fun hGR (h (k+(-k)))
  refine ⟨S.toLinearMap, ?_, ?_⟩
  ·
    apply LinearMap.ext; intro h
    show LinearMap.mul' ℤ_[p] _ (S.toLinearMap.rTensor _ (Δ p u h)) = algebraMap ℤ_[p] _ (ε p u h)
    have hrT : S.toLinearMap.rTensor (Carrier p u) (Δ p u h)
        = Algebra.TensorProduct.map S (AlgHom.id ℤ_[p] (Carrier p u)) (Δ p u h) := rfl
    have hmul : LinearMap.mul' ℤ_[p] (Carrier p u)
        = (Algebra.TensorProduct.lmul' ℤ_[p] (S := Carrier p u)).toLinearMap := rfl
    rw [hrT, hmul, AlgHom.toLinearMap_apply]
    funext k
    rw [hmul'_comp, hSr_comp, hΔ_comp, Pi.algebraMap_apply]
    exact DFunLike.congr_fun (hpercomp_r k) h
  ·
    apply LinearMap.ext; intro h
    show LinearMap.mul' ℤ_[p] _ (S.toLinearMap.lTensor _ (Δ p u h)) = algebraMap ℤ_[p] _ (ε p u h)
    have hlT : S.toLinearMap.lTensor (Carrier p u) (Δ p u h)
        = Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (Carrier p u)) S (Δ p u h) := rfl
    have hmul : LinearMap.mul' ℤ_[p] (Carrier p u)
        = (Algebra.TensorProduct.lmul' ℤ_[p] (S := Carrier p u)).toLinearMap := rfl
    rw [hlT, hmul, AlgHom.toLinearMap_apply]
    funext k
    rw [hmul'_comp, hSl_comp, hΔ_comp, Pi.algebraMap_apply]
    exact DFunLike.congr_fun (hpercomp_l k) h

end S_PadicInt_KummerCarrier_exists_antipode
end P2MW
export P2MW.S_PadicInt_KummerCarrier_exists_antipode (solution)
