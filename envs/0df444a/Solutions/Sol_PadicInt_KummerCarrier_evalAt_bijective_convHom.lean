-- Prove2me | solution 1 for PadicInt.KummerCarrier.evalAt_bijective_convHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4e46bcde-8323-52e4-aabc-23024e9fe199

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_KummerCarrier_evalAt_bijective_convHom

open scoped TensorProduct
open PadicInt.KummerCarrier Polynomial

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u : ℤ_[p])) :
    ∃ ψ₀ : ZMod p × ZMod p → (Carrier p u →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      Function.Bijective ψ₀ ∧
      (∀ i j : ZMod p, ∃ hw, ψ₀ (i, j) = evalAt p u j (ζ ^ i.val * η ^ j.val) hw) ∧
      ∀ a b : ZMod p × ZMod p,
        (Algebra.TensorProduct.lmul' ℤ_[p] (S := AlgebraicClosure ℚ_[p])).comp
          ((Algebra.TensorProduct.map (ψ₀ a) (ψ₀ b)).comp (Δ p u))
          = ψ₀ (a + b) := by
  have hp : (0:ℕ) < p := (Fact.out : p.Prime).pos
  have hp' : p ≠ 0 := hp.ne'
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hinj : Function.Injective (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
    exact (algebraMap ℚ_[p] _).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have huL_ne : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u : ℤ_[p]) ≠ 0 :=
    fun h => u.isUnit.ne_zero (hinj (h.trans (map_zero _).symm))
  have hη_ne : η ≠ 0 := fun h => huL_ne (by rw [← hη, h, zero_pow hp'])
  have hζwrap : ∀ a b : ZMod p, ζ ^ (a.val + b.val) = ζ ^ (a + b).val := by
    intro a b
    conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) p, pow_add, pow_mul, hζp, one_pow,
      mul_one, ← ZMod.val_add]
  have hηwrap : ∀ a b : ZMod p,
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (cfac p u a b) * η ^ (a.val + b.val)
        = η ^ (a + b).val := by
    intro a b
    have hcf : cfac p u a b * (u:ℤ_[p]) ^ ((a.val+b.val)/p) = 1 := by
      unfold PadicInt.KummerCarrier.cfac
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]
    calc algebraMap ℤ_[p] _ (cfac p u a b) * η^(a.val+b.val)
        = algebraMap ℤ_[p] _ (cfac p u a b) * (η^p)^((a.val+b.val)/p) * η^((a+b).val) := by
          conv_lhs => rw [← Nat.mod_add_div (a.val+b.val) p, pow_add, pow_mul, ← ZMod.val_add]
          ring
      _ = algebraMap ℤ_[p] _ (cfac p u a b * (u:ℤ_[p])^((a.val+b.val)/p)) * η^((a+b).val) := by
          rw [hη, ← map_pow, ← map_mul]
      _ = η^((a+b).val) := by rw [hcf, map_one, one_mul]
  have hw : ∀ i j : ZMod p,
      (ζ ^ i.val * η ^ j.val) ^ p
        = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) ((u : ℤ_[p]) ^ j.val) := by
    intro i j
    rw [mul_pow, ← pow_mul, mul_comm i.val p, pow_mul, hζp, one_pow, one_mul,
      ← pow_mul, mul_comm j.val p, pow_mul, hη, ← map_pow]
  have hkey : ∀ i₁ j₁ i₂ j₂ : ZMod p,
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (cfac p u j₁ j₂)
        * (ζ^i₁.val * η^j₁.val) * (ζ^i₂.val * η^j₂.val)
        = ζ^(i₁+i₂).val * η^(j₁+j₂).val := by
    intro i₁ j₁ i₂ j₂
    calc _ = ζ^(i₁.val+i₂.val) * (algebraMap ℤ_[p] _ (cfac p u j₁ j₂) * η^(j₁.val+j₂.val)) := by
            rw [pow_add, pow_add]; ring
      _ = ζ^(i₁+i₂).val * η^(j₁+j₂).val := by rw [hζwrap, hηwrap]
  have hmap_eval : ∀ (a b : ZMod p) (y : Carrier p u ⊗[ℤ_[p]] Carrier p u),
      Algebra.TensorProduct.map (Pi.evalAlgHom ℤ_[p] (A p u) a) (Pi.evalAlgHom ℤ_[p] (A p u) b) y
        = piPiEquiv p u y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]
  have hlift_root : ∀ (j : ZMod p) (w : AlgebraicClosure ℚ_[p]) (hwj),
      AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] (AlgebraicClosure ℚ_[p])) w hwj
        (AdjoinRoot.root (kpoly p u j)) = w := by
    intro j w hwj
    rw [show AdjoinRoot.root (kpoly p u j) = (AdjoinRoot.mk _) X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  have hevalAt_apply : ∀ (j : ZMod p) (w : AlgebraicClosure ℚ_[p]) (hwj) (h : Carrier p u),
      evalAt p u j w hwj h
        = AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] _) w
            (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
                exact hwj.trans rfl) (h j) := fun _ _ _ _ => rfl
  refine ⟨fun ⟨i, j⟩ => evalAt p u j (ζ ^ i.val * η ^ j.val) (hw i j), ?_, ?_, ?_⟩

  · constructor

    · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
      have hprobe := DFunLike.congr_fun heq (Pi.single j₁ 1)
      rw [hevalAt_apply, hevalAt_apply] at hprobe
      have hj : j₁ = j₂ := by
        by_contra hne
        simp only [Pi.single_eq_same, map_one,
          Pi.single_eq_of_ne (Ne.symm hne), map_zero] at hprobe
        exact one_ne_zero hprobe
      subst hj
      have hprobe2 := DFunLike.congr_fun heq (Pi.single j₁ (z p u j₁))
      rw [hevalAt_apply, hevalAt_apply, Pi.single_eq_same, hlift_root, hlift_root] at hprobe2
      have hi : ζ ^ i₁.val = ζ ^ i₂.val :=
        mul_right_cancel₀ (pow_ne_zero _ hη_ne) hprobe2
      exact Prod.ext (ZMod.val_injective p (hζ.pow_inj i₁.val_lt i₂.val_lt hi)) rfl

    · intro φ
      have h1dec : (1 : Carrier p u) = ∑ k : ZMod p, (Pi.single k 1 : Carrier p u) := by
        funext l; simp [Finset.sum_apply, Finset.sum_pi_single]
      obtain ⟨j, hjne⟩ : ∃ j : ZMod p, φ (Pi.single j 1) ≠ 0 := by
        by_contra hall; push_neg at hall
        have h10 : (1 : AlgebraicClosure ℚ_[p]) = 0 := by
          rw [← map_one φ, h1dec, map_sum]
          exact Finset.sum_eq_zero fun k _ => hall k
        exact one_ne_zero h10
      have hj1 : φ (Pi.single j 1) = 1 := by
        have hidem : (Pi.single j 1 : Carrier p u) * Pi.single j 1 = Pi.single j 1 := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl]
        have h2 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
          have := congrArg φ hidem; rw [map_mul] at this; linear_combination this
        exact (mul_eq_zero.mp h2).elim (fun h => absurd h hjne) sub_eq_zero.mp
      have hk0 : ∀ k, k ≠ j → φ (Pi.single k 1) = 0 := fun k hk => by
        have hperp : (Pi.single j 1 : Carrier p u) * Pi.single k 1 = 0 := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp [Pi.single_eq_of_ne (Ne.symm hk)]
          · simp [Pi.single_eq_of_ne hl]
        have := congrArg φ hperp; rwa [map_mul, hj1, one_mul, map_zero] at this
      have hfactor : ∀ h : Carrier p u, φ h = φ (Pi.single j (h j)) := by
        intro h
        have hdec : h = ∑ k : ZMod p, Pi.single k (h k) := by
          funext l; simp [Finset.sum_apply, Finset.sum_pi_single]
        conv_lhs => rw [hdec, map_sum]
        refine Finset.sum_eq_single j (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ j) h)
        have : (Pi.single k (h k) : Carrier p u) = Pi.single k 1 * Pi.mulSingle k (h k) := by
          funext l
          rcases eq_or_ne l k with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
        rw [this, map_mul, hk0 k hk, zero_mul]
      have hmulSingle_eq : ∀ y : A p u j, φ (Pi.mulSingle j y) = φ (Pi.single j y) := by
        intro y
        have heq : (Pi.mulSingle j y : Carrier p u) = Pi.single j y + (1 - Pi.single j 1) := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
        rw [heq, map_add, map_sub, map_one, hj1]; ring
      let φ₀ : A p u j →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := AlgHom.ofLinearMap
        (φ.toLinearMap ∘ₗ LinearMap.single ℤ_[p] (fun k => A p u k) j)
        (by simp only [LinearMap.comp_apply, LinearMap.coe_single, AlgHom.toLinearMap_apply];
            exact hj1)
        (fun x y => by
          simp only [LinearMap.comp_apply, LinearMap.coe_single, AlgHom.toLinearMap_apply]
          have : (Pi.single j (x * y) : Carrier p u) = Pi.single j x * Pi.mulSingle j y := by
            funext l
            rcases eq_or_ne l j with rfl | hl
            · simp
            · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
          rw [this, map_mul, hmulSingle_eq])
      have hφ₀_apply : ∀ x, φ₀ x = φ (Pi.single j x) := fun _ => rfl
      set w := φ₀ (z p u j) with hw_def
      have hwp : w ^ p = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) ((u:ℤ_[p])^j.val) := by
        rw [hw_def, ← map_pow, z_pow_p, AlgHom.commutes]
      have hηj_ne : (η : AlgebraicClosure ℚ_[p]) ^ j.val ≠ 0 := pow_ne_zero _ hη_ne
      have huLpow_ne : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) ((u:ℤ_[p])^j.val) ≠ 0 :=
        fun h => (u.isUnit.pow j.val).ne_zero (hinj (h.trans (map_zero _).symm))
      have hratio : (w * (η^j.val)⁻¹) ^ p = 1 := by
        rw [mul_pow, hwp, inv_pow, ← pow_mul, mul_comm j.val p, pow_mul, hη, ← map_pow,
          mul_inv_cancel₀ huLpow_ne]
      have hmem : w * (η^j.val)⁻¹ ∈ Polynomial.nthRoots p (1 : AlgebraicClosure ℚ_[p]) :=
        (Polynomial.mem_nthRoots hp).mpr hratio
      rw [hζ.nthRoots_eq (one_pow p : (1:AlgebraicClosure ℚ_[p])^p = 1)] at hmem
      obtain ⟨m, hm_mem, hm_eq⟩ := Multiset.mem_map.mp hmem
      have hmlt : m < p := Multiset.mem_range.mp hm_mem
      let i : ZMod p := (m : ZMod p)
      have hi_val : i.val = m := ZMod.val_natCast_of_lt hmlt
      have hi_eq : ζ ^ i.val * η ^ j.val = w := by
        rw [hi_val]
        have hm' : ζ ^ m = w * (η^j.val)⁻¹ := (mul_one (ζ^m)).symm.trans hm_eq
        rw [hm', mul_assoc, inv_mul_cancel₀ hηj_ne, mul_one]
      refine ⟨(i, j), AlgHom.ext fun h => ?_⟩
      rw [hevalAt_apply, hfactor h, ← hφ₀_apply]
      congr 1
      apply AdjoinRoot.algHom_ext
      rw [hlift_root, hi_eq, hw_def]

  · intro i j; exact ⟨hw i j, rfl⟩

  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    let lift₁ : A p u j₁ →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u j₁) (Algebra.ofId ℤ_[p] _) (ζ^i₁.val * η^j₁.val)
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw i₁ j₁).trans rfl)
    let lift₂ : A p u j₂ →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u j₂) (Algebra.ofId ℤ_[p] _) (ζ^i₂.val * η^j₂.val)
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw i₂ j₂).trans rfl)
    let μlift : A p u (j₁+j₂) →ₐ[ℤ_[p]] A p u j₁ ⊗[ℤ_[p]] A p u j₂ :=
      AdjoinRoot.liftAlgHom (kpoly p u (j₁+j₂)) (Algebra.ofId _ _)
        (cfac p u j₁ j₂ • (z p u j₁ ⊗ₜ z p u j₂))
        (by
          simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
          rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u j₁),
            Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u j₂),
            TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
    let rlift : A p u (j₁+j₂) →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
      AdjoinRoot.liftAlgHom (kpoly p u (j₁+j₂)) (Algebra.ofId ℤ_[p] _)
        (ζ^(i₁+i₂).val * η^(j₁+j₂).val)
        (by simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw (i₁+i₂) (j₁+j₂)).trans rfl)
    have hlift₁_root : lift₁ (z p u j₁) = ζ^i₁.val * η^j₁.val := hlift_root _ _ _
    have hlift₂_root : lift₂ (z p u j₂) = ζ^i₂.val * η^j₂.val := hlift_root _ _ _
    have hμlift_root : μlift (AdjoinRoot.root (kpoly p u (j₁+j₂)))
        = cfac p u j₁ j₂ • (z p u j₁ ⊗ₜ z p u j₂) := by
      show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root (kpoly p u (j₁+j₂))) = _
      rw [show AdjoinRoot.root (kpoly p u (j₁+j₂)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
        AdjoinRoot.liftAlgHom_mk, eval₂_X]
    have hrlift_root : rlift (AdjoinRoot.root (kpoly p u (j₁+j₂)))
        = ζ^(i₁+i₂).val * η^(j₁+j₂).val := hlift_root _ _ _
    have key : (Algebra.TensorProduct.lmul' ℤ_[p]).comp
        ((Algebra.TensorProduct.map lift₁ lift₂).comp μlift) = rlift := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hlift₁_root, hlift₂_root,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, hrlift_root, Algebra.smul_def,
        ← mul_assoc]
      exact hkey i₁ j₁ i₂ j₂
    have he1 : evalAt p u j₁ (ζ^i₁.val * η^j₁.val) (hw i₁ j₁)
        = lift₁.comp (Pi.evalAlgHom ℤ_[p] (A p u) j₁) := rfl
    have he2 : evalAt p u j₂ (ζ^i₂.val * η^j₂.val) (hw i₂ j₂)
        = lift₂.comp (Pi.evalAlgHom ℤ_[p] (A p u) j₂) := rfl
    have he12 : evalAt p u (j₁+j₂) (ζ^(i₁+i₂).val * η^(j₁+j₂).val) (hw (i₁+i₂) (j₁+j₂))
        = rlift.comp (Pi.evalAlgHom ℤ_[p] (A p u) (j₁+j₂)) := rfl
    ext h
    simp only [AlgHom.comp_apply, Prod.fst_add, Prod.snd_add]
    have hΔh : piPiEquiv p u (Δ p u h) j₁ j₂ = μ p u j₁ j₂ h := by
      have hrfl : Δ p u h = (piPiEquiv p u).symm
          ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b) h) := rfl
      rw [hrfl, AlgEquiv.apply_symm_apply]; rfl
    have hμ : μ p u j₁ j₂ h = μlift (h (j₁+j₂)) := rfl
    rw [he1, he2, Algebra.TensorProduct.map_comp, AlgHom.comp_apply, hmap_eval, hΔh, hμ, he12,
      AlgHom.comp_apply, Pi.evalAlgHom_apply]
    exact DFunLike.congr_fun key (h (j₁+j₂))

end S_PadicInt_KummerCarrier_evalAt_bijective_convHom
end P2MW
export P2MW.S_PadicInt_KummerCarrier_evalAt_bijective_convHom (solution)
