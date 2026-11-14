-- Prove2me | solution 1 for RamanujanPetersson.trace_heckeT_mul_diamond_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T23:13:57.953793+00:00
-- url     : https://prove2.me/submissions/77715773-81d3-4ecd-b6b9-53aa119f50e8

import Mathlib
import Definitions.Def_RPLib_S3_EichlerSelberg

open UpperHalfPlane MatrixGroups ModularForm

set_option autoImplicit false

noncomputable section

namespace UploadES

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.HeckeAlgebra RPLib

lemma companion_pow (t n : ℤ) : ∀ j : ℕ,
    ((!![t, -n; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (j + 1)) 0 0 = SymTrace.U (j + 1) t n ∧
    ((!![t, -n; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (j + 1)) 0 1 = -n * SymTrace.U j t n
  | 0 => by simp
  | j + 1 => by
    obtain ⟨h0, h1⟩ := companion_pow t n j
    rw [pow_succ]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h0, h1, SymTrace.U_add_two]
    simp
    constructor <;> ring

lemma companion_U (t n : ℤ) (j : ℕ) :
    ((!![t, -n; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ j) 0 0 = SymTrace.U j t n := by
  cases j with
  | zero => simp
  | succ j => exact (companion_pow t n j).1

lemma sum_range_shift (n : ℕ) (g : ℤ → ℚ) :
    ∑ i ∈ Finset.range (4 * n + 1), g ((i : ℤ) - 2 * n) = ∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n), g t := by
  refine Finset.sum_nbij' (fun i => (i : ℤ) - 2 * n) (fun t => (t + 2 * n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe,
      Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro t ht
    simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe,
      Finset.mem_range, Finset.mem_Icc] at ht ⊢
    omega
  · intro i _
    simp
  · intro t ht
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at ht
    have : (0 : ℤ) ≤ t + 2 * n := by omega
    simp only [Int.toNat_of_nonneg this]
    ring
  · intro i _
    rfl

lemma redForms_eq (D : ℤ) : S3.redForms D =
    (Finset.Icc (0 : ℤ) D.natAbs ×ˢ Finset.Icc (-(D.natAbs : ℤ)) D.natAbs ×ˢ Finset.Icc (0 : ℤ) D.natAbs).filter
      (fun Q : ℤ × ℤ × ℤ => 1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = D ∧
        -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧ (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))) := by
  ext ⟨a, b, c⟩
  simp only [S3.redForms, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨⟨a', b', c', ⟨ha, hb, hc⟩, h1, h2, h3⟩, hP⟩
    subst h1 h2 h3
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hP⟩
  · rintro ⟨⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, ⟨hc0, hc1⟩⟩, hP⟩
    refine ⟨⟨a.toNat, (b + D.natAbs).toNat, c.toNat, ⟨by omega, by omega, by omega⟩, by omega, by omega,
      by omega⟩, hP⟩

lemma levelCount_eq (M : ℕ) [NeZero M] (δ' : ZMod M) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    S3.levelCount M δ' g = (Finset.univ.filter fun v : Fin 2 → ZMod M =>
      addOrderOf v = M ∧ (g.map (Int.castRingHom (ZMod M))).mulVec v = δ' • v).card := by
  unfold S3.levelCount
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  have hMv : M • v = 0 := by
    funext i
    simp [nsmul_eq_mul]
  rw [addOrderOf_eq_iff (NeZero.pos M)]
  simp only [hMv, true_and, Finset.mem_range]

lemma charSum_eq (L a k : ℕ) : S3.charSum L (a : ℤ) ((-1) ^ k) =
    (if L ≤ 2 then (if Even k ∧ Nat.Coprime a L then 1 else 0)
    else (Nat.totient L : ℚ) / 2 *
      ((if (a : ZMod L) = 1 then 1 else 0) + (-1) ^ k * (if (a : ZMod L) = -1 then 1 else 0))) := by
  unfold S3.charSum
  have h1 : ((-1 : ℤ) ^ k = 1) ↔ Even k := neg_one_pow_eq_one_iff_even (by decide)
  have h2 : Int.gcd (a : ℤ) (L : ℤ) = 1 ↔ Nat.Coprime a L := by
    rw [Int.gcd_natCast_natCast]
  simp only [h1, h2, Int.cast_natCast]
  push_cast
  congr

theorem main (M : ℕ) [NeZero M] (hM : 3 ≤ M)
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    ∃ T : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
        CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ T' : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
          CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
        (∀ γ : ℕ → SL(2, ℤ),
          (∀ d : ℕ, d.Coprime M →
            γ d ∈ CongruenceSubgroup.Gamma0 M ∧ (((γ d) 1 1 : ℤ) : ZMod M) = (d : ZMod M) * (δ : ZMod M)) →
          ∀ (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
            (m : ℕ),
            (qExpansion 1 (T' f)).coeff m =
              ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
                (d : ℂ) ^ (k - 1) * (qExpansion 1 (⇑f ∣[(k : ℤ)] γ d)).coeff (m * n / d ^ 2)) ↔
          T' = T) ∧
      LinearMap.trace ℂ _ T =
        (((if Nat.sqrt n * Nat.sqrt n = n then
              ((k : ℚ) - 1) / 12 * ((M : ℚ) * ∏ l ∈ M.primeFactors, (1 + 1 / (l : ℚ))) *
                (Nat.sqrt n : ℚ) ^ (k - 2) * ((Nat.totient M : ℚ) / 2 *
                  ((if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = 1 then 1 else 0) +
                    (-1) ^ k * (if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = -1 then 1 else 0)))
            else 0) -
          (∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n),
              ((((!![t, -(n : ℤ); 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (k - 2)) 0 0 : ℤ) : ℚ) *
                (∑ Q ∈ (Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (-((t ^ 2 - 4 * n).natAbs : ℤ)) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs).filter
                    (fun Q : ℤ × ℤ × ℤ => 1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = t ^ 2 - 4 * n ∧
                      -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
                      (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))),
                  (((Finset.univ.filter fun v : Fin 2 → ZMod M =>
                      addOrderOf v = M ∧
                        ((!![(t - Q.2.1) / 2, -Q.2.2; Q.1, (t + Q.2.1) / 2] : Matrix (Fin 2) (Fin 2) ℤ).map
                          (Int.castRingHom (ZMod M))).mulVec v = ((δ⁻¹ : (ZMod M)ˣ) : ZMod M) • v).card : ℚ) /
                    ((if Q.1 = Q.2.1 ∧ Q.2.1 = Q.2.2 then 6 else if Q.2.1 = 0 ∧ Q.1 = Q.2.2 then 4 else 2 : ℕ) :
                      ℚ)))) -
          1 / 2 * (∑ e ∈ n.divisors, ((min e (n / e) : ℕ) : ℚ) ^ (k - 1) *
            (∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
              (∑ x ∈ (Finset.range M).filter (fun x : ℕ =>
                  (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
                (if M / Nat.gcd τ (M / τ) ≤ 2 then
                  (if Even k ∧ Nat.Coprime ((δ : ZMod M).val * x) (M / Nat.gcd τ (M / τ)) then 1 else 0)
                else (Nat.totient (M / Nat.gcd τ (M / τ)) : ℚ) / 2 *
                  ((if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = 1 then 1 else 0) +
                    (-1) ^ k *
                      (if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = -1 then 1 else 0))))))
          : ℚ) : ℂ) := by
  have hz : ∀ d : ℕ, (d : ℂ) ^ ((k : ℤ) - 1) = (d : ℂ) ^ (k - 1) := fun d => by
    rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have key : ∀ γ : ℕ → SL(2, ℤ),
      (∀ d : ℕ, d.Coprime M →
        γ d ∈ CongruenceSubgroup.Gamma0 M ∧ (((γ d) 1 1 : ℤ) : ZMod M) = (d : ZMod M) * (δ : ZMod M)) →
      ∀ (f : S1 M (k : ℤ)) (m : ℕ),
        (qExpansion 1 ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ : Module.End ℂ (S1 M (k : ℤ))) f)).coeff m =
          ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
            (d : ℂ) ^ (k - 1) * (qExpansion 1 (⇑f ∣[(k : ℤ)] γ d)).coeff (m * n / d ^ 2) := by
    intro γ hγ f m
    set g := diamond (k : ℤ) δ f with hg
    have hR : ∀ d ∈ (Nat.gcd m n).divisors.filter (fun d => d.Coprime M),
        (d : ℂ) ^ (k - 1) * (qExpansion 1 (⇑f ∣[(k : ℤ)] γ d)).coeff (m * n / d ^ 2) =
          ∑ χ : DirichletCharacter ℂ M,
            χ d * (d : ℂ) ^ ((k : ℤ) - 1) * (qExpansion 1 (proj (k : ℤ) χ g)).coeff (m * n / d ^ 2) := by
      intro d hd
      have hdc : d.Coprime M := (Finset.mem_filter.1 hd).2
      obtain ⟨hγ0, hγ1⟩ := hγ d hdc
      have h1 : ⇑f ∣[(k : ℤ)] γ d = ⇑(diamond (k : ℤ) (ZMod.unitOfCoprime d hdc) g) := by
        rw [hg, ← Module.End.mul_apply, ← map_mul]
        refine (coe_diamond_of_mem (k : ℤ) hγ0 _ ?_ f).symm
        rw [hγ1, Units.val_mul, ZMod.coe_unitOfCoprime]
      have hs : diamond (k : ℤ) (ZMod.unitOfCoprime d hdc) g =
          ∑ χ : DirichletCharacter ℂ M, χ (d : ZMod M) • proj (k : ℤ) χ g := by
        conv_lhs => rw [← sum_proj (k : ℤ) g]
        rw [map_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [diamond_proj, ZMod.coe_unitOfCoprime]
      rw [h1, hs]
      change (d : ℂ) ^ (k - 1) * csL M (k : ℤ) _ (m * n / d ^ 2) = _
      rw [map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, hz, csL_apply]
      ring
    rw [Finset.sum_congr rfl hR, Finset.sum_comm, Module.End.mul_apply, ← hg]
    change csL M (k : ℤ) _ m = _
    conv_lhs => rw [← sum_proj (k : ℤ) g]
    rw [map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [csL_apply, coeff_heckeTn_chi' (k : ℤ) (proj_mem (k : ℤ) χ g) hn m]
  let γ0 : ℕ → SL(2, ℤ) := fun d =>
    if h : d.Coprime M then ((lift0 (ZMod.unitOfCoprime d h * δ) : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ))
    else 1
  have hγ0 : ∀ d : ℕ, d.Coprime M →
      γ0 d ∈ CongruenceSubgroup.Gamma0 M ∧ (((γ0 d) 1 1 : ℤ) : ZMod M) = (d : ZMod M) * (δ : ZMod M) := by
    intro d h
    simp only [γ0, dif_pos h]
    refine ⟨(lift0 _).2, ?_⟩
    rw [← coe_unitMap, unitMap_lift0, Units.val_mul, ZMod.coe_unitOfCoprime]
  refine ⟨heckeTn (k : ℤ) n * diamond (k : ℤ) δ, fun T' => ⟨fun hP => ?_, fun h => by rw [h]; exact key⟩, ?_⟩
  · refine LinearMap.ext fun f => eq_of_csL (k : ℤ) (funext fun m => ?_)
    rw [csL_apply, csL_apply, hP γ0 hγ0 f m, key γ0 hγ0 f m]
  · rw [ES.trace_heckeTn_diamond hM hk hn hnM δ]
    congr 1
    have hA1 : S3.scalarG1 M k n (δ : ZMod M) =
        (if Nat.sqrt n * Nat.sqrt n = n then
              ((k : ℚ) - 1) / 12 * ((M : ℚ) * ∏ l ∈ M.primeFactors, (1 + 1 / (l : ℚ))) *
                (Nat.sqrt n : ℚ) ^ (k - 2) * ((Nat.totient M : ℚ) / 2 *
                  ((if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = 1 then 1 else 0) +
                    (-1) ^ k * (if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = -1 then 1 else 0)))
            else 0) := by
      unfold S3.scalarG1 S3.dedekindPsi
      rw [show ((δ : ZMod M).val : ℤ) * (Nat.sqrt n : ℤ) = (((δ : ZMod M).val * Nat.sqrt n : ℕ) : ℤ) by
        push_cast; ring, charSum_eq, if_neg (show ¬ M ≤ 2 by omega)]
      simp only [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    have hA2 : S3.ellG1 M k n (δ : ZMod M) =
        -(∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n),
              ((((!![t, -(n : ℤ); 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (k - 2)) 0 0 : ℤ) : ℚ) *
                (∑ Q ∈ (Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (-((t ^ 2 - 4 * n).natAbs : ℤ)) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs).filter
                    (fun Q : ℤ × ℤ × ℤ => 1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = t ^ 2 - 4 * n ∧
                      -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
                      (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))),
                  (((Finset.univ.filter fun v : Fin 2 → ZMod M =>
                      addOrderOf v = M ∧
                        ((!![(t - Q.2.1) / 2, -Q.2.2; Q.1, (t + Q.2.1) / 2] : Matrix (Fin 2) (Fin 2) ℤ).map
                          (Int.castRingHom (ZMod M))).mulVec v = ((δ⁻¹ : (ZMod M)ˣ) : ZMod M) • v).card : ℚ) /
                    ((if Q.1 = Q.2.1 ∧ Q.2.1 = Q.2.2 then 6 else if Q.2.1 = 0 ∧ Q.1 = Q.2.2 then 4 else 2 : ℕ) :
                      ℚ)))) := by
      unfold S3.ellG1
      congr 1
      refine (sum_range_shift n (fun t => (S3.chebU (k - 2) t n : ℚ) * S3.ellCount M (δ : ZMod M)⁻¹ t n)).trans ?_
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [S3.chebU, ← companion_U, S3.ellCount, redForms_eq]
      congr 1
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [levelCount_eq, ZMod.inv_coe_unit]
      rfl
    have hA3 : S3.hypG1 M k n (δ : ZMod M) =
        -(1 / 2 * (∑ e ∈ n.divisors, ((min e (n / e) : ℕ) : ℚ) ^ (k - 1) *
            (∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
              (∑ x ∈ (Finset.range M).filter (fun x : ℕ =>
                  (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
                (if M / Nat.gcd τ (M / τ) ≤ 2 then
                  (if Even k ∧ Nat.Coprime ((δ : ZMod M).val * x) (M / Nat.gcd τ (M / τ)) then 1 else 0)
                else (Nat.totient (M / Nat.gcd τ (M / τ)) : ℚ) / 2 *
                  ((if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = 1 then 1 else 0) +
                    (-1) ^ k *
                      (if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = -1 then 1 else 0))))))) := by
      unfold S3.hypG1
      rw [neg_mul]
      congr 2
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [min_def]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [show ((δ : ZMod M).val : ℤ) * (x : ℤ) = (((δ : ZMod M).val * x : ℕ) : ℤ) by push_cast; ring,
        charSum_eq]
    rw [S3.traceFormulaG1, ES.eisG1_of_ne (by omega : k ≠ 2), hA1, hA2, hA3]
    ring

end UploadES

theorem solution (M : ℕ) [NeZero M] (hM : 3 ≤ M)
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    ∃ T : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
        CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ T' : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
          CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
        (∀ γ : ℕ → SL(2, ℤ),
          (∀ d : ℕ, d.Coprime M →
            γ d ∈ CongruenceSubgroup.Gamma0 M ∧ (((γ d) 1 1 : ℤ) : ZMod M) = (d : ZMod M) * (δ : ZMod M)) →
          ∀ (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
            (m : ℕ),
            (qExpansion 1 (T' f)).coeff m =
              ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
                (d : ℂ) ^ (k - 1) * (qExpansion 1 (⇑f ∣[(k : ℤ)] γ d)).coeff (m * n / d ^ 2)) ↔
          T' = T) ∧
      LinearMap.trace ℂ _ T =
        (((if Nat.sqrt n * Nat.sqrt n = n then
              ((k : ℚ) - 1) / 12 * ((M : ℚ) * ∏ l ∈ M.primeFactors, (1 + 1 / (l : ℚ))) *
                (Nat.sqrt n : ℚ) ^ (k - 2) * ((Nat.totient M : ℚ) / 2 *
                  ((if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = 1 then 1 else 0) +
                    (-1) ^ k * (if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = -1 then 1 else 0)))
            else 0) -
          (∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n),
              ((((!![t, -(n : ℤ); 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (k - 2)) 0 0 : ℤ) : ℚ) *
                (∑ Q ∈ (Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (-((t ^ 2 - 4 * n).natAbs : ℤ)) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs).filter
                    (fun Q : ℤ × ℤ × ℤ => 1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = t ^ 2 - 4 * n ∧
                      -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
                      (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))),
                  (((Finset.univ.filter fun v : Fin 2 → ZMod M =>
                      addOrderOf v = M ∧
                        ((!![(t - Q.2.1) / 2, -Q.2.2; Q.1, (t + Q.2.1) / 2] : Matrix (Fin 2) (Fin 2) ℤ).map
                          (Int.castRingHom (ZMod M))).mulVec v = ((δ⁻¹ : (ZMod M)ˣ) : ZMod M) • v).card : ℚ) /
                    ((if Q.1 = Q.2.1 ∧ Q.2.1 = Q.2.2 then 6 else if Q.2.1 = 0 ∧ Q.1 = Q.2.2 then 4 else 2 : ℕ) :
                      ℚ)))) -
          1 / 2 * (∑ e ∈ n.divisors, ((min e (n / e) : ℕ) : ℚ) ^ (k - 1) *
            (∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
              (∑ x ∈ (Finset.range M).filter (fun x : ℕ =>
                  (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
                (if M / Nat.gcd τ (M / τ) ≤ 2 then
                  (if Even k ∧ Nat.Coprime ((δ : ZMod M).val * x) (M / Nat.gcd τ (M / τ)) then 1 else 0)
                else (Nat.totient (M / Nat.gcd τ (M / τ)) : ℚ) / 2 *
                  ((if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = 1 then 1 else 0) +
                    (-1) ^ k *
                      (if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = -1 then 1 else 0))))))
          : ℚ) : ℂ) := by
  exact UploadES.main M hM k hk n hn hnM δ

end
