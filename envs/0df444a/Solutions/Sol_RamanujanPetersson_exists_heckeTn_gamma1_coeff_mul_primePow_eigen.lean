-- Prove2me | solution 1 for RamanujanPetersson.exists_heckeTn_gamma1_coeff_mul_primePow_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T08:39:45.944789+00:00
-- url     : https://prove2.me/submissions/09e8e362-522b-4565-b02c-e4d864229d48

import Mathlib
import Definitions.Def_RPLib_S1_HeckeAlgebra

set_option autoImplicit false

open UpperHalfPlane MatrixGroups ModularForm

noncomputable section

namespace RamanujanPetersson.SW43Aux

open RamanujanPetersson.Diamond RamanujanPetersson.QExp RamanujanPetersson.Hecke
  RamanujanPetersson.HeckeAlgebra

variable {M : ℕ} [NeZero M]

/-- `⟨d⟩` for `gcd(d, M) = 1`, and `0` otherwise. -/
def dia (k : ℤ) (d : ℕ) : Module.End ℂ (S1 M k) :=
  if h : d.Coprime M then diamond k (ZMod.unitOfCoprime d h) else 0

lemma dia_of_coprime (k : ℤ) {d : ℕ} (h : d.Coprime M) :
    dia (M := M) k d = diamond k (ZMod.unitOfCoprime d h) := by
  rw [dia, dif_pos h]

lemma dia_chi (k : ℤ) {d : ℕ} (h : d.Coprime M) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : dia k d f = χ d • f := by
  rw [dia_of_coprime k h, (mem_chiSubspace_iff_diamond k χ f).1 hf, ZMod.coe_unitOfCoprime]

/-- The coefficient formula on all of `S_k(Γ₁(M))`. -/
theorem coeff_gen (k : ℤ) {n : ℕ} (hn : 0 < n) (f : S1 M k) (m : ℕ) :
    (qExpansion 1 (heckeTn k n f)).coeff m = ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
      (d : ℂ) ^ (k - 1) * (qExpansion 1 (dia k d f)).coeff (m * n / d ^ 2) := by
  have hL : (qExpansion 1 (heckeTn k n f)).coeff m = ∑ χ : DirichletCharacter ℂ M,
      ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
        χ d * (d : ℂ) ^ (k - 1) * (qExpansion 1 (proj k χ f)).coeff (m * n / d ^ 2) := by
    show csL M k (heckeTn k n f) m = _
    conv_lhs => rw [← sum_proj k f]
    rw [map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact coeff_heckeTn_chi' k (proj_mem k χ f) hn m
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdM : d.Coprime M := (Finset.mem_filter.1 hd).2
  have hR : (qExpansion 1 (dia k d f)).coeff (m * n / d ^ 2) = ∑ χ : DirichletCharacter ℂ M,
      χ d * (qExpansion 1 (proj k χ f)).coeff (m * n / d ^ 2) := by
    show csL M k (dia k d f) _ = _
    conv_lhs => rw [← sum_proj k f]
    rw [map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [dia_chi k hdM (proj_mem k χ f), map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  ring

lemma heckeTn_comm (k : ℤ) (m n : ℕ) :
    heckeTn (M := M) k m * heckeTn k n = heckeTn k n * heckeTn k m := by
  have h : Commute (heckeTn (M := M) k m) (heckeTn k n) := by
    refine Finset.noncommProd_commute _ _ _ _ fun q _ => ?_
    exact (Finset.noncommProd_commute _ _ _ _ fun p _ => heckePow_commute k q p _ _).symm
  exact h

lemma heckePow_of_dvd (k : ℤ) {p : ℕ} [Fact p.Prime] (hpM : p ∣ M) :
    ∀ r, heckePow (M := M) k p r = heckeTP k p ^ r
  | 0 => by rw [heckePow_zero, pow_zero]
  | 1 => by rw [heckePow_one, pow_one]
  | r + 2 => by
    rw [heckePow_succ_succ, heckeCorr_of_dvd k hpM, zero_mul, sub_zero, heckePow_of_dvd k hpM (r + 1),
      ← pow_succ']

end RamanujanPetersson.SW43Aux

open RamanujanPetersson.Diamond RamanujanPetersson.QExp RamanujanPetersson.Hecke
  RamanujanPetersson.HeckeAlgebra RamanujanPetersson.SW43Aux in
theorem solution (M : ℕ) [NeZero M] (k : ℤ) :
    ∃ D T : ℕ → Module.End ℂ
        (CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
      (∀ d : ℕ, d.Coprime M → ∀ γ ∈ CongruenceSubgroup.Gamma0 M, ((γ 1 1 : ℤ) : ZMod M) = d →
        ∀ f, ⇑(D d f) = ⇑f ∣[k] γ) ∧
      (∀ n : ℕ, 0 < n → ∀ T' : Module.End ℂ
          (CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        (∀ f (m : ℕ), (qExpansion 1 (T' f)).coeff m =
            ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
              (d : ℂ) ^ (k - 1) * (qExpansion 1 (D d f)).coeff (m * n / d ^ 2)) ↔ T' = T n) ∧
      (∀ m n : ℕ, T m * T n = T n * T m) ∧
      (∀ m n : ℕ, m.Coprime n → T (m * n) = T m * T n) ∧
      (∀ p r : ℕ, p.Prime → ¬ p ∣ M →
        T (p ^ (r + 2)) = T p * T (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) • (D p * T (p ^ r))) ∧
      (∀ p r : ℕ, p.Prime → p ∣ M → T (p ^ r) = T p ^ r) ∧
      (∀ (χ : DirichletCharacter ℂ M)
          (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        (∀ γ ∈ CongruenceSubgroup.Gamma0 M, ⇑f ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • ⇑f) →
        (∀ n m : ℕ, 0 < n → (qExpansion 1 (T n f)).coeff m =
            ∑ d ∈ (Nat.gcd m n).divisors, χ d * (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2)) ∧
        ((qExpansion 1 f).coeff 1 = 1 → (∀ p : ℕ, p.Prime → ∃ c : ℂ, T p f = c • f) →
          ∀ n : ℕ, 0 < n → T n f = (qExpansion 1 f).coeff n • f)) := by
  classical
  refine ⟨fun d => dia k d, fun n => heckeTn k n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd γ hγ hγd f
    show ⇑(dia k d f) = _
    rw [dia_of_coprime k hd]
    exact coe_diamond_of_mem k hγ _ (by rw [ZMod.coe_unitOfCoprime, hγd]) f
  · intro n hn T'
    constructor
    · intro h
      refine LinearMap.ext fun f => eq_of_csL k (funext fun m => ?_)
      show (qExpansion 1 (T' f)).coeff m = (qExpansion 1 (heckeTn k n f)).coeff m
      rw [h f m, coeff_gen k hn f m]
    · rintro rfl f m
      exact coeff_gen k hn f m
  · intro m n
    exact heckeTn_comm k m n
  · intro m n hmn
    exact heckeTn_mul k hmn
  · intro p r hp hpM
    have := Fact.mk hp
    show heckeTn k (p ^ (r + 2)) =
      heckeTn k p * heckeTn k (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) • (dia k p * heckeTn k (p ^ r))
    rw [heckeTn_prime_pow_succ_succ k hp r, heckeTn_prime k hp, heckeCorr_of_not_dvd k hpM,
      dia_of_coprime k (coprime_of_not_dvd hpM), smul_mul_assoc]
  · intro p r hp hpM
    have := Fact.mk hp
    show heckeTn k (p ^ r) = heckeTn k p ^ r
    rw [heckeTn_prime_pow' k hp r, heckeTn_prime k hp, heckePow_of_dvd k hpM r]
  · intro χ f hf
    have hf' : f ∈ chiSubspace k χ := hf
    refine ⟨fun n m hn => coeff_heckeTn_chi k hf' hn m, fun h1 he n hn => heckeTn_eigen k hf' h1 ?_ hn⟩
    intro p hp
    obtain ⟨c, hc⟩ := he p hp
    exact ⟨c, by rw [← heckeTn_prime k hp]; exact hc⟩
