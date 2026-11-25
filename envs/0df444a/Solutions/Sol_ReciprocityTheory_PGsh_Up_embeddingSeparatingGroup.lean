-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.embeddingSeparatingGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:02.766609+00:00
-- url     : https://prove2.me/submissions/3c327030-f64b-48c5-8123-761fad01c16c

import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroup
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_fermat
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_pair
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_proj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_ne_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_seed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : EmbeddingSeparatingGroupStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U
  have hv : v.Integers R := hS.integers
  have hpv : v (algebraMap R C (p : R)) < 1 := hS.p_lt
  have hp : p.Prime := Fact.out

  have hvnat : ∀ n : ℕ, ¬ p ∣ n → v (algebraMap R C (n : R)) = 1 := by
    intro n hn
    by_contra hne
    have hlt : v (algebraMap R C (n : R)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h2 : (p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) h1
      push_cast at this
      exact this
    have h3 : v (algebraMap R C ((p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R))) < 1 := by
      rw [map_add]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hpv
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hlt
    rw [h2, map_one, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
    intro n hn
    have hn0 : (n : C) ≠ 0 := by
      have : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
      exact_mod_cast this
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [map_natCast]; exact hn0)) (hvnat n hn)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have heig : ∀ a j, (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • U.εT j := U.εT_eig
  have hres1 : FrobeniusGroupField.res hv 1 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 1).2 (by simp)

  have hex : ∀ t : Option (Fin U.m × Fin U.m × Bool), ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧
      H.ρ b ^ m = 1 ∧
      (match t with
        | none => ∀ j, U.εT j ≠ 0 → v (algebraMap R C (U.sg j b - 1)) = 1
        | some (i, k, e) => U.εT i ≠ 0 → U.εT k ≠ 0 → cond e (k ≠ U.φ i) (i ≠ k) →
            FrobeniusGroupField.res hv (U.sg k b) ≠ FrobeniusGroupField.res hv (U.sg i b) ^ p ^ e.toNat) := by
    intro t
    rcases t with _ | ⟨i, k, e⟩
    · obtain ⟨b, m, s, hm, hmp, hbm, hb⟩ := FrobeniusGroupField.seed p hv hpv H.ρ U.εT U.sg heig 0 2
      refine ⟨b, m, hm, hmp, hbm, ?_⟩
      intro j hj
      have h2 : FrobeniusGroupField.res hv (U.sg j 0 + ((2 : ℤ) : R)) = FrobeniusGroupField.res hv 2 := by simp
      have hr2 : FrobeniusGroupField.res hv 2 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 2).2 (by simpa using hvnat 2 hp2')
      have hfer : ∀ s : ℕ, FrobeniusGroupField.res hv 2 ^ p ^ s = FrobeniusGroupField.res hv 2 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          have hf := FrobeniusGroupField.fermat p hv hpv (2 : ℤ_[p])
          rw [map_ofNat] at hf
          rw [pow_succ, pow_mul, ih, hf]
      have hbj := hb j hj (by rw [h2]; exact hr2)
      rw [h2, hfer] at hbj
      apply (FrobeniusGroupField.res_ne_zero hv _).1
      rw [map_sub, hbj, map_one]
      have h21 : FrobeniusGroupField.res hv 2 - 1 = FrobeniusGroupField.res hv 1 := by
        rw [← map_one (FrobeniusGroupField.res hv), ← map_sub]
        norm_num
      rw [h21]
      exact hres1
    · by_cases hall : U.εT i ≠ 0 ∧ U.εT k ≠ 0 ∧ cond e (k ≠ U.φ i) (i ≠ k)
      · obtain ⟨hi, hk, hik⟩ := hall
        have ha : ∃ a, FrobeniusGroupField.res hv (U.sg k a) ≠ FrobeniusGroupField.res hv (U.sg i a) ^ p ^ e.toNat := by
          cases e
          · simp only [cond_false, Bool.toNat_false, pow_zero, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct i k hik
            refine ⟨a, fun heq => ?_⟩
            have h0 : FrobeniusGroupField.res hv (U.sg i a - U.sg k a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
          · simp only [cond_true, Bool.toNat_true, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct k (U.φ i) hik
            refine ⟨a, ?_⟩
            have hfr : FrobeniusGroupField.res hv (U.sg (U.φ i) a) = FrobeniusGroupField.res hv (U.sg i a) ^ p := by
              have h0 := (FrobeniusGroupField.res_eq_zero hv _).2 (U.frob i a)
              rw [map_sub, map_pow, sub_eq_zero] at h0
              exact h0
            rw [← hfr]
            intro heq
            have h0 : FrobeniusGroupField.res hv (U.sg k a - U.sg (U.φ i) a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, m, hm, hmp, hbm, hb⟩ :=
          FrobeniusGroupField.pair p hp2 hv hpv H.ρ U.εT U.sg heig a e.toNat i k hi hk ha
        exact ⟨b, m, hm, hmp, hbm, fun _ _ _ => hb⟩
      · exact ⟨1, 1, one_pos, hp.not_dvd_one, by simp, fun hi hk hik => absurd ⟨hi, hk, hik⟩ hall⟩
  choose b m0 hm0 hmp0 hbm0 hQ using hex

  let m : Option (Fin U.m × Fin U.m × Bool) → ℕ := fun t => 2 * m0 t
  have hm : ∀ t, 0 < m t := fun t => by
    have := hm0 t
    show 0 < 2 * m0 t
    omega
  have hmp : ∀ t, ¬ p ∣ m t := fun t h => ((Nat.Prime.dvd_mul hp).1 h).elim hp2' (hmp0 t)
  have hbm : ∀ t, H.ρ (b t) ^ m t = 1 := fun t => by
    show H.ρ (b t) ^ (2 * m0 t) = 1
    rw [mul_comm, pow_mul, hbm0 t, one_pow]
  haveI : ∀ t, NeZero (m t) := fun t => ⟨(hm t).ne'⟩
  have hone : ∀ t, (1 : ZMod (m t)).val = 1 := fun t => by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by have := hm0 t; show 1 < 2 * m0 t; omega)
  let G := ∀ t : Option (Fin U.m × Fin U.m × Bool), Multiplicative (ZMod (m t))
  let β : G → O := fun γ => ∏ t, b t ^ (Multiplicative.toAdd (γ t)).val
  have key : ∀ (s : Finset (Option (Fin U.m × Fin U.m × Bool)))
      (n : Option (Fin U.m × Fin U.m × Bool) → ℕ),
      H.ρ (∏ t ∈ s, b t ^ n t) = H.ρ (∏ t ∈ s, b t ^ (n t % m t)) := by
    intro s n
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, ih, map_pow, map_pow,
      ← pow_eq_pow_mod _ (hbm a)]
  have hmul : ∀ γ γ' : G, H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ') := by
    intro γ γ'
    have e1 : β (γ * γ') = ∏ t, b t ^ (((Multiplicative.toAdd (γ t)).val +
        (Multiplicative.toAdd (γ' t)).val) % m t) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Pi.mul_apply, toAdd_mul, ZMod.val_add]
    have k2 := key Finset.univ
      (fun t => (Multiplicative.toAdd (γ t)).val + (Multiplicative.toAdd (γ' t)).val)
    beta_reduce at k2
    rw [e1, ← k2, ← map_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => pow_add _ _ _
  have h1 : H.ρ (β 1) = 1 := by
    have hb1 : β 1 = 1 := by
      refine (Finset.prod_congr rfl fun t _ => ?_).trans Finset.prod_const_one
      show b t ^ (Multiplicative.toAdd ((1 : G) t)).val = 1
      rw [Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero]
    rw [hb1, map_one]
  have hcard : IsUnit (Fintype.card G : R) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun t _ => ?_
    have hc : Fintype.card (Multiplicative (ZMod (m t))) = m t := by simp
    rw [hc]
    exact hunit _ (hmp t)
  let gen : Option (Fin U.m × Fin U.m × Bool) → G := fun t =>
    Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t)))
  have hgen : ∀ t, β (gen t) = b t := by
    intro t
    show ∏ u, b u ^ (Multiplicative.toAdd
      (Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t))) u)).val
      = b t
    rw [Finset.prod_eq_single t]
    · rw [Pi.mulSingle_eq_same, toAdd_ofAdd, hone, pow_one]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, toAdd_one, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsep' : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      FrobeniusGroupField.res hv (U.sg k (b (some (i, k, false)))) ≠ FrobeniusGroupField.res hv (U.sg i (b (some (i, k, false)))) := by
    intro i k hi hk hik
    have hq := hQ (some (i, k, false)) hi hk (by simpa using hik)
    simpa using hq
  have hsepψ : ∀ j k, U.εT j ≠ 0 → U.εT k ≠ 0 → j ≠ k → ∃ γ : G, U.sg j (β γ) ≠ U.sg k (β γ) := by
    intro j k hj hk hjk
    refine ⟨gen (some (j, k, false)), ?_⟩
    rw [hgen]
    intro heq
    exact hsep' j k hj hk hjk (by rw [heq])
  refine ⟨G, inferInstance, inferInstance, β, hmul, h1, hcard, ?_, ?_, ?_⟩
  · intro i γ hi
    obtain ⟨j, hj, hψ⟩ := FrobeniusGroupField.proj p hv hpv hcard (fun γ => H.ρ (β γ)) hmul h1 U.εT U.εT_orth
      U.εT_sum (fun j γ => U.sg j (β γ)) (fun j γ => U.εT_eig (β γ) j)
      (fun j k hj hk hjk => hsepψ j k hj hk hjk) i hi
    have hjφ : j = U.φ i := by
      by_contra hne
      have hq := hQ (some (i, j, true)) hi hj (by simpa using hne)
      simp only [Bool.toNat_true, pow_one] at hq
      have h2 := hψ (gen (some (i, j, true)))
      simp only [hgen] at h2
      exact hq (by rw [h2, map_pow])
    rw [← hjφ]
    exact hψ γ
  · intro i k hi hk hik
    refine ⟨gen (some (i, k, false)), ?_⟩
    rw [hgen]
    apply (FrobeniusGroupField.res_ne_zero hv _).1
    rw [map_sub, sub_ne_zero]
    exact (hsep' i k hi hk hik).symm
  · intro i hi
    exact ⟨gen none, by rw [hgen]; exact hQ none i hi⟩
end ReciprocityTheory.PGsh.Up
