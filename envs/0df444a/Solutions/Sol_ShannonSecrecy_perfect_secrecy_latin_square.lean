-- Prove2me | solution 1 for ShannonSecrecy.perfect_secrecy_latin_square
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T04:16:03.184726+00:00
-- url     : https://prove2.me/submissions/91369d30-fca8-4ec4-8fe3-b31b9ed47e50

import Mathlib
import Definitions.Def_shannon_secrecy_system

set_option autoImplicit false

namespace LatinAux
open ShannonSecrecy

variable {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]

lemma numerator (C : Cipher M K E) (p : M → ℝ) (e : E) (m : M) :
    (∑ k : K, if C.encipher k m = e then p m * C.keyProb k else 0) = p m * msgToCrypto C m e := by
  simp only [msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]

lemma cryptoProb_eq (C : Cipher M K E) (p : M → ℝ) (e : E) :
    cryptoProb C p e = ∑ m, p m * msgToCrypto C m e := by
  simp only [cryptoProb, msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]

/-- Under perfect secrecy with a uniform prior, a cryptogram of positive probability is reachable
from every message, and `P_m(e) = P(e)`. -/
lemma reach (C : Cipher M K E) (h : PerfectSecrecy C) (p : M → ℝ) (hp : IsPMF p)
    (hpos : ∀ m, 0 < p m) (e : E) (he : cryptoProb C p e ≠ 0) (m : M) :
    msgToCrypto C m e = cryptoProb C p e ∧ ∃ k, C.encipher k m = e := by
  have hpost := h p hp e he m
  unfold postProb at hpost
  rw [numerator, div_eq_iff he] at hpost
  have hmc : msgToCrypto C m e = cryptoProb C p e :=
    mul_left_cancel₀ (hpos m).ne' (by linarith [hpost])
  refine ⟨hmc, ?_⟩
  by_contra hno
  push Not at hno
  have : msgToCrypto C m e = 0 := by simp [msgToCrypto, hno]
  rw [this] at hmc
  exact he hmc.symm

end LatinAux

open ShannonSecrecy LatinAux in
theorem solution
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C)
    (hMK : Fintype.card M = Fintype.card K) (hKE : Fintype.card K = Fintype.card E) :
    (∀ (m : M) (e : E), ∃! k : K, C.encipher k m = e) ∧
      ∀ k k' : K, C.keyProb k = C.keyProb k' := by
  classical
  -- `K` is nonempty since key probabilities sum to 1
  have hK : Nonempty K := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := C.keyProb_sum
    simp at this
  have hcardK : 0 < Fintype.card K := Fintype.card_pos
  have hM : Nonempty M := Fintype.card_pos_iff.mp (hMK ▸ hcardK)
  -- uniform prior
  set p : M → ℝ := fun _ => (Fintype.card M : ℝ)⁻¹ with hpdef
  have hpos : ∀ m, 0 < p m := fun _ => by
    simp only [hpdef]; exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hp : IsPMF p := by
    refine ⟨fun m => (hpos m).le, ?_⟩
    simp only [hpdef, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hmc_nn : ∀ m e, 0 ≤ msgToCrypto C m e := fun m e =>
    Finset.sum_nonneg fun k _ => by split_ifs; exacts [C.keyProb_nonneg k, le_rfl]
  -- For a positive-probability cryptogram, the reaching keys form a bijection `M ≃ K`.
  have key : ∀ e, cryptoProb C p e ≠ 0 →
      (∀ m, ∃! k, C.encipher k m = e) ∧ ∀ k k', C.keyProb k = C.keyProb k' := by
    intro e he
    have hr := fun m => reach C h p hp hpos e he m
    choose f hf using fun m => (hr m).2
    have finj : Function.Injective f := by
      intro m1 m2 h12
      apply C.encipher_injective (f m1)
      rw [hf m1, h12, hf m2]
    have fbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨finj, hMK⟩
    -- uniqueness: two keys reaching `e` from `m` would both be `f`-images
    have huniq : ∀ m k, C.encipher k m = e → k = f m := by
      intro m k hk
      obtain ⟨m', rfl⟩ := fbij.2 k
      have : m' = m := by
        apply C.encipher_injective (f m')
        rw [hf m', hk]
      rw [this]
    refine ⟨fun m => ⟨f m, hf m, fun k hk => huniq m k hk⟩, ?_⟩
    -- `P_m(e) = P(f m)` and is independent of `m`
    have hval : ∀ m, msgToCrypto C m e = C.keyProb (f m) := by
      intro m
      unfold msgToCrypto
      rw [Finset.sum_eq_single (f m)]
      · rw [if_pos (hf m)]
      · intro k _ hk; rw [if_neg]; exact fun hk' => hk (huniq m k hk')
      · simp
    intro k k'
    obtain ⟨m, rfl⟩ := fbij.2 k
    obtain ⟨m', rfl⟩ := fbij.2 k'
    rw [← hval, ← hval, (hr m).1, (hr m').1]
  -- a key of positive probability exists
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < C.keyProb k := by
    by_contra hcon
    push Not at hcon
    have : ∑ k, C.keyProb k ≤ 0 := Finset.sum_nonpos (fun k _ => hcon k)
    linarith [C.keyProb_sum]
  obtain ⟨m0⟩ := hM
  have hpos_e : ∀ k m, 0 < C.keyProb k → cryptoProb C p (C.encipher k m) ≠ 0 := by
    intro k m hk
    apply ne_of_gt
    rw [cryptoProb_eq]
    have hterm : 0 < p m * msgToCrypto C m (C.encipher k m) := by
      apply mul_pos (hpos m)
      calc 0 < C.keyProb k := hk
        _ = (if C.encipher k m = C.encipher k m then C.keyProb k else 0) := by simp
        _ ≤ msgToCrypto C m (C.encipher k m) :=
            Finset.single_le_sum (f := fun k' => if C.encipher k' m = C.encipher k m then C.keyProb k' else 0)
              (fun k' _ => by split_ifs; exacts [C.keyProb_nonneg k', le_rfl]) (Finset.mem_univ k)
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (f := fun m' => p m' * msgToCrypto C m' (C.encipher k m))
      (fun m' _ => mul_nonneg (hpos m').le (hmc_nn _ _)) (Finset.mem_univ m))
  have hequi := (key _ (hpos_e k0 m0 hk0)).2
  refine ⟨fun m e => ?_, hequi⟩
  -- every key has positive probability, and every cryptogram is reached by `k0`
  have hsurj : Function.Surjective (C.encipher k0) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨C.encipher_injective k0, hMK.trans hKE⟩).2
  obtain ⟨m1, rfl⟩ := hsurj e
  exact (key _ (hpos_e k0 m1 hk0)).1 m
