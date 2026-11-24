-- Prove2me | solution 1 for Poly1305.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:06:53.530974+00:00
-- url     : https://prove2.me/submissions/19a6b59e-419f-41be-8dcd-710f866077ce

import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Poly1305Bernstein
import Theorems.Thm_Poly1305_theorem_3_1
import Theorems.Thm_Poly1305_theorem_3_2
import Theorems.Thm_Poly1305_card_U_le_eight

namespace Poly1305.GoalThm33

open Polynomial

/-- Reading back a 16-byte little-endian representation gives `n mod 2^128`. -/
theorem leVal_toStr16 (n : ℕ) : leVal (toStr16 n) = n % 2 ^ 128 := by
  have key : ∀ k : ℕ, (∑ j ∈ Finset.range k, 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256))
      = n % 2 ^ (8 * k) := by
    intro k
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ∀ j, (2 : ℕ) ^ (8 * j) = 256 ^ j := fun j => by
        rw [pow_mul]; norm_num
      simp only [h1]
      rw [Nat.mod_pow_succ]
  unfold leVal toStr16
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256)) 16, key]

theorem toStr16_eq_imp (a b : ℕ) (h : toStr16 a = toStr16 b) : a % 2 ^ 128 = b % 2 ^ 128 := by
  rw [← leVal_toStr16, ← leVal_toStr16, h]

theorem p1305_eq : (p1305 : ℤ) = 2 ^ 130 - 5 := by
  unfold p1305; norm_num

attribute [local irreducible] p1305

/-- The polynomial of a message has degree at most its number of chunks. -/
theorem natDegree_poly_le (m : Message) : (poly m).natDegree ≤ numChunks m := by
  unfold poly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  have := (Finset.mem_Icc.mp hi).1
  omega

theorem numChunks_le (m : Message) (L : ℕ) (hm : m.length ≤ L) :
    numChunks m ≤ ⌈(L : ℚ) / 16⌉₊ := by
  set c := ⌈(L : ℚ) / 16⌉₊
  have h1 : (L : ℚ) / 16 ≤ c := Nat.le_ceil _
  have h2 : (L : ℚ) ≤ 16 * c := by linarith
  have h3 : L ≤ 16 * c := by exact_mod_cast h2
  unfold numChunks
  omega

/-- The count of Theorem 3.3. -/
theorem count (m m' : Message) (hmm' : m ≠ m') (L : ℕ) (hm : m.length ≤ L)
    (hm' : m'.length ≤ L) (g : Str16) (R : Finset ℤ) (hR : R ⊆ Finset.Icc 0 (2 ^ 130 - 6)) :
    (R.filter (fun r => H r m = add16 (H r m') g)).card ≤ 8 * ⌈(L : ℚ) / 16⌉₊ := by
  have : Fact (Nat.Prime p1305) := ⟨theorem_3_1⟩
  set c := ⌈(L : ℚ) / 16⌉₊
  set U := (Finset.Icc (-(2 ^ 130 - 6 : ℤ)) (2 ^ 130 - 6)).filter
      (fun x => x ≡ (leVal g : ℤ) [ZMOD 2 ^ 128]) with hU
  have hp : (0 : ℤ) < p1305 := by rw [p1305_eq]; norm_num
  -- the polynomial for each `u`
  let f : ℤ → (ZMod p1305)[X] := fun u =>
    (poly m - poly m' - C u).map (Int.castRingHom (ZMod p1305))
  have hf0 : ∀ u, f u ≠ 0 := by
    intro u hu
    exact hmm' (theorem_3_2 m' m u hu).symm
  have hfdeg : ∀ u, (f u).natDegree ≤ c := by
    intro u
    refine (Polynomial.natDegree_map_le).trans ?_
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_C, Nat.max_zero]
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    exact max_le ((natDegree_poly_le m).trans (numChunks_le m L hm))
      ((natDegree_poly_le m').trans (numChunks_le m' L hm'))
  have hfeval : ∀ u (r : ℤ), (f u).eval (r : ZMod p1305) =
      (((poly m).eval r - (poly m').eval r - u : ℤ) : ZMod p1305) := by
    intro u r
    simp only [f, Polynomial.eval_map, ← eq_intCast (Int.castRingHom (ZMod p1305)) r]
    rw [Polynomial.eval₂_hom]
    simp
  -- each good `r` lies in the piece of some `u ∈ U`
  have hsub : R.filter (fun r => H r m = add16 (H r m') g) ⊆
      U.biUnion (fun u => R.filter (fun r : ℤ => (f u).IsRoot ((r : ℤ) : ZMod p1305))) := by
    intro r hr
    have hrR := (Finset.mem_filter.mp hr).1
    have hH := (Finset.mem_filter.mp hr).2
    set A : ℤ := (poly m).eval r % p1305 with hA
    set B : ℤ := (poly m').eval r % p1305 with hB
    have hA0 : 0 ≤ A := Int.emod_nonneg _ hp.ne'
    have hAp : A < p1305 := Int.emod_lt_of_pos _ hp
    have hB0 : 0 ≤ B := Int.emod_nonneg _ hp.ne'
    have hBp : B < p1305 := Int.emod_lt_of_pos _ hp
    rw [p1305_eq] at hAp hBp
    have hH' : toStr16 (A.toNat % 2 ^ 128) =
        toStr16 ((leVal (toStr16 (B.toNat % 2 ^ 128)) + leVal g) % 2 ^ 128) := hH
    have hmod := toStr16_eq_imp _ _ hH'
    simp only [Nat.mod_mod] at hmod
    rw [leVal_toStr16] at hmod
    have hcong : A - B ≡ (leVal g : ℤ) [ZMOD 2 ^ 128] := by
      have e1 : ((A.toNat : ℕ) : ℤ) = A := Int.toNat_of_nonneg hA0
      have e2 : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hB0
      have hz : ((A.toNat % 2 ^ 128 : ℕ) : ℤ) =
          (((B.toNat % 2 ^ 128 % 2 ^ 128 + leVal g) % 2 ^ 128 : ℕ) : ℤ) := by
        rw [hmod]
      push_cast at hz
      rw [e1, e2] at hz
      unfold Int.ModEq
      omega
    rw [Finset.mem_biUnion]
    refine ⟨A - B, ?_, ?_⟩
    · rw [hU, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hcong⟩
    · rw [Finset.mem_filter]
      refine ⟨hrR, ?_⟩
      rw [Polynomial.IsRoot, hfeval, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h1 := Int.emod_add_mul_ediv ((poly m).eval r) p1305
      have h2 := Int.emod_add_mul_ediv ((poly m').eval r) p1305
      refine ⟨(poly m).eval r / p1305 - (poly m').eval r / p1305, ?_⟩
      rw [← hA] at h1
      rw [← hB] at h2
      linear_combination h2 - h1
  -- each piece has at most `c` elements
  have hpiece : ∀ u, (R.filter (fun r : ℤ => (f u).IsRoot ((r : ℤ) : ZMod p1305))).card ≤ c := by
    intro u
    refine le_trans ?_ ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' (f u)).trans (hfdeg u)))
    apply Finset.card_le_card_of_injOn (fun r : ℤ => (r : ZMod p1305))
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (hf0 u)]
      exact hr.2
    · intro r hr s hs hrs
      rw [Finset.mem_coe, Finset.mem_filter] at hr hs
      have hr' := Finset.mem_Icc.mp (hR hr.1)
      have hs' := Finset.mem_Icc.mp (hR hs.1)
      simp only at hrs
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hrs
      obtain ⟨k, hk⟩ := hrs
      rw [p1305_eq] at hk
      have : k = 0 := by
        by_contra hk0
        rcases lt_or_gt_of_ne hk0 with h | h <;> nlinarith
      subst this
      linarith
  calc (R.filter (fun r => H r m = add16 (H r m') g)).card
      ≤ (U.biUnion (fun u => R.filter (fun r : ℤ => (f u).IsRoot ((r : ℤ) : ZMod p1305)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (R.filter (fun r : ℤ => (f u).IsRoot ((r : ℤ) : ZMod p1305))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, c := Finset.sum_le_sum (fun u _ => hpiece u)
    _ = U.card * c := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 8 * c := Nat.mul_le_mul_right _ (card_U_le_eight g)

theorem theorem_3_3_dev (m m' : Message) (hmm' : m ≠ m') (L : ℕ) (hm : m.length ≤ L)
    (hm' : m'.length ≤ L) (g : Str16) (R : Finset ℤ) (hR : R ⊆ Finset.Icc 0 (2 ^ 130 - 6)) :
    (R.filter (fun r => H r m = add16 (H r m') g)).card ≤ 8 * ⌈(L : ℚ) / 16⌉₊ ∧
    ∀ hR' : R.Nonempty, R.card = 2 ^ 106 →
      (PMF.uniformOfFinset R hR').toOuterMeasure {r | H r m = add16 (H r m') g} ≤
        (8 * ⌈(L : ℚ) / 16⌉₊ : ENNReal) / 2 ^ 106 := by
  have hc := count m m' hmm' L hm hm' g R hR
  refine ⟨hc, ?_⟩
  intro hR' hcard
  rw [PMF.toOuterMeasure_uniformOfFinset_apply, hcard, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  have hc' : ((R.filter (fun r => H r m = add16 (H r m') g)).card : ENNReal) ≤
      (8 * ⌈(L : ℚ) / 16⌉₊ : ENNReal) := by exact_mod_cast hc
  convert hc' using 3
  ext x
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]

end Poly1305.GoalThm33

open Poly1305 in
theorem solution (m m' : Message) (hmm' : m ≠ m') (L : ℕ) (hm : m.length ≤ L)
    (hm' : m'.length ≤ L) (g : Str16) (R : Finset ℤ) (hR : R ⊆ Finset.Icc 0 (2 ^ 130 - 6)) :
    (R.filter (fun r => H r m = add16 (H r m') g)).card ≤ 8 * ⌈(L : ℚ) / 16⌉₊ ∧
    ∀ hR' : R.Nonempty, R.card = 2 ^ 106 →
      (PMF.uniformOfFinset R hR').toOuterMeasure {r | H r m = add16 (H r m') g} ≤
        (8 * ⌈(L : ℚ) / 16⌉₊ : ENNReal) / 2 ^ 106 :=
  Poly1305.GoalThm33.theorem_3_3_dev m m' hmm' L hm hm' g R hR
