-- Prove2me | solution 1 for QAlgorithms.Arunachalam.count_basis_sums
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:34:48.188142+00:00
-- url     : https://prove2.me/submissions/384d41ed-be68-4748-bfcb-db67079fce46

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Mathlib.Data.Nat.Factorial.Basic
set_option autoImplicit false
open scoped BigOperators
open QAlgorithms

private abbrev basis {m : ℕ} (a : Fin m) : Fin m → ZMod 2 := Pi.single a 1

private def walkCount {m : ℕ} (l : ℕ) (S : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i : Fin l → Fin m => ∑ j, basis (i j) = S).card

private lemma toggle_weight {m : ℕ} (S : Fin m → ZMod 2) (a : Fin m) :
    (S a = 0 → hammingNorm (S + basis a) = hammingNorm S + 1) ∧
    (S a ≠ 0 → hammingNorm (S + basis a) + 1 = hammingNorm S) := by
  classical
  have scalar (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
    have hv : z.val = 1 := by
      have := ZMod.val_lt z
      have hn := (ZMod.val_eq_zero z).not.mpr hz
      omega
    exact ZMod.val_injective 2 (by simpa only [ZMod.val_one_eq_one_mod] using hv)
  constructor
  · intro h
    have he : (Finset.univ.filter fun b => (S + basis a) b ≠ 0) =
        insert a (Finset.univ.filter fun b => S b ≠ 0) := by
      ext b
      by_cases hb : b = a
      · subst b; simp [basis, h]
      · simp [basis, hb]
    change (Finset.univ.filter fun b => (S + basis a) b ≠ 0).card = _
    rw [he, Finset.card_insert_of_notMem (by simp [h])]; rfl
  · intro h
    have he : (Finset.univ.filter fun b => (S + basis a) b ≠ 0) =
        (Finset.univ.filter fun b => S b ≠ 0).erase a := by
      ext b
      by_cases hb : b = a
      · subst b; simp [basis, scalar _ h, CharTwo.add_self_eq_zero]
      · simp [basis, hb]
    rw [hammingNorm, he]
    exact Finset.card_erase_add_one (by simp [h])

private lemma walk_succ {m l : ℕ} (S : Fin m → ZMod 2) :
    walkCount (l+1) S = ∑ a : Fin m, walkCount l (S + basis a) := by
  classical
  simp only [walkCount, Finset.card_filter]
  calc
    _ = ∑ p : Fin m × (Fin l → Fin m),
        if basis p.1 + ∑ j, basis (p.2 j) = S then 1 else 0 := by
      apply Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (l+1) => Fin m).symm
      intro i
      simp only [Fin.consEquiv_symm_apply, Fin.sum_univ_succ]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      have neg (x : Fin m → ZMod 2) : -x = x := by
        ext b; exact ZMod.neg_eq_self_mod_two _
      apply propext
      rw [add_comm (basis a) _, ← eq_sub_iff_add_eq, sub_eq_add_neg, neg]

private lemma walk_feasible {m l : ℕ} (i : Fin l → Fin m) :
    ∃ r : ℕ, l = hammingNorm (∑ j, basis (i j)) + 2*r := by
  induction l with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    let S := ∑ j : Fin l, basis (i j.succ)
    obtain ⟨r, hr⟩ := ih (fun j => i j.succ)
    change l = hammingNorm S + 2*r at hr
    rw [Fin.sum_univ_succ]
    change ∃ r, l+1 = hammingNorm (basis (i 0) + S) + 2*r
    rw [add_comm (basis (i 0)) S]
    by_cases h : S (i 0) = 0
    · exact ⟨r, by rw [(toggle_weight S (i 0)).1 h]; omega⟩
    · exact ⟨r+1, by have := (toggle_weight S (i 0)).2 h; omega⟩

private lemma walk_zero {m l : ℕ} (S : Fin m → ZMod 2)
    (h : ¬ ∃ r : ℕ, l = hammingNorm S + 2*r) : walkCount l S = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _ hi
  exact h (hi ▸ walk_feasible i)

private lemma walk_base {m : ℕ} (S : Fin m → ZMod 2) :
    walkCount 0 S = if S = 0 then 1 else 0 := by
  classical
  by_cases h : S = 0 <;> simp [walkCount, eq_comm, h]

-- Multiplying by the pairing denominator keeps the counting induction integral.
private lemma walk_bound {m : ℕ} (l : ℕ) :
    ∀ (S : Fin m → ZMod 2) (r : ℕ), l = hammingNorm S + 2*r →
      (walkCount l S : ℝ) * ((2 : ℝ)^r * (r.factorial : ℝ)) ≤
        (l.factorial : ℝ) * (m : ℝ)^r := by
  classical
  induction l with
  | zero =>
    intro S r h
    have hr : r = 0 := by omega
    have hs : S = 0 := hammingNorm_eq_zero.mp (by omega)
    subst r; subst S
    simp [walk_base]
  | succ l ih =>
    intro S r h
    let A : ℝ := (l.factorial : ℝ) * (m : ℝ)^r
    let B : ℝ := (2 * (r : ℝ)) * (l.factorial : ℝ) * (m : ℝ)^(r-1)
    let D : ℝ := (2 : ℝ)^r * (r.factorial : ℝ)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hstep (a : Fin m) :
        (walkCount l (S + basis a) : ℝ) * D ≤ if S a ≠ 0 then A else B := by
      by_cases ha : S a ≠ 0
      · rw [if_pos ha]
        exact ih (S + basis a) r (by have := (toggle_weight S a).2 ha; omega)
      · rw [if_neg ha]
        have ha' : S a = 0 := not_ne_iff.mp ha
        have hw := (toggle_weight S a).1 ha'
        by_cases hr : r = 0
        · have hz : walkCount l (S + basis a) = 0 :=
            walk_zero _ (by rintro ⟨t, ht⟩; omega)
          simp [hz]; exact hB
        · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
          have hh := ih (S + basis a) s (by omega)
          have hp : D = (2*(s+1 : ℕ) : ℝ) * ((2:ℝ)^s * (s.factorial : ℝ)) := by
            dsimp [D]; rw [pow_succ, Nat.factorial_succ]; push_cast; ring
          rw [hp]
          have := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ 2*(s+1 : ℕ))
          simpa [B, mul_assoc, mul_left_comm, mul_comm] using this
    have hsum : (walkCount (l+1) S : ℝ) * D ≤ (hammingNorm S : ℝ)*A + (m:ℝ)*B := by
      rw [walk_succ, Nat.cast_sum, Finset.sum_mul]
      refine (Finset.sum_le_sum fun a _ => hstep a).trans ?_
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (hammingNorm S : ℝ)*A + _ ≤ _
      gcongr
      have hb : (Finset.univ.filter fun a : Fin m => ¬ S a ≠ 0).card ≤ m := by
        simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun a => ¬ S a ≠ 0))
      exact_mod_cast hb
    have hfinal : (hammingNorm S : ℝ)*A + (m:ℝ)*B =
        ((l+1).factorial : ℝ) * (m:ℝ)^r := by
      have hc : (l+1 : ℝ) = (hammingNorm S : ℝ) + 2*(r:ℝ) := by exact_mod_cast h
      by_cases hr : r = 0
      · subst r; simp only [A, B, Nat.cast_zero, mul_zero, zero_mul, pow_zero, add_zero]
        rw [Nat.factorial_succ]; push_cast; rw [hc]; ring
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
        dsimp [A, B]
        rw [Nat.factorial_succ]
        push_cast
        rw [pow_succ]
        push_cast at hc
        rw [hc]
        ring
    exact hsum.trans_eq hfinal

theorem solution {m T ℓ : ℕ} (S : Fin m → ZMod 2) (hqℓ : hammingNorm S ≤ ℓ)
    (_hℓT : ℓ ≤ T) :
    (Even (ℓ - hammingNorm S) →
        (((Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card : ℕ) : ℝ) ≤
          ((ℓ.factorial : ℕ) : ℝ) * (m : ℝ) ^ ((ℓ - hammingNorm S) / 2) /
            ((2 : ℝ) ^ ((ℓ - hammingNorm S) / 2) *
              (((ℓ - hammingNorm S) / 2).factorial : ℕ))) ∧
      (¬ Even (ℓ - hammingNorm S) →
        (Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card = 0) := by
  classical
  constructor
  · rintro ⟨r, hr⟩
    have hl : ℓ = hammingNorm S + 2*r := by omega
    have hd : (ℓ - hammingNorm S)/2 = r := by omega
    rw [hd]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2^r * (r.factorial : ℝ))).mpr
    exact walk_bound ℓ S r hl
  · intro ho
    exact walk_zero S (by
      rintro ⟨r, hr⟩
      apply ho
      exact ⟨r, by omega⟩)
