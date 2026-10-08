-- Prove2me | solution 1 for RV27.interval_pair_weight_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T15:08:16.114285+00:00
-- url     : https://prove2.me/submissions/12db7711-7683-4d99-b89c-1e206223e1b0

import Mathlib
import Theorems.Thm_MVSieve_primitive_character_large_sieve
import Theorems.Thm_MVSieve_large_sieve_weight_lower

open Finset

namespace RV27C

lemma normSq_eq_mul_star (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma pair_count_char (d : ℕ) [NeZero d] (T : Finset ℕ) (hT : ∀ t ∈ T, Nat.Coprime t d) :
    ((d.totient : ℂ) * (((T ×ˢ T).filter (fun x => d ∣ x.1 + x.2)).card : ℂ)) =
      ∑ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) := by
  have hunit : ∀ t ∈ T, IsUnit ((t : ℕ) : ZMod d) := fun t ht =>
    (ZMod.isUnit_iff_coprime t d).2 (hT t ht)
  have key : ∀ t ∈ T, ∀ t' ∈ T, ∑ χ : DirichletCharacter ℂ d, χ (-1) * (χ t * star (χ t')) =
      if d ∣ t + t' then (d.totient : ℂ) else 0 := by
    intro t ht t' ht'
    obtain ⟨u, hu⟩ := hunit t' ht'
    have h1 : ∀ χ : DirichletCharacter ℂ d, χ (-1) * (χ t * star (χ t')) =
        χ (-(t : ZMod d) * (u⁻¹ : (ZMod d)ˣ)) := by
      intro χ
      rw [MulChar.star_apply', MulChar.inv_apply, ← hu, Ring.inverse_unit, map_mul,
        show (-(t : ZMod d)) = -1 * t by ring, map_mul]
      ring
    simp_rw [h1]
    rw [DirichletCharacter.sum_characters_eq]
    congr 1
    apply propext
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro h
      have : -(t : ZMod d) = u := by
        have := congrArg (· * (u : ZMod d)) h
        simpa [mul_assoc] using this
      rw [← hu, ← this]; ring
    · intro h
      have : (u : ZMod d) = -(t : ZMod d) := by rw [hu]; linear_combination h
      rw [← this]; simp
  calc ((d.totient : ℂ) * (((T ×ˢ T).filter (fun x => d ∣ x.1 + x.2)).card : ℂ))
      = ∑ t ∈ T, ∑ t' ∈ T, if d ∣ t + t' then (d.totient : ℂ) else 0 := by
        rw [card_filter, ← sum_product']
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro x _
        split_ifs <;> simp
    _ = ∑ t ∈ T, ∑ t' ∈ T, ∑ χ : DirichletCharacter ℂ d, χ (-1) * (χ t * star (χ t')) := by
        apply sum_congr rfl; intro t ht; apply sum_congr rfl; intro t' ht'
        rw [key t ht t' ht']
    _ = _ := by
        have : ∀ χ : DirichletCharacter ℂ d, χ (-1) * ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) =
            ∑ t ∈ T, ∑ t' ∈ T, χ (-1) * (χ t * star (χ t')) := by
          intro χ
          rw [normSq_eq_mul_star, star_sum, sum_mul_sum, mul_sum]
          simp_rw [mul_sum]
        simp_rw [this]
        symm
        rw [sum_comm]
        apply sum_congr rfl; intro t _
        rw [sum_comm]


/-! ### products of distinct primes -/

lemma coprime_prod_of_not_mem (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (p : ℕ) (hp : p.Prime)
    (hpD : p ∉ D) : Nat.Coprime p (∏ q ∈ D, q) := by
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Nat.coprime_primes hp (hD q hq)).2 (fun h => hpD (h ▸ hq))

lemma squarefree_prod_primes (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    Squarefree (∏ p ∈ D, p) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert p D hpD ih =>
    rw [prod_insert hpD]
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    rw [Nat.squarefree_mul_iff]
    exact ⟨coprime_prod_of_not_mem D hD' p (hD p (mem_insert_self p D)) hpD,
      (hD p (mem_insert_self p D)).squarefree, ih hD'⟩

lemma totient_prod_primes (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    ((∏ p ∈ D, p).totient : ℝ) = ∏ p ∈ D, ((p : ℝ) - 1) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert p D hpD ih =>
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    have hp := hD p (mem_insert_self p D)
    rw [prod_insert hpD, prod_insert hpD, Nat.totient_mul (coprime_prod_of_not_mem D hD' p hp hpD),
      Nat.totient_prime hp, Nat.cast_mul, ih hD', Nat.cast_sub hp.one_le]
    simp

lemma prod_primes_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (m : ℕ) :
    (∏ p ∈ D, p) ∣ m ↔ ∀ p ∈ D, p ∣ m := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem _ hp).trans h
  · intro h
    induction D using Finset.induction_on with
    | empty => simp
    | insert p D hpD ih =>
      have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
      rw [prod_insert hpD]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (coprime_prod_of_not_mem D hD' p (hD p (mem_insert_self p D)) hpD)
        (h p (mem_insert_self p D)) (ih hD' (fun q hq => h q (mem_insert_of_mem hq)))

/-- divisors of a product of distinct primes are the products over subsets. -/
lemma sum_divisors_prod_primes {M : Type*} [AddCommMonoid M] (D : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (H : ℕ → M) :
    ∑ c ∈ (∏ p ∈ D, p).divisors, H c = ∑ C ∈ D.powerset, H (∏ p ∈ C, p) := by
  have hsq := squarefree_prod_primes D hD
  symm
  apply sum_nbij' (fun C => ∏ p ∈ C, p) (fun c => c.primeFactors)
  · intro C hC
    rw [mem_powerset] at hC
    rw [Nat.mem_divisors]
    exact ⟨prod_dvd_prod_of_subset _ _ _ hC, hsq.ne_zero⟩
  · intro c hc
    rw [Nat.mem_divisors] at hc
    rw [mem_powerset]
    have := Nat.primeFactors_mono hc.1 hc.2
    rwa [Nat.primeFactors_prod hD] at this
  · intro C hC
    rw [mem_powerset] at hC
    exact Nat.primeFactors_prod (fun p hp => hD p (hC hp))
  · intro c hc
    rw [Nat.mem_divisors] at hc
    exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hc.1)
  · intro C _; rfl

/-- weight expansion: `∏_{p ∈ S} (1 - [p ∣ m]/(p-1)) = Σ_{D ⊆ S} (-1)^|D| [∏D ∣ m] / ∏_{D}(p-1)`. -/
lemma weight_expand (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    ∏ p ∈ S, (if p ∣ m then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) =
      ∑ D ∈ S.powerset, (if (∏ p ∈ D, p) ∣ m then
        (-1 : ℝ) ^ D.card / ∏ p ∈ D, ((p : ℝ) - 1) else 0) := by
  have h1 : ∀ p ∈ S, (if p ∣ m then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) =
      1 + (if p ∣ m then -1 / ((p : ℝ) - 1) else 0) := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    split_ifs
    · field_simp; ring
    · ring
  rw [prod_congr rfl h1, prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [mem_powerset] at hD
  have hD' : ∀ p ∈ D, p.Prime := fun p hp => hS p (hD hp)
  by_cases hdvd : ∀ p ∈ D, p ∣ m
  · rw [if_pos ((prod_primes_dvd_iff D hD' m).2 hdvd)]
    rw [prod_congr rfl (fun p hp => if_pos (hdvd p hp)), prod_div_distrib, prod_const]
  · rw [if_neg (fun h => hdvd ((prod_primes_dvd_iff D hD' m).1 h))]
    push Not at hdvd
    obtain ⟨p, hp, hpm⟩ := hdvd
    exact prod_eq_zero hp (if_neg hpm)

/-! ### grouping characters by conductor -/

lemma sum_by_conductor (d : ℕ) [NeZero d] (F : DirichletCharacter ℂ d → ℂ) :
    ∑ χ, F χ = ∑ c ∈ d.divisors, if h : c ∣ d then
      ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.conductor = c),
        F (DirichletCharacter.changeLevel h ψ) else 0 := by
  rw [← sum_fiberwise_of_maps_to (g := fun χ : DirichletCharacter ℂ d => χ.conductor)
    (t := d.divisors)]
  · apply sum_congr rfl
    intro c hc
    have h : c ∣ d := Nat.dvd_of_mem_divisors hc
    rw [dif_pos h]
    have : NeZero c := ⟨fun h0 => by subst h0; exact NeZero.ne d (zero_dvd_iff.1 h)⟩
    symm
    apply sum_bij (fun ψ _ => DirichletCharacter.changeLevel h ψ)
    · intro ψ hψ
      rw [mem_filter] at hψ ⊢
      exact ⟨mem_univ _, (DirichletCharacter.conductor_changeLevel ψ h).trans hψ.2⟩
    · intro ψ₁ _ ψ₂ _ he
      exact DirichletCharacter.changeLevel_injective h he
    · intro χ hχ
      rw [mem_filter] at hχ
      have hmem : c ∈ χ.conductorSet :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ h).2 (dvd_of_eq hχ.2)
      obtain ⟨_, χ₀, hχ₀⟩ := hmem
      refine ⟨χ₀, ?_, hχ₀.symm⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [← DirichletCharacter.conductor_changeLevel χ₀ h, ← hχ₀, hχ.2]
    · intro ψ _; rfl
  · intro χ _
    rw [Nat.mem_divisors]
    exact ⟨DirichletCharacter.conductor_dvd_level χ, NeZero.ne d⟩

lemma changeLevel_apply_coprime {c d : ℕ} (h : c ∣ d) (ψ : DirichletCharacter ℂ c) (a : ℕ)
    (ha : Nat.Coprime a d) : DirichletCharacter.changeLevel h ψ a = ψ a := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ h (a := (a : ℤ))
    (Nat.isCoprime_iff_coprime.2 ha)
  simpa using this

lemma changeLevel_apply_neg_one {c d : ℕ} (h : c ∣ d) (ψ : DirichletCharacter ℂ c) :
    DirichletCharacter.changeLevel h ψ (-1) = ψ (-1) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ h (a := (-1 : ℤ)) isCoprime_one_left.neg_left
  simpa using this


/-! ### Euler-product rearrangement -/

lemma sum_supersets {ι : Type*} [DecidableEq ι] (S C : Finset ι) (hC : C ⊆ S) (b : ι → ℂ) :
    ∑ D ∈ S.powerset.filter (fun D => C ⊆ D), ∏ p ∈ D, b p =
      (∏ p ∈ C, b p) * ∏ p ∈ S \ C, (1 + b p) := by
  rw [prod_one_add, mul_sum]
  symm
  apply sum_nbij' (fun E => C ∪ E) (fun D => D \ C)
  · intro E hE
    rw [mem_powerset] at hE
    rw [mem_filter, mem_powerset]
    refine ⟨union_subset hC (hE.trans sdiff_subset), subset_union_left⟩
  · intro D hD
    rw [mem_filter, mem_powerset] at hD
    rw [mem_powerset]
    exact sdiff_subset_sdiff hD.1 le_rfl
  · intro E hE
    rw [mem_powerset] at hE
    ext x; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd h hx
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hx => (mem_sdiff.1 (hE h)).2 hx⟩
  · intro D hD
    rw [mem_filter] at hD
    exact union_sdiff_of_subset hD.2
  · intro E hE
    rw [mem_powerset] at hE
    rw [prod_union]
    exact disjoint_left.2 fun x hx hxE => (mem_sdiff.1 (hE hxE)).2 hx

lemma sum_powerset_rearrange {ι : Type*} [DecidableEq ι] (S : Finset ι) (b : ι → ℂ)
    (G : Finset ι → ℂ) :
    ∑ D ∈ S.powerset, (∏ p ∈ D, b p) * ∑ C ∈ D.powerset, G C =
      ∑ C ∈ S.powerset, G C * ((∏ p ∈ C, b p) * ∏ p ∈ S \ C, (1 + b p)) := by
  simp_rw [mul_sum]
  rw [sum_comm' (t' := S.powerset) (s' := fun C => S.powerset.filter (fun D => C ⊆ D))]
  · apply sum_congr rfl
    intro C hC
    rw [← sum_supersets S C (mem_powerset.1 hC) b, mul_sum]
    apply sum_congr rfl; intro D _; ring
  · intro D C
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h2.trans h1⟩
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩

/-! ### the expansion -/

/-- primitive-character sum `G(C)` at modulus `∏ C`. -/
noncomputable def primSum (T : Finset ℕ) (C : Finset ℕ) : ℂ :=
  ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ (∏ p ∈ C, p) => ψ.conductor = ∏ p ∈ C, p),
    ψ (-1) * ((‖∑ t ∈ T, ψ t‖ ^ 2 : ℝ) : ℂ)

theorem pair_weight_char_expansion (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (T : Finset ℕ) (hT : ∀ t ∈ T, ∀ p ∈ S, ¬ p ∣ t) :
    (((∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
        (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1)) : ℝ) : ℂ) =
      ((∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) : ℝ) : ℂ) *
        ∑ C ∈ S.powerset, (∏ p ∈ C, (-1 / ((p : ℂ) * ((p : ℂ) - 2)))) * primSum T C := by
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hp3 : ∀ p ∈ S, (3 : ℝ) ≤ p := by
    intro p hp
    have := (hS p hp).1.two_le; have := (hS p hp).2
    exact_mod_cast (show 3 ≤ p by omega)
  -- coprimality with every `∏ D`
  have hcop : ∀ D ∈ S.powerset, ∀ t ∈ T, Nat.Coprime t (∏ p ∈ D, p) := by
    intro D hD t ht
    rw [mem_powerset] at hD
    apply Nat.Coprime.prod_right
    intro p hp
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hSp p (hD hp))).2 (hT t ht p (hD hp)))
  -- step 1: expand the weight and count pairs
  have step1 : ((∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
        (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) : ℝ) : ℂ) =
      ∑ D ∈ S.powerset, (∏ p ∈ D, (-1 / ((p : ℂ) - 1) ^ 2)) *
        ∑ χ : DirichletCharacter ℂ (∏ p ∈ D, p), χ (-1) * ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [weight_expand S hSp]
    rw [sum_comm]
    simp_rw [sum_comm (s := T) (t := S.powerset)]
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro D hD
    have hD' : ∀ p ∈ D, p.Prime := fun p hp => hSp p (mem_powerset.1 hD hp)
    have : NeZero (∏ p ∈ D, p) := ⟨prod_ne_zero_iff.2 fun p hp => (hD' p hp).ne_zero⟩
    have hpc := pair_count_char _ T (hcop D hD)
    have hφ : (((∏ p ∈ D, p).totient : ℕ) : ℂ) = ∏ p ∈ D, ((p : ℂ) - 1) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (totient_prod_primes D hD')
      push_cast at this; exact this
    have hne : ∀ p ∈ D, (p : ℂ) - 1 ≠ 0 := by
      intro p hp h
      have : (p : ℂ) = 1 := by linear_combination h
      exact (hD' p hp).one_lt.ne' (by exact_mod_cast this)
    set c : ℝ := (-1 : ℝ) ^ D.card / ∏ p ∈ D, ((p : ℝ) - 1) with hc
    have hcount : ((∑ x ∈ T, ∑ i ∈ T, (if (∏ p ∈ D, p) ∣ i + x then c else 0) : ℝ) : ℂ) =
        (c : ℂ) * ((((T ×ˢ T).filter (fun x => (∏ p ∈ D, p) ∣ x.1 + x.2)).card : ℕ) : ℂ) := by
      rw [card_filter, sum_product, sum_comm]
      push_cast
      rw [mul_sum]
      apply sum_congr rfl; intro x _
      rw [mul_sum]
      apply sum_congr rfl; intro i _
      split_ifs <;> simp
    rw [hcount, ← hpc, hφ, ← mul_assoc]
    congr 1
    rw [hc, ← prod_mul_distrib]
    push_cast
    have e2 : ∀ p ∈ D, (-1 / ((p : ℂ) - 1) ^ 2 * ((p : ℂ) - 1)) = -1 / ((p : ℂ) - 1) := by
      intro p hp
      have := hne p hp
      field_simp
    rw [prod_congr rfl e2, prod_div_distrib, prod_const]
  -- step 2: group characters by conductor
  have step2 : ∀ D ∈ S.powerset,
      ∑ χ : DirichletCharacter ℂ (∏ p ∈ D, p), χ (-1) * ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) =
        ∑ C ∈ D.powerset, primSum T C := by
    intro D hD
    have hD' : ∀ p ∈ D, p.Prime := fun p hp => hSp p (mem_powerset.1 hD hp)
    have : NeZero (∏ p ∈ D, p) := ⟨prod_ne_zero_iff.2 fun p hp => (hD' p hp).ne_zero⟩
    rw [sum_by_conductor, sum_divisors_prod_primes D hD']
    apply sum_congr rfl
    intro C hC
    have hCD : (∏ p ∈ C, p) ∣ ∏ p ∈ D, p := prod_dvd_prod_of_subset _ _ _ (mem_powerset.1 hC)
    rw [dif_pos hCD, primSum]
    apply sum_congr rfl
    intro ψ _
    rw [changeLevel_apply_neg_one]
    congr 3
    congr 1
    apply sum_congr rfl
    intro t ht
    exact changeLevel_apply_coprime hCD ψ t (hcop D hD t ht)
  rw [step1, sum_congr rfl (fun D hD => by rw [step2 D hD])]
  rw [sum_powerset_rearrange S (fun p => -1 / ((p : ℂ) - 1) ^ 2) (primSum T), mul_sum]
  apply sum_congr rfl
  intro C hC
  have hCS := mem_powerset.1 hC
  have hne1 : ∀ p ∈ S, (1 + -1 / ((p : ℂ) - 1) ^ 2) ≠ 0 := by
    intro p hp
    have h3 := hp3 p hp
    have : (1 + -1 / ((p : ℝ) - 1) ^ 2) ≠ 0 := by
      have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
        rw [div_lt_one (by nlinarith)]; nlinarith
      have e : -1 / ((p : ℝ) - 1) ^ 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by ring
      rw [e]; linarith
    exact_mod_cast this
  have hsplit : ∏ p ∈ S, (1 + -1 / ((p : ℂ) - 1) ^ 2) =
      (∏ p ∈ S \ C, (1 + -1 / ((p : ℂ) - 1) ^ 2)) * ∏ p ∈ C, (1 + -1 / ((p : ℂ) - 1) ^ 2) :=
    (prod_sdiff hCS).symm
  have hP : ((∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) : ℝ) : ℂ) =
      ∏ p ∈ S, (1 + -1 / ((p : ℂ) - 1) ^ 2) := by
    push_cast; apply prod_congr rfl; intro p _; ring
  rw [hP, hsplit]
  have hloc : ∀ p ∈ C, -1 / ((p : ℂ) - 1) ^ 2 =
      (1 + -1 / ((p : ℂ) - 1) ^ 2) * (-1 / ((p : ℂ) * ((p : ℂ) - 2))) := by
    intro p hp
    have h3 := hp3 p (hCS hp)
    have h1 : (p : ℂ) - 1 ≠ 0 := by
      intro h; have : (p : ℂ) = 1 := by linear_combination h
      have : (p : ℝ) = 1 := by exact_mod_cast this
      linarith
    have h2 : (p : ℂ) - 2 ≠ 0 := by
      intro h; have : (p : ℂ) = 2 := by linear_combination h
      have : (p : ℝ) = 2 := by exact_mod_cast this
      linarith
    have h0 : (p : ℂ) ≠ 0 := by
      intro h; have : (p : ℝ) = 0 := by exact_mod_cast h
      linarith
    field_simp
    ring
  rw [prod_congr rfl hloc, prod_mul_distrib]
  ring

end RV27C

section LowerPart

open Finset Real

namespace RV27C

/-! ### diagonal orthogonality and the trivial bound for one modulus -/

lemma diag_count_char (d : ℕ) [NeZero d] (T : Finset ℕ) (hT : ∀ t ∈ T, Nat.Coprime t d) :
    ((d.totient : ℂ) * (((T ×ˢ T).filter (fun x => ((x.1 : ℕ) : ZMod d) = x.2)).card : ℂ)) =
      ∑ χ : DirichletCharacter ℂ d, ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) := by
  have hunit : ∀ t ∈ T, IsUnit ((t : ℕ) : ZMod d) := fun t ht =>
    (ZMod.isUnit_iff_coprime t d).2 (hT t ht)
  have key : ∀ t ∈ T, ∀ t' ∈ T, ∑ χ : DirichletCharacter ℂ d, χ t * star (χ t') =
      if ((t : ℕ) : ZMod d) = t' then (d.totient : ℂ) else 0 := by
    intro t _ t' ht'
    obtain ⟨u, hu⟩ := hunit t' ht'
    have h1 : ∀ χ : DirichletCharacter ℂ d, χ t * star (χ t') =
        χ ((t : ZMod d) * (u⁻¹ : (ZMod d)ˣ)) := by
      intro χ
      rw [MulChar.star_apply', MulChar.inv_apply, ← hu, Ring.inverse_unit, map_mul]
    simp_rw [h1]
    rw [DirichletCharacter.sum_characters_eq]
    congr 1
    apply propext
    constructor
    · intro h
      have := congrArg (· * (u : ZMod d)) h
      simp only [mul_assoc, Units.inv_mul, mul_one, one_mul] at this
      rw [this, hu]
    · intro h
      rw [h, ← hu, Units.mul_inv]
  calc ((d.totient : ℂ) * (((T ×ˢ T).filter (fun x => ((x.1 : ℕ) : ZMod d) = x.2)).card : ℂ))
      = ∑ t ∈ T, ∑ t' ∈ T, if ((t : ℕ) : ZMod d) = t' then (d.totient : ℂ) else 0 := by
        rw [card_filter, ← sum_product']
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro x _
        split_ifs <;> simp
    _ = ∑ t ∈ T, ∑ t' ∈ T, ∑ χ : DirichletCharacter ℂ d, χ t * star (χ t') := by
        apply sum_congr rfl; intro t ht; apply sum_congr rfl; intro t' ht'
        rw [key t ht t' ht']
    _ = _ := by
        have : ∀ χ : DirichletCharacter ℂ d, ((‖∑ t ∈ T, χ t‖ ^ 2 : ℝ) : ℂ) =
            ∑ t ∈ T, ∑ t' ∈ T, χ t * star (χ t') := by
          intro χ
          rw [normSq_eq_mul_star, star_sum, sum_mul_sum]
        simp_rw [this]
        symm
        rw [sum_comm]
        apply sum_congr rfl; intro t _
        rw [sum_comm]

lemma card_residue_le (M N q r : ℕ) (hq : 0 < q) :
    (((Finset.Ico M (M + N)).filter (fun x => x % q = r)).card : ℝ) ≤ N / q + 2 := by
  set A := (Finset.Ico M (M + N)).filter (fun x => x % q = r)
  have hinj : Set.InjOn (fun x => x / q) (A : Set ℕ) := by
    intro x hx y hy hxy
    simp only [A, coe_filter, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    rw [← Nat.div_add_mod x q, ← Nat.div_add_mod y q, hxy, hx.2, hy.2]
  have hsub : A.image (fun x => x / q) ⊆ Finset.Icc (M / q) ((M + N) / q) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hk
    simp only [A, mem_filter, mem_Ico] at hx
    rw [mem_Icc]
    exact ⟨Nat.div_le_div_right hx.1.1, Nat.div_le_div_right hx.1.2.le⟩
  have h1 : A.card ≤ (M + N) / q + 1 - M / q := by
    rw [← card_image_of_injOn hinj]
    exact (card_le_card hsub).trans (by rw [Nat.card_Icc])
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : (((M + N) / q : ℕ) : ℝ) ≤ ((M : ℝ) + N) / q := by
    rw [le_div_iff₀ hqR]; exact_mod_cast Nat.div_mul_le_self (M + N) q
  have h3 : (M : ℝ) / q - 1 ≤ ((M / q : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := M) hq
    rw [div_sub_one hqR.ne', div_le_iff₀ hqR]
    have : (M : ℝ) < (M / q : ℕ) * q + q := by exact_mod_cast this
    linarith
  have h4 : (A.card : ℝ) ≤ ((M + N) / q : ℕ) + 1 - ((M / q : ℕ) : ℝ) := by
    have : M / q ≤ (M + N) / q + 1 := (Nat.div_le_div_right (Nat.le_add_right M N)).trans (Nat.le_succ _)
    have h := h1
    rw [← Nat.cast_le (α := ℝ)] at h
    push_cast [Nat.cast_sub this] at h
    linarith
  have : ((M : ℝ) + N) / q - M / q = N / q := by ring
  linarith

lemma diag_bound (q : ℕ) [NeZero q] (M N : ℕ) (T : Finset ℕ) (hTI : T ⊆ Finset.Ico M (M + N))
    (hT : ∀ t ∈ T, Nat.Coprime t q) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ t ∈ T, χ t‖ ^ 2 ≤ q.totient * (T.card * (N / q + 2)) := by
  have h := diag_count_char q T hT
  have hR : ((q.totient : ℝ) * (((T ×ˢ T).filter (fun x => ((x.1 : ℕ) : ZMod q) = x.2)).card : ℝ)) =
      ∑ χ : DirichletCharacter ℂ q, ‖∑ t ∈ T, χ t‖ ^ 2 := by
    exact_mod_cast h
  rw [← hR]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [card_filter, sum_product]
  push_cast
  calc ∑ x ∈ T, ∑ y ∈ T, (if ((x : ℕ) : ZMod q) = y then (1 : ℝ) else 0)
      ≤ ∑ x ∈ T, ((N : ℝ) / q + 2) := by
        apply sum_le_sum; intro x _
        rw [sum_boole]
        have hsub : T.filter (fun y : ℕ => ((x : ℕ) : ZMod q) = (y : ZMod q)) ⊆
            (Finset.Ico M (M + N)).filter (fun y : ℕ => y % q = x % q) := by
          intro y hy
          rw [mem_filter] at hy ⊢
          refine ⟨hTI hy.1, ?_⟩
          exact ((ZMod.natCast_eq_natCast_iff' x y q).1 hy.2).symm
        exact (Nat.cast_le.2 (card_le_card hsub)).trans (card_residue_le M N q _ hq)
    _ = _ := by rw [sum_const, nsmul_eq_mul]


/-! ### special moduli -/

/-- `G'(C)`: the primitive-character energy at modulus `∏ C`. -/
noncomputable def primEnergy (T : Finset ℕ) (C : Finset ℕ) : ℝ :=
  ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ (∏ p ∈ C, p) => ψ.conductor = ∏ p ∈ C, p),
    ‖∑ t ∈ T, ψ t‖ ^ 2

lemma primEnergy_nonneg (T C : Finset ℕ) : 0 ≤ primEnergy T C :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma re_primSum_ge (T C : Finset ℕ) : -primEnergy T C ≤ (primSum T C).re := by
  rw [primSum, Complex.re_sum, primEnergy, ← sum_neg_distrib]
  apply sum_le_sum
  intro ψ _
  rw [Complex.re_mul_ofReal]
  have h1 : |(ψ (-1)).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one ψ _)
  have h2 : 0 ≤ ‖∑ t ∈ T, ψ t‖ ^ 2 := sq_nonneg _
  have := neg_abs_le (ψ (-1)).re
  nlinarith

lemma re_primSum_le (T C : Finset ℕ) : (primSum T C).re ≤ primEnergy T C := by
  rw [primSum, Complex.re_sum, primEnergy]
  apply sum_le_sum
  intro ψ _
  rw [Complex.re_mul_ofReal]
  have h1 : |(ψ (-1)).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one ψ _)
  have h2 : 0 ≤ ‖∑ t ∈ T, ψ t‖ ^ 2 := sq_nonneg _
  have := le_abs_self (ψ (-1)).re
  nlinarith

lemma level_one_sum (n : ℕ) (hn : n = 1) (T : Finset ℕ) :
    (∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ n => ψ.conductor = n),
      ψ (-1) * ((‖∑ t ∈ T, ψ t‖ ^ 2 : ℝ) : ℂ)) = ((T.card : ℝ) ^ 2 : ℝ) := by
  subst hn
  have hall : ∀ ψ : DirichletCharacter ℂ 1, ∀ a : ZMod 1, ψ a = 1 := by
    intro ψ a
    rw [Subsingleton.elim a 1, map_one]
  have hfil : univ.filter (fun ψ : DirichletCharacter ℂ 1 => ψ.conductor = 1) = {1} := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _
      ext a
      rw [hall, hall]
    · rintro rfl
      exact DirichletCharacter.conductor_one (n := 1)
  rw [hfil, sum_singleton]
  simp only [hall, sum_const, nsmul_eq_mul, mul_one, one_mul]
  push_cast
  rw [Complex.norm_natCast]
  norm_cast

lemma primSum_empty (T : Finset ℕ) : primSum T ∅ = ((T.card : ℝ) ^ 2 : ℝ) :=
  level_one_sum _ prod_empty T

lemma level_three_odd (n : ℕ) (hn : n = 3) (ψ : DirichletCharacter ℂ n) (hψ : ψ.conductor = n) :
    ψ (-1) = -1 := by
  subst hn
  have hne : ψ ≠ 1 := by
    intro h
    rw [h, DirichletCharacter.conductor_one] at hψ
    norm_num at hψ
  have hsq : ψ (-1) * ψ (-1) = 1 := by
    rw [← map_mul]; norm_num
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · exfalso
    apply hne
    apply MulChar.ext
    intro a
    rw [MulChar.one_apply_coe]
    have : (a : ZMod 3) = 1 ∨ (a : ZMod 3) = -1 := by
      revert a; decide
    rcases this with ha | ha
    · rw [ha, map_one]
    · rw [ha, h]
  · exact h

lemma primSum_three (T : Finset ℕ) : (primSum T {3}).re = -primEnergy T {3} := by
  rw [primSum, primEnergy, Complex.re_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro ψ hψ
  rw [mem_filter] at hψ
  have h3 := level_three_odd _ (by simp) ψ hψ.2
  rw [h3, neg_one_mul, Complex.neg_re, Complex.ofReal_re]


/-! ### the Montgomery–Vaughan large sieve over a family of moduli `∏ C` -/

theorem mv_energy (Q : ℕ+) (M N : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N) (T : Finset ℕ)
    (hTI : T ⊆ Finset.Ico M (M + N)) (hTp : ∀ t ∈ T, t.Prime ∧ (Q : ℕ) < t)
    (𝒦 : Finset (Finset ℕ)) (h𝒦 : ∀ C ∈ 𝒦, (∀ p ∈ C, p.Prime) ∧ ∏ p ∈ C, p ≤ (Q : ℕ)) :
    ∑ C ∈ 𝒦, (Real.log (((Q : ℕ) : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ)) - Real.log 4) * primEnergy T C ≤
      (N : ℝ) * T.card := by
  classical
  have hpos : ∀ C ∈ 𝒦, 0 < ∏ p ∈ C, p := fun C hC =>
    prod_pos fun p hp => ((h𝒦 C hC).1 p hp).pos
  let rC : Finset ℕ → ℕ+ := fun C => Nat.toPNat' (∏ p ∈ C, p)
  have hrC : ∀ C ∈ 𝒦, ((rC C : ℕ+) : ℕ) = ∏ p ∈ C, p := by
    intro C hC; simp only [rC, Nat.toPNat'_coe, if_pos (hpos C hC)]
  have hinj : Set.InjOn rC (𝒦 : Set (Finset ℕ)) := by
    intro C hC D hD h
    have h1 : ((rC C : ℕ+) : ℕ) = ((rC D : ℕ+) : ℕ) := congrArg (fun r : ℕ+ => (r : ℕ)) h
    rw [hrC C hC, hrC D hD] at h1
    have := congrArg Nat.primeFactors h1
    rwa [Nat.primeFactors_prod (h𝒦 C hC).1, Nat.primeFactors_prod (h𝒦 D hD).1] at this
  -- the weight
  let W : ℕ → ℝ := fun r => ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => r * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
        (r : ℝ) / ((r.totient : ℝ) * (m.totient : ℝ) *
          ((N : ℝ) + 16 * ((r * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ)))
  let X : ℕ → ℝ := fun r =>
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = r),
      ‖∑ t ∈ T, χ t‖ ^ 2
  have hW0 : ∀ r, 0 ≤ W r := fun r => sum_nonneg fun m _ => by positivity
  have hX0 : ∀ r, 0 ≤ X r := fun r => sum_nonneg fun _ _ => sq_nonneg _
  -- the large sieve with `a = 1_T`
  have hMV := MVSieve.primitive_character_large_sieve Q M N (fun n => if n ∈ T then 1 else 0)
    (by
      intro n hn ha p hp hpn
      have hnT : n ∈ T := by by_contra h; exact ha (by simp [h])
      have := hTp n hnT
      rw [(Nat.prime_dvd_prime_iff_eq hp this.1).1 hpn]; exact this.2)
  have hind : ∀ (r : ℕ) (χ : DirichletCharacter ℂ r),
      ∑ n ∈ Finset.Ico M (M + N), (if n ∈ T then (1 : ℂ) else 0) * χ n = ∑ t ∈ T, χ t := by
    intro r χ
    rw [← sum_subset hTI (fun n _ hn => by simp [hn])]
    apply sum_congr rfl; intro n hn; simp [hn]
  simp_rw [hind] at hMV
  have hmass : ∑ n ∈ Finset.Ico M (M + N), ‖(if n ∈ T then (1 : ℂ) else 0)‖ ^ 2 = T.card := by
    rw [← sum_subset hTI (fun n _ hn => by simp [hn])]
    rw [sum_congr rfl (fun n hn => by simp [hn] : ∀ n ∈ T, ‖(if n ∈ T then (1 : ℂ) else 0)‖ ^ 2 = 1)]
    simp
  rw [hmass] at hMV
  simp_rw [← sum_mul] at hMV
  change ∑ r ∈ Finset.Icc 1 Q, W r * X r ≤ T.card at hMV
  -- restrict to the image of `𝒦`
  have hsub : ∑ C ∈ 𝒦, W (rC C) * X (rC C) ≤ ∑ r ∈ Finset.Icc 1 Q, W r * X r := by
    rw [← sum_image (f := fun r : ℕ+ => W r * X r) hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨C, hC, rfl⟩ := mem_image.1 hr
      rw [mem_Icc]
      refine ⟨PNat.one_le _, ?_⟩
      rw [← PNat.coe_le_coe, hrC C hC]; exact (h𝒦 C hC).2
    · intro r _ _; exact mul_nonneg (hW0 r) (hX0 r)
  have hXC : ∀ C ∈ 𝒦, X (rC C) = primEnergy T C := by
    intro C hC
    rw [hrC C hC]
    rfl
  calc ∑ C ∈ 𝒦, (Real.log (((Q : ℕ) : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ)) - Real.log 4) * primEnergy T C
      ≤ ∑ C ∈ 𝒦, (N : ℝ) * (W (rC C) * X (rC C)) := by
        apply sum_le_sum
        intro C hC
        rw [hXC C hC, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (primEnergy_nonneg T C)
        have hle : rC C ≤ Q := by rw [← PNat.coe_le_coe, hrC C hC]; exact (h𝒦 C hC).2
        have := MVSieve.large_sieve_weight_lower Q N hN (rC C) hle
        change _ ≤ (N : ℝ) * W (rC C) at this
        rw [hrC C hC] at this ⊢
        exact this
    _ = (N : ℝ) * ∑ C ∈ 𝒦, W (rC C) * X (rC C) := by rw [mul_sum]
    _ ≤ (N : ℝ) * T.card := mul_le_mul_of_nonneg_left (hsub.trans hMV) (Nat.cast_nonneg _)


lemma level_one_energy (n : ℕ) (hn : n = 1) (T : Finset ℕ) :
    (∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ n => ψ.conductor = n),
      ‖∑ t ∈ T, ψ t‖ ^ 2) = (T.card : ℝ) ^ 2 := by
  subst hn
  have hall : ∀ ψ : DirichletCharacter ℂ 1, ∀ a : ZMod 1, ψ a = 1 := by
    intro ψ a
    rw [Subsingleton.elim a 1, map_one]
  have hfil : univ.filter (fun ψ : DirichletCharacter ℂ 1 => ψ.conductor = 1) = {1} := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _
      ext a
      rw [hall, hall]
    · rintro rfl
      exact DirichletCharacter.conductor_one (n := 1)
  rw [hfil, sum_singleton]
  simp only [hall, sum_const, nsmul_eq_mul, mul_one]
  rw [Complex.norm_natCast]

lemma primEnergy_empty (T : Finset ℕ) : primEnergy T ∅ = (T.card : ℝ) ^ 2 :=
  level_one_energy _ prod_empty T

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `f(q) ≤ L(q) / (15 L(5))` for the moduli `5 ≤ q ≤ w`. -/
lemma f_le_weight (C : Finset ℕ) (hC : ∀ p ∈ C, p.Prime ∧ p ≠ 2) (hne : C ≠ ∅) (h3 : C ≠ {3})
    (Q w : ℕ) (hwq : ∏ p ∈ C, p ≤ w) (hwQ : 12 * w ≤ Q) (hQ : 20 < Q) :
    ∏ p ∈ C, (1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
      (Real.log ((Q : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ)) - Real.log 4) /
        (15 * (Real.log Q - Real.log 20)) := by
  have hp3 : ∀ p ∈ C, (3 : ℝ) ≤ p := by
    intro p hp
    have := (hC p hp).1.two_le; have := (hC p hp).2
    exact_mod_cast (show 3 ≤ p by omega)
  -- a prime `≥ 5` in `C`
  obtain ⟨p0, hp0, hp05⟩ : ∃ p0 ∈ C, 5 ≤ p0 := by
    by_contra hcon
    push Not at hcon
    apply h3
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hne
    ext x
    simp only [mem_singleton]
    constructor
    · intro hx
      have := (hC x hx).1.two_le; have := (hC x hx).2; have := hcon x hx
      have : x ≠ 4 := fun h => by subst h; exact absurd (hC 4 hx).1 (by norm_num)
      omega
    · rintro rfl
      have := (hC a ha).1.two_le; have := (hC a ha).2; have := hcon a ha
      have : a ≠ 4 := fun h => by subst h; exact absurd (hC 4 ha).1 (by norm_num)
      have : a = 3 := by omega
      exact this ▸ ha
  set q := ∏ p ∈ C, p with hq
  have hqpos : 0 < q := prod_pos fun p hp => (hC p hp).1.pos
  have hp0q : p0 ≤ q := Nat.le_of_dvd hqpos (dvd_prod_of_mem _ hp0)
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hp05.trans hp0q
  have hqR : ((q : ℕ) : ℝ) = ∏ p ∈ C, (p : ℝ) := by rw [hq]; push_cast; rfl
  -- `f(q) * q = ∏ 1/(p-2) ≤ 1/3`
  have hfq : ∏ p ∈ C, (1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤ 1 / (3 * q) := by
    have hsplit : ∏ p ∈ C, (1 / ((p : ℝ) * ((p : ℝ) - 2))) =
        (∏ p ∈ C, (1 / ((p : ℝ) - 2))) / q := by
      rw [hqR, ← prod_div_distrib]
      apply prod_congr rfl; intro p hp
      have := hp3 p hp
      field_simp
    rw [hsplit]
    have hprod : ∏ p ∈ C, (1 / ((p : ℝ) - 2)) ≤ 1 / 3 := by
      rw [← mul_prod_erase C _ hp0]
      have h1 : 1 / ((p0 : ℝ) - 2) ≤ 1 / 3 := by
        have : (5 : ℝ) ≤ p0 := by exact_mod_cast hp05
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h2 : ∏ p ∈ C.erase p0, (1 / ((p : ℝ) - 2)) ≤ 1 := by
        apply prod_le_one
        · intro p hp; have := hp3 p (mem_of_mem_erase hp)
          apply div_nonneg (by norm_num); linarith
        · intro p hp; have := hp3 p (mem_of_mem_erase hp)
          rw [div_le_one (by linarith)]; linarith
      have h0 : 0 ≤ ∏ p ∈ C.erase p0, (1 / ((p : ℝ) - 2)) := by
        apply prod_nonneg; intro p hp; have := hp3 p (mem_of_mem_erase hp)
        apply div_nonneg (by norm_num); linarith
      have h1' : 0 ≤ 1 / ((p0 : ℝ) - 2) := by
        have : (5 : ℝ) ≤ p0 := by exact_mod_cast hp05
        apply div_nonneg (by norm_num); linarith
      nlinarith
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  -- `5 L(5) ≤ q L(q)`
  have hQR : (20 : ℝ) < Q := by exact_mod_cast hQ
  have hwR : (12 : ℝ) * q ≤ Q := by
    have : 12 * q ≤ Q := (Nat.mul_le_mul_left 12 hwq).trans hwQ
    exact_mod_cast this
  have hL5 : 0 < Real.log Q - Real.log 20 := by
    rw [sub_pos]; exact Real.log_lt_log (by norm_num) hQR
  have hlogQ : Real.log 12 + Real.log q ≤ Real.log Q := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) hwR
  have h12 : Real.log 12 = Real.log 3 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h20 : Real.log 20 = Real.log 5 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hA : 1 ≤ Real.log Q - Real.log q - Real.log 4 := by
    have := one_lt_log_three; linarith
  have hlq : Real.log (q / 5) ≤ q / 5 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hlq
  have hkey : 5 * (Real.log Q - Real.log 20) ≤ q * (Real.log Q - Real.log q - Real.log 4) := by
    nlinarith
  rw [Real.log_div (by positivity) (by positivity)]
  refine hfq.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith


/-- Riesel–Vaughan §8 (Lemma 13 with Lemmas 10–12 folded in) for one interval, with the truncated
weight `∏_{p ∈ S, p ∣ n} (p-2)/(p-1)`. -/
theorem interval_pair_weight_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (Q : ℕ+) (M N w : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N) (hw : 1 ≤ w) (hwQ : 12 * w ≤ (Q : ℕ))
    (hQ20 : 20 < (Q : ℕ)) (T : Finset ℕ) (hTI : T ⊆ Finset.Ico M (M + N))
    (hTp : ∀ t ∈ T, t.Prime ∧ (Q : ℕ) < t) (hTS : ∀ t ∈ T, ∀ p ∈ S, ¬ p ∣ t) :
    (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
      ((16 / 15) * (T.card : ℝ) ^ 2 - (N : ℝ) * T.card / (15 * (Real.log Q - Real.log 20)) -
        ((N : ℝ) / w + 2) * (∏ p ∈ S, (1 + ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)))) * T.card) ≤
    ∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
      (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) := by
  classical
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hp3 : ∀ p ∈ S, (3 : ℝ) ≤ p := by
    intro p hp
    have := (hS p hp).1.two_le; have := (hS p hp).2
    exact_mod_cast (show 3 ≤ p by omega)
  set PP := ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) with hPP
  have hPPpos : 0 < PP := by
    apply prod_pos; intro p hp
    have := hp3 p hp
    have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by rw [div_lt_one (by nlinarith)]; nlinarith
    linarith
  set c : Finset ℕ → ℝ := fun C => ∏ p ∈ C, (-1 / ((p : ℝ) * ((p : ℝ) - 2))) with hc
  set f : Finset ℕ → ℝ := fun C => ∏ p ∈ C, (1 / ((p : ℝ) * ((p : ℝ) - 2))) with hf
  -- real form of the expansion
  have hexp := pair_weight_char_expansion S hS T hTS
  have hreal : (∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
      (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1)) =
      PP * ∑ C ∈ S.powerset, c C * (primSum T C).re := by
    have := congrArg Complex.re hexp
    rw [Complex.ofReal_re] at this
    rw [this, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    apply sum_congr rfl; intro C _
    have : (∏ p ∈ C, (-1 / ((p : ℂ) * ((p : ℂ) - 2)))) = ((c C : ℝ) : ℂ) := by
      simp only [hc]; push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hreal]
  apply mul_le_mul_of_nonneg_left _ hPPpos.le
  -- termwise lower bounds
  have hcabs : ∀ C ∈ S.powerset, |c C| = f C := by
    intro C hC
    simp only [hc, hf, abs_prod]
    apply prod_congr rfl; intro p hp
    have := hp3 p (mem_powerset.1 hC hp)
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by nlinarith)]
  have hf0 : ∀ C ∈ S.powerset, 0 ≤ f C := fun C hC => (hcabs C hC) ▸ abs_nonneg _
  set g : Finset ℕ → ℝ := fun C =>
    if C = ∅ then (T.card : ℝ) ^ 2 else if C = {3} then 0 else -(f C * primEnergy T C) with hg
  have hterm : ∀ C ∈ S.powerset, g C ≤ c C * (primSum T C).re := by
    intro C hC
    by_cases h0 : C = ∅
    · subst h0
      simp only [hg, if_pos rfl, hc, prod_empty, one_mul, primSum_empty, Complex.ofReal_re]
      exact le_rfl
    by_cases h3 : C = {3}
    · subst h3
      simp only [hg, if_neg h0, if_pos rfl, hc, prod_singleton, primSum_three]
      have := primEnergy_nonneg T {3}
      norm_num
      nlinarith
    · simp only [hg, if_neg h0, if_neg h3]
      have h1 := re_primSum_ge T C
      have h2 := re_primSum_le T C
      have habs : |(primSum T C).re| ≤ primEnergy T C := abs_le.2 ⟨h1, h2⟩
      have := hcabs C hC
      have hmul : |c C * (primSum T C).re| ≤ f C * primEnergy T C := by
        rw [abs_mul, this]
        exact mul_le_mul_of_nonneg_left habs (hf0 C hC)
      linarith [neg_abs_le (c C * (primSum T C).re)]
  refine le_trans ?_ (sum_le_sum hterm)
  -- notation
  set B := ∏ p ∈ S, (1 + ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2))) with hB
  set L : Finset ℕ → ℝ := fun C =>
    Real.log (((Q : ℕ) : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ)) - Real.log 4 with hL
  set L5 := Real.log Q - Real.log 20 with hL5
  have hQR : (20 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast hQ20
  have hL5pos : 0 < L5 := by
    rw [hL5, sub_pos]; exact Real.log_lt_log (by norm_num) hQR
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  set R := (S.powerset.filter (fun C => C ≠ ∅ ∧ C ≠ {3})) with hR
  set R₁ := R.filter (fun C => ∏ p ∈ C, p ≤ w) with hR₁
  set R₂ := R.filter (fun C => ¬ ∏ p ∈ C, p ≤ w) with hR₂
  have hsumg : ∑ C ∈ S.powerset, g C =
      (T.card : ℝ) ^ 2 - (∑ C ∈ R₁, f C * primEnergy T C + ∑ C ∈ R₂, f C * primEnergy T C) := by
    have hpt : ∀ C ∈ S.powerset, g C = (if C = ∅ then (T.card : ℝ) ^ 2 else 0) +
        (if C ≠ ∅ ∧ C ≠ {3} then -(f C * primEnergy T C) else 0) := by
      intro C _
      simp only [hg]
      by_cases h0 : C = ∅
      · simp [h0]
      · by_cases h3 : C = {3}
        · simp [h3]
        · simp [h0, h3]
    rw [sum_congr rfl hpt, sum_add_distrib, sum_ite_eq' S.powerset ∅,
      if_pos (empty_mem_powerset S), ← sum_filter, sum_neg_distrib,
      sum_filter_add_sum_filter_not R (fun C => ∏ p ∈ C, p ≤ w)]
    ring
  rw [hsumg]
  -- (a) large moduli
  have hcop : ∀ C ∈ S.powerset, ∀ t ∈ T, Nat.Coprime t (∏ p ∈ C, p) := by
    intro C hC t ht
    apply Nat.Coprime.prod_right
    intro p hp
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hSp p (mem_powerset.1 hC hp))).2
      (hTS t ht p (mem_powerset.1 hC hp)))
  have hh0 : ∀ C ∈ S.powerset, 0 ≤ ∏ p ∈ C, (((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2))) := by
    intro C hC
    apply prod_nonneg; intro p hp
    have := hp3 p (mem_powerset.1 hC hp)
    apply div_nonneg (by linarith); nlinarith
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hlarge : ∑ C ∈ R₂, f C * primEnergy T C ≤ ((N : ℝ) / w + 2) * B * T.card := by
    have hb : ∀ C ∈ R₂, f C * primEnergy T C ≤
        (∏ p ∈ C, (((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)))) * (T.card * ((N : ℝ) / w + 2)) := by
      intro C hC
      simp only [hR₂, hR, mem_filter] at hC
      obtain ⟨⟨hCS, -⟩, hCw⟩ := hC
      have hCp : ∀ p ∈ C, p.Prime := fun p hp => hSp p (mem_powerset.1 hCS hp)
      have : NeZero (∏ p ∈ C, p) := ⟨prod_ne_zero_iff.2 fun p hp => (hCp p hp).ne_zero⟩
      have hE : primEnergy T C ≤ ∑ χ : DirichletCharacter ℂ (∏ p ∈ C, p), ‖∑ t ∈ T, χ t‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      have hD := diag_bound (∏ p ∈ C, p) M N T hTI (hcop C hCS)
      rw [totient_prod_primes C hCp] at hD
      have hqw : (w : ℝ) < ((∏ p ∈ C, p : ℕ) : ℝ) := by exact_mod_cast (not_le.1 hCw)
      have hNq : (N : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ) ≤ N / w :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) hqw.le
      have hfC : 0 ≤ f C := hf0 C hCS
      have hfφ : f C * ∏ p ∈ C, ((p : ℝ) - 1) =
          ∏ p ∈ C, (((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2))) := by
        simp only [hf]
        rw [← prod_mul_distrib]
        apply prod_congr rfl; intro p _; ring
      calc f C * primEnergy T C
          ≤ f C * ((∏ p ∈ C, ((p : ℝ) - 1)) * (T.card * ((N : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_left (hE.trans hD) hfC
        _ = (f C * ∏ p ∈ C, ((p : ℝ) - 1)) *
              (T.card * ((N : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ) + 2)) := by ring
        _ ≤ (f C * ∏ p ∈ C, ((p : ℝ) - 1)) * (T.card * ((N : ℝ) / w + 2)) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left _ hTc; linarith
            · rw [hfφ]; exact hh0 C hCS
        _ = _ := by rw [hfφ]
    refine (sum_le_sum hb).trans ?_
    rw [← sum_mul]
    have hsub : ∑ C ∈ R₂, ∏ p ∈ C, (((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2))) ≤ B := by
      rw [hB, prod_one_add]
      apply sum_le_sum_of_subset_of_nonneg
      · intro C hC; simp only [hR₂, hR, mem_filter] at hC; exact hC.1.1
      · intro C hC _; exact hh0 C hC
    have : 0 ≤ (T.card : ℝ) * ((N : ℝ) / w + 2) := by positivity
    nlinarith
  -- (b) small moduli
  have hsmall : ∑ C ∈ R₁, f C * primEnergy T C ≤
      ((N : ℝ) * T.card - (Real.log Q - Real.log 4) * (T.card : ℝ) ^ 2) / (15 * L5) := by
    set 𝒦 := S.powerset.filter (fun C => ∏ p ∈ C, p ≤ w) with h𝒦
    have hQw : w ≤ (Q : ℕ) := by omega
    have hmv := mv_energy Q M N hN T hTI hTp 𝒦 (by
      intro C hC
      simp only [h𝒦, mem_filter] at hC
      exact ⟨fun p hp => hSp p (mem_powerset.1 hC.1 hp), hC.2.trans hQw⟩)
    have hLnn : ∀ C ∈ 𝒦, 0 ≤ L C * primEnergy T C := by
      intro C hC
      simp only [h𝒦, mem_filter] at hC
      apply mul_nonneg _ (primEnergy_nonneg T C)
      simp only [hL]
      have hqpos : (0 : ℝ) < ((∏ p ∈ C, p : ℕ) : ℝ) := by
        exact_mod_cast prod_pos fun p hp => (hSp p (mem_powerset.1 hC.1 hp)).pos
      have h12 : (12 : ℝ) * ((∏ p ∈ C, p : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) := by
        have : 12 * ∏ p ∈ C, p ≤ (Q : ℕ) := (Nat.mul_le_mul_left 12 hC.2).trans hwQ
        exact_mod_cast this
      have : (4 : ℝ) ≤ ((Q : ℕ) : ℝ) / ((∏ p ∈ C, p : ℕ) : ℝ) := by
        rw [le_div_iff₀ hqpos]; linarith
      have := Real.log_le_log (by norm_num) this
      linarith
    have hsplit : L ∅ * primEnergy T ∅ + ∑ C ∈ R₁, L C * primEnergy T C ≤
        ∑ C ∈ 𝒦, L C * primEnergy T C := by
      have hmem : ∅ ∈ 𝒦 := by
        simp only [h𝒦, mem_filter, prod_empty]; exact ⟨empty_mem_powerset S, hw⟩
      rw [← add_sum_erase 𝒦 _ hmem]
      apply add_le_add le_rfl
      apply sum_le_sum_of_subset_of_nonneg
      · intro C hC
        simp only [hR₁, hR, mem_filter] at hC
        simp only [h𝒦, mem_erase, mem_filter]
        exact ⟨hC.1.2.1, hC.1.1, hC.2⟩
      · intro C hC _; exact hLnn C (mem_of_mem_erase hC)
    have hL0 : L ∅ = Real.log Q - Real.log 4 := by
      simp only [hL, prod_empty, Nat.cast_one, div_one]
    rw [hL0, primEnergy_empty] at hsplit
    have hfL : ∀ C ∈ R₁, f C * primEnergy T C ≤ (L C / (15 * L5)) * primEnergy T C := by
      intro C hC
      simp only [hR₁, hR, mem_filter] at hC
      apply mul_le_mul_of_nonneg_right _ (primEnergy_nonneg T C)
      exact f_le_weight C (fun p hp => hS p (mem_powerset.1 hC.1.1 hp)) hC.1.2.1 hC.1.2.2
        Q w hC.2 hwQ hQ20
    refine (sum_le_sum hfL).trans ?_
    have : ∑ C ∈ R₁, L C / (15 * L5) * primEnergy T C =
        (∑ C ∈ R₁, L C * primEnergy T C) / (15 * L5) := by
      rw [sum_div]; apply sum_congr rfl; intro C _; ring
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  -- combine
  have hL4 : L5 ≤ Real.log Q - Real.log 4 := by
    rw [hL5]; have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 20)
    linarith
  have hfrac : (T.card : ℝ) ^ 2 / 15 ≤ (Real.log Q - Real.log 4) * (T.card : ℝ) ^ 2 / (15 * L5) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have := sq_nonneg (T.card : ℝ)
    nlinarith
  have e1 : ((N : ℝ) * T.card - (Real.log Q - Real.log 4) * (T.card : ℝ) ^ 2) / (15 * L5) =
      (N : ℝ) * T.card / (15 * L5) - (Real.log Q - Real.log 4) * (T.card : ℝ) ^ 2 / (15 * L5) := by
    ring
  rw [e1] at hsmall
  linarith

end RV27C
end LowerPart

theorem solution (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (Q : ℕ+) (M N w : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N) (hw : 1 ≤ w) (hwQ : 12 * w ≤ (Q : ℕ))
    (hQ20 : 20 < (Q : ℕ)) (T : Finset ℕ) (hTI : T ⊆ Finset.Ico M (M + N))
    (hTp : ∀ t ∈ T, t.Prime ∧ (Q : ℕ) < t) (hTS : ∀ t ∈ T, ∀ p ∈ S, ¬ p ∣ t) :
    (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
      ((16 / 15) * (T.card : ℝ) ^ 2 - (N : ℝ) * T.card / (15 * (Real.log Q - Real.log 20)) -
        ((N : ℝ) / w + 2) * (∏ p ∈ S, (1 + ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)))) * T.card) ≤
    ∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
      (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) :=
  RV27C.interval_pair_weight_lower S hS Q M N w hN hw hwQ hQ20 T hTI hTp hTS
