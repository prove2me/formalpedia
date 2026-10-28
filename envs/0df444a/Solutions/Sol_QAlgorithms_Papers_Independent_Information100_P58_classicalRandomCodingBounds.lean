-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.classicalRandomCodingBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:41:28.761913+00:00
-- url     : https://prove2.me/submissions/feea9cdb-5fdd-446c-ab07-83313056ed19

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

open Matrix
open scoped ComplexOrder

def p58rm_P {n d : ℕ} (S : Finset (Fin n)) : Operator (Output n d) :=
  diagonal fun y => if support y = S then 1 else 0

lemma p58rm_sum_finset_prod {n : ℕ} (f : Fin n → Bool → ℂ) :
    ∑ S : Finset (Fin n), ∏ i, f i (decide (i ∈ S)) = ∏ i, (f i true + f i false) := by
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.prod_mul_prod_compl S]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · rw [Finset.compl_eq_univ_sdiff]
    exact Finset.prod_congr rfl fun i hi => by
      have : i ∉ S := by simpa using hi
      simp [this]

lemma p58rm_w {n : ℕ} (p : ℝ) (S : Finset (Fin n)) :
    ((patternWeight n p S : ℝ) : ℂ) = ∏ i, (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) := by
  rw [← Finset.prod_mul_prod_compl S]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ S) => by simp [hi] : ∀ i ∈ S,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = ((1 - p : ℝ) : ℂ))]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ Sᶜ) => by
      have : i ∉ S := by simpa using hi
      simp [this] : ∀ i ∈ Sᶜ,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = (p : ℂ))]
  simp [patternWeight, Finset.card_compl]


lemma p58rm_PH {n d : ℕ} (S : Finset (Fin n)) : (p58rm_P S : Operator (Output n d))ᴴ = p58rm_P S := by
  unfold p58rm_P
  rw [diagonal_conjTranspose]
  congr 1; ext y; simp only [Pi.star_apply]; split_ifs <;> simp

/-! ## sector-wise partial traces -/

def p58rm_kk {d : ℕ} (o : Fin d) (b : Bool) (u : Option (Fin d)) (a z : Fin d) : ℂ :=
  if b then (if u = some a ∧ z = o then 1 else 0) else (if u = none ∧ a = z then 1 else 0)

def p58rm_K {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (z : Word n d) :
    Matrix (Output n d) (Word n d) ℂ :=
  Matrix.of fun y x => ∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)

def p58rm_sig {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    Operator (Output n d) :=
  ∑ z, p58rm_K o S z * ρ * (p58rm_K o S z)ᴴ

lemma p58rm_star_kk {d : ℕ} (o : Fin d) (b : Bool) (u : Option (Fin d)) (a z : Fin d) :
    star (p58rm_kk o b u a z) = p58rm_kk o b u a z := by
  unfold p58rm_kk; split_ifs <;> simp

lemma p58rm_kk_sum {d : ℕ} (o : Fin d) (b : Bool) (a a' : Fin d) :
    ∑ z, ∑ u, p58rm_kk o b u a z * p58rm_kk o b u a' z = if a = a' then 1 else 0 := by
  cases b
  · simp only [p58rm_kk, Bool.false_eq_true, if_false, Fintype.sum_option]
    simp only [reduceCtorEq, false_and, if_false, mul_zero, Finset.sum_const_zero, add_zero, true_and]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases h : a = a'
    · subst h; simp
    · simp [h]
      try (intros; simp_all [eq_comm])
  · simp only [p58rm_kk, if_true, Fintype.sum_option]
    simp only [reduceCtorEq, false_and, if_false, mul_zero, zero_add, Option.some.injEq]
    by_cases h : a = a'
    · subst h
      simp [ite_and]
    · simp [ite_and, h]
      try (intros; simp_all [eq_comm])

lemma p58rm_KK {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) :
    ∑ z, (p58rm_K o S z)ᴴ * p58rm_K o S z = 1 := by
  ext x x'
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, p58rm_K, Matrix.of_apply, star_prod,
    p58rm_star_kk, ← Finset.prod_mul_distrib]
  have h1 : ∀ z : Word n d, ∑ y : Output n d, ∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i) *
      p58rm_kk o (decide (i ∈ S)) (y i) (x' i) (z i) =
      ∏ i, ∑ u, p58rm_kk o (decide (i ∈ S)) u (x i) (z i) * p58rm_kk o (decide (i ∈ S)) u (x' i) (z i) := by
    intro z
    rw [Fintype.prod_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i a => ∑ u, p58rm_kk o (decide (i ∈ S)) u (x i) a *
    p58rm_kk o (decide (i ∈ S)) u (x' i) a)]
  simp_rw [p58rm_kk_sum, Matrix.one_apply]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma p58rm_sig_psd {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d))
    (hρ : ρ.PosSemidef) : (p58rm_sig o S ρ).PosSemidef :=
  posSemidef_sum _ fun z _ => hρ.mul_mul_conjTranspose_same _

lemma p58rm_sig_tr {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    (p58rm_sig o S ρ).trace = ρ.trace := by
  unfold p58rm_sig
  rw [trace_sum]
  simp_rw [fun z => Matrix.trace_mul_comm (p58rm_K o S z * ρ) (p58rm_K o S z)ᴴ, ← Matrix.mul_assoc]
  rw [← trace_sum, ← Finset.sum_mul, p58rm_KK, Matrix.one_mul]

lemma p58rm_PK {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (z : Word n d) :
    (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) * p58rm_K o S z = p58rm_K o S z := by
  ext y x
  rw [p58rm_P, diagonal_mul]
  by_cases hy : support y = S
  · simp [hy]
  · rw [if_neg hy, zero_mul]
    obtain ⟨i, hi⟩ : ∃ i, ¬ ((y i).isSome ↔ i ∈ S) := by
      by_contra hc; push Not at hc
      exact hy (Finset.ext fun i => by simp [support, hc i])
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hyi : y i with _ | a <;> by_cases hS : i ∈ S <;> simp_all [p58rm_kk]

lemma p58rm_Psig {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) * p58rm_sig o S ρ = p58rm_sig o S ρ := by
  unfold p58rm_sig
  rw [Matrix.mul_sum]
  simp_rw [← Matrix.mul_assoc, p58rm_PK]

lemma p58rm_sigP {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    p58rm_sig o S ρ * (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) = p58rm_sig o S ρ := by
  unfold p58rm_sig
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_assoc, ← p58rm_PH S, ← conjTranspose_mul, p58rm_PK]

lemma p58rm_conj_apply {A B : Type*} [Fintype A] [Fintype B] (K : Matrix B A ℂ) (ρ : Matrix A A ℂ)
    (y y' : B) : (K * ρ * Kᴴ) y y' = ∑ x, ∑ x', ρ x x' * (K y x * star (K y' x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring

lemma p58rm_coord {d : ℕ} (o : Fin d) (p : ℝ) (u u' : Option (Fin d)) (a a' : Fin d) :
    ((1 - p : ℝ) : ℂ) * ∑ z, p58rm_kk o true u a z * p58rm_kk o true u' a' z +
      (p : ℂ) * ∑ z, p58rm_kk o false u a z * p58rm_kk o false u' a' z =
    singleErasure d p (Matrix.single a a' 1) u u' := by
  rcases u with _ | i <;> rcases u' with _ | j
  · simp only [p58rm_kk, singleErasure, if_true, Bool.false_eq_true, if_false]
    simp [ite_and]
    by_cases h : a = a'
    · subst h; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne _ _ _ h]
      simp
      try (intros; simp_all [eq_comm])
  · simp [p58rm_kk, singleErasure]
  · simp [p58rm_kk, singleErasure]
  · simp only [p58rm_kk, singleErasure, if_true, Bool.false_eq_true, if_false]
    simp [ite_and, Matrix.single_apply]
    by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

lemma p58rm_key {n d : ℕ} (o : Fin d) (p : ℝ) (y y' : Output n d) (x x' : Word n d) :
    ∑ S : Finset (Fin n), ((patternWeight n p S : ℝ) : ℂ) *
      ∑ z : Word n d, (∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
        (∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i)) =
    ∏ i, singleErasure d p (Matrix.single (x i) (x' i) 1) (y i) (y' i) := by
  have h1 : ∀ S : Finset (Fin n), ((patternWeight n p S : ℝ) : ℂ) *
      ∑ z : Word n d, (∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
        (∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i)) =
      ∏ i, ((if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
        ∑ c, p58rm_kk o (decide (i ∈ S)) (y i) (x i) c *
          p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) c) := by
    intro S
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i c => p58rm_kk o (decide (i ∈ S)) (y i) (x i) c *
      p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) c), p58rm_w, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [p58rm_sum_finset_prod (fun i b => (if b then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
      ∑ c, p58rm_kk o b (y i) (x i) c * p58rm_kk o b (y' i) (x' i) c)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← p58rm_coord o p]
  simp

lemma p58rm_erasure {n d : ℕ} (o : Fin d) (p : ℝ) (ρ : Operator (Word n d)) :
    erasure n d p ρ = ∑ S, ((patternWeight n p S : ℝ) : ℂ) • p58rm_sig o S ρ := by
  ext y y'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, p58rm_sig, Matrix.sum_apply, p58rm_conj_apply,
    p58rm_K, Matrix.of_apply, star_prod, p58rm_star_kk]
  unfold erasure piSuperop
  simp only [Matrix.of_apply]
  simp_rw [← p58rm_key o p y y', Finset.mul_sum]
  symm
  calc _ = ∑ S : Finset (Fin n), ∑ x : Word n d, ∑ z : Word n d, ∑ x' : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun S _ => Finset.sum_comm
    _ = ∑ S : Finset (Fin n), ∑ x : Word n d, ∑ x' : Word n d, ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : Word n d, ∑ S : Finset (Fin n), ∑ x' : Word n d, ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) := Finset.sum_comm
    _ = ∑ x : Word n d, ∑ x' : Word n d, ∑ S : Finset (Fin n), ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
      refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun z _ => ?_
      ring


/-! ## operator inequalities -/

lemma p58rm_tr_sub_psd {A : Type*} [Fintype A] [DecidableEq A] (σ : Matrix A A ℂ)
    (hσ : σ.PosSemidef) : (σ.trace • (1 : Matrix A A ℂ) - σ).PosSemidef := by
  set U := hσ.1.eigenvectorUnitary
  have hs := hσ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set lam := hσ.1.eigenvalues
  have htr := hσ.1.trace_eq_sum_eigenvalues
  have hUU : (U : Matrix A A ℂ) * star (U : Matrix A A ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have key : σ.trace • (1 : Matrix A A ℂ) - σ =
      (U : Matrix A A ℂ) * diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) * star (U : Matrix A A ℂ) := by
    have : diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) =
        σ.trace • (1 : Matrix A A ℂ) - diagonal (RCLike.ofReal ∘ lam) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [htr, diagonal_apply]; rfl
      · simp [diagonal_apply, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hUU]
  rw [key, Matrix.star_eq_conjTranspose]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  apply Complex.zero_le_real.mpr
  have : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => hσ.eigenvalues_nonneg j) (Finset.mem_univ i)
  linarith



theorem rc_group (n : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ S : Finset (Fin n), patternWeight n p S * g S.card =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n p k * g k := by
  have := Finset.sum_powerset_apply_card (fun k => (1 - p) ^ k * p ^ (n - k) * g k)
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
  unfold patternWeight binomialWeight
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]; ring

theorem rc_wsum (n : ℕ) (p : ℝ) : ∑ S : Finset (Fin n), patternWeight n p S = 1 := by
  have := rc_group n p (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  have h := (add_pow (1 - p) p n).symm
  rw [show 1 - p + p = 1 by ring, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold binomialWeight; ring

theorem rc_w_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ patternWeight n p S := by
  unfold patternWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- Σ_m 1/|fiber of f m| = |image f|. -/
theorem rc_fiber {M : ℕ} {β : Type*} [DecidableEq β] (f : Fin M → β) :
    ∑ m, (1 : ℝ) / (Finset.univ.filter fun j => f j = f m).card =
      (Finset.univ.image f).card := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hc : ∀ m ∈ Finset.univ.filter (fun m => f m = v),
      (1 : ℝ) / (Finset.univ.filter fun j => f j = f m).card =
        1 / (Finset.univ.filter fun j => f j = v).card := by
    intro m hm
    rw [(Finset.mem_filter.mp hm).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hv
  have hpos : (0 : ℝ) < (Finset.univ.filter fun j => f j = v).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨m, by simp [hm]⟩
  field_simp
  simp

theorem rc_received_eq {n d : ℕ} (S : Finset (Fin n)) (x x' : Word n d) :
    received x S = received x' S ↔ ∀ i ∈ S, x i = x' i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [received, if_pos hi, Option.some.injEq] at this
    exact this
  · intro h; funext i
    simp only [received]
    split_ifs with hi
    · rw [h i hi]
    · rfl

theorem rc_detInd {n d M : ℕ} (p : ℝ) (C : Fin M → Word n d) :
    deterministicAverage p C =
      (∑ S : Finset (Fin n), patternWeight n p S *
        (Finset.univ.image fun j => received (C j) S).card) / M := by
  unfold deterministicAverage deterministicIndividual
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← rc_fiber (fun j => received (C j) S), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold compatible
  simp only [rc_received_eq]
  ring

/-- number of words with a given restriction -/
theorem rc_fib_card {n d : ℕ} (S : Finset (Fin n)) (x0 : Word n d) :
    (Finset.univ.filter fun x : Word n d => received x S = received x0 S).card = d ^ (n - S.card) := by
  have : (Finset.univ.filter fun x : Word n d => received x S = received x0 S) =
      Fintype.piFinset (fun i => if i ∈ S then {x0 i} else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, rc_received_eq]
    constructor
    · intro h i
      split_ifs with hi
      · simp [h i hi]
      · simp
    · intro h i hi
      have := h i
      rw [if_pos hi] at this
      simpa using this
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

theorem rc_codes_avoid {M : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) :
    (Finset.univ.filter fun C : Fin M → X => ∀ j, C j ∈ A).card = A.card ^ M := by
  have : (Finset.univ.filter fun C : Fin M → X => ∀ j, C j ∈ A) = Fintype.piFinset fun _ => A := by
    ext C; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]; simp

/-- Σ_C #distinct projections = d^k (N^M - (N - d^{n-k})^M). -/
theorem rc_sum_distinct {n d M : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n)) :
    ∑ C : Fin M → Word n d, ((Finset.univ.image fun j => received (C j) S).card : ℝ) =
      (d:ℝ) ^ S.card * (((d:ℝ) ^ n) ^ M - ((d:ℝ) ^ n - (d:ℝ) ^ (n - S.card)) ^ M) := by
  set T := Finset.univ.image fun x : Word n d => received x S with hT
  have hcard : ∀ C : Fin M → Word n d, ((Finset.univ.image fun j => received (C j) S).card : ℝ) =
      ∑ y ∈ T, if ∃ j, received (C j) S = y then 1 else 0 := by
    intro C
    rw [Finset.sum_boole]
    congr 1
    congr 1
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, hT]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨⟨C j, rfl⟩, j, rfl⟩
    · rintro ⟨_, j, hj⟩; exact ⟨j, hj⟩
  simp only [hcard]
  rw [Finset.sum_comm]
  have hy : ∀ y ∈ T, (∑ C : Fin M → Word n d, if ∃ j, received (C j) S = y then (1:ℝ) else 0) =
      ((d:ℝ) ^ n) ^ M - ((d:ℝ) ^ n - (d:ℝ) ^ (n - S.card)) ^ M := by
    intro y hyT
    obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hyT
    rw [Finset.sum_boole]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin M → Word n d))) (fun C => ∃ j, received (C j) S = received x0 S)
    have hneg : (Finset.univ.filter fun C : Fin M → Word n d =>
        ¬ ∃ j, received (C j) S = received x0 S).card =
        (Finset.univ.filter fun x : Word n d => received x S ≠ received x0 S).card ^ M := by
      rw [← rc_codes_avoid]
      congr 1; ext C; simp
    have hA : ((Finset.univ.filter fun x : Word n d => received x S ≠ received x0 S).card : ℝ) =
        (d:ℝ) ^ n - (d:ℝ) ^ (n - S.card) := by
      have h2 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Word n d))) (fun x => received x S = received x0 S)
      rw [rc_fib_card, Finset.card_univ] at h2
      simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at h2
      have : ((Finset.univ.filter fun x : Word n d => received x S ≠ received x0 S).card : ℝ) =
          ((d ^ n : ℕ) : ℝ) - ((d ^ (n - S.card) : ℕ) : ℝ) := by
        rw [← h2]; push_cast; ring
      rw [this]; push_cast; ring
    rw [Finset.card_univ] at hsplit
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hsplit
    have : ((Finset.univ.filter fun C : Fin M → Word n d =>
        ∃ j, received (C j) S = received x0 S).card : ℝ) =
        (((d ^ n) ^ M : ℕ) : ℝ) - ((Finset.univ.filter fun C : Fin M → Word n d =>
          ¬ ∃ j, received (C j) S = received x0 S).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    rw [this, hneg]; push_cast; rw [hA]
  rw [Finset.sum_congr rfl hy, Finset.sum_const, nsmul_eq_mul]
  congr 1
  -- |T| = d^k
  have hN : ∑ y ∈ T, (Finset.univ.filter fun x : Word n d => received x S = y).card =
      (Finset.univ : Finset (Word n d)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Word n d => received x S) (t := T)
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  have hc : ∀ y ∈ T, (Finset.univ.filter fun x : Word n d => received x S = y).card =
      d ^ (n - S.card) := by
    intro y hyT
    obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hyT
    exact rc_fib_card S x0
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hN
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hN
  have hk : S.card ≤ n := by
    have := Finset.card_le_univ S; simpa using this
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hN' : (T.card : ℝ) * (d:ℝ) ^ (n - S.card) = (d:ℝ) ^ (n - S.card) * (d:ℝ) ^ S.card := by
    have : ((T.card * d ^ (n - S.card) : ℕ) : ℝ) = ((d ^ n : ℕ) : ℝ) := by rw [hN]
    push_cast at this
    rw [this, ← pow_add, Nat.sub_add_cancel hk]
  have := mul_right_cancel₀ (pow_ne_zero (n - S.card) hdpos.ne') (hN'.trans (mul_comm _ _))
  exact this

theorem rc_bonf (M : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) ^ M ≤ 1 - M * u + (M * (M - 1) / 2) * u ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [pow_succ]
    have h1 : 0 ≤ 1 - u := by linarith
    have := mul_le_mul_of_nonneg_right ih h1
    push_cast
    have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
    have h3 : 0 ≤ (M * (M - 1) / 2) * u ^ 3 ∨ M = 0 := by
      rcases Nat.eq_zero_or_pos M with h | h
      · right; exact h
      · left
        have : (1:ℝ) ≤ M := by exact_mod_cast h
        have : 0 ≤ (M:ℝ) - 1 := by linarith
        positivity
    rcases h3 with h3 | h3
    · nlinarith
    · subst h3; simp at this ⊢

/-- per-sector random coding term -/
def rcT (M : ℕ) (x : ℝ) : ℝ := x / M * (1 - (1 - x⁻¹) ^ M)

theorem rc_link1_term {M : ℕ} (hM : 0 < M) {x : ℝ} (hx : 1 ≤ x) :
    (1 - Real.exp (-1)) * min 1 (x / M) ≤ rcT M x := by
  unfold rcT
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := by linarith
  set u := x⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact inv_le_one_of_one_le₀ hx
  have hpow : (1 - u) ^ M ≤ Real.exp (-(M * u)) := by
    have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    calc (1 - u) ^ M ≤ Real.exp (-u) ^ M := pow_le_pow_left₀ (by linarith) h1 M
      _ = Real.exp (-(M * u)) := by rw [← Real.exp_nat_mul]; ring_nf
  set t := (M:ℝ) * u with ht
  have htpos : 0 < t := by positivity
  have hxM : x / M = t⁻¹ := by rw [ht, hu]; field_simp
  rw [hxM]
  have hmain : t⁻¹ * (1 - Real.exp (-t)) ≤ t⁻¹ * (1 - (1 - u) ^ M) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine le_trans ?_ hmain
  rcases le_or_gt 1 t with h1 | h1
  · rw [min_eq_right (inv_le_one_of_one_le₀ h1)]
    have : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have : 0 ≤ t⁻¹ := by positivity
    nlinarith
  · rw [min_eq_left (one_le_inv₀ htpos |>.mpr h1.le)]
    have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
      (show (0:ℝ) ≤ 1 - t by linarith) htpos.le (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
    rw [show t * -1 = -t by ring] at hconv
    have h2 : t * (1 - Real.exp (-1)) ≤ 1 - Real.exp (-t) := by linarith
    calc (1 - Real.exp (-1)) * 1 = t⁻¹ * (t * (1 - Real.exp (-1))) := by field_simp
      _ ≤ t⁻¹ * (1 - Real.exp (-t)) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem rc_link6_term {M : ℕ} (hM : 0 < M) {x : ℝ} (hx : 1 ≤ x) :
    1 - rcT M x ≤ min 1 (((M - 1 : ℕ) : ℝ) / (2 * x)) := by
  unfold rcT
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := by linarith
  set u := x⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact inv_le_one_of_one_le₀ hx
  have hpow1 : (1 - u) ^ M ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hcast : ((M - 1 : ℕ) : ℝ) = (M:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  apply le_min
  · have : 0 ≤ x / M * (1 - (1 - u) ^ M) := by
      apply mul_nonneg (by positivity); linarith
    linarith
  · have hb := rc_bonf M hu0.le hu1
    have hxu : x * u = 1 := by rw [hu]; field_simp
    have key : x / M * (1 - (1 - u) ^ M) ≥ x / M * (M * u - (M * (M - 1) / 2) * u ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : x / M * (M * u - (M * (M - 1) / 2) * u ^ 2) = 1 - (M - 1) / (2 * x) := by
      rw [hu]; field_simp
    linarith

theorem rc_avg {n d M : ℕ} (hd : 1 ≤ d) (hM : 0 < M) (p : ℝ) :
    ∑ C : Fin M → Word n d, deterministicAverage p C =
      ((d:ℝ) ^ n) ^ M * randomCodingSuccess n d M p := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  simp only [rc_detInd, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, rc_sum_distinct hd]
  have h : ∀ S : Finset (Fin n), patternWeight n p S *
      ((d:ℝ) ^ S.card * (((d:ℝ) ^ n) ^ M - ((d:ℝ) ^ n - (d:ℝ) ^ (n - S.card)) ^ M)) / M =
      ((d:ℝ) ^ n) ^ M * (patternWeight n p S * rcT M ((d:ℝ) ^ S.card)) := by
    intro S
    have hk : S.card ≤ n := by have := Finset.card_le_univ S; simpa using this
    have hN : (d:ℝ) ^ n = (d:ℝ) ^ (n - S.card) * (d:ℝ) ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have e : (d:ℝ) ^ n - (d:ℝ) ^ (n - S.card) = (d:ℝ) ^ n * (1 - ((d:ℝ) ^ S.card)⁻¹) := by
      rw [hN]; field_simp
    rw [e, mul_pow]
    unfold rcT
    have : (0:ℝ) < M := by exact_mod_cast hM
    field_simp
  rw [Finset.sum_div, Finset.sum_congr rfl fun S _ => h S, ← Finset.mul_sum,
    rc_group n p (fun k => rcT M ((d:ℝ) ^ k))]
  unfold randomCodingSuccess rcT
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

theorem rc_nonempty_codes {n d M : ℕ} (hd : 1 ≤ d) : (Finset.univ : Finset (Fin M → Word n d)).Nonempty :=
  ⟨fun _ _ => ⟨0, by omega⟩, Finset.mem_univ _⟩

theorem rc_link5 {n d M : ℕ} (hd : 1 ≤ d) (hM : 0 < M) (p : ℝ) :
    ∃ C : Fin M → Word n d, randomCodingSuccess n d M p ≤ deterministicAverage p C := by
  have h : ∑ _C : Fin M → Word n d, randomCodingSuccess n d M p ≤
      ∑ C : Fin M → Word n d, deterministicAverage p C := by
    rw [rc_avg hd hM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
  obtain ⟨C, _, hC⟩ := Finset.exists_le_of_sum_le (rc_nonempty_codes hd) h
  exact ⟨C, hC⟩

theorem rc_wpos_sum (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ binomialWeight n p k := by
  unfold binomialWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem rc_bsum (n : ℕ) (p : ℝ) : ∑ k ∈ Finset.range (n + 1), binomialWeight n p k = 1 := by
  have := rc_group n p (fun _ => 1)
  simp only [mul_one] at this
  rw [← this, rc_wsum]

theorem rc_link6 {n d M : ℕ} (hd : 1 ≤ d) (hM : 0 < M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C : Fin M → Word n d, 1 - deterministicAverage p C ≤ collisionBound n d M p := by
  have hb : 1 - randomCodingSuccess n d M p ≤ collisionBound n d M p := by
    have e : 1 - randomCodingSuccess n d M p = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n p k * (1 - rcT M ((d:ℝ) ^ k)) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, rc_bsum]
      unfold randomCodingSuccess rcT
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    unfold collisionBound
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (rc_wpos_sum n hp0 hp1 k)
    exact rc_link6_term hM (one_le_pow₀ (by exact_mod_cast hd))
  have h : ∑ C : Fin M → Word n d, (1 - deterministicAverage p C) ≤
      ∑ _C : Fin M → Word n d, collisionBound n d M p := by
    rw [Finset.sum_sub_distrib, rc_avg hd hM, Finset.sum_const, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, nsmul_eq_mul]
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    push_cast
    have : (0:ℝ) ≤ ((d:ℝ) ^ n) ^ M := by positivity
    nlinarith
  obtain ⟨C, _, hC⟩ := Finset.exists_le_of_sum_le (rc_nonempty_codes hd) h
  exact ⟨C, hC⟩

theorem rc_link1 {n d M : ℕ} (hd : 1 ≤ d) (hM : 0 < M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - Real.exp (-1)) * dimensionSuccess n d p M ≤ randomCodingSuccess n d M p := by
  unfold dimensionSuccess randomCodingSuccess
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left (rc_link1_term hM (x := (d:ℝ) ^ k)
    (one_le_pow₀ (by exact_mod_cast hd))) (rc_wpos_sum n hp0 hp1 k)
  unfold rcT at this
  linarith


/-! ## quantum converse -/

lemma rcq_diag_tr {A : Type*} [Fintype A] [DecidableEq A] (lam : A → ℝ) (hl : ∀ i, 0 ≤ lam i)
    (Z : Matrix A A ℂ) (hZ : Z.PosSemidef) :
    0 ≤ ((diagonal (fun i => ((lam i : ℝ) : ℂ)) * Z).trace).re := by
  have e : (diagonal (fun i => ((lam i : ℝ) : ℂ)) * Z).trace = ∑ i, ((lam i : ℝ) : ℂ) * Z i i := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, diagonal_mul]
  rw [e, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have h3 : 0 ≤ (Z i i).re := by
    have h4 : (0:ℂ) ≤ Z i i := hZ.diag_nonneg
    exact (Complex.nonneg_iff.mp h4).1
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (hl i) h3

lemma rcq_tr_nonneg {A : Type*} [Fintype A] [DecidableEq A] (X Y : Matrix A A ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ ((X * Y).trace).re := by
  have hs := hX.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have key : ∀ (V D : Matrix A A ℂ), X = V * D * star V →
      (X * Y).trace = (D * (star V * Y * V)).trace := by
    intro V D h
    calc (X * Y).trace = (V * (D * (star V * Y))).trace := by rw [h]; simp only [Matrix.mul_assoc]
      _ = (D * (star V * Y) * V).trace := Matrix.trace_mul_comm _ _
      _ = (D * (star V * Y * V)).trace := by simp only [Matrix.mul_assoc]
  rw [key _ _ hs]
  have hZ := hY.conjTranspose_mul_mul_same (hX.1.eigenvectorUnitary : Matrix A A ℂ)
  rw [← Matrix.star_eq_conjTranspose] at hZ
  exact rcq_diag_tr _ (hX.eigenvalues_nonneg) _ hZ

lemma rcq_PP {n d : ℕ} (S : Finset (Fin n)) :
    (p58rm_P S : Operator (Output n d)) * p58rm_P S = p58rm_P S := by
  unfold p58rm_P
  rw [diagonal_mul_diagonal]
  congr 1; funext y; split_ifs <;> simp

lemma rcq_P_psd {n d : ℕ} (S : Finset (Fin n)) : (p58rm_P S : Operator (Output n d)).PosSemidef := by
  unfold p58rm_P
  apply PosSemidef.diagonal
  intro y; simp only [Pi.zero_apply]; split_ifs <;> simp

lemma rcq_trP {n d : ℕ} (S : Finset (Fin n)) :
    ((p58rm_P S : Operator (Output n d)).trace).re = (d:ℝ) ^ S.card := by
  unfold p58rm_P
  rw [trace_diagonal]
  have e : (∑ y : Output n d, (if support y = S then (1:ℂ) else 0)) =
      (((Finset.univ.filter fun y : Output n d => support y = S).card : ℕ) : ℂ) := by
    rw [Finset.sum_boole]
  rw [e]
  have hc : (Finset.univ.filter fun y : Output n d => support y = S) =
      Fintype.piFinset (fun i => if i ∈ S then Finset.univ.image some else {none}) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i
      by_cases hi : (y i).isSome
      · have : i ∈ support y := by simp [support, hi]
        rw [if_pos this]
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hi
        simp [ha]
      · have : i ∉ support y := by simp [support, hi]
        rw [if_neg this]
        simp only [Option.not_isSome_iff_eq_none] at hi
        simp [hi]
    · intro h
      ext i
      have := h i
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ S
      · rw [if_pos hi] at this
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp this
        simp [← ha, hi]
      · rw [if_neg hi, Finset.mem_singleton] at this
        simp [this, hi]
  rw [hc, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ, Fintype.card_fin]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [show ((d ^ S.card : ℕ) : ℂ) = (((d:ℝ) ^ S.card : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]

lemma rcq_effect_le {A : Type*} [Fintype A] [DecidableEq A] {M : ℕ} (D : Fin M → Matrix A A ℂ)
    (hD : IsPOVM D) (m : Fin M) : (1 - D m).PosSemidef := by
  have h := hD.2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at h
  rw [← h, add_sub_cancel_left]
  exact posSemidef_sum _ fun j _ => hD.1 j

lemma rcq_sector {n d M : ℕ} (o : Fin d) (C : QuantumCode n d M) (S : Finset (Fin n)) :
    ∑ m, ((C.decoder m * p58rm_sig o S (C.input m)).trace).re ≤ min (M:ℝ) ((d:ℝ) ^ S.card) := by
  have hσ : ∀ m, (p58rm_sig o S (C.input m)).PosSemidef := fun m =>
    p58rm_sig_psd o S _ (C.normalized m).1
  have hσtr : ∀ m, (p58rm_sig o S (C.input m)).trace = 1 := fun m => by
    rw [p58rm_sig_tr]; exact (C.normalized m).2
  apply le_min
  · have : ∀ m, ((C.decoder m * p58rm_sig o S (C.input m)).trace).re ≤ 1 := by
      intro m
      have h := rcq_tr_nonneg _ _ (rcq_effect_le C.decoder C.measurement m) (hσ m)
      rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re, hσtr m] at h
      simp at h; linarith
    calc _ ≤ ∑ _m : Fin M, (1:ℝ) := Finset.sum_le_sum fun m _ => this m
      _ = M := by simp
  · set P : Operator (Output n d) := p58rm_P S
    have hb : ∀ m, ((C.decoder m * p58rm_sig o S (C.input m)).trace).re ≤
        ((C.decoder m * P).trace).re := by
      intro m
      set σ := p58rm_sig o S (C.input m)
      have hPσP : P * σ * P = σ := by rw [p58rm_Psig, p58rm_sigP]
      have e1 : (C.decoder m * σ).trace = (P * C.decoder m * P * σ).trace := by
        conv_lhs => rw [← hPσP]
        rw [show C.decoder m * (P * σ * P) = (C.decoder m * P * σ) * P by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have e2 : (P * C.decoder m * P).trace = (C.decoder m * P).trace := by
        have hPP : P * P = P := rcq_PP S
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hPP]
      have hX : (P * C.decoder m * P).PosSemidef := by
        have := (C.measurement.1 m).conjTranspose_mul_mul_same P
        rwa [p58rm_PH] at this
      have hY : (1 - σ).PosSemidef := by
        have := p58rm_tr_sub_psd σ (hσ m)
        rwa [hσtr m, one_smul] at this
      have h := rcq_tr_nonneg _ _ hX hY
      rw [Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re, e2, ← e1] at h
      linarith
    calc _ ≤ ∑ m, ((C.decoder m * P).trace).re := Finset.sum_le_sum fun m _ => hb m
      _ = ((∑ m, C.decoder m) * P).trace.re := by
          rw [Finset.sum_mul, trace_sum, Complex.re_sum]
      _ = (d:ℝ) ^ S.card := by rw [C.measurement.2, Matrix.one_mul, rcq_trP]

lemma rcq_qind {n d M : ℕ} (o : Fin d) (p : ℝ) (C : QuantumCode n d M) (m : Fin M) :
    quantumIndividual p C m = ∑ S, patternWeight n p S *
      ((C.decoder m * p58rm_sig o S (C.input m)).trace).re := by
  unfold quantumIndividual effectProb
  rw [p58rm_erasure o p, Matrix.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma rcq_link4_code {n d M : ℕ} (hd : 1 ≤ d) (hM : 0 < M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : QuantumCode n d M) : quantumAverage p C ≤ dimensionSuccess n d p M := by
  have o : Fin d := ⟨0, by omega⟩
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  unfold quantumAverage
  simp only [rcq_qind o p C]
  rw [Finset.sum_comm, div_le_iff₀ hMr]
  unfold dimensionSuccess
  rw [← rc_group n p (fun k => min 1 ((d:ℝ) ^ k / M)), Finset.sum_mul]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← Finset.mul_sum, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (rc_w_nonneg n hp0 hp1 S)
  rw [min_mul_of_nonneg _ _ hMr.le, one_mul, div_mul_cancel₀ _ hMr.ne']
  exact rcq_sector o C S

/-! ## classical codes inside quantum codes -/

def rcCreal (p : ℝ) {d : ℕ} (a : Fin d) (u : Option (Fin d)) : ℝ :=
  if u = none then p else if u = some a then 1 - p else 0

lemma rcq_coord {d : ℕ} (p : ℝ) (a : Fin d) (u : Option (Fin d)) :
    singleErasure d p (Matrix.single a a 1) u u = ((rcCreal p a u : ℝ) : ℂ) := by
  rcases u with _ | j
  · simp [singleErasure, rcCreal, Matrix.trace_single_eq_same]
  · simp only [singleErasure, rcCreal, reduceCtorEq, if_false, Option.some.injEq]
    rw [Matrix.single_apply]
    by_cases h : a = j
    · subst h; simp
    · simp [h, Ne.symm h]

lemma rcq_erasure_diag {n d : ℕ} (p : ℝ) (q : Word n d → ℝ) (y : Output n d) :
    erasure n d p (diagonal fun x => ((q x : ℝ) : ℂ)) y y =
      ((∑ x, q x * ∏ i, rcCreal p (x i) (y i) : ℝ) : ℂ) := by
  unfold erasure piSuperop
  simp only [Matrix.of_apply, diagonal_apply]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp only [if_true]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    exact rcq_coord p (x i) (y i)
  · intro x' _ hx'; rw [if_neg (Ne.symm hx'), zero_mul]
  · simp

lemma rcq_supp_received {n d : ℕ} (x : Word n d) (S : Finset (Fin n)) : support (received x S) = S := by
  ext i; by_cases h : i ∈ S <;> simp [support, received, h]

lemma rcq_received_inj {n d : ℕ} (x : Word n d) : Function.Injective fun S : Finset (Fin n) => received x S := by
  intro S S' h
  have := congrArg support h
  simpa [rcq_supp_received] using this

lemma rcq_sum_pattern {n d : ℕ} (p : ℝ) (x : Word n d) (r : Output n d → ℝ) :
    ∑ y, r y * ∏ i, rcCreal p (x i) (y i) = ∑ S, patternWeight n p S * r (received x S) := by
  symm
  refine Fintype.sum_of_injective (fun S => received x S) (rcq_received_inj x) _ _ ?_ ?_
  · intro y hy
    have : ∃ i, ∃ j, y i = some j ∧ j ≠ x i := by
      by_contra hc
      push_neg at hc
      apply hy
      refine ⟨support y, funext fun i => ?_⟩
      simp only [received, support, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hyi : y i with _ | j
      · simp
      · simp [hc i j hyi]
    obtain ⟨i, j, hyi, hj⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [rcCreal, hyi, hj]), mul_zero]
  · intro S
    rw [mul_comm]
    congr 1
    unfold patternWeight
    rw [show (∏ i, rcCreal p (x i) (received x S i)) = ∏ i, (if i ∈ S then 1 - p else p) from
      Finset.prod_congr rfl fun i _ => by
        by_cases h : i ∈ S <;> simp [rcCreal, received, h]]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

lemma rcq_swap {n d : ℕ} (p : ℝ) (r : Output n d → ℝ) (q : Word n d → ℝ) :
    ∑ y, r y * ∑ x, q x * ∏ i, rcCreal p (x i) (y i) =
      ∑ S, patternWeight n p S * ∑ x, q x * r (received x S) := by
  have h : ∀ x, ∑ y, r y * (q x * ∏ i, rcCreal p (x i) (y i)) =
      q x * ∑ S, patternWeight n p S * r (received x S) := by
    intro x
    rw [← rcq_sum_pattern p x r, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum] at h ⊢
  rw [Finset.sum_congr rfl fun x _ => h x]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => by ring

def rcEmbed {n d M : ℕ} (C : ClassicalCode n d M) : QuantumCode n d M where
  input m := diagonal fun x => (((C.encoder m).val x : ℝ) : ℂ)
  normalized m := by
    refine ⟨?_, ?_⟩
    · apply PosSemidef.diagonal
      intro x; simp only [Pi.zero_apply]
      exact Complex.zero_le_real.mpr ((C.encoder m).2.1 x)
    · rw [trace_diagonal, ← Complex.ofReal_sum, (C.encoder m).2.2]; simp
  decoder j := diagonal fun y => (((C.decoder y).val j : ℝ) : ℂ)
  measurement := by
    refine ⟨fun j => ?_, ?_⟩
    · apply PosSemidef.diagonal
      intro y; simp only [Pi.zero_apply]
      exact Complex.zero_le_real.mpr ((C.decoder y).2.1 j)
    · ext y y'
      rw [Matrix.sum_apply]
      by_cases h : y = y'
      · subst h
        simp only [diagonal_apply_eq, one_apply_eq]
        rw [← Complex.ofReal_sum, (C.decoder y).2.2]; simp
      · simp [diagonal_apply_ne _ h, one_apply_ne h]

lemma rcq_embed_ind {n d M : ℕ} (p : ℝ) (C : ClassicalCode n d M) (m : Fin M) :
    quantumIndividual p (rcEmbed C) m = classicalIndividual p C m := by
  unfold quantumIndividual effectProb
  have e : ((rcEmbed C).decoder m * erasure n d p ((rcEmbed C).input m)).trace =
      ((∑ y, (C.decoder y).val m * ∑ x, (C.encoder m).val x * ∏ i, rcCreal p (x i) (y i) : ℝ) : ℂ) := by
    unfold Matrix.trace
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.diag_apply]
    show (diagonal (fun y => (((C.decoder y).val m : ℝ) : ℂ)) *
      erasure n d p (diagonal fun x => (((C.encoder m).val x : ℝ) : ℂ))) y y = _
    rw [diagonal_mul, rcq_erasure_diag]
    push_cast; ring
  rw [e, Complex.ofReal_re]
  exact rcq_swap p (fun y => (C.decoder y).val m) (fun x => (C.encoder m).val x)

def rcUnif {M : ℕ} (K : Finset (Fin M)) (hK : K.Nonempty) : Distribution (Fin M) :=
  ⟨fun j => if j ∈ K then 1 / (K.card : ℝ) else 0, by
    refine ⟨fun j => by show 0 ≤ (if j ∈ K then 1 / (K.card : ℝ) else 0); split_ifs <;> positivity, ?_⟩
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have : (0:ℝ) < K.card := by exact_mod_cast hK.card_pos
    field_simp⟩

def rcPoint {n d : ℕ} (w : Word n d) : Distribution (Word n d) :=
  ⟨fun x => if x = w then 1 else 0, by
    refine ⟨fun x => by show (0:ℝ) ≤ (if x = w then 1 else 0); split_ifs <;> norm_num, ?_⟩
    simp⟩

def rcDet {n d M : ℕ} (hM : 0 < M) (C : Fin M → Word n d) : ClassicalCode n d M where
  encoder m := rcPoint (C m)
  decoder y :=
    if h : (Finset.univ.filter fun j => received (C j) (support y) = y).Nonempty then rcUnif _ h
    else rcUnif Finset.univ ⟨⟨0, hM⟩, Finset.mem_univ _⟩

lemma rcq_det_avg {n d M : ℕ} (hM : 0 < M) (p : ℝ) (C : Fin M → Word n d) :
    classicalAverage p (rcDet hM C) = deterministicAverage p C := by
  unfold classicalAverage deterministicAverage
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold classicalIndividual deterministicIndividual
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : ∑ x : Word n d, ((rcDet hM C).encoder m).val x * ((rcDet hM C).decoder (received x S)).val m =
      ((rcDet hM C).decoder (received (C m) S)).val m := by
    show ∑ x : Word n d, (if x = C m then (1:ℝ) else 0) * _ = _
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']; simp
  rw [h1]
  have hK : (Finset.univ.filter fun j => received (C j) (support (received (C m) S)) = received (C m) S) =
      compatible C S m := by
    unfold compatible
    rw [rcq_supp_received]
    ext j; simp [rc_received_eq]
  have hne : (Finset.univ.filter fun j => received (C j) (support (received (C m) S)) =
      received (C m) S).Nonempty := ⟨m, by simp [rcq_supp_received]⟩
  show patternWeight n p S * ((if h : _ then rcUnif _ h else _ : Distribution (Fin M)).val m) = _
  rw [dif_pos hne]
  show patternWeight n p S * (if m ∈ _ then 1 / ((Finset.univ.filter fun j =>
    received (C j) (support (received (C m) S)) = received (C m) S).card : ℝ) else 0) = _
  rw [if_pos (by simp [rcq_supp_received]), hK]
  ring

lemma rcq_embed_avg {n d M : ℕ} (p : ℝ) (C : ClassicalCode n d M) :
    quantumAverage p (rcEmbed C) = classicalAverage p C := by
  unfold quantumAverage classicalAverage
  simp only [rcq_embed_ind]

theorem rc_main (n d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-Real.exp (-1))*dimensionSuccess n d p M ≤ randomCodingSuccess n d M p ∧
    randomCodingSuccess n d M p ≤ classicalOptimum n d M p ∧
    classicalOptimum n d M p ≤ quantumOptimum n d M p ∧
    quantumOptimum n d M p ≤ dimensionSuccess n d p M ∧
    (∃ C : Fin M → Word n d, randomCodingSuccess n d M p ≤ deterministicAverage p C) ∧
    (∃ C : Fin M → Word n d, 1-deterministicAverage p C ≤ collisionBound n d M p) := by
  have hd1 : 1 ≤ d := by omega
  set Qs := {v : ℝ | ∃ C : QuantumCode n d M,
    v = if false then ⨅ m, quantumIndividual p C m else quantumAverage p C} with hQs
  set Cs := {v : ℝ | ∃ C : ClassicalCode n d M,
    v = if false then ⨅ m, classicalIndividual p C m else classicalAverage p C} with hCs
  have hQ : quantumOptimum n d M p = sSup Qs := rfl
  have hCl : classicalOptimum n d M p = sSup Cs := rfl
  have hQb : BddAbove Qs := ⟨dimensionSuccess n d p M, by
    rintro v ⟨C, rfl⟩
    simp only [Bool.false_eq_true, if_false]
    exact rcq_link4_code hd1 hM hp0 hp1 C⟩
  have hsub : Cs ⊆ Qs := by
    rintro v ⟨C, rfl⟩
    refine ⟨rcEmbed C, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    rw [rcq_embed_avg]
  obtain ⟨C0, hC0⟩ := rc_link5 (n := n) hd1 hM p
  have hmem : deterministicAverage p C0 ∈ Cs := ⟨rcDet hM C0, by
    simp only [Bool.false_eq_true, if_false]; rw [rcq_det_avg]⟩
  have hCne : Cs.Nonempty := ⟨_, hmem⟩
  refine ⟨rc_link1 hd1 hM hp0 hp1, ?_, ?_, ?_, ⟨C0, hC0⟩, rc_link6 hd1 hM hp0 hp1⟩
  · rw [hCl]; exact hC0.trans (le_csSup (hQb.mono hsub) hmem)
  · rw [hCl, hQ]; exact csSup_le_csSup hQb hCne hsub
  · rw [hQ]
    refine csSup_le (hCne.mono hsub) ?_
    rintro v ⟨C, rfl⟩
    simp only [Bool.false_eq_true, if_false]
    exact rcq_link4_code hd1 hM hp0 hp1 C

end

end QAlgorithms.Papers.Independent.Information100.P58

theorem solution (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (1-Real.exp (-1))*QAlgorithms.Papers.Independent.Information100.P58.dimensionSuccess n d p M ≤
      QAlgorithms.Papers.Independent.Information100.P58.randomCodingSuccess n d M p ∧
    QAlgorithms.Papers.Independent.Information100.P58.randomCodingSuccess n d M p ≤
      QAlgorithms.Papers.Independent.Information100.P58.classicalOptimum n d M p ∧
    QAlgorithms.Papers.Independent.Information100.P58.classicalOptimum n d M p ≤
      QAlgorithms.Papers.Independent.Information100.P58.quantumOptimum n d M p ∧
    QAlgorithms.Papers.Independent.Information100.P58.quantumOptimum n d M p ≤
      QAlgorithms.Papers.Independent.Information100.P58.dimensionSuccess n d p M ∧
    (∃ C : Fin M → QAlgorithms.Papers.Independent.Information100.P58.Word n d,
      QAlgorithms.Papers.Independent.Information100.P58.randomCodingSuccess n d M p ≤
        QAlgorithms.Papers.Independent.Information100.P58.deterministicAverage p C) ∧
    (∃ C : Fin M → QAlgorithms.Papers.Independent.Information100.P58.Word n d,
      1-QAlgorithms.Papers.Independent.Information100.P58.deterministicAverage p C ≤
        QAlgorithms.Papers.Independent.Information100.P58.collisionBound n d M p) :=
  QAlgorithms.Papers.Independent.Information100.P58.rc_main n d M hd hM p hp0 hp1
