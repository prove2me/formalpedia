-- Prove2me | solution 1 for ValiantBorder.flatApproxRate
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:30:56.240464+00:00
-- url     : https://prove2.me/submissions/e22fafb3-e7eb-4e03-898e-d4fa674f2629

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_gridComplete
import Theorems.Thm_ValiantBorder_flatNetworkLowerBound

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, the complete-network
polynomial, the flat-case bound, and Appendix N. Sources at commit
11b6c7e3c927df2658f513b6b68ea7f8929c62c5 of `anthropics/formal-math` include
`vp-vnp/Nc/CaseI/Fkl.lean`, `Nc/{LowDegree,PermValiant,Rate/Circuit}.lean` and
`Paper/{Grids,Flat,Rate,Approximate}.lean`. Apache-2.0. -/
namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}

/-- Entry `k` of the list `l` is a variable, a constant, or the sum or product of two earlier entries. -/
def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

/-- `p` is computed by an arithmetic circuit with `s` gates (inputs and constants count as gates). -/
def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

end Nc

namespace Nc

open Finset MvPolynomial

section Approx

variable {F X : Type*} [Field F]

/-- `f` is approximated by a circuit with at most `s` gates: a circuit over the Laurent series in ε computes some
`f + ε * g`, every coefficient of `g` being a power series. -/
def Approximates (f : MvPolynomial X F) (s : ℕ) : Prop :=
  ∃ p : MvPolynomial X (LaurentSeries F), Computes p s ∧
    ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0

end Approx

end Nc

namespace Nc
open Finset MvPolynomial ValiantBorder
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_affIn (o : Option ι) : (1 : MvPolynomial ι F) ∈ affIn (F := F) o := by
  cases o
  · exact Submodule.subset_span rfl
  · exact Submodule.subset_span (by simp)

omit [Fintype ι] [DecidableEq ι] in
theorem C_mem_affIn (o : Option ι) (b : F) : (C b : MvPolynomial ι F) ∈ affIn (F := F) o := by
  have := (affIn (F := F) o).smul_mem b (one_mem_affIn o)
  rwa [MvPolynomial.smul_eq_C_mul, mul_one] at this

omit [Fintype ι] [DecidableEq ι] in
theorem isAffine_of_mem {o : Option ι} {p : MvPolynomial ι F} (h : p ∈ affIn (F := F) o) : IsAffine p := by
  cases o with
  | none =>
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact Or.inl ⟨b, by rw [MvPolynomial.smul_eq_C_mul, mul_one]⟩
  | some i =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
    exact Or.inr ⟨i, a, b, by rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, mul_one]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Substituting affine polynomials into a circuit costs a factor 5. -/
theorem Computes.aeval {κ : Type*} {p : MvPolynomial κ F} {s : ℕ} (h : Computes p s)
    (E : κ → MvPolynomial ι F) (hE : ∀ k, IsAffine (E k)) : Computes (MvPolynomial.aeval E p) (5 * s) := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  have hblock : ∀ n, n < s → ∃ b : ℕ → MvPolynomial ι F, b 4 = MvPolynomial.aeval E (l n) ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := by
    intro n hn
    have hconst : ∀ a : F, ∃ b : ℕ → MvPolynomial ι F, b 4 = C a ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := fun a =>
      ⟨fun _ => C a, rfl, fun m _ hb t ht => Or.inr (Or.inl ⟨a, hb t ht⟩)⟩
    rcases hl n hn with ⟨x, hx⟩ | ⟨a, ha⟩ | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · rw [hx, aeval_X]
      rcases hE x with ⟨b, hb⟩ | ⟨i, a, b, hab⟩
      · rw [hb]
        exact hconst b
      · rw [hab]
        refine ⟨fun t => if t = 0 then C a else if t = 1 then X i else if t = 2 then C a * X i else
          if t = 3 then C b else C a * X i + C b, rfl, fun m _ hm t ht => ?_⟩
        have h0 := hm 0 (by omega)
        have h1 := hm 1 (by omega)
        have h2 := hm 2 (by omega)
        have h3 := hm 3 (by omega)
        have h4 := hm 4 (by omega)
        simp only [if_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, one_ne_zero,
          Nat.reduceEqDiff] at h0 h1 h2 h3 h4
        interval_cases t
        · exact Or.inr (Or.inl ⟨a, h0⟩)
        · exact Or.inl ⟨i, h1⟩
        · exact Or.inr (Or.inr (Or.inr ⟨5 * n + 0, by omega, 5 * n + 1, by omega, by rw [h0, h1, h2]⟩))
        · exact Or.inr (Or.inl ⟨b, h3⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨5 * n + 2, by omega, 5 * n + 3, by omega, by rw [h2, h3, h4]⟩))
    · rw [ha, algHom_C]
      exact hconst a
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inl ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_add]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inr ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_mul]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
  choose! b hb4 hb using hblock
  refine ⟨fun q => b (q / 5) (q % 5), fun q hq => ?_, 5 * k + 4, by omega, ?_⟩
  · have hlt : q % 5 < 5 := Nat.mod_lt _ (by omega)
    have := hb (q / 5) (by omega) (fun q => b (q / 5) (q % 5)) (fun i hi => ?_) (fun t ht => ?_) (q % 5) hlt
    · rwa [Nat.div_add_mod] at this
    · have e1 : (5 * i + 4) / 5 = i := by omega
      have e2 : (5 * i + 4) % 5 = 4 := by omega
      simp only [e1, e2]
      exact hb4 i (by omega)
    · have e1 : (5 * (q / 5) + t) / 5 = q / 5 := by omega
      have e2 : (5 * (q / 5) + t) % 5 = t := by omega
      simp only [e1, e2]
  · have e1 : (5 * k + 4) / 5 = k := by omega
    have e2 : (5 * k + 4) % 5 = 4 := by omega
    simp only [e1, e2]
    exact hb4 k hk

end Nc

namespace Nc

open Finset MvPolynomial ValiantBorder

variable {F X Y : Type*} [Field F]

/-- An affine substitution keeps approximation; the number of gates grows by a factor
at most 5. -/
theorem Approximates.aeval {f : MvPolynomial X F} {s : ℕ} (h : Approximates f s) (M : X → MvPolynomial Y F)
    (hM : ∀ q, IsAffine (M q)) : Approximates (MvPolynomial.aeval M f) (5 * s) := by
  obtain ⟨p, hp, hpf⟩ := h
  refine ⟨MvPolynomial.aeval (fun q => MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) (M q)) p,
    hp.aeval _ fun q => ?_, fun d i hi => ?_⟩
  · rcases hM q with ⟨b, hb⟩ | ⟨j, a, b, hb⟩
    · exact Or.inl ⟨HahnSeries.C b, by rw [hb, map_C]⟩
    · exact Or.inr ⟨j, HahnSeries.C a, HahnSeries.C b, by rw [hb, map_add, map_mul, map_C, map_C, map_X]⟩
  · classical
    have hsub : f.support ⊆ p.support := fun b hb => by
      rw [mem_support_iff] at hb ⊢
      intro h0
      have h1 := hpf b 0 le_rfl
      rw [h0, if_pos rfl] at h1
      exact hb (h1.symm.trans (by simp))
    have e1 : coeff d (MvPolynomial.aeval (fun q => MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) (M q)) p) =
        ∑ b ∈ p.support, coeff b p * HahnSeries.C (coeff d (MvPolynomial.aeval M (monomial b (1 : F)))) := by
      conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_one (coeff b p), ← C_mul_monomial, map_mul, aeval_C, MvPolynomial.algebraMap_eq, coeff_C_mul, mul_one]
      congr 1
      rw [← coeff_map, aeval_monomial, aeval_monomial, map_one, map_one, one_mul, one_mul, map_finsuppProd]
      simp only [map_pow]
    have e2 : coeff d (MvPolynomial.aeval M f) =
        ∑ b ∈ p.support, coeff b f * coeff d (MvPolynomial.aeval M (monomial b (1 : F))) := by
      conv_lhs => rw [f.as_sum, map_sum, coeff_sum]
      rw [Finset.sum_subset hsub (fun b _ hb => by rw [notMem_support_iff.1 hb, monomial_zero, map_zero, coeff_zero])]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_one (coeff b f), ← C_mul_monomial, map_mul, aeval_C, MvPolynomial.algebraMap_eq, coeff_C_mul, mul_one]
    have e3 : ∀ (a : LaurentSeries F) (r : F), (a * HahnSeries.C r).coeff i = a.coeff i * r := by
      intro a r
      rw [mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
    rw [e1, HahnSeries.coeff_sum]
    simp only [e3, hpf _ i hi]
    by_cases h0 : i = 0
    · simp only [if_pos h0, e2]
    · simp [h0]

end Nc
namespace Paper
open Finset MvPolynomial Nc ValiantBorder Nc.CaseI
/-- A clause sum: the sum over the bits of the product over the clauses of the weight of the clause if all its
literals hold, and 1 otherwise. -/
noncomputable def clauseSum {R V K : Type} [CommRing R] [Fintype V] [DecidableEq V] [Fintype K]
    (lits : K → List (V × Bool)) (wt : K → R) : R :=
  ∑ x : V → Bool, ∏ κ, if ∀ l ∈ lits κ, x l.1 = l.2 then wt κ else 1

/-- A clause sum is a projection of every family that is complete for grid sums. -/
theorem clauses_of_complete {F : Type} [Field F] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {c : ℕ}
    (hG : GridComplete F G c) {ι V K : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (lits : K → List (V × Bool)) (hne : ∀ κ, lits κ ≠ []) (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b)
    (wt : K → MvPolynomial ι F) (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : c * ∑ κ, (lits κ).length ≤ S) :
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧ aeval M (G S) = clauseSum lits wt := by
  classical
  let N := Σ κ, Fin (lits κ).length
  let v : N → V := fun n => ((lits n.1).get n.2).1
  let W : N → Bool → Bool → MvPolynomial ι F := fun n x r =>
    if r then (if x = ((lits n.1).get n.2).2 then (if n.2.1 = 0 then wt n.1 - 1 else 1) else 0) else 1
  let o : K → Option ι := fun κ => if h : ∃ i, wt κ = X i then some h.choose else none
  have hwt' : ∀ κ, wt κ ∈ affIn (F := F) (o κ) := by
    intro κ
    by_cases h : ∃ i, wt κ = X i
    · have key : ∀ i, wt κ = X i → wt κ ∈ affIn (F := F) (some i) := fun i e => by
        rw [e]
        exact Submodule.subset_span (by simp)
      rw [show o κ = some h.choose from dif_pos h]
      exact key _ h.choose_spec
    · obtain ⟨a, ha⟩ := (hwt κ).resolve_left h
      rw [ha]
      exact C_mem_affIn _ _
  have hv : Function.Surjective v := by
    intro b
    obtain ⟨κ, l, hl, rfl⟩ := hocc b
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨⟨κ, i⟩, rfl⟩
  have hW : ∀ n x r, W n x r ∈ affIn (F := F) (o n.1) := fun n x r => by
    simp only [W]
    split_ifs
    · exact Submodule.sub_mem _ (hwt' _) (one_mem_affIn _)
    · exact one_mem_affIn _
    · exact Submodule.zero_mem _
    · exact one_mem_affIn _
  obtain ⟨M, hM, he⟩ := hG v (fun n : N => n.1) hv (fun κ => ⟨⟨κ, ⟨0, List.length_pos_iff.2 (hne κ)⟩⟩, rfl⟩) W o
    hW S (by simpa [N] using hS)
  · refine ⟨M, hM, he.trans (Finset.sum_congr rfl fun x _ => ?_)⟩
    have hp : ∀ r : K → Bool, ∏ n : N, W n (x (v n)) (r n.1) =
        ∏ κ, ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) (r κ) := fun r => Fintype.prod_sigma _
    simp only [hp]
    rw [← Fintype.prod_sum fun κ b => ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) b]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have hpos := List.length_pos_iff.2 (hne κ)
    rw [Fintype.sum_bool]
    simp only [W, if_true, Bool.false_eq_true, if_false, Finset.prod_const_one]
    by_cases hall : ∀ l ∈ lits κ, x l.1 = l.2
    · rw [if_pos hall]
      have : ∀ i : Fin (lits κ).length, x ((lits κ).get i).1 = ((lits κ).get i).2 := fun i => hall _ (List.get_mem _ _)
      simp only [v, this, if_true]
      rw [Finset.prod_eq_single (⟨0, hpos⟩ : Fin (lits κ).length)]
      · simp
      · intro i _ hi
        exact if_neg fun h => hi (Fin.ext h)
      · simp
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨l, hl, hne'⟩ := hall
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hne'), zero_add]

/-- The other end of a pair. -/
def pairOf {k : ℕ} (a b : Fin k) (h : b ≠ a) : Pr k :=
  if hab : a < b then ⟨(a, b), hab⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.1 hab) h⟩

theorem asm_pairOf {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a b : Fin k) (h : b ≠ a) :
    asm (fun e _ => σ e) a b = σ (pairOf a b h) := by
  unfold asm pairOf
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h1) (not_lt.1 h2)) h

theorem asm_self {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a : Fin k) :
    asm (fun e _ => σ e) a a = fun _ => false := by
  simp [asm]

/-- A value of σ_a: a table with no string for a itself. -/
abbrev Val (k ℓ : ℕ) := {κ : Fin k × Ix k ℓ // κ.2 κ.1 = fun _ => false}

/-- The literals of the clause σ_a = ρ. -/
noncomputable def fklLits {k ℓ : ℕ} (κ : Val k ℓ) : List ((Pr k × Fin ℓ) × Bool) :=
  (univ : Finset ({b : Fin k // b ≠ κ.1.1} × Fin ℓ)).toList.map fun p =>
    ((pairOf κ.1.1 p.1.1 p.1.2, p.2), κ.1.2 p.1.1 p.2)

/-- The weight x_{a,ρ} of the clause σ_a = ρ. -/
noncomputable def fklWt (F : Type) [Field F] {k ℓ : ℕ} (κ : Val k ℓ) : MvPolynomial (Fin k × Ix k ℓ) F := X κ.1

theorem forall_fklLits {k ℓ : ℕ} (κ : Val k ℓ) (x : Pr k × Fin ℓ → Bool) :
    (∀ l ∈ fklLits κ, x l.1 = l.2) ↔ asm (fun e _ i => x (e, i)) κ.1.1 = κ.1.2 := by
  obtain ⟨⟨a, t⟩, ht⟩ := κ
  constructor
  · intro h
    funext b
    by_cases hb : b = a
    · subst hb
      exact (asm_self (fun e i => x (e, i)) b).trans ht.symm
    · refine (asm_pairOf (fun e i => x (e, i)) a b hb).trans (funext fun i => ?_)
      exact h ((pairOf a b hb, i), t b i) (List.mem_map.2 ⟨(⟨b, hb⟩, i), by simp, rfl⟩)
  · intro h l hl
    obtain ⟨⟨⟨b, hb⟩, i⟩, -, rfl⟩ := List.mem_map.1 hl
    show x (pairOf a b hb, i) = t b i
    exact (congrFun (asm_pairOf (fun e i => x (e, i)) a b hb) i).symm.trans
      (congrFun (congrFun (h : asm (fun e _ i => x (e, i)) a = t) b) i)

/-- "It is the clause sum over the bits of σ in which, for every a and every value ρ of σ_a, the clause saying σ_a = ρ
has the weight x_{a,ρ}." -/
theorem lem_fkl_perm_clauseSum (F : Type) [Field F] (k ℓ : ℕ) :
    clauseSum (fklLits (k := k) (ℓ := ℓ)) (fklWt F) = fkl F k ℓ := by
  classical
  unfold clauseSum fkl
  refine Fintype.sum_equiv (Equiv.curry (Pr k) (Fin ℓ) Bool) _ _ fun x => ?_
  simp only [forall_fklLits, fklWt]
  rw [← Finset.prod_filter]
  refine Finset.prod_bij' (fun κ _ => κ.1.1)
    (fun a _ => ⟨(a, asm (fun e _ i => x (e, i)) a), asm_self (fun e i => x (e, i)) a⟩) ?_ ?_ ?_ ?_ ?_
  · intros
    exact mem_univ _
  · intro a _
    exact mem_filter.2 ⟨mem_univ _, rfl⟩
  · intro κ hκ
    exact Subtype.ext (Prod.ext rfl (mem_filter.1 hκ).2)
  · intros
    rfl
  · intro κ hκ
    exact congrArg X (Prod.ext rfl (mem_filter.1 hκ).2.symm)

theorem fklLits_ne {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (κ : Val k ℓ) : fklLits κ ≠ [] := by
  have h1 : Fintype.card {b : Fin k // b ≠ κ.1.1} = k - 1 := by simp
  have h2 : 0 < (fklLits κ).length := by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, h1, Fintype.card_fin]
    exact Nat.mul_pos (by omega) (by omega)
  exact List.length_pos_iff.1 h2

theorem fklLits_occ {k ℓ : ℕ} (b : Pr k × Fin ℓ) : ∃ κ : Val k ℓ, ∃ l ∈ fklLits κ, l.1 = b := by
  obtain ⟨⟨⟨a, c⟩, hac⟩, i⟩ := b
  refine ⟨⟨(a, fun _ _ => false), rfl⟩, ((pairOf a c (ne_of_gt hac), i), false),
    List.mem_map.2 ⟨(⟨c, ne_of_gt hac⟩, i), by simp, rfl⟩, ?_⟩
  simp only [pairOf, dif_pos (show a < c from hac)]

theorem fklLits_count {k ℓ : ℕ} (hk : 2 ≤ k) : ∑ κ : Val k ℓ, (fklLits κ).length ≤ k ^ 3 * ℓ * 2 ^ (k * ℓ) := by
  have h1 : ∀ κ : Val k ℓ, (fklLits κ).length ≤ k * ℓ := fun κ => by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin k))
  have h2 : Fintype.card (Val k ℓ) ≤ k * 2 ^ (k * ℓ) := by
    refine (Fintype.card_subtype_le _).trans (le_of_eq ?_)
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← pow_mul, mul_comm ℓ k]
  calc ∑ κ : Val k ℓ, (fklLits κ).length ≤ ∑ _κ : Val k ℓ, k * ℓ := Finset.sum_le_sum fun κ _ => h1 κ
    _ = Fintype.card (Val k ℓ) * (k * ℓ) := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ k * 2 ^ (k * ℓ) * (k * ℓ) := Nat.mul_le_mul_right _ h2
    _ = k ^ 2 * ℓ * 2 ^ (k * ℓ) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))

/-- The form of Lemma lem:fkl-perm for every family that is complete for grid sums: if M ≥ κk³ℓ2^(kℓ), then f_{k,ℓ} is a
projection of G_M with affine entries. -/
theorem fkl_complete {F : Type} [Field F] {G : ∀ M, MvPolynomial (Fin M × Fin M) F} {κ : ℕ}
    (hG : GridComplete F G κ) {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {M : ℕ}
    (hM : κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ M) :
    ∃ E : Fin M × Fin M → MvPolynomial (Fin k × Ix k ℓ) F, (∀ q, IsAffine (E q)) ∧ aeval E (G M) = fkl F k ℓ := by
  obtain ⟨E, hE, he⟩ := clauses_of_complete hG fklLits (fklLits_ne hk hℓ) fklLits_occ (fklWt F)
    (fun κ => Or.inl ⟨κ.1, rfl⟩) (S := M) (le_trans (le_trans (Nat.mul_le_mul_left _ (fklLits_count hk))
      (le_of_eq (by ring))) hM)
  exact ⟨E, hE, he.trans (lem_fkl_perm_clauseSum F k ℓ)⟩

theorem rate_pow {k ℓ s : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s) (h : (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow,
    ← Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hs)]
  have : (0 : ℝ) ≤ (ℓ : ℝ) * (k * √k) := by positivity
  linarith

theorem exists_cube_root (B : ℕ) : ∃ r, 200 * r ^ 3 ≤ B ∧ B < 200 * (r + 1) ^ 3 := by
  classical
  have hex : ∃ r, B < 200 * (r + 1) ^ 3 := ⟨B, by
    have : B + 1 ≤ (B + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · simp [h0]
  · have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h0] at h1
    omega

/-- The proof of Theorem thm:flat-rate for anything that gives circuits for f_{k,ℓ} with five times as many gates
once m ≥ κk³ℓ2^(kℓ): r is largest with 200r³ ≤ ⌊log m⌋, k = r², ℓ = 100r. -/
theorem rate_of_projection (κ : ℕ) : ∃ m₀ : ℕ, ∀ P : ℕ → ℕ → Prop,
    (∀ k ℓ m s : ℕ, 2 ≤ k → 1 ≤ ℓ → 100 * √k ≤ (ℓ : ℝ) → κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ m → P m s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ ((5 * s : ℕ) : ℝ)) →
    ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  refine ⟨2 ^ (200 * (κ + 3) ^ 3), fun P hP m hm s hs => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Nat.log 2 m := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    have : 1 ≤ 2 ^ (200 * (κ + 3) ^ 3) := Nat.one_le_two_pow
    omega
  have hB1 : 200 * (κ + 3) ^ 3 ≤ B := hB ▸ Nat.le_log_of_pow_le (by norm_num) hm
  obtain ⟨r, hr1, hr2⟩ := exists_cube_root B
  have hr : κ + 2 ≤ r := by
    by_contra hlt
    have : (r + 1) ^ 3 ≤ (κ + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hmL : 2 ^ B ≤ m := hB ▸ Nat.pow_log_le_self 2 hm0
  have hmU : m < 2 ^ (B + 1) := hB ▸ Nat.lt_pow_succ_log_self (by norm_num) m
  have hfit : κ * (r ^ 2) ^ 3 * (100 * r) * 2 ^ (r ^ 2 * (100 * r)) ≤ 2 ^ (200 * r ^ 3) := by
    have a1 : κ ≤ 2 ^ r := (Nat.lt_two_pow_self (n := κ)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have a2 : (r ^ 2) ^ 3 ≤ 2 ^ (6 * r) := by
      rw [← pow_mul, show (2 : ℕ) * 3 = 6 from rfl, Nat.mul_comm 6 r, pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := r)).le 6
    have a3 : 100 * r ≤ 2 ^ (100 * r) := (Nat.lt_two_pow_self).le
    have h2 : κ * (r ^ 2) ^ 3 * (100 * r) ≤ 2 ^ (100 * r ^ 3) := by
      calc κ * (r ^ 2) ^ 3 * (100 * r) ≤ 2 ^ r * 2 ^ (6 * r) * 2 ^ (100 * r) :=
            Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3
        _ = 2 ^ (107 * r) := by rw [← pow_add, ← pow_add]; congr 1; ring
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul hr hr])
    rw [show r ^ 2 * (100 * r) = 100 * r ^ 3 by ring]
    calc κ * (r ^ 2) ^ 3 * (100 * r) * 2 ^ (100 * r ^ 3) ≤ 2 ^ (100 * r ^ 3) * 2 ^ (100 * r ^ 3) :=
          Nat.mul_le_mul_right _ h2
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
  have hsq : √((r ^ 2 : ℕ) : ℝ) = r := by push_cast; exact Real.sqrt_sq (by linarith)
  have hlow := hP (r ^ 2) (100 * r) m s (le_trans (by omega : 2 ≤ r) (Nat.le_self_pow (by norm_num) r)) (by omega)
    (by rw [hsq]; push_cast; exact le_rfl) (hfit.trans ((Nat.pow_le_pow_right (by norm_num) hr1).trans hmL)) hs
  have hs0 : (0 : ℝ) < s := by
    have := (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) _).trans_le hlow
    push_cast at this
    linarith
  have hk0 : (0 : ℝ) < ((r ^ 2 : ℕ) : ℝ) := by push_cast; positivity
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow, hsq] at hlow
  push_cast at hlow
  rw [← Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.logb_mul (by norm_num) hs0.ne'] at hlow
  have h5 : Real.logb 2 5 ≤ 3 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    norm_num
  have hlM : Real.logb 2 m ≤ 1600 * (r : ℝ) ^ 3 := by
    have h1 : B + 1 ≤ 1600 * r ^ 3 := by
      have h2 : (r + 1) ^ 3 ≤ (2 * r) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      rw [mul_pow] at h2
      omega
    have h3 : Real.logb 2 m ≤ ((B + 1 : ℕ) : ℝ) := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hm0), Real.rpow_natCast]
      exact_mod_cast hmU.le
    exact h3.trans (by exact_mod_cast h1)
  have hl0 : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hpow : Real.logb 2 m ^ (4 / 3 : ℝ) ≤ 1600 ^ 2 * (r : ℝ) ^ 4 := by
    refine (Real.rpow_le_rpow hl0 hlM (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    refine mul_le_mul ?_ (le_of_eq ?_) (by positivity) (by norm_num)
    · calc (1600 : ℝ) ^ (4 / 3 : ℝ) ≤ (1600 : ℝ) ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = _ := Real.rpow_natCast _ 2
    · rw [← Real.rpow_natCast (r : ℝ) 3, ← Real.rpow_mul (by linarith)]
      norm_num
  have h4 : (16 : ℝ) ≤ (r : ℝ) ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hrR 4
  rw [← Real.lt_logb_iff_rpow_lt (by norm_num) hs0, div_lt_iff₀ (by norm_num)]
  nlinarith

end Paper
open ValiantBorder Paper Nc.CaseI
theorem solution (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Paper.Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, ValiantBorder.GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Statement.Approximates (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := rate_of_projection κ
  refine ⟨m₀, fun K _ hK G hG => h _ fun k ℓ m s hk hℓ hℓk hm hs => ?_⟩
  obtain ⟨E, hE, he⟩ := fkl_complete hG hk hℓ hm
  change Nc.Approximates (G m) s at hs
  have hap : Nc.Approximates (fkl K k ℓ) (5 * s) := he ▸ hs.aeval E hE
  refine rate_pow hk ?_ (ValiantBorder.flatNetworkLowerBound hK hk hℓk hap)
  obtain ⟨Q, ⟨l, -, a, ha, -⟩, -⟩ := hap
  omega

