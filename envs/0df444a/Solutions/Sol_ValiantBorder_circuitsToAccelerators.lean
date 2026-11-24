-- Prove2me | solution 1 for ValiantBorder.circuitsToAccelerators
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:15.59795+00:00
-- url     : https://prove2.me/submissions/3668e41a-5005-4f7f-9f8a-156bb99ec1fc

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_universalGridProjection
import Theorems.Thm_ValiantBorder_boundedDegreeCircuitProgram
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math`, revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The compiler, universal grid projection, and Laurent approximation arguments appear
in `Paper/Circuit.lean`, `Paper/LowDeg.lean` and `Paper/ApproxScales.lean`. Apache-2.0. -/
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
namespace LaurentTransferProof

open MvPolynomial

def IsStep {R X : Type*} [CommSemiring R] (l : ℕ → MvPolynomial X R) (k : ℕ) : Prop :=
  (∃ v : X, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

def Computes {R X : Type*} [CommSemiring R] (f : MvPolynomial X R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial X R, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = f

theorem Computes.map {R S X : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {f : MvPolynomial X R} {s : ℕ} (h : Computes f s) :
    Computes (MvPolynomial.map φ f) s := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  refine ⟨fun i => MvPolynomial.map φ (l i), ?_, k, hk, rfl⟩
  intro j hj
  rcases hl j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, t, ht, he⟩ | ⟨i, hi, t, ht, he⟩
  · exact Or.inl ⟨v, by simp [hv]⟩
  · exact Or.inr (Or.inl ⟨φ a, by simp [ha]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, by simp [he]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, by simp [he]⟩))

def Approximates {R X : Type*} [Field R] (f : MvPolynomial X R) (s : ℕ) : Prop :=
  ∃ q : MvPolynomial X (LaurentSeries R), Computes q s ∧
    ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d q).coeff i = if i = 0 then coeff d f else 0


open MvPolynomial

section Steps

variable {A R X : Type*} [CommSemiring A] [CommSemiring R]

/-- A circuit with t gates is extended by one gate g, which is a variable, a constant, or the sum or product of two of
the t gates. -/
theorem isStep_update {L : ℕ → MvPolynomial X A} {t : ℕ} (h : ∀ k < t, IsStep L k) {g : MvPolynomial X A}
    (hg : (∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨ (∃ i < t, ∃ j < t, g = L i + L j) ∨
      (∃ i < t, ∃ j < t, g = L i * L j)) :
    ∀ k < t + 1, IsStep (Function.update L t g) k := by
  have e : ∀ i < t, Function.update L t g i = L i := fun i hi => Function.update_of_ne (by omega) _ _
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · rcases h k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [e k hk, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [e k hk, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
  · rcases hg with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [Function.update_self, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [Function.update_self, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))

/-- A circuit over R all of whose constants are images of elements of A under a homomorphism φ is the image under φ,
gate by gate, of a circuit over A. -/
theorem exists_lift_steps (φ : A →+* R) {l : ℕ → MvPolynomial X R} {s : ℕ} (hl : ∀ k < s, IsStep l k)
    (hc : ∀ k < s, ∀ c, l k = C c → c ∈ Set.range φ) :
    ∃ L : ℕ → MvPolynomial X A, (∀ k < s, IsStep L k) ∧ ∀ k < s, map φ (L k) = l k := by
  induction s with
  | zero => exact ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨L, hL, hm⟩ := ih (fun k hk => hl k (by omega)) (fun k hk => hc k (by omega))
    have key : ∃ g : MvPolynomial X A, ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧ map φ g = l t := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, by rw [h1, map_X]⟩
      · obtain ⟨a, rfl⟩ := hc t (by omega) c h1
        exact ⟨C a, Or.inr (Or.inl ⟨a, rfl⟩), by rw [h1, map_C]⟩
      · exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_add, hm i hi, hm j hj]⟩
      · exact ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_mul, hm i hi, hm j hj]⟩
    obtain ⟨g, hg, hgm⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega), hm k hk]
    · rw [Function.update_self, hgm]

end Steps

section Series

variable {F : Type*} [CommRing F]

/-- A Laurent polynomial in ε, read as a Laurent series in ε. -/
noncomputable def laurentToSeries (F : Type*) [CommRing F] : LaurentPolynomial F →+* LaurentSeries F :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_laurentToSeries (x : LaurentPolynomial F) (i : ℤ) :
    (laurentToSeries F x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    classical
    rw [laurentToSeries, AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : F)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]

/-- Every Laurent series agrees below any given power ε ^ n with a Laurent polynomial. -/
theorem exists_laurentPolynomial_coeff (c : LaurentSeries F) (n : ℤ) :
    ∃ c' : LaurentPolynomial F, ∀ i < n, c'.coeff i = c.coeff i := by
  refine ⟨.ofCoeff (Finsupp.onFinset (Finset.Ico c.order n) (fun i => if i < n then c.coeff i else 0) ?_), ?_⟩
  · intro i hi
    by_cases h : i < n
    · rw [if_pos h] at hi
      refine Finset.mem_Ico.2 ⟨?_, h⟩
      by_contra h'
      exact hi (HahnSeries.coeff_eq_zero_of_lt_order (not_le.1 h'))
    · exact absurd (if_neg h) hi
  · intro i hi
    simp [hi]

end Series

section Order

variable {F : Type*} [CommRing F] {X : Type*}

/-- All coefficients of the polynomial u are Laurent series without terms below ε ^ n. -/
def OrdGe (n : ℤ) (u : MvPolynomial X (LaurentSeries F)) : Prop :=
  ∀ (d : X →₀ ℕ) (i : ℤ), i < n → (coeff d u).coeff i = 0

theorem OrdGe.mono {m n : ℤ} {u : MvPolynomial X (LaurentSeries F)} (h : OrdGe n u) (hmn : m ≤ n) : OrdGe m u :=
  fun d i hi => h d i (by omega)

theorem OrdGe.zero (n : ℤ) : OrdGe n (0 : MvPolynomial X (LaurentSeries F)) := fun d i _ => by simp

theorem OrdGe.add {n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe n u) (hv : OrdGe n v) :
    OrdGe n (u + v) := fun d i hi => by rw [coeff_add, HahnSeries.coeff_add, hu d i hi, hv d i hi, add_zero]

/-- The product of a series without terms below ε ^ m and one without terms below ε ^ n has none below ε ^ (m + n). -/
theorem coeff_mul_eq_zero {m n : ℤ} {x y : LaurentSeries F} (hx : ∀ i < m, x.coeff i = 0)
    (hy : ∀ i < n, y.coeff i = 0) {i : ℤ} (hi : i < m + n) : (x * y).coeff i = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have h := (Finset.mem_antidiagonal.1 hij).2.2
  by_cases h1 : ij.1 < m
  · rw [hx _ h1, zero_mul]
  · rw [hy ij.2 (by omega), mul_zero]

theorem OrdGe.mul {m n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe m u) (hv : OrdGe n v) :
    OrdGe (m + n) (u * v) := fun d i hi => by
  classical
  rw [coeff_mul, HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun x _ => coeff_mul_eq_zero (hu x.1) (hv x.2) hi

/-- The poles of the coefficients of finitely many polynomials over the Laurent series have bounded order. -/
theorem exists_ordGe (l : ℕ → MvPolynomial X (LaurentSeries F)) (s : ℕ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ k < s, OrdGe (-B) (l k) := by
  have one : ∀ u : MvPolynomial X (LaurentSeries F), ∃ B : ℤ, 0 ≤ B ∧ OrdGe (-B) u := by
    intro u
    induction u using MvPolynomial.induction_on' with
    | monomial e a =>
      refine ⟨|a.order|, abs_nonneg _, fun d i hi => ?_⟩
      classical
      rw [coeff_monomial]
      split_ifs
      · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (neg_abs_le _))
      · rfl
    | add p q hp hq =>
      obtain ⟨B, hB, h⟩ := hp
      obtain ⟨B', hB', h'⟩ := hq
      exact ⟨B + B', by omega, (h.mono (by omega)).add (h'.mono (by omega))⟩
  induction s with
  | zero => exact ⟨0, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨B, hB, h⟩ := ih
    obtain ⟨B', hB', h'⟩ := one (l t)
    refine ⟨B + B', by omega, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (h k hk).mono (by omega)
    · exact h'.mono (by omega)

end Order

section Truncate

variable {F : Type*} [CommRing F] {X : Type*}

/-- If every constant of a circuit over the Laurent series is cut off
at a sufficiently high power of ε, every gate changes only by terms from ε ^ n on: for every circuit over the Laurent
series and every n there is a circuit of the same shape over the Laurent polynomials whose gates differ from the given
ones by polynomials all of whose coefficients have no terms below ε ^ n. -/
theorem exists_truncated_steps {l : ℕ → MvPolynomial X (LaurentSeries F)} {s : ℕ} (hl : ∀ k < s, IsStep l k) (n : ℤ) :
    ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < s, IsStep L k) ∧
      ∀ k < s, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r := by
  obtain ⟨B, hB, hlB⟩ := exists_ordGe l s
  suffices H : ∀ t ≤ s, ∀ n : ℤ, 0 ≤ n → ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < t, IsStep L k) ∧
      ∀ k < t, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r by
    obtain ⟨L, hL, h⟩ := H s le_rfl |n| (abs_nonneg n)
    exact ⟨L, hL, fun k hk => let ⟨r, hr, e⟩ := h k hk; ⟨r, hr.mono (le_abs_self n), e⟩⟩
  intro t
  induction t with
  | zero =>
    exact fun _ _ _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    intro ht n hn
    obtain ⟨L, hL, hr⟩ := ih (by omega) (n + B) (by omega)
    have key : ∃ g : MvPolynomial X (LaurentPolynomial F), ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧
        ∃ r, OrdGe n r ∧ map (laurentToSeries F) g = l t + r := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, 0, OrdGe.zero n, by rw [h1, map_X, add_zero]⟩
      · obtain ⟨c', hc'⟩ := exists_laurentPolynomial_coeff c n
        refine ⟨C c', Or.inr (Or.inl ⟨c', rfl⟩), C (laurentToSeries F c' - c), fun d i hi => ?_, ?_⟩
        · classical
          rw [coeff_C]
          split_ifs
          · rw [HahnSeries.coeff_sub, coeff_laurentToSeries, hc' i hi, sub_self]
          · rfl
        · rw [h1, map_C, ← C_add, add_sub_cancel]
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), ri + rj,
          (hri.add hrj).mono (by omega), by rw [h1, map_add, ei, ej]; ring⟩
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        refine ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), ri * l j + l i * rj + ri * rj,
          ((?_ : OrdGe n _).add ?_).add ?_, by rw [h1, map_mul, ei, ej]; ring⟩
        · exact (hri.mul (hlB j (by omega))).mono (by omega)
        · exact ((hlB i (by omega)).mul hrj).mono (by omega)
        · exact (hri.mul hrj).mono (by omega)
    obtain ⟨g, hg, hgr⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      obtain ⟨r, h, e⟩ := hr k hk
      exact ⟨r, h.mono (by omega), e⟩
    · rw [Function.update_self]
      exact hgr

end Truncate

section Approx

variable {F X : Type*} [Field F] {s : ℕ}

/-- A polynomial f that is approximated by a circuit with s gates is approximated
by one whose constants are Laurent polynomials in ε: this circuit computes a polynomial p over the Laurent polynomials
in which no negative power of ε occurs and in which the terms without ε are those of f. -/
theorem Approximates.exists_laurentPolynomial {f : MvPolynomial X F} (h : Approximates f s) :
    ∃ p : MvPolynomial X (LaurentPolynomial F), Computes p s ∧
      ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0 := by
  obtain ⟨_, ⟨l, hl, k, hk, rfl⟩, hp⟩ := h
  obtain ⟨L, hL, hr⟩ := exists_truncated_steps hl 1
  obtain ⟨r, hr, e⟩ := hr k hk
  refine ⟨L k, ⟨L, hL, k, hk, rfl⟩, fun d i hi => ?_⟩
  rw [← hp d i hi, ← coeff_laurentToSeries, ← coeff_map, e, coeff_add, HahnSeries.coeff_add, hr d i (by omega), add_zero]

end Approx


open MvPolynomial
end LaurentTransferProof
namespace Nc.Acc
open Finset
variable {F σ : Type*} [CommRing F]
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

theorem sum_coeff_eq_eval (u : σ → F) (p : MvPolynomial σ F) {d n : ℕ} (hd : p.totalDegree ≤ d) (hn : d < n) :
    ∑ i ∈ range n, (line u p).coeff i = MvPolynomial.eval u p := by
  have hdeg : (line u p).natDegree ≤ d := by
    have := MvPolynomial.aeval_natDegree_le p hd
      (fun i => Polynomial.C (u i) * Polynomial.X) (n := 1)
      (fun i => (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    simpa [line] using this
  rw [← eval_one_line, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg hn)]
  simp

end Nc.Acc
namespace NS1
open LaurentPolynomial
variable {A E : Type} [CommRing A] [CommRing E] [Algebra A E]
theorem coeff_algebraMap (a : A) (i : ℤ) :
    (algebraMap A E[T;T⁻¹] a).coeff i = if i = 0 then algebraMap A E a else 0 := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem exists_coeff_mul_ne_zero {P Q : E[T;T⁻¹]} {i : ℤ} (h : (P * Q).coeff i ≠ 0) :
    ∃ a b, P.coeff a ≠ 0 ∧ Q.coeff b ≠ 0 ∧ a + b = i := by
  classical
  rw [AddMonoidAlgebra.coeff_mul] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  refine ⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, ?_⟩
  by_contra hne
  exact h2 (if_neg hne)

theorem OrdGE.zero (r : ℤ) : OrdGE r (0 : E[T;T⁻¹]) := fun i _ => by simp

theorem OrdGE.mono {r s : ℤ} {P : E[T;T⁻¹]} (h : OrdGE r P) (hs : s ≤ r) : OrdGE s P :=
  fun i hi => h i (lt_of_lt_of_le hi hs)

theorem OrdGE.add {r : ℤ} {P Q : E[T;T⁻¹]} (h : OrdGE r P) (h' : OrdGE r Q) : OrdGE r (P + Q) :=
  fun i hi => by simp [h i hi, h' i hi]

theorem OrdGE.mul {r s : ℤ} {P Q : E[T;T⁻¹]} (h : OrdGE r P) (h' : OrdGE s Q) : OrdGE (r + s) (P * Q) := by
  intro i hi
  by_contra hne
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coeff_mul_ne_zero hne
  have h1 : r ≤ a := by
    by_contra h1
    exact ha (h a (by omega))
  have h2 : s ≤ b := by
    by_contra h2
    exact hb (h' b (by omega))
  omega

theorem OrdGE.list_sum {r : ℤ} {l : List E[T;T⁻¹]} (h : ∀ P ∈ l, OrdGE r P) : OrdGE r l.sum := by
  induction l with
  | nil => simpa using OrdGE.zero r
  | cons P l ih =>
    rw [List.sum_cons]
    exact (h P List.mem_cons_self).add (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

theorem OrdGE.of_algebraMap (a : A) : OrdGE 0 (algebraMap A E[T;T⁻¹] a) := fun i hi => by
  rw [coeff_algebraMap, if_neg hi.ne]

end NS1
namespace NS1

open _root_.NS1.Tree

section Values

open LaurentPolynomial

variable {A : Type} [CommRing A] {E : Type} [CommRing E] [Algebra A E]

/-- All coefficients are without terms below ε ^ r. -/
def PolyOrdGE (r : ℤ) (P : Polynomial E[T;T⁻¹]) : Prop := ∀ i, OrdGE r (P.coeff i)

theorem PolyOrdGE.mul {r s : ℤ} {P Q : Polynomial E[T;T⁻¹]} (hP : PolyOrdGE r P) (hQ : PolyOrdGE s Q) :
    PolyOrdGE (r + s) (P * Q) := by
  intro i
  rw [Polynomial.coeff_mul, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨ab, -, rfl⟩ := hx
  exact (hP _).mul (hQ _)

theorem polyOrdGE_C {r : ℤ} {a : E[T;T⁻¹]} (h : OrdGE r a) : PolyOrdGE r (Polynomial.C a) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact OrdGE.zero r

theorem ordGE_one : OrdGE 0 (1 : E[T;T⁻¹]) := by
  simpa using OrdGE.of_algebraMap (E := E) (1 : E)

/-- **The parts of a small error stay small** at points whose coordinates have no poles. -/
theorem ordGE_line_coeff {σ : Type} {u : σ → E[T;T⁻¹]} (hu : ∀ i, OrdGE 0 (u i))
    {r : MvPolynomial σ E[T;T⁻¹]} (hr : ∀ d, OrdGE 1 (MvPolynomial.coeff d r)) (i : ℕ) :
    OrdGE 1 ((Nc.Acc.line u r).coeff i) := by
  classical
  have hpow : ∀ (l : σ) (k : ℕ), PolyOrdGE 0 ((Polynomial.C (u l) * Polynomial.X) ^ k) := by
    intro l k
    induction k with
    | zero => simpa using polyOrdGE_C (ordGE_one (E := E))
    | succ k ih =>
      rw [pow_succ]
      refine ih.mul (s := 0) fun j => ?_
      rw [Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hu l
      · exact OrdGE.zero 0
  have hprod : ∀ d : σ →₀ ℕ, PolyOrdGE 0 (d.prod fun l k => (Polynomial.C (u l) * Polynomial.X) ^ k) := fun d =>
    Finset.prod_induction _ (PolyOrdGE 0) (fun P Q hP hQ => hP.mul hQ) (polyOrdGE_C ordGE_one) fun l _ => hpow l _
  rw [r.as_sum, map_sum, Polynomial.finsetSum_coeff, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨d, -, rfl⟩ := hx
  rw [Nc.Acc.line, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  exact ((polyOrdGE_C (hr d)).mul (hprod d)) i

theorem ordGE_codeB (N : ℕ) (w : List Bool) (q : Fin N × Option Bool) : OrdGE 0 (codeB E[T;T⁻¹] N w q) := by
  unfold codeB
  split_ifs
  · exact ordGE_one
  · exact OrdGE.zero 0

/-- **Paper: proof of Theorem thm:approx, the parts of an approximated polynomial approximate its value.** -/
theorem ordGE_sum_coeff_sub {N d n : ℕ} {f : MvPolynomial (Fin N × Option Bool) E}
    {p : MvPolynomial (Fin N × Option Bool) E[T;T⁻¹]}
    (hp : ∀ e (i : ℤ), i ≤ 0 → (MvPolynomial.coeff e p).coeff i = if i = 0 then MvPolynomial.coeff e f else 0)
    (hd : f.totalDegree ≤ d) (hn : d < n) (w : List Bool) (a : A)
    (hval : MvPolynomial.eval (codeB E N w) f = algebraMap A E a) :
    OrdGE 1 (∑ i ∈ Finset.range n, (Nc.Acc.line (codeB E[T;T⁻¹] N w) p).coeff i - algebraMap A E[T;T⁻¹] a) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = algebraMap E E[T;T⁻¹] := ⟨_, rfl⟩
  have hdiff : ∀ e, OrdGE 1 (MvPolynomial.coeff e (p - MvPolynomial.map φ f)) := by
    intro e i hi
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp e i (by omega),
      hφ, coeff_algebraMap, Algebra.algebraMap_self_apply]
    exact sub_self _
  have hu : (codeB E[T;T⁻¹] N w) = φ ∘ codeB E N w := by
    funext q
    simp only [Function.comp_apply, codeB]
    split_ifs <;> simp
  have hf : ∑ i ∈ Finset.range n, (Nc.Acc.line (codeB E[T;T⁻¹] N w) (MvPolynomial.map φ f)).coeff i =
      algebraMap A E[T;T⁻¹] a := by
    rw [Nc.Acc.sum_coeff_eq_eval _ _ ((Finset.sup_mono (MvPolynomial.support_map_subset φ f)).trans hd) hn, hu]
    have h1 : MvPolynomial.eval (φ ∘ codeB E N w) (MvPolynomial.map φ f) = φ (MvPolynomial.eval (codeB E N w) f) :=
      (MvPolynomial.map_eval φ (codeB E N w) f).symm
    rw [h1, hval, hφ, ← IsScalarTower.algebraMap_apply]
  rw [← hf, ← Finset.sum_sub_distrib, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rw [← Polynomial.coeff_sub, ← map_sub]
  exact ordGE_line_coeff (ordGE_codeB N w) hdiff i

end Values

end NS1

namespace Paper
open Nc.Acc in
/-- The part of degree i is what the point scales by the ith power. -/
theorem line_coeff_eq {R σ : Type} [CommRing R] (u : σ → R) (p : MvPolynomial σ R) (i : ℕ) :
    (line u p).coeff i = MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_monomial a rfl : (MvPolynomial.monomial d a).IsHomogeneous d.degree))]
    have e : line u (MvPolynomial.monomial d a) =
        Polynomial.C (MvPolynomial.eval u (MvPolynomial.monomial d a)) * Polynomial.X ^ d.degree := by
      simp only [line, MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
      simp [Finsupp.degree, mul_assoc]
      rfl
    rw [e, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

end Paper
open NS1 MvPolynomial LaurentPolynomial
private theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := Nat.succ_le_succ (Nat.log_mono_right h)

private theorem le_lg_pow {n k : ℕ} (hn : n ≠ 0) : k * (lg n - 1) + 1 ≤ lg (n ^ k) := by
  unfold lg
  rw [Nat.add_sub_cancel]
  refine Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) ?_)
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) k

private theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) h)

private theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn

/-- Powers of the logarithm are small. -/
private theorem poly_lg (c k : ℕ) : ∃ n₀, ∀ n, n₀ ≤ n → c * lg n ^ k ≤ n := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
  have h2 : ∀ᶠ L : ℕ in Filter.atTop, (L : ℝ) ^ k / 2 ^ L < 1 / (2 * (c + 1)) :=
    h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 h2
  refine ⟨2 ^ L₀ + 1, fun n hn => ?_⟩
  have hp : 1 ≤ 2 ^ L₀ := Nat.one_le_two_pow
  have hn0 : n ≠ 0 := by omega
  have hL : L₀ ≤ lg n := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have h3 := hL₀ (lg n) hL
  have h4 := two_pow_lg_le hn0
  have hlg : 1 ≤ lg n := by unfold lg; omega
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  have h5 : (c : ℝ) * (lg n : ℝ) ^ k ≤ 2 ^ (lg n - 1) := by
    have e : (2 : ℝ) ^ lg n = 2 * 2 ^ (lg n - 1) := by
      have : lg n = lg n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [e] at h3
    have : (0 : ℝ) ≤ (lg n : ℝ) ^ k := by positivity
    nlinarith
  have h6 : c * lg n ^ k ≤ 2 ^ (lg n - 1) := by exact_mod_cast h5
  exact h6.trans h4

private theorem lg_ge_two {u : ℕ} (hu : 4 ≤ u) : 2 ≤ lg u := le_trans (by norm_num) (le_lg_of_two_pow_le (k := 2) (by omega))
private theorem lem_circuit_names {H v a k : ℕ} (hv : 4 ≤ v) (hk : k ≤ (3 * a + H + 20) * lg v) :
    k ≤ lg (max (v ^ H) (v ^ (3 * a + H + 20))) ^ 2 := by
  have hl := lg_ge_two hv
  obtain ⟨l, hl'⟩ : ∃ l, lg v = l + 1 := ⟨Nat.log 2 v, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = lg (max (v ^ H) (v ^ (3 * a + H + 20))) := ⟨_, rfl⟩
  have h1 : (3 * a + H + 20) * l + 1 ≤ X := by
    rw [hX]
    refine le_trans ?_ (lg_mono (le_max_right _ _))
    have := le_lg_pow (n := v) (k := 3 * a + H + 20) (by omega)
    rw [hl', Nat.add_sub_cancel] at this
    exact this
  have h2 : (3 * a + H + 20) * 1 ≤ (3 * a + H + 20) * l := Nat.mul_le_mul_left _ (by omega)
  have h3 : (3 * a + H + 20) * (l + 1) ≤ 2 * X := by rw [mul_add]; omega
  rw [← hX, pow_two]
  rw [hl'] at hk
  exact hk.trans (h3.trans (Nat.mul_le_mul_right _ (by omega)))

/-- The arithmetic of the constants of Lemma lem:circuit. -/
private theorem lem_circuit_bound {c H v a : ℕ} (hc : c + H + 8 + 1 ≤ lg v) (h0 : c * (H + 7) * lg v ≤ v)
    (hl : lg v ^ ((H + 35) * a) ≤ v) : c * (a + 5 + H + 2) * lg v ≤ v := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine le_trans (le_of_eq ?_) h0
    ring
  · have h6 : a + 5 + H + 2 ≤ lg v * lg v ^ a := by
      calc a + 5 + H + 2 ≤ lg v * 2 ^ a := by
            have : a < 2 ^ a := Nat.lt_two_pow_self
            nlinarith
        _ ≤ lg v * lg v ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (show c ≤ lg v by omega) h6)) (le_trans ?_ hl)
    calc lg v * (lg v * lg v ^ a) * lg v = lg v ^ (a + 3) := by ring
      _ ≤ lg v ^ ((H + 35) * a) := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem solution {F : Type} [Field F] (A : Subring F) (θ : List Bool → A)
    (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ C v₀ : ℕ, 0 < B₀ ∧ ∀ (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      ValiantBorder.GridComplete F G κ → ∀ v, v₀ ≤ v → ∀ a, NS1.lg v ^ (C * a) ≤ v → ∀ m, v ^ B₀ ≤ m →
        Statement.Approximates (G m) (v ^ a) → NS1.HasAccA θ F H v (v ^ (C * (a + 1))) := by
  obtain ⟨B₀, Z, hB₀, hproj⟩ := ValiantBorder.universalGridProjection hθ hH κ
  obtain ⟨c, hc⟩ := ValiantBorder.boundedDegreeCircuitProgram H hH
  obtain ⟨n₀, hn₀⟩ := poly_lg (c * (H + 7)) 1
  refine ⟨B₀, H + 35, Z + n₀ + 2 ^ (c + H + 8) + 100, hB₀, fun G hG v hv a hl m hm hs => ?_⟩
  have hp := Nat.one_le_two_pow (n := c + H + 8)
  have hlv : c + H + 8 + 1 ≤ lg v := le_lg_of_two_pow_le (by omega)
  have hcv := lem_circuit_bound hlv (by simpa using hn₀ v (by omega)) hl
  obtain ⟨Mat, hMat, hdeg, hev⟩ := hproj F G hG v m (by omega) hm
  have hgates : 5 * v ^ a ≤ v ^ (a + 5) := by
    rw [pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (le_trans (by omega : 5 ≤ v) (Nat.le_self_pow (by norm_num) v))
  obtain ⟨p, hp', hpf⟩ := LaurentTransferProof.Approximates.exists_laurentPolynomial (Nc.Approximates.aeval (f := G m) hs Mat hMat)
  obtain ⟨K, D, hD, hn, hsz, hht⟩ := hc v (a + 5) (by omega) hcv A F[T;T⁻¹] θ (5 * v ^ a) p hgates hp'
  have hle : v ^ (3 * (a + 5) + H + 20) ≤ v ^ ((H + 35) * (a + 1)) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hlg := lg_mono (max_le_max (le_refl (v ^ H)) hle)
  refine ⟨K, 1, D, ⟨fun z hz => ⟨(hD z hz).1, (hD z hz).2.1⟩, fun z hz hpl => ?_⟩, hn.trans hle, hsz.trans hle,
    (lem_circuit_names (by omega) hht).trans (Nat.pow_le_pow_left hlg 2), Nat.one_le_pow _ _ (Nat.succ_pos _)⟩
  rw [(hD z hz).2.2, ← Finset.sum_congr rfl (fun i _ => Paper.line_coeff_eq _ p i)]
  exact ordGE_sum_coeff_sub hpf hdeg (by omega) _ _ (hev z hz hpl)

