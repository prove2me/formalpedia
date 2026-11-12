-- Prove2me | solution 1 for SumsHighPowers.PITLifting.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:14:37.947061+00:00
-- url     : https://prove2.me/submissions/0d68a956-5355-497e-b5d0-042992c4d04e

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_SumPowClass
import Definitions.Def_SumsHighPowers_PITLifting_IsHittingSet
import Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate
import Theorems.Thm_SumsHighPowers_PITLifting_claim_3_2
import Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_10

section
namespace SumsHighPowers.PITLifting.Dev31

open SumsHighPowers.PITLifting

theorem eval_aeval {F : Type*} [Field F] {n : ℕ} (H : Fin n → Polynomial F) (a : F)
    (g : MvPolynomial (Fin n) F) :
    (MvPolynomial.aeval H g).eval a = MvPolynomial.eval (fun j => (H j).eval a) g := by
  have h1 : (MvPolynomial.aeval H g).eval a
      = MvPolynomial.eval₂ ((Polynomial.evalRingHom a).comp (algebraMap F (Polynomial F)))
          ((Polynomial.evalRingHom a) ∘ H) g := by
    rw [MvPolynomial.aeval_def]
    exact MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom a) _ _ _
  rw [h1]
  have : (Polynomial.evalRingHom a).comp (algebraMap F (Polynomial F)) = RingHom.id F := by
    ext x; simp
  rw [this]; rfl

theorem natDegree_aeval_le {F : Type*} [Field F] {n : ℕ} (H : Fin n → Polynomial F) (m : ℕ)
    (hH : ∀ j, (H j).natDegree ≤ m) (g : MvPolynomial (Fin n) F) :
    (MvPolynomial.aeval H g).natDegree ≤ g.totalDegree * m := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun e he => ?_)
  have hdeg : (e.sum fun _ k => k) ≤ g.totalDegree := by
    have := MvPolynomial.le_totalDegree (p := g) he
    simpa [Finsupp.degree] using this
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (algebraMap F (Polynomial F) (g.coeff e)).natDegree = 0 := by
    simp [Polynomial.natDegree_C]
  rw [h0, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ e.support, ((H j) ^ (e j)).natDegree ≤ ∑ j ∈ e.support, e j * m :=
        Finset.sum_le_sum (fun j _ => (Polynomial.natDegree_pow_le).trans
          (Nat.mul_le_mul_left _ (hH j)))
    _ = (e.sum fun _ k => k) * m := by
        rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ g.totalDegree * m := Nat.mul_le_mul_right _ hdeg

theorem natDegree_le_of_degree_lt {F : Type*} [Field F] (p : Polynomial F) (s : ℕ)
    (h : p.degree < s) : p.natDegree ≤ s - 1 := by
  by_cases hp : p = 0
  · simp [hp]
  · have := (Polynomial.natDegree_lt_iff_degree_lt hp).2 h
    omega

theorem pna_pair {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M] (A B : M)
    (h : LinearIndependent F ![A, B]) : PairwiseNonAssociate (F := F) ![A, B] := by
  intro i j hij
  have h' := (LinearIndependent.pair_iff.1 h)
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using h
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hst ⊢
    have := h' t s (by rw [add_comm]; simpa using hst)
    exact ⟨this.2, this.1⟩


theorem aeval_ne_zero_of_mem {F : Type*} [Field F] {n Δ s : ℕ}
    {C : Set (MvPolynomial (Fin n) F)}
    {u : Fin s → Fin n → F} (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    {a : Fin s → F} {H : Fin n → Polynomial F}
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    {A : MvPolynomial (Fin n) F} (hA : A ∈ degBounded C Δ) (hA0 : A ≠ 0) :
    MvPolynomial.aeval H A ≠ 0 := by
  have hmem : A ∈ sumPowClass 2 1 (degBounded C Δ) := by
    refine ⟨![1, 0], ![A, A], ?_, ?_⟩
    · intro i; fin_cases i <;> simpa using hA
    · simp [Fin.sum_univ_two]
  obtain ⟨i, hi⟩ := hu _ hmem hA0
  intro h
  apply hi
  have h2 := eval_aeval H (a i) A
  rw [h] at h2
  simp only [hHint] at h2
  simpa using h2.symm

theorem two_case {F : Type*} [Field F] (g₁ g₂ : Polynomial F) (d : ℕ) (hd : 1 ≤ d)
    (h1 : g₁ ≠ 0) (h2 : g₂ ≠ 0) (α₁ α₂ : F) (hα : α₁ • g₁ ^ d + α₂ • g₂ ^ d = 0)
    (hli : LinearIndependent F ![g₁, g₂]) (hne : α₁ ≠ 0 ∨ α₂ ≠ 0) : False := by
  have hg1 : g₁ ^ d ≠ 0 := pow_ne_zero _ h1
  have hg2 : g₂ ^ d ≠ 0 := pow_ne_zero _ h2
  have ha1 : α₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add, smul_eq_zero] at hα
    rcases hα with h | h
    · rcases hne with h' | h' <;> simp_all
    · exact hg2 h
  have ha2 : α₂ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero, smul_eq_zero] at hα
    rcases hα with h | h
    · exact ha1 h
    · exact hg1 h
  have e1 : g₂ ^ d = Polynomial.C (-α₁ / α₂) * g₁ ^ d := by
    have : α₂ • g₂ ^ d = -(α₁ • g₁ ^ d) := eq_neg_of_add_eq_zero_right hα
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul] at this
    have h3 : Polynomial.C α₂ * (g₂ ^ d - Polynomial.C (-α₁ / α₂) * g₁ ^ d) = 0 := by
      rw [mul_sub, this, ← mul_assoc, ← Polynomial.C_mul]
      field_simp
      simp
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (Polynomial.C_eq_zero.1 h) ha2
    · exact sub_eq_zero.1 h
  have e2 : g₁ ^ d = Polynomial.C (-α₂ / α₁) * g₂ ^ d := by
    have : α₁ • g₁ ^ d = -(α₂ • g₂ ^ d) := eq_neg_of_add_eq_zero_left hα
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul] at this
    have h3 : Polynomial.C α₁ * (g₁ ^ d - Polynomial.C (-α₂ / α₁) * g₂ ^ d) = 0 := by
      rw [mul_sub, this, ← mul_assoc, ← Polynomial.C_mul]
      field_simp
      simp
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (Polynomial.C_eq_zero.1 h) ha1
    · exact sub_eq_zero.1 h
  have hc1 : -α₁ / α₂ ≠ 0 := by simp [ha1, ha2]
  have hc2 : -α₂ / α₁ ≠ 0 := by simp [ha1, ha2]
  have d1 : g₁ ^ d ∣ g₂ ^ d := ⟨Polynomial.C (-α₁ / α₂), by rw [e1, mul_comm]⟩
  have d2 : g₂ ^ d ∣ g₁ ^ d := ⟨Polynomial.C (-α₂ / α₁), by rw [e2, mul_comm]⟩
  have hd0 : d ≠ 0 := by omega
  have d1' := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hd0).1 d1
  have d2' := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hd0).1 d2
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd d1' d2'
  obtain ⟨c, hcu, hc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hg : g₂ = c • g₁ := by
    rw [← hu, Polynomial.smul_eq_C_mul, hc]; ring
  have := LinearIndependent.pair_iff.1 hli c (-1) (by simp [hg])
  simp at this


theorem main {F : Type*} [Field F] {n r d Δ s : ℕ} (hd : 1 ≤ d)
    (hrd : (r - 1) ^ 2 ≤ d + 1)
    {C : Set (MvPolynomial (Fin n) F)}
    {u : Fin s → Fin n → F} (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * Δ * s < ringChar F)
    {a : Fin s → F} (ha : Function.Injective a)
    {H : Fin n → Polynomial F} (hHdeg : ∀ j, (H j).degree < s)
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    (f : Fin r → MvPolynomial (Fin n) F) (hf : ∀ i, f i ∈ degBounded C Δ) :
    ∀ N (T : Finset (Fin r)), T.card = N → ∀ α : Fin r → F,
      ∑ i ∈ T, α i • f i ^ d ≠ 0 →
      MvPolynomial.aeval H (∑ i ∈ T, α i • f i ^ d) ≠ 0 := by
  have hd0 : d ≠ 0 := by omega
  have hHnat : ∀ j, (H j).natDegree ≤ s - 1 := fun j => natDegree_le_of_degree_lt _ _ (hHdeg j)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hT α hP
  by_cases hz : ∃ j ∈ T, f j = 0
  · obtain ⟨j, hj, hfj⟩ := hz
    have hsum : ∑ i ∈ T, α i • f i ^ d = ∑ i ∈ T.erase j, α i • f i ^ d := by
      rw [← Finset.add_sum_erase T _ hj, hfj, zero_pow hd0, smul_zero, zero_add]
    have hc : (T.erase j).card < N := by
      rw [Finset.card_erase_of_mem hj]; have := Finset.card_pos.2 ⟨j, hj⟩; omega
    rw [hsum] at hP ⊢
    exact ih _ hc (T.erase j) rfl α hP
  push Not at hz
  by_cases hdep : ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ ¬ LinearIndependent F ![f i, f j]
  · obtain ⟨i, hi, j, hj, hij, hnli⟩ := hdep
    rw [LinearIndependent.pair_iff] at hnli
    push Not at hnli
    obtain ⟨s', t', hst, hne⟩ := hnli
    have hfi := hz i hi
    have hfj := hz j hj
    have ht : t' ≠ 0 := by
      intro h0
      rw [h0, zero_smul, add_zero, smul_eq_zero] at hst
      rcases hst with h | h
      · exact hne h (by simp [h0])
      · exact hfi h
    have hfeq : f j = (-(t'⁻¹ * s')) • f i := by
      have h1 : t' • f j = -(s' • f i) := eq_neg_of_add_eq_zero_right hst
      calc f j = t'⁻¹ • (t' • f j) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-(t'⁻¹ * s')) • f i := by rw [h1, smul_neg, smul_smul, neg_smul]
    set c : F := -(t'⁻¹ * s') with hc
    set α' : Fin r → F := Function.update α i (α i + α j * c ^ d) with hα'
    have hiE : i ∈ T.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
    have hsum : ∑ x ∈ T, α x • f x ^ d = ∑ x ∈ T.erase j, α' x • f x ^ d := by
      rw [← Finset.add_sum_erase T _ hj, ← Finset.add_sum_erase (T.erase j) _ hiE,
        ← Finset.add_sum_erase (T.erase j) (fun x => α' x • f x ^ d) hiE]
      have e1 : ∑ x ∈ (T.erase j).erase i, α x • f x ^ d
          = ∑ x ∈ (T.erase j).erase i, α' x • f x ^ d := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [hα', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
      rw [e1, hα', Function.update_self, hfeq, smul_pow, add_smul, mul_smul]
      abel
    have hcard : (T.erase j).card < N := by
      rw [Finset.card_erase_of_mem hj]; have := Finset.card_pos.2 ⟨j, hj⟩; omega
    rw [hsum] at hP ⊢
    exact ih _ hcard (T.erase j) rfl α' hP
  push Not at hdep
  have hpairφ : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      LinearIndependent F ![MvPolynomial.aeval H (f i), MvPolynomial.aeval H (f j)] := by
    intro i hi j hj hij
    have := claim_3_2 n Δ s C u hu a ha H hHdeg hHint (f i) (f j) (hf i) (hf j)
      (pna_pair _ _ (hdep i hi j hj hij))
    simpa using this 0 1 (by decide)
  have hmap : MvPolynomial.aeval H (∑ i ∈ T, α i • f i ^ d)
      = ∑ i ∈ T, α i • (MvPolynomial.aeval H (f i)) ^ d := by simp
  rw [hmap]
  by_cases h3 : 3 ≤ T.card
  · let e := T.equivFin
    set m := T.card with hm
    have hmr : m ≤ r := by
      have := Finset.card_le_univ T; simpa using this
    have hch : ringChar F = 0 ∨ (m - 1) * d * ((s - 1) * Δ) < ringChar F := by
      rcases hchar with h | h
      · exact Or.inl h
      · right
        refine lt_of_le_of_lt ?_ h
        have h1 : m - 1 ≤ r - 1 := by omega
        have h2 : (s - 1) * Δ ≤ Δ * s := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        calc (m - 1) * d * ((s - 1) * Δ) ≤ (r - 1) * d * (Δ * s) :=
              Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) h2
          _ = (r - 1) * d * Δ * s := by ring
    have hrd' : (m - 1) ^ 2 ≤ d + 1 :=
      (Nat.pow_le_pow_left (by omega) 2).trans hrd
    have h210 := theorem_2_10 (F := F) m d ((s - 1) * Δ) h3 hch
      (fun k => MvPolynomial.aeval H (f (e.symm k)))
      (by
        intro k l hkl
        have hne : (e.symm k : Fin r) ≠ e.symm l := fun h => hkl (e.symm.injective (Subtype.ext h))
        exact hpairφ _ (e.symm k).2 _ (e.symm l).2 hne)
      (by
        intro k
        refine (natDegree_aeval_le H (s - 1) hHnat _).trans ?_
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (hf _).2)
      hrd'
    intro h0
    have hsum : ∑ k : Fin m, α (e.symm k) • (MvPolynomial.aeval H (f (e.symm k))) ^ d = 0 := by
      rw [Equiv.sum_comp e.symm (fun x : T => α x • (MvPolynomial.aeval H (f x)) ^ d)]
      rw [Finset.sum_coe_sort T (fun x => α x • (MvPolynomial.aeval H (f x)) ^ d)]
      exact h0
    have := Fintype.linearIndependent_iff.1 h210 (fun k => α (e.symm k)) hsum
    apply hP
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have := this (e ⟨i, hi⟩)
    simp at this
    simp [this]
  · have hcard : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
    rcases hcard with h | h | h
    · rw [Finset.card_eq_zero] at h
      subst h
      simp at hP
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h
      simp only [Finset.sum_singleton] at hP ⊢
      have hα : α i ≠ 0 := by
        intro h0; apply hP; simp [h0]
      have hg := aeval_ne_zero_of_mem hu hHint (hf i) (hz i (by simp))
      exact smul_ne_zero hα (pow_ne_zero _ hg)
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 h
      rw [Finset.sum_pair hij] at hP ⊢
      intro h0
      refine two_case _ _ d hd ?_ ?_ (α i) (α j) h0
        (hpairφ i (by simp) j (by simp) hij) ?_
      · exact aeval_ne_zero_of_mem hu hHint (hf i) (hz i (by simp))
      · exact aeval_ne_zero_of_mem hu hHint (hf j) (hz j (by simp))
      · by_contra hh
        push Not at hh
        apply hP; simp [hh.1, hh.2]


end SumsHighPowers.PITLifting.Dev31

namespace SumsHighPowers.PITLifting

open Dev31 in
theorem chk_theorem_3_1 {F : Type*} [Field F] (n r d Δ s : ℕ)
    (hrd : (r - 1) ^ 2 ≤ d + 1)
    (C : Set (MvPolynomial (Fin n) F))
    (u : Fin s → Fin n → F) (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * Δ * s < ringChar F)
    (a : Fin s → F) (ha : Function.Injective a)
    (H : Fin n → Polynomial F) (hHdeg : ∀ j, (H j).degree < s)
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    (S : Set F) (P : MvPolynomial (Fin n) F)
    (hP : P ∈ sumPowClass r d (degBounded C Δ)) (hP0 : P ≠ 0) :
    {t | t ∈ S ∧ MvPolynomial.eval (fun j => (H j).eval t) P = 0}.encard ≤
      (((s - 1) * Δ * d : ℕ) : ℕ∞) := by
  obtain ⟨α, f, hfC, hPeq⟩ := hP
  have hHnat : ∀ j, (H j).natDegree ≤ s - 1 := fun j => natDegree_le_of_degree_lt _ _ (hHdeg j)
  have hnz : MvPolynomial.aeval H P ≠ 0 := by
    by_cases hd : d = 0
    · subst hd
      have hP' : P = (∑ i, α i) • (1 : MvPolynomial (Fin n) F) := by
        rw [hPeq]; simp [Finset.sum_smul]
      have hsum : (∑ i, α i) ≠ 0 := by
        intro h0; apply hP0; rw [hP', h0, zero_smul]
      rw [hP']
      simp [hsum]
    · have := main (by omega) hrd hu hchar ha hHdeg hHint f hfC _ Finset.univ rfl α
        (by rw [← hPeq]; exact hP0)
      rwa [← hPeq] at this
  have hdeg : (MvPolynomial.aeval H P).natDegree ≤ (s - 1) * Δ * d := by
    refine (natDegree_aeval_le H (s - 1) hHnat P).trans ?_
    have htd : P.totalDegree ≤ d * Δ := by
      rw [hPeq]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i _ => ?_))
      refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      exact Nat.mul_le_mul_left _ (hfC i).2
    calc P.totalDegree * (s - 1) ≤ d * Δ * (s - 1) := Nat.mul_le_mul_right _ htd
      _ = (s - 1) * Δ * d := by ring
  classical
  have hsub : {t | t ∈ S ∧ MvPolynomial.eval (fun j => (H j).eval t) P = 0}
      ⊆ ((MvPolynomial.aeval H P).roots.toFinset : Set F) := by
    intro t ht
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hnz,
      Polynomial.IsRoot.def]
    rw [eval_aeval]; exact ht.2
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans hdeg)

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_theorem_3_1 := @SumsHighPowers.PITLifting.chk_theorem_3_1
