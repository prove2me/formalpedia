-- Prove2me | solution 1 for SumsHighPowers.PITLifting.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:31:40.106228+00:00
-- url     : https://prove2.me/submissions/80ac4781-9c90-479f-95da-c1634a02161e

import Mathlib
import Definitions.Def_BorderDiffEq_wronskian

section
open Polynomial

namespace SumsHighPowers.PITLifting.DevWr

variable {F : Type} [Field F]

theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (w g : Polynomial F) (hg : g.natDegree < p)
    (k r : ℕ) (hr : r < p) :
    (expand F p w * g).coeff (p * k + r) = w.coeff k * g.coeff r := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (p * k, r)]
  · rw [Polynomial.coeff_expand hp]
    simp [Nat.mul_div_cancel_left _ hp]
  · rintro ⟨a, b⟩ hab hne
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    show (expand F p w).coeff a * g.coeff b = 0
    by_cases hb : g.coeff b = 0
    · rw [hb, mul_zero]
    · have hb' : b < p := lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero hb) hg
      rw [Polynomial.coeff_expand hp]
      by_cases hdiv : p ∣ a
      · obtain ⟨k', rfl⟩ := hdiv
        exfalso
        apply hne
        have h1 : (p * k' + b) / p = (p * k + r) / p := by rw [hab]
        have h2 : (p * k' + b) % p = (p * k + r) % p := by rw [hab]
        rw [Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt hb',
          Nat.div_eq_of_lt hr] at h1
        rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hr] at h2
        simp only [add_zero] at h1
        subst h1; subst h2; rfl
      · simp [hdiv]
  · intro h
    exfalso; apply h
    simp [Finset.mem_antidiagonal]


theorem deriv0 {n : ℕ} (g : Fin n → Polynomial F) (d : ℕ) (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) (v : Fin n → Polynomial F)
    (hv : ∀ i, Polynomial.derivative (v i) = 0) (hsum : ∑ i, v i * g i = 0)
    (hne : ∃ i, v i ≠ 0) : ¬ LinearIndependent F g := by
  rw [Fintype.not_linearIndependent_iff]
  obtain ⟨i0, hi0⟩ := hne
  rcases hchar with h0 | hp
  · haveI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 h0
    have hC : ∀ i, v i = Polynomial.C ((v i).coeff 0) := fun i =>
      Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero (hv i))
    refine ⟨fun i => (v i).coeff 0, ?_, i0, ?_⟩
    · have : ∑ i, v i * g i = ∑ i, (v i).coeff 0 • g i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Polynomial.smul_eq_C_mul, ← hC i]
      rw [← this]; exact hsum
    · intro h
      apply hi0; rw [hC i0]; simp only at h; rw [h, map_zero]
  · have hp0 : 0 < ringChar F := lt_of_le_of_lt (Nat.zero_le _) hp
    set p := ringChar F with hpdef
    haveI : CharP F p := ringChar.charP F
    have hw : ∀ i, Polynomial.expand F p (Polynomial.contract p (v i)) = v i :=
      fun i => Polynomial.expand_contract p (hv i) hp0.ne'
    set w : Fin n → Polynomial F := fun i => Polynomial.contract p (v i) with hwdef
    have hw0 : w i0 ≠ 0 := by
      intro h; apply hi0; rw [← hw i0]; simp only [hwdef] at h; rw [h]; simp
    obtain ⟨k, hk⟩ : ∃ k, (w i0).coeff k ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hw0 (Polynomial.ext (by simpa using hcon))
    refine ⟨fun i => (w i).coeff k, ?_, i0, hk⟩
    ext r
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero]
    by_cases hr : r < p
    · have h1 := congrArg (fun q => q.coeff (p * k + r)) hsum
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← hw i, coeff_expand_mul hp0 (w i) (g i) (lt_of_le_of_lt (hdeg i) hp) k r hr]
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := g i)
        (lt_of_le_of_lt (hdeg i) (lt_of_lt_of_le hp (not_lt.1 hr))), mul_zero]


theorem normalize_step {m : ℕ} (g : Fin m → Polynomial F) (d : ℕ) (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) (l : Fin m) (v : Fin m → Polynomial F)
    (hl : v l ≠ 0)
    (hode : ∀ i, v l * Polynomial.derivative (v i) = Polynomial.derivative (v l) * v i)
    (hsum : ∑ i, v i * g i = 0) : ¬ LinearIndependent F g := by
  classical
  obtain ⟨v', hv1, hv2⟩ := Finset.extract_gcd v (Finset.univ_nonempty_iff.2 ⟨l⟩)
  set u := Finset.univ.gcd v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hu, Finset.gcd_eq_zero_iff] at h0
    exact hl (h0 l (Finset.mem_univ _))
  have hsum' : ∑ i, v' i * g i = 0 := by
    have : u * ∑ i, v' i * g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hv1 i (Finset.mem_univ _)]; ring
    exact (mul_eq_zero.1 this).resolve_left hu0
  have hl' : v' l ≠ 0 := by
    intro h0; apply hl; rw [hv1 l (Finset.mem_univ _), h0, mul_zero]
  have hode' : ∀ i, v' l * Polynomial.derivative (v' i) = Polynomial.derivative (v' l) * v' i := by
    intro i
    have h1 := hode i
    rw [hv1 l (Finset.mem_univ _), hv1 i (Finset.mem_univ _)] at h1
    simp only [Polynomial.derivative_mul] at h1
    have h2 : u ^ 2 * (v' l * Polynomial.derivative (v' i)) =
        u ^ 2 * (Polynomial.derivative (v' l) * v' i) := by
      linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero 2 hu0) h2
  have hdvd : v' l ∣ Polynomial.derivative (v' l) := by
    have h1 : v' l ∣ Finset.univ.gcd (fun i => Polynomial.derivative (v' l) * v' i) :=
      Finset.dvd_gcd (fun i _ => ⟨Polynomial.derivative (v' i), (hode' i).symm⟩)
    rw [Finset.gcd_mul_left, hv2, mul_one] at h1
    exact h1.trans (normalize_associated _).dvd
  have hd0 : Polynomial.derivative (v' l) = 0 := by
    by_contra hne
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hne
    by_cases hdg : (v' l).natDegree = 0
    · apply hne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdg]; simp
    · have := Polynomial.natDegree_derivative_lt hdg
      omega
  refine deriv0 g d hdeg hchar v' (fun i => ?_) hsum' ⟨l, hl'⟩
  have := hode' i
  rw [hd0, zero_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hl'


theorem step {n : ℕ} (g : Fin (n + 1) → Polynomial F)
    (hW' : BorderDiffEq.wronskian (fun i : Fin n => g i.castSucc) ≠ 0) (hW : BorderDiffEq.wronskian g = 0) :
    ∃ v : Fin (n + 1) → Polynomial F, v (Fin.last n) ≠ 0 ∧
      (∀ i, v (Fin.last n) * Polynomial.derivative (v i) =
        Polynomial.derivative (v (Fin.last n)) * v i) ∧ ∑ i, v i * g i = 0 := by
  classical
  unfold BorderDiffEq.wronskian at hW hW'
  obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hW
  have hrel : ∀ j : ℕ, j ≤ n → ∑ i, v i * Polynomial.derivative^[j] (g i) = 0 := by
    intro j hj
    have := congrFun hvM ⟨j, by omega⟩
    simpa [Matrix.vecMul, dotProduct] using this
  -- first n columns, rows castSucc
  have hcut : ∀ (w : Fin (n + 1) → Polynomial F), w (Fin.last n) = 0 →
      (∀ j : ℕ, j < n → ∑ i, w i * Polynomial.derivative^[j] (g i) = 0) →
      (∀ i : Fin n, w i.castSucc = 0) := by
    intro w hwl hwr
    by_contra hcon
    push Not at hcon
    obtain ⟨i1, hi1⟩ := hcon
    have hex : ∃ w' : Fin n → Polynomial F, w' ≠ 0 ∧
        Matrix.vecMul w' (Matrix.of fun i j : Fin n => Polynomial.derivative^[(j : ℕ)] (g i.castSucc)) = 0 := by
      refine ⟨fun i => w i.castSucc, fun h => hi1 (congrFun h i1), ?_⟩
      funext j
      have := hwr j j.2
      rw [Fin.sum_univ_castSucc, hwl, zero_mul, add_zero] at this
      simpa [Matrix.vecMul, dotProduct] using this
    exact hW' (Matrix.exists_vecMul_eq_zero_iff.1 hex)
  have hlast : v (Fin.last n) ≠ 0 := by
    intro h0
    apply hv0
    have := hcut v h0 (fun j hj => hrel j (by omega))
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using h0
    · simpa using this i
  set w : Fin (n + 1) → Polynomial F := fun i =>
    v (Fin.last n) * Polynomial.derivative (v i) - Polynomial.derivative (v (Fin.last n)) * v i
    with hwdef
  have hwl : w (Fin.last n) = 0 := by simp only [hwdef]; ring
  have hwr : ∀ j : ℕ, j < n → ∑ i, w i * Polynomial.derivative^[j] (g i) = 0 := by
    intro j hj
    have h1 := hrel j (by omega)
    have h2 := hrel (j + 1) (by omega)
    have h3 : ∑ i, Polynomial.derivative (v i) * Polynomial.derivative^[j] (g i) = 0 := by
      have := congrArg Polynomial.derivative h1
      rw [map_sum, map_zero] at this
      simp only [Polynomial.derivative_mul] at this
      rw [Finset.sum_add_distrib] at this
      have h4 : ∑ i, v i * Polynomial.derivative (Polynomial.derivative^[j] (g i)) = 0 := by
        simpa [Function.iterate_succ_apply'] using h2
      rw [h4, add_zero] at this
      exact this
    have : ∑ i, w i * Polynomial.derivative^[j] (g i) =
        v (Fin.last n) * ∑ i, Polynomial.derivative (v i) * Polynomial.derivative^[j] (g i) -
        Polynomial.derivative (v (Fin.last n)) * ∑ i, v i * Polynomial.derivative^[j] (g i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hwdef]; ring
    rw [this, h1, h3]; ring
  have hw0 := hcut w hwl hwr
  refine ⟨v, hlast, fun i => ?_, by simpa using hrel 0 (Nat.zero_le _)⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · ring
  · have := hw0 i
    simp only [hwdef] at this
    exact sub_eq_zero.1 this


theorem iter_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → Polynomial F) :
    Polynomial.derivative^[j] (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.derivative^[j] (f i) := by
  induction j with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih, map_sum]

theorem iter_zero (j : ℕ) : Polynomial.derivative^[j] (0 : Polynomial F) = 0 := by
  induction j with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

theorem dep_of_wr_zero (d : ℕ) (hchar : ringChar F = 0 ∨ d < ringChar F) :
    ∀ (n : ℕ) (g : Fin n → Polynomial F), (∀ i, (g i).natDegree ≤ d) →
      BorderDiffEq.wronskian g = 0 → ¬ LinearIndependent F g := by
  intro n
  induction n with
  | zero =>
    intro g _ hW
    exfalso
    unfold BorderDiffEq.wronskian at hW
    simp at hW
  | succ n ih =>
    intro g hdeg hW
    by_cases hW' : BorderDiffEq.wronskian (fun i : Fin n => g i.castSucc) = 0
    · intro hLI
      exact ih (fun i => g i.castSucc) (fun i => hdeg _) hW'
        (hLI.comp Fin.castSucc (Fin.castSucc_injective n))
    · obtain ⟨v, hv1, hv2, hv3⟩ := step g hW' hW
      exact normalize_step g d hdeg hchar (Fin.last n) v hv1 hv2 hv3

theorem wr_zero_of_dep {n : ℕ} (g : Fin n → Polynomial F) (hd : ¬ LinearIndependent F g) :
    BorderDiffEq.wronskian g = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hd
  obtain ⟨c, hc, i0, hi0⟩ := hd
  unfold BorderDiffEq.wronskian
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨fun i => Polynomial.C (c i), fun h => hi0 ?_, ?_⟩
  · have := congrFun h i0
    simpa using this
  · funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    have : ∀ i, Polynomial.C (c i) * Polynomial.derivative^[(j : ℕ)] (g i)
        = Polynomial.derivative^[(j : ℕ)] (c i • g i) := by
      intro i
      rw [Polynomial.smul_eq_C_mul]
      induction (j : ℕ) with
      | zero => simp
      | succ k ihk => simp [Function.iterate_succ_apply', ← ihk]
    simp_rw [this]
    rw [← iter_sum, hc]
    exact iter_zero _

end SumsHighPowers.PITLifting.DevWr

namespace SumsHighPowers.PITLifting

theorem chk_theorem_2_3 {F : Type} [Field F] {n : ℕ} (g : Fin n → Polynomial F) (d : ℕ)
    (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) :
    ¬ LinearIndependent F g ↔ BorderDiffEq.wronskian g = 0 :=
  ⟨DevWr.wr_zero_of_dep g, fun h hLI => DevWr.dep_of_wr_zero d hchar n g hdeg h hLI⟩

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_theorem_2_3 := @SumsHighPowers.PITLifting.chk_theorem_2_3
