-- Prove2me | solution 1 for ProximityPadeGaugeCount.polynomial_gauge_mca_card_le
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T17:07:46.752994+00:00
-- url     : https://prove2.me/submissions/802ff751-6154-4e5b-b45d-bd219273ef3f

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Finset.Card
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination


namespace ProximityPadeGaugeObstruction
noncomputable section
open Polynomial
variable {K : Type*} [Field K]

def obstruction (σ : K →+* K) (p : ℕ) (a b : K[X]) : K[X] :=
  a^p * b.map σ - a.map σ * b^p

theorem degree_contradiction (σ : K →+* K) (p : ℕ) (hp : 1<p)
    (a b : K[X]) (hab : IsCoprime a b) (ha : 0<a.natDegree)
    (heq : a^p*b.map σ=a.map σ*b^p) : False := by
  have ha0 : a≠0 := by intro h; simp [h] at ha
  have hmap : a.map σ≠0 := by
    intro hz
    apply ha0
    exact Polynomial.map_injective σ σ.injective (hz.trans (Polynomial.map_zero σ).symm)
  have hcop : IsCoprime (a^p) (b^p) := hab.pow
  have hdvd : a^p ∣ a.map σ := hcop.dvd_of_dvd_mul_right (by
    rw [←heq]
    exact dvd_mul_right _ _)
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hmap
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_map] at hdeg
  nlinarith

/-- Coprime nonconstant pencils have a nonzero one-variable obstruction. -/
theorem obstruction_ne_zero (σ : K →+* K) (p : ℕ) (hp : 1<p)
    (a b : K[X]) (hab : IsCoprime a b)
    (hdegree : 0<max a.natDegree b.natDegree) : obstruction σ p a b≠0 := by
  intro hz
  have heq : a^p*b.map σ=a.map σ*b^p := sub_eq_zero.mp hz
  rcases lt_max_iff.mp hdegree with ha | hb
  · exact degree_contradiction σ p hp a b hab ha heq
  · apply degree_contradiction σ p hp b a hab.symm hb
    simpa only [mul_comm] using heq.symm

theorem obstruction_natDegree_le (σ : K →+* K) (p d : ℕ)
    (a b : K[X]) (ha : a.natDegree≤d) (hb : b.natDegree≤d) :
    (obstruction σ p a b).natDegree≤d*(p+1) := by
  have hleft : (a^p*b.map σ).natDegree≤p*d+d := by
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_map]
    exact Nat.add_le_add (Nat.mul_le_mul_left p ha) hb
  have hright : (a.map σ*b^p).natDegree≤d+p*d := by
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_map]
    exact Nat.add_le_add ha (Nat.mul_le_mul_left p hb)
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le
    (by nlinarith) (by nlinarith))

end
end ProximityPadeGaugeObstruction


namespace ProximityPadePolynomialGauge

open Polynomial

variable {K : Type*} [Field K]

theorem eval_map_of_fixed (σ : K →+* K) (P : K[X]) {x : K} (hx : σ x=x) :
    (P.map σ).eval x=σ (P.eval x) := by
  simpa only [hx] using Polynomial.eval_map_apply (p := P) σ x

/-- A coprime polynomial and its coefficient conjugate have no fixed-node root. -/
theorem eval_ne_zero_of_coprime_map (σ : K →+* K) (η : K[X])
    (hcop : IsCoprime η (η.map σ)) {x : K} (hx : σ x=x) : η.eval x≠0 := by
  intro hz
  obtain ⟨a,b,hab⟩ := hcop
  have h := congrArg (Polynomial.eval x) hab
  rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_mul,
    eval_map_of_fixed σ η hx,hz,map_zero,mul_zero,mul_zero,zero_add,Polynomial.eval_one] at h
  exact zero_ne_one h

/-- Too many fixed-value agreements force the polynomial cross identity. -/
theorem cross_eq_zero_of_fit (σ : K →+* K) (T : Finset K) (c : K → K)
    (hx : ∀ x∈T, σ x=x) (hc : ∀ x∈T, σ (c x)=c x)
    (η P : K[X]) (k : ℕ) (hP : P.natDegree<k)
    (hcard : k+η.natDegree≤T.card)
    (hfit : ∀ x∈T, P.eval x=η.eval x*c x) :
    P.map σ*η-P*(η.map σ)=0 := by
  classical
  let D : K[X] := P.map σ*η-P*(η.map σ)
  have hleft : (P.map σ*η).natDegree≤P.natDegree+η.natDegree :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_map_le _)
  have hright : (P*(η.map σ)).natDegree≤P.natDegree+η.natDegree :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left Polynomial.natDegree_map_le _)
  have hdeg : D.natDegree<T.card := by
    apply lt_of_lt_of_le _ hcard
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hleft hright) |>.trans_lt
      (Nat.add_lt_add_right hP _)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero D
    (f := fun x : T => (x : K)) Subtype.val_injective
  · intro x
    simp only [D,Polynomial.eval_sub,Polynomial.eval_mul,
      eval_map_of_fixed σ P (hx x x.property), eval_map_of_fixed σ η (hx x x.property),
      hfit x x.property,map_mul,hc x x.property]
    ring
  · simpa only [Fintype.card_coe] using hdeg

/-- Coprimality turns the zero cross identity into actual divisibility of the fit. -/
theorem gauge_dvd_of_fit (σ : K →+* K) (T : Finset K) (c : K → K)
    (hx : ∀ x∈T, σ x=x) (hc : ∀ x∈T, σ (c x)=c x)
    (η P : K[X]) (k : ℕ) (hP : P.natDegree<k)
    (hcard : k+η.natDegree≤T.card) (hcop : IsCoprime η (η.map σ))
    (hfit : ∀ x∈T, P.eval x=η.eval x*c x) : η∣P := by
  have hcross := sub_eq_zero.mp (cross_eq_zero_of_fit σ T c hx hc η P k hP hcard hfit)
  apply hcop.dvd_of_dvd_mul_right
  rw [← hcross]
  exact dvd_mul_left η (P.map σ)

/-- With its degree preserved, a coprime gauge makes both original words fit on the same set. -/
theorem simultaneous_fit_of_coprime_gauge (σ : K →+* K)
    (T : Finset K) (c : K → K) (hx : ∀ x∈T, σ x=x)
    (hc : ∀ x∈T, σ (c x)=c x)
    (η η₀ η₁ P : K[X]) (k : ℕ) (hη : η≠0)
    (h₀ : η₀.natDegree≤η.natDegree) (h₁ : η₁.natDegree≤η.natDegree)
    (hP : P.natDegree<k) (hcard : k+η.natDegree≤T.card)
    (hcop : IsCoprime η (η.map σ))
    (hfit : ∀ x∈T, P.eval x=η.eval x*c x) :
    ∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
      (∀ x∈T, P₀.eval x=η₀.eval x*c x) ∧
      (∀ x∈T, P₁.eval x=η₁.eval x*c x) := by
  obtain ⟨f,hfactor⟩ := gauge_dvd_of_fit σ T c hx hc η P k hP hcard hcop hfit
  have hfvalues : ∀ x∈T, f.eval x=c x := by
    intro x hxT
    apply mul_left_cancel₀ (eval_ne_zero_of_coprime_map σ η hcop (hx x hxT))
    have h := congrArg (Polynomial.eval x) hfactor
    simpa only [Polynomial.eval_mul,hfit x hxT] using h.symm
  have hdegree (Q : K[X]) (hQ : Q.natDegree≤η.natDegree) : (Q*f).natDegree<k := by
    by_cases hf : f=0
    · have hk : 0<k := (Nat.zero_le _).trans_lt hP
      simpa only [hf,mul_zero,Polynomial.natDegree_zero] using hk
    · calc
        (Q*f).natDegree≤Q.natDegree+f.natDegree := Polynomial.natDegree_mul_le
        _ ≤ η.natDegree+f.natDegree := Nat.add_le_add_right hQ _
        _ = P.natDegree := by rw [hfactor,Polynomial.natDegree_mul hη hf]
        _ < k := hP
  refine ⟨η₀*f,η₁*f,hdegree _ h₀,hdegree _ h₁,?_,?_⟩
  · intro x hxT
    rw [Polynomial.eval_mul,hfvalues x hxT]
  · intro x hxT
    rw [Polynomial.eval_mul,hfvalues x hxT]

/-- The actual Frobenius affine-pencil specialization, with degree-cancellation gates explicit. -/
theorem frobenius_affine_gauge_simultaneous_fit (p : ℕ) [Fact p.Prime] [CharP K p]
    (T : Finset K) (c : K → K) (hx : ∀ x∈T, x^p=x)
    (hc : ∀ x∈T, (c x)^p=c x) (η₀ η₁ P : K[X]) (γ : K) (k : ℕ)
    (hη : η₀+γ • η₁≠0)
    (h₀ : η₀.natDegree≤(η₀+γ • η₁).natDegree)
    (h₁ : η₁.natDegree≤(η₀+γ • η₁).natDegree)
    (hP : P.natDegree<k) (hcard : k+(η₀+γ • η₁).natDegree≤T.card)
    (hcop : IsCoprime (η₀+γ • η₁) ((η₀+γ • η₁).map (frobenius K p)))
    (hfit : ∀ x∈T, P.eval x=(η₀+γ • η₁).eval x*c x) :
    ∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
      (∀ x∈T, P₀.eval x=η₀.eval x*c x) ∧
      (∀ x∈T, P₁.eval x=η₁.eval x*c x) :=
  simultaneous_fit_of_coprime_gauge (frobenius K p) T c hx hc (η₀+γ • η₁)
    η₀ η₁ P k hη h₀ h₁ hP hcard hcop hfit

/-- Literal same-support MCA is impossible in the coprime, degree-preserving branch. -/
theorem frobenius_affine_gauge_not_mca (p : ℕ) [Fact p.Prime] [CharP K p]
    (T : Finset K) (c : K → K) (hx : ∀ x∈T, x^p=x)
    (hc : ∀ x∈T, (c x)^p=c x) (η₀ η₁ : K[X]) (γ : K) (k : ℕ)
    (hη : η₀+γ • η₁≠0)
    (h₀ : η₀.natDegree≤(η₀+γ • η₁).natDegree)
    (h₁ : η₁.natDegree≤(η₀+γ • η₁).natDegree)
    (hcard : k+(η₀+γ • η₁).natDegree≤T.card)
    (hcop : IsCoprime (η₀+γ • η₁) ((η₀+γ • η₁).map (frobenius K p))) :
    ¬∃ P : K[X], P.natDegree<k ∧
      (∀ x∈T, P.eval x=η₀.eval x*c x+γ*(η₁.eval x*c x)) ∧
      ¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=η₀.eval x*c x) ∧
        (∀ x∈T, P₁.eval x=η₁.eval x*c x) := by
  rintro ⟨P,hP,hfit,hnot⟩
  apply hnot
  apply frobenius_affine_gauge_simultaneous_fit p T c hx hc η₀ η₁ P γ k
    hη h₀ h₁ hP hcard hcop
  intro x hxT
  simpa only [Polynomial.eval_add,Polynomial.eval_smul,smul_eq_mul,add_mul,mul_assoc]
    using hfit x hxT

end ProximityPadePolynomialGauge




namespace ProximityPadePolynomialGauge

open Polynomial
variable {K : Type*} [Field K]

/-- The fixed factor remains under coefficient conjugation in the coprimality gate. -/
theorem moving_gauge_dvd_of_fit (σ : K →+* K) (T : Finset K) (c : K → K)
    (hx : ∀ x∈T, σ x=x) (hc : ∀ x∈T, σ (c x)=c x)
    (g α P : K[X]) (k : ℕ) (hP : P.natDegree<k)
    (hcard : k+(g*α).natDegree≤T.card)
    (hcop : IsCoprime α (g.map σ*α.map σ))
    (hfit : ∀ x∈T, P.eval x=(g*α).eval x*c x) : α∣P := by
  have hcross := sub_eq_zero.mp (cross_eq_zero_of_fit σ T c hx hc (g*α) P k hP hcard hfit)
  rw [Polynomial.map_mul] at hcross
  apply hcop.dvd_of_dvd_mul_right
  rw [← hcross]
  refine ⟨P.map σ*g,?_⟩
  ring

/-- The quotient fits g*c, which is not assumed fixed by the endomorphism. -/
theorem simultaneous_fit_of_coprime_fixed_factor (σ : K →+* K)
    (T : Finset K) (c : K → K) (hx : ∀ x∈T, σ x=x)
    (hc : ∀ x∈T, σ (c x)=c x)
    (g α α₀ α₁ P : K[X]) (k : ℕ)
    (h₀ : α₀.natDegree≤α.natDegree) (h₁ : α₁.natDegree≤α.natDegree)
    (hP : P.natDegree<k) (hcard : k+(g*α).natDegree≤T.card)
    (hcop : IsCoprime α (g.map σ*α.map σ))
    (hfit : ∀ x∈T, P.eval x=(g*α).eval x*c x) :
    ∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
      (∀ x∈T, P₀.eval x=(g*α₀).eval x*c x) ∧
      (∀ x∈T, P₁.eval x=(g*α₁).eval x*c x) := by
  have hweak : IsCoprime α (α.map σ) :=
    hcop.of_isCoprime_of_dvd_right (dvd_mul_left (α.map σ) (g.map σ))
  have hα : α≠0 := by
    intro hz
    obtain ⟨a,b,hab⟩ := hweak
    simp only [hz,Polynomial.map_zero,mul_zero,zero_add] at hab
    exact zero_ne_one hab
  obtain ⟨f,hfactor⟩ := moving_gauge_dvd_of_fit σ T c hx hc g α P k hP hcard hcop hfit
  have hfvalues : ∀ x∈T, f.eval x=g.eval x*c x := by
    intro x hxT
    apply mul_left_cancel₀ (eval_ne_zero_of_coprime_map σ α hweak (hx x hxT))
    calc
      α.eval x*f.eval x=P.eval x := by rw [hfactor,Polynomial.eval_mul]
      _ = (g*α).eval x*c x := hfit x hxT
      _ = α.eval x*(g.eval x*c x) := by rw [Polynomial.eval_mul]; ring
  have hdegree (Q : K[X]) (hQ : Q.natDegree≤α.natDegree) : (Q*f).natDegree<k := by
    by_cases hf : f=0
    · have hk : 0<k := (Nat.zero_le _).trans_lt hP
      simpa only [hf,mul_zero,Polynomial.natDegree_zero] using hk
    · calc
        (Q*f).natDegree≤Q.natDegree+f.natDegree := Polynomial.natDegree_mul_le
        _ ≤ α.natDegree+f.natDegree := Nat.add_le_add_right hQ _
        _ = P.natDegree := by rw [hfactor,Polynomial.natDegree_mul hα hf]
        _ < k := hP
  refine ⟨α₀*f,α₁*f,hdegree _ h₀,hdegree _ h₁,?_,?_⟩
  · intro x hxT
    rw [Polynomial.eval_mul,hfvalues x hxT,Polynomial.eval_mul]
    ring
  · intro x hxT
    rw [Polynomial.eval_mul,hfvalues x hxT,Polynomial.eval_mul]
    ring

/-- Same-support exclusion with an arbitrary K-coefficient fixed factor. -/
theorem frobenius_fixed_factor_not_mca (p : ℕ) [Fact p.Prime] [CharP K p]
    (T : Finset K) (c : K → K) (hx : ∀ x∈T, x^p=x)
    (hc : ∀ x∈T, (c x)^p=c x) (g α₀ α₁ : K[X]) (γ : K) (k : ℕ)
    (h₀ : α₀.natDegree≤(α₀+γ • α₁).natDegree)
    (h₁ : α₁.natDegree≤(α₀+γ • α₁).natDegree)
    (hcard : k+(g*(α₀+γ • α₁)).natDegree≤T.card)
    (hcop : IsCoprime (α₀+γ • α₁)
      (g.map (frobenius K p)*(α₀+γ • α₁).map (frobenius K p))) :
    ¬∃ P : K[X], P.natDegree<k ∧
      (∀ x∈T, P.eval x=(g*α₀).eval x*c x+γ*((g*α₁).eval x*c x)) ∧
      ¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=(g*α₀).eval x*c x) ∧
        (∀ x∈T, P₁.eval x=(g*α₁).eval x*c x) := by
  rintro ⟨P,hP,hfit,hnot⟩
  apply hnot
  apply simultaneous_fit_of_coprime_fixed_factor (frobenius K p) T c hx hc
    g (α₀+γ • α₁) α₀ α₁ P k h₀ h₁ hP hcard hcop
  intro x hxT
  rw [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_smul]
  simp only [smul_eq_mul]
  rw [hfit x hxT,Polynomial.eval_mul,Polynomial.eval_mul]
  ring

end ProximityPadePolynomialGauge



open Polynomial

namespace ProximityPadeDegreeDrop

variable {K : Type*} [Field K]

/-- Dropping below the larger input degree determines the affine parameter. -/
theorem degree_drop_parameter_unique (a b : K[X]) (γ δ : K)
    (hγ : (a + γ • b).natDegree < max a.natDegree b.natDegree)
    (hδ : (a + δ • b).natDegree < max a.natDegree b.natDegree) : γ = δ := by
  let d := max a.natDegree b.natDegree
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hγ
  have hcγ : a.coeff d + γ * b.coeff d = 0 := by
    simpa only [coeff_add, coeff_smul, smul_eq_mul] using
      (coeff_eq_zero_of_natDegree_lt hγ)
  have hcδ : a.coeff d + δ * b.coeff d = 0 := by
    simpa only [coeff_add, coeff_smul, smul_eq_mul] using
      (coeff_eq_zero_of_natDegree_lt hδ)
  have hb : b.coeff d ≠ 0 := by
    intro hb
    have ha : a.coeff d = 0 := by simpa only [hb, mul_zero, add_zero] using hcγ
    have hlt (P : K[X]) (hle : P.natDegree ≤ d) (hc : P.coeff d = 0) :
        P.natDegree < d := by
      apply lt_of_le_of_ne hle
      intro heq
      have hP : P = 0 := leadingCoeff_eq_zero.mp (by
        simpa only [← heq, coeff_natDegree] using hc)
      exact (Nat.ne_of_gt hd) (by simpa only [hP, natDegree_zero] using heq.symm)
    have had : a.natDegree < d := hlt a (le_max_left _ _) ha
    have hbd : b.natDegree < d := hlt b (le_max_right _ _) hb
    exact (lt_irrefl d) (max_lt had hbd)
  exact mul_right_cancel₀ hb (add_left_cancel (hcγ.trans hcδ.symm))

/-- At most one member of any finite parameter set can lower the maximal degree. -/
theorem degree_drop_parameters_card_le (a b : K[X]) (Γ : Finset K)
    (hdrop : ∀ γ ∈ Γ,
      (a + γ • b).natDegree < max a.natDegree b.natDegree) : Γ.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro γ hγ δ hδ
  exact degree_drop_parameter_unique a b γ δ (hdrop γ hγ) (hdrop δ hδ)

/-- A nonzero scalar combination fitting a common word recovers both originals. -/
theorem scalar_pair_simultaneous_fit (T : Finset K) (w : K → K)
    (A B γ : K) (k : ℕ) (P : K[X])
    (hP : P.natDegree < k)
    (hfit : ∀ x ∈ T, P.eval x = A * w x + γ * (B * w x))
    (hscale : A + γ * B ≠ 0) :
    ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      ∀ x ∈ T, P₀.eval x = A * w x ∧ P₁.eval x = B * w x := by
  refine ⟨(A * (A + γ * B)⁻¹) • P, (B * (A + γ * B)⁻¹) • P,
    (natDegree_smul_le _ _).trans_lt hP, (natDegree_smul_le _ _).trans_lt hP, ?_⟩
  intro x hx
  have hv : P.eval x = (A + γ * B) * w x := by rw [hfit x hx]; ring
  simp only [eval_smul, smul_eq_mul, hv, mul_assoc, inv_mul_cancel_left₀ hscale,
    and_self]

/-- Literal same-support failure forces the scalar combination to vanish. -/
theorem scalar_pair_mca_scale_eq_zero (T : Finset K) (w : K → K)
    (A B γ : K) (k : ℕ) (P : K[X])
    (hP : P.natDegree < k)
    (hfit : ∀ x ∈ T, P.eval x = A * w x + γ * (B * w x))
    (hnonfit : ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      ∀ x ∈ T, P₀.eval x = A * w x ∧ P₁.eval x = B * w x) :
    A + γ * B = 0 := by
  by_contra hscale
  exact hnonfit (scalar_pair_simultaneous_fit T w A B γ k P hP hfit hscale)

/-- Such a failure also forces the second scalar to be nonzero. -/
theorem scalar_pair_mca_second_ne_zero (T : Finset K) (w : K → K)
    (A B γ : K) (k : ℕ) (P : K[X])
    (hP : P.natDegree < k)
    (hfit : ∀ x ∈ T, P.eval x = A * w x + γ * (B * w x))
    (hnonfit : ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      ∀ x ∈ T, P₀.eval x = A * w x ∧ P₁.eval x = B * w x) :
    B ≠ 0 := by
  intro hB
  have hA : A = 0 := by
    simpa only [hB, mul_zero, add_zero] using
      scalar_pair_mca_scale_eq_zero T w A B γ k P hP hfit hnonfit
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hP
  apply hnonfit
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simpa only [natDegree_zero] using hk
  · simpa only [natDegree_zero] using hk
  · simp only [eval_zero, hA, hB, zero_mul, and_self, implies_true]

/-- The support and interpolating polynomial may vary with the parameter. -/
theorem scalar_pair_mca_parameters_card_le (w : K → K) (A B : K)
    (k : ℕ) (Γ : Finset K)
    (hmca : ∀ γ ∈ Γ, ∃ (T : Finset K) (P : K[X]), P.natDegree < k ∧
      (∀ x ∈ T, P.eval x = A * w x + γ * (B * w x)) ∧
      ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
        ∀ x ∈ T, P₀.eval x = A * w x ∧ P₁.eval x = B * w x) :
    Γ.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro γ hγ δ hδ
  obtain ⟨Tγ, Pγ, hPγ, hfitγ, hnonfitγ⟩ := hmca γ hγ
  obtain ⟨Tδ, Pδ, hPδ, hfitδ, hnonfitδ⟩ := hmca δ hδ
  have heγ := scalar_pair_mca_scale_eq_zero Tγ w A B γ k Pγ hPγ hfitγ hnonfitγ
  have heδ := scalar_pair_mca_scale_eq_zero Tδ w A B δ k Pδ hPδ hfitδ hnonfitδ
  have hB := scalar_pair_mca_second_ne_zero Tγ w A B γ k Pγ hPγ hfitγ hnonfitγ
  exact mul_right_cancel₀ hB (add_left_cancel (heγ.trans heδ.symm))

/-- Degree-zero moving gauges admit at most one literal MCA parameter, even with
an arbitrary fixed polynomial factor and common word. -/
theorem constant_gauge_mca_parameters_card_le (g a b : K[X]) (c : K → K)
    (k : ℕ) (Γ : Finset K) (hdeg : max a.natDegree b.natDegree = 0)
    (hmca : ∀ γ ∈ Γ, ∃ (T : Finset K) (P : K[X]), P.natDegree < k ∧
      (∀ x ∈ T, P.eval x = (g * a).eval x * c x + γ * ((g * b).eval x * c x)) ∧
      ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
        ∀ x ∈ T, P₀.eval x = (g * a).eval x * c x ∧
          P₁.eval x = (g * b).eval x * c x) :
    Γ.card ≤ 1 := by
  have ha : a = C (a.coeff 0) := eq_C_of_natDegree_le_zero
    ((le_max_left a.natDegree b.natDegree).trans_eq hdeg)
  have hb : b = C (b.coeff 0) := eq_C_of_natDegree_le_zero
    ((le_max_right a.natDegree b.natDegree).trans_eq hdeg)
  have hval (q : K[X]) (hq : q = C (q.coeff 0)) (x : K) :
      (g * q).eval x * c x = q.coeff 0 * (g.eval x * c x) := by
    rw [eval_mul, hq, eval_C, coeff_C_zero]
    ring
  apply scalar_pair_mca_parameters_card_le (fun x => g.eval x * c x)
    (a.coeff 0) (b.coeff 0) k Γ
  simpa only [hval a ha, hval b hb] using hmca


end ProximityPadeDegreeDrop


namespace ProximityPadeGaugeCount
noncomputable section
open Polynomial ProximityPadeGaugeObstruction
variable {K : Type*} [Field K]

/-- A bad conjugate-coprimality parameter has a common root in the algebraic closure. -/
theorem bad_parameter_root (p : ℕ) [Fact p.Prime] [CharP K p]
    (a b g : K[X]) (γ : K) (hab : IsCoprime a b)
    (hbad : ¬ IsCoprime (a+γ • b)
      (g.map (frobenius K p)*(a+γ • b).map (frobenius K p))) :
    ∃ z : AlgebraicClosure K,
      aeval z (a+γ • b)=0 ∧ aeval z b≠0 ∧
      aeval z (obstruction (frobenius K p) p a b * g.map (frobenius K p))=0 := by
  classical
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)] at hbad
  push Not at hbad
  obtain ⟨z,hz,hprod⟩ := hbad
  refine ⟨z,hz,?_,?_⟩
  · intro hb
    have ha : aeval z a=0 := by simpa [map_add,map_smul,hb] using hz
    exact (Polynomial.aeval_ne_zero_of_isCoprime hab z).elim (fun h => h ha) (fun h => h hb)
  · simp only [map_mul] at hprod ⊢
    rcases mul_eq_zero.mp hprod with hg | hσ
    · exact mul_eq_zero.mpr (Or.inr hg)
    · apply mul_eq_zero.mpr; left
      have hz' : aeval z a + algebraMap K (AlgebraicClosure K) γ * aeval z b=0 := by
        simpa [map_add,map_smul,Algebra.smul_def] using hz
      have hpz := congrArg (frobenius (AlgebraicClosure K) p) hz'
      have hσ' : aeval z (a.map (frobenius K p)) +
          (algebraMap K (AlgebraicClosure K) γ)^p * aeval z (b.map (frobenius K p))=0 := by
        simpa [Polynomial.map_add,Polynomial.map_smul,Algebra.smul_def,frobenius_def,map_pow] using hσ
      simp only [obstruction,map_sub,map_mul,map_pow]
      simp only [map_add,map_mul,map_zero,frobenius_def] at hpz
      linear_combination aeval z (b.map (frobenius K p))*hpz - (aeval z b)^p*hσ'

/-- Distinct bad parameters choose distinct roots of a single nonzero polynomial. -/
theorem bad_parameters_card_le (p : ℕ) [Fact p.Prime] [CharP K p]
    (a b g : K[X]) (hab : IsCoprime a b) (hg : g≠0)
    (hdegree : 0<max a.natDegree b.natDegree)
    (Γ : Finset K)
    (hbad : ∀ γ∈Γ, ¬ IsCoprime (a+γ • b)
      (g.map (frobenius K p)*(a+γ • b).map (frobenius K p))) :
    Γ.card ≤ max a.natDegree b.natDegree*(p+1)+g.natDegree := by
  classical
  let f := algebraMap K (AlgebraicClosure K)
  let W := obstruction (frobenius K p) p a b * g.map (frobenius K p)
  have hW : W≠0 := mul_ne_zero
    (obstruction_ne_zero _ p (Fact.out : p.Prime).one_lt a b hab hdegree)
    ((Polynomial.map_ne_zero_iff (frobenius K p).injective).mpr hg)
  have hWmap : W.map f≠0 := (Polynomial.map_ne_zero_iff f.injective).mpr hW
  choose z hz hzb hzw using fun γ : Γ => bad_parameter_root p a b g γ hab (hbad γ γ.prop)
  let Z := (W.map f).roots.toFinset
  let ι : Γ → Z := fun γ => ⟨z γ, by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hWmap).mpr
    simpa only [f,W,Polynomial.IsRoot.def,Polynomial.eval_map_algebraMap] using hzw γ⟩
  have hinj : Function.Injective ι := by
    intro γ δ heq
    have hzsame : z γ=z δ := congrArg Subtype.val heq
    have hγ := hz γ
    have hδ := hz δ
    rw [←hzsame] at hδ
    simp [map_add,Algebra.smul_def] at hγ hδ
    have hmul : f (γ:K)*aeval (z γ) b=f (δ:K)*aeval (z γ) b := by
      exact add_left_cancel (hγ.trans hδ.symm)
    apply Subtype.ext
    exact f.injective (mul_right_cancel₀ (hzb γ) hmul)
  have hc := Fintype.card_le_of_injective ι hinj
  simp only [Fintype.card_coe] at hc
  calc
    Γ.card ≤ Z.card := hc
    _ ≤ (W.map f).natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
    _ = W.natDegree := Polynomial.natDegree_map f
    _ ≤ (obstruction (frobenius K p) p a b).natDegree+(g.map (frobenius K p)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ max a.natDegree b.natDegree*(p+1)+g.natDegree := by
      rw [Polynomial.natDegree_map]
      exact Nat.add_le_add_right (obstruction_natDegree_le _ p _ a b (le_max_left _ _) (le_max_right _ _)) _

end
end ProximityPadeGaugeCount

open Polynomial ProximityPadePolynomialGauge ProximityPadeDegreeDrop ProximityPadeGaugeCount

theorem solution {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (g a b : K[X]) (hab : IsCoprime a b) (c : K → K) (k : ℕ) (Γ : Finset K)
    (hmca : ∀ γ∈Γ, ∃ (T : Finset K) (P : K[X]),
      k+g.natDegree+max a.natDegree b.natDegree≤T.card ∧
      (∀ x∈T, x^p=x) ∧ (∀ x∈T, (c x)^p=c x) ∧
      P.natDegree<k ∧
      (∀ x∈T, P.eval x=(g*a).eval x*c x+γ*((g*b).eval x*c x)) ∧
      ¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=(g*a).eval x*c x) ∧
        (∀ x∈T, P₁.eval x=(g*b).eval x*c x)) :
    Γ.card≤max a.natDegree b.natDegree*(p+1)+g.natDegree+1 := by
  classical
  by_cases hg : g=0
  · have hΓ : Γ=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨T,P,hcard,hx,hc,hP,hfit,hnot⟩ := hmca γ hγ
      have hk : 0<k := (Nat.zero_le _).trans_lt hP
      apply hnot
      refine ⟨0,0,?_,?_,?_,?_⟩
      · simpa using hk
      · simpa using hk
      · simp [hg]
      · simp [hg]
    simp [hΓ]
  by_cases hdegree : max a.natDegree b.natDegree=0
  · have hsmall : Γ.card≤1 := constant_gauge_mca_parameters_card_le g a b c k Γ hdegree (by
      intro γ hγ
      obtain ⟨T,P,hcard,hx,hc,hP,hfit,hnot⟩ := hmca γ hγ
      refine ⟨T,P,hP,hfit,?_⟩
      rintro ⟨P₀,P₁,h₀,h₁,hvalues⟩
      exact hnot ⟨P₀,P₁,h₀,h₁,fun x hx => (hvalues x hx).1,fun x hx => (hvalues x hx).2⟩)
    omega
  let d := max a.natDegree b.natDegree
  let G := Γ.filter (fun γ => d≤(a+γ • b).natDegree)
  let D := Γ.filter (fun γ => ¬ d≤(a+γ • b).natDegree)
  have hGbad : ∀ γ∈G, ¬ IsCoprime (a+γ • b)
      (g.map (frobenius K p)*(a+γ • b).map (frobenius K p)) := by
    intro γ hγ hcop
    obtain ⟨hγΓ,hdγ⟩ := Finset.mem_filter.mp hγ
    obtain ⟨T,P,hcard,hx,hc,hP,hfit,hnot⟩ := hmca γ hγΓ
    have hsum : (a+γ • b).natDegree≤d :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (le_max_left _ _)
        ((Polynomial.natDegree_smul_le _ _).trans (le_max_right _ _)))
    have hprod : (g*(a+γ • b)).natDegree≤g.natDegree+d :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left hsum _)
    exact (frobenius_fixed_factor_not_mca p T c hx hc g a b γ k
      ((le_max_left _ _).trans hdγ) ((le_max_right _ _).trans hdγ)
      (by omega) hcop) ⟨P,hP,hfit,hnot⟩
  have hG : G.card≤d*(p+1)+g.natDegree := bad_parameters_card_le p a b g hab hg
    (Nat.pos_of_ne_zero hdegree) G hGbad
  have hD : D.card≤1 := degree_drop_parameters_card_le a b D (by
    intro γ hγ
    exact Nat.lt_of_not_ge (Finset.mem_filter.mp hγ).2)
  have hsplit : G.card+D.card=Γ.card := Finset.card_filter_add_card_filter_not _
  change Γ.card≤d*(p+1)+g.natDegree+1
  omega

