-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_ideal_colon
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T13:30:45.904381+00:00
-- url     : https://prove2.me/submissions/34024857-e7a3-407e-8555-e72a023fe737

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open WeierstrassEllipticZeta

private lemma contact_colon_iterate_time
    (D : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ))
    (t : MvPolynomial (Fin 4) ℂ) (ht : D t = 1)
    (p : MvPolynomial (Fin 4) ℂ) (k : ℕ) :
    D^[k + 1] (p * t) = D^[k + 1] p * t + (k + 1) • D^[k] p := by
  induction k with
  | zero => simp [D.leibniz, ht, mul_comm]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_add, D.leibniz, ht, smul_eq_mul,
      smul_eq_mul, mul_one, map_nsmul]
    simp only [← Function.iterate_succ_apply']
    simp only [add_nsmul, one_nsmul]
    ac_rfl

private lemma contact_colon_cancel_time (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (p : MvPolynomial (Fin 4) ℂ) (k : ℕ)
    (hp : p * (MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v 0)) ∈
      extensionChartContactIdeal g₂ g₃ c v (k + 1)) :
    p ∈ extensionChartContactIdeal g₂ g₃ c v k := by
  have hc := (elliptic_extension_contact_ideal_structure g₂ g₃).1
  have ht : extensionChartDerivation g₂ g₃ c
      (MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v 0)) = 1 := by
    fin_cases c <;> simp [extensionChartDerivation]
  apply (hc c v k p).mpr
  intro j hj
  have hz := (hc c v (k + 1) _).mp hp (j + 1) (Nat.add_lt_add_right hj 1)
  rw [contact_colon_iterate_time _ _ ht] at hz
  have he : ((j + 1 : ℕ) : ℂ) *
      MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0 := by
    simpa [nsmul_eq_mul] using hz
  exact (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))

private lemma contact_colon_cancel_power (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (p : MvPolynomial (Fin 4) ℂ) (k e : ℕ)
    (hp : p * (MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v 0)) ^ e ∈
      extensionChartContactIdeal g₂ g₃ c v (k + e)) :
    p ∈ extensionChartContactIdeal g₂ g₃ c v k := by
  induction e with
  | zero => simpa using hp
  | succ e ih =>
    apply ih
    apply contact_colon_cancel_time g₂ g₃ c v _ (k + e)
    simpa only [pow_succ, mul_assoc, Nat.add_assoc] using hp

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
    let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    R = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = ∑ v : V, (n v - e v) := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
  let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
  let E : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  have hmono (w : V) : extensionChartContactIdeal g₂ g₃ c w.val (n w) ≤
      extensionChartContactIdeal g₂ g₃ c w.val (e w) := by
    intro p hp
    exact (hc.1 c w.val (e w) p).mpr fun j hj =>
      (hc.1 c w.val (n w) p).mp hp j (hj.trans_le (he w))
  have hRE : R = E := by
    apply le_antisymm
    · intro q hq
      apply (Submodule.mem_iInf _).mpr
      intro v
      let t := MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v.val 0)
      let a : V → MvPolynomial (Fin 4) ℂ := fun w => if w = v then t ^ e v else 0
      obtain ⟨p, hp⟩ := hc.2.2.2.2.2.2 c V n a
      have ha (w : V) : a w ∈ extensionChartContactIdeal g₂ g₃ c w.val (e w) := by
        by_cases hw : w = v
        · subst w
          simp only [a, if_pos rfl]
          have ht : t ∈ RingHom.ker (MvPolynomial.eval v.val) := by
            simp [t, RingHom.mem_ker]
          exact (hc.2.2.1 c v.val (e v)) (Ideal.pow_mem_pow ht (e v))
        · simp [a, hw]
      have hpJ : p ∈ J := by
        apply (Submodule.mem_iInf _).mpr
        intro w
        simpa only [sub_add_cancel] using
          (extensionChartContactIdeal g₂ g₃ c w.val (e w)).add_mem (hmono w (hp w)) (ha w)
      have hqp : q * p ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) :=
        (Submodule.mem_iInf _).mp
          (show q * p ∈ I from (Submodule.mem_colon.mp hq p hpJ)) v
      have hdiff : q * (p - t ^ e v) ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) :=
        Ideal.mul_mem_left _ q (by simpa [a] using hp v)
      have hpow : q * t ^ e v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
        have hz := (extensionChartContactIdeal g₂ g₃ c v.val (n v)).sub_mem hqp hdiff
        convert hz using 1
        ring
      apply contact_colon_cancel_power g₂ g₃ c v.val q (n v - e v) (e v)
      simpa only [Nat.sub_add_cancel (he v)] using hpow
    · intro q hq
      apply Submodule.mem_colon.mpr
      intro p hp
      change q * p ∈ I
      apply (Submodule.mem_iInf _).mpr
      intro v
      have hm := hc.2.1 c v.val (n v - e v) (e v)
        (Ideal.mul_mem_mul ((Submodule.mem_iInf _).mp hq v) ((Submodule.mem_iInf _).mp hp v))
      simpa only [Nat.sub_add_cancel (he v)] using hm
  obtain ⟨hfinite, hdim, _⟩ :=
    elliptic_extension_contact_quotient_dimension g₂ g₃ c V (fun v => n v - e v)
  refine ⟨hRE, ?_, ?_⟩
  · change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R)
    rw [hRE]
    exact hfinite
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = _
    rw [hRE]
    exact hdim

