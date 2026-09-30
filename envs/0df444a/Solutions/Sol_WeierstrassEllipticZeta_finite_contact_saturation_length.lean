-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_saturation_length
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T02:26:19.151666+00:00
-- url     : https://prove2.me/submissions/6db8259d-5bb9-4c1d-9e42-0a1bc6391c4d

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.IsPrimary

noncomputable section
open WeierstrassEllipticZeta

private lemma saturation_cancel_power (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (n r : ℕ) (p q : MvPolynomial (Fin 4) ℂ)
    (hp : MvPolynomial.eval v p ≠ 0)
    (hq : q * p ^ r ∈ extensionChartContactIdeal g₂ g₃ c v n) :
    q ∈ extensionChartContactIdeal g₂ g₃ c v n := by
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (hc.1 c v 0 q).mpr (by intro k hk; omega)
  obtain ⟨hrad, hprimary⟩ := hc.2.2.2.1 c v n hn
  rcases (Ideal.isPrimary_iff.mp hprimary).2 hq with h | h
  · exact h
  · rw [hrad, RingHom.mem_ker, map_pow] at h
    exact (pow_ne_zero r hp h).elim

private lemma saturation_power_mem (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (n N : ℕ) (hn : n ≤ N)
    (p : MvPolynomial (Fin 4) ℂ) (hp : MvPolynomial.eval v p = 0) :
    p ^ N ∈ extensionChartContactIdeal g₂ g₃ c v n := by
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  exact hc.2.2.1 c v n (Ideal.pow_le_pow_right hn
    (Ideal.pow_mem_pow (show p ∈ RingHom.ker (MvPolynomial.eval v) from hp) N))

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (p : MvPolynomial (Fin 4) ℂ)
    (N : ℕ) (hN : ∀ v : V, n v ≤ N) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let e : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else n v
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
    I.colon {p ^ N} = J ∧
      (∀ q : MvPolynomial (Fin 4) ℂ, (∃ r : ℕ, q * p ^ r ∈ I) ↔ q ∈ J) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p ^ N}) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p ^ N}) = ∑ v : V, e v := by
  classical
  dsimp only
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let e : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else n v
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  have hforward (q : MvPolynomial (Fin 4) ℂ) (r : ℕ) (hq : q * p ^ r ∈ I) : q ∈ J := by
    apply (Submodule.mem_iInf _).mpr
    intro v
    by_cases hp : MvPolynomial.eval v.val p = 0
    · simp only [e, hp, ite_true]
      exact (hc.1 c v.val 0 q).mpr (by intro k hk; omega)
    · simp only [e, hp, ite_false]
      exact saturation_cancel_power g₂ g₃ c v.val (n v) r p q hp
        ((Submodule.mem_iInf _).mp hq v)
  have hback (q : MvPolynomial (Fin 4) ℂ) (hq : q ∈ J) : q * p ^ N ∈ I := by
    apply (Submodule.mem_iInf _).mpr
    intro v
    by_cases hp : MvPolynomial.eval v.val p = 0
    · exact (extensionChartContactIdeal g₂ g₃ c v.val (n v)).mul_mem_left q
        (saturation_power_mem g₂ g₃ c v.val (n v) N (hN v) p hp)
    · have h := (Submodule.mem_iInf _).mp hq v
      simp only [e, hp, ite_false] at h
      exact (extensionChartContactIdeal g₂ g₃ c v.val (n v)).mul_mem_right (p ^ N) h
  have heq : I.colon {p ^ N} = J := by
    ext q
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    exact ⟨hforward q N, hback q⟩
  have hd := elliptic_extension_contact_quotient_dimension g₂ g₃ c V e
  refine ⟨heq, ?_, ?_, ?_⟩
  · intro q
    exact ⟨fun ⟨r, h⟩ => hforward q r h, fun h => ⟨N, hback q h⟩⟩
  · change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p ^ N})
    rw [heq]
    exact hd.1
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p ^ N}) = ∑ v : V, e v
    rw [heq]
    exact hd.2.1

