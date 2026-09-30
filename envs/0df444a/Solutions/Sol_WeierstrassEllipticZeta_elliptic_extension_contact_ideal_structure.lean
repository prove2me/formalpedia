-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_contact_ideal_structure
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T21:36:30.750349+00:00
-- url     : https://prove2.me/submissions/6462b640-e783-486d-8804-beaf64c716a6

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta

private lemma jets_add (D : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ))
    (v : Fin 4 → ℂ) (p q : MvPolynomial (Fin 4) ℂ) (k : ℕ) :
    eval v (D^[k] (p + q)) = eval v (D^[k] p) + eval v (D^[k] q) := by
  simpa only [Module.End.pow_apply] using!
    (show eval v ((D.toLinearMap ^ k) (p + q)) =
      eval v ((D.toLinearMap ^ k) p) + eval v ((D.toLinearMap ^ k) q) by simp)

private lemma jets_mul_closed
    (D : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ))
    (v : Fin 4 → ℂ) (k : ℕ) (p q : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ i ≤ k, eval v (D^[i] p) = 0) : eval v (D^[k] (q * p)) = 0 := by
  induction k generalizing p q with
  | zero => simpa using congrArg (fun z : ℂ => eval v q * z) (hp 0 le_rfl)
  | succ k ih =>
    rw [Function.iterate_succ_apply, D.leibniz, smul_eq_mul, smul_eq_mul, jets_add]
    have hDp : ∀ i ≤ k, eval v (D^[i] (D p)) = 0 := by
      intro i hi
      rw [← Function.iterate_succ_apply]
      exact hp (i + 1) (by omega)
    rw [ih (D p) q hDp, mul_comm p (D q), ih p (D q) (fun i hi => hp i (by omega))]
    exact add_zero 0

private lemma contact_mem_iff (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ)
    (p : MvPolynomial (Fin 4) ℂ) :
    p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
      ∀ k < n, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0 := by
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem p hp => exact hp
    | zero =>
      intro k _
      simpa only [Module.End.pow_apply] using!
        (show eval v (((extensionChartDerivation g₂ g₃ c).toLinearMap ^ k) 0) = 0 by simp)
    | add p q _ _ hp hq =>
      intro k hk
      rw [jets_add, hp k hk, hq k hk, add_zero]
    | smul q p _ hp =>
      intro k hk
      exact jets_mul_closed _ v k p q (fun i hi => hp i (lt_of_le_of_lt hi hk))
  · intro hp
    exact Ideal.subset_span hp

private lemma contact_zero (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) :
    extensionChartContactIdeal g₂ g₃ c v 0 = ⊤ := by
  ext p
  simp [contact_mem_iff]

private lemma contact_mul (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) (m n : ℕ) :
    extensionChartContactIdeal g₂ g₃ c v m * extensionChartContactIdeal g₂ g₃ c v n ≤
      extensionChartContactIdeal g₂ g₃ c v (m + n) := by
  apply Ideal.mul_le.mpr
  intro p hp q hq
  rw [contact_mem_iff] at hp hq ⊢
  intro k hk
  induction k generalizing m n p q with
  | zero =>
    simp only [Function.iterate_zero_apply, map_mul]
    by_cases hm : m = 0
    · have hq0 : eval v q = 0 := hq 0 (by omega)
      rw [hq0, mul_zero]
    · have hp0 : eval v p = 0 := hp 0 (by omega)
      rw [hp0, zero_mul]
  | succ k ih =>
    by_cases hm : m = 0
    · exact jets_mul_closed _ v (k + 1) q p (fun i hi => hq i (by omega))
    by_cases hn : n = 0
    · rw [mul_comm]
      exact jets_mul_closed _ v (k + 1) p q (fun i hi => hp i (by omega))
    rw [Function.iterate_succ_apply, Derivation.leibniz, smul_eq_mul, smul_eq_mul, jets_add]
    have hDp : ∀ i < m - 1, eval v ((extensionChartDerivation g₂ g₃ c)^[i]
        (extensionChartDerivation g₂ g₃ c p)) = 0 := by
      intro i hi
      rw [← Function.iterate_succ_apply]
      exact hp (i + 1) (by omega)
    have hDq : ∀ i < n - 1, eval v ((extensionChartDerivation g₂ g₃ c)^[i]
        (extensionChartDerivation g₂ g₃ c q)) = 0 := by
      intro i hi
      rw [← Function.iterate_succ_apply]
      exact hq (i + 1) (by omega)
    rw [ih (m := m) (n := n - 1) (p := p) (q := _) hp hDq (by omega),
      ih (m := n) (n := m - 1) (p := q) (q := _) hq hDp (by omega), add_zero]

private lemma contact_one (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) :
    extensionChartContactIdeal g₂ g₃ c v 1 = RingHom.ker (eval v) := by
  ext p
  simp [contact_mem_iff, RingHom.mem_ker]

private lemma contact_power (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) :
    RingHom.ker (eval v) ^ n ≤ extensionChartContactIdeal g₂ g₃ c v n := by
  induction n with
  | zero => simp [contact_zero]
  | succ n ih =>
    calc
      _ = RingHom.ker (eval v) ^ n * extensionChartContactIdeal g₂ g₃ c v 1 := by
        rw [contact_one, pow_succ]
      _ ≤ extensionChartContactIdeal g₂ g₃ c v n *
          extensionChartContactIdeal g₂ g₃ c v 1 := Ideal.mul_mono ih le_rfl
      _ ≤ _ := contact_mul g₂ g₃ c v n 1

private lemma contact_radical (g₂ g₃ : ℂ) (c : Fin 2) (v : Fin 4 → ℂ)
    (n : ℕ) (hn : 0 < n) :
    (extensionChartContactIdeal g₂ g₃ c v n).radical = RingHom.ker (eval v) := by
  apply le_antisymm
  · apply (RingHom.ker_isPrime (eval v)).radical_le_iff.mpr
    intro p hp
    exact (contact_mem_iff g₂ g₃ c v n p).mp hp 0 hn
  · intro p hp
    exact ⟨n, contact_power g₂ g₃ c v n (Ideal.pow_mem_pow hp n)⟩

private lemma eval_kernel_maximal (v : Fin 4 → ℂ) : (RingHom.ker (eval v)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval v) (fun z => ⟨C z, eval_C z⟩)

private lemma contact_coprime (g₂ g₃ : ℂ) (c : Fin 2) (v w : Fin 4 → ℂ)
    (hv : v ≠ w) (m n : ℕ) :
    extensionChartContactIdeal g₂ g₃ c v m ⊔ extensionChartContactIdeal g₂ g₃ c w n = ⊤ := by
  have := eval_kernel_maximal v
  have := eval_kernel_maximal w
  have hne : RingHom.ker (eval v) ≠ RingHom.ker (eval w) := by
    intro heq
    apply hv
    funext i
    have hp : X i - C (v i) ∈ RingHom.ker (eval v) := by simp [RingHom.mem_ker]
    rw [heq] at hp
    have : w i - v i = 0 := by simpa [RingHom.mem_ker] using hp
    exact (sub_eq_zero.mp this).symm
  have htop := Ideal.pow_sup_pow_eq_top (m := m) (n := n)
    (Ideal.isCoprime_of_isMaximal hne).sup_eq
  apply top_unique
  rw [← htop]
  exact sup_le_sup (contact_power g₂ g₃ c v m) (contact_power g₂ g₃ c w n)

theorem solution (g₂ g₃ : ℂ) :
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (m n : ℕ),
      extensionChartContactIdeal g₂ g₃ c v m * extensionChartContactIdeal g₂ g₃ c v n ≤
        extensionChartContactIdeal g₂ g₃ c v (m + n)) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ),
      RingHom.ker (eval v) ^ n ≤ extensionChartContactIdeal g₂ g₃ c v n) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ), 0 < n →
      (extensionChartContactIdeal g₂ g₃ c v n).radical = RingHom.ker (eval v) ∧
        (extensionChartContactIdeal g₂ g₃ c v n).IsPrimary) ∧
    (∀ (c : Fin 2) (v w : Fin 4 → ℂ), v ≠ w → ∀ m n : ℕ,
      extensionChartContactIdeal g₂ g₃ c v m ⊔ extensionChartContactIdeal g₂ g₃ c w n = ⊤) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v (n + 1) →
        extensionChartDerivation g₂ g₃ c p ∈ extensionChartContactIdeal g₂ g₃ c v n) ∧
    (∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
        (p : V → MvPolynomial (Fin 4) ℂ),
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v)) := by
  refine ⟨contact_mem_iff g₂ g₃, contact_mul g₂ g₃, contact_power g₂ g₃, ?_,
    contact_coprime g₂ g₃, ?_, ?_⟩
  · intro c v n hn
    have hr := contact_radical g₂ g₃ c v n hn
    exact ⟨hr, Ideal.isPrimary_of_isMaximal_radical (hr.symm ▸ eval_kernel_maximal v)⟩
  · intro c v n p hp
    rw [contact_mem_iff] at hp ⊢
    intro k hk
    rw [← Function.iterate_succ_apply]
    exact hp (k + 1) (by omega)
  · intro c V n p
    apply Ideal.exists_forall_sub_mem_ideal (I := fun v : V =>
      extensionChartContactIdeal g₂ g₃ c v.val (n v)) _ p
    intro v w hne
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (contact_coprime g₂ g₃ c v.val w.val (fun h => hne (Subtype.ext h)) (n v) (n w))

