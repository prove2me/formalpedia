-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_generator_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T16:37:56.902682+00:00
-- url     : https://prove2.me/submissions/d3630378-d154-4132-bb67-ac2224510f38

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_iterated_differentiation

noncomputable section
open WeierstrassEllipticZeta

private lemma generator_derivation_span
    (A : Type*) [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A)
    (s : Set A) (J : Ideal A) (hle : Ideal.span s ≤ J)
    (hD : ∀ p ∈ s, D p ∈ J) (p : A) (hp : p ∈ Ideal.span s) : D p ∈ J := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact hD p hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using J.add_mem hp hq
  | smul a p hp ih =>
    simpa only [smul_eq_mul, D.leibniz] using
      J.add_mem (Ideal.mul_mem_left J a ih) (Ideal.mul_mem_right (D a) J (hle hp))

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (r : ℕ)
    (f : Fin r → MvPolynomial (Fin 4) ℂ)
    (hgen : Ideal.span (Set.range f) =
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) (k : ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r =>
      (extensionChartDerivation g₂ g₃ c)^[i.1.val] (f i.2)))
    K = I ⊔ Ideal.span ((extensionChartDerivation g₂ g₃ c)^[k] ''
      (I : Set (MvPolynomial (Fin 4) ℂ))) ∧
      K = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - k)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (n v - k) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ I ∧
          p - (extensionChartDerivation g₂ g₃ c)^[k] q ∈ I) ∧
      (K = ⊤ ↔ ∀ v : V, n v ≤ k) := by
  classical
  let D := extensionChartDerivation g₂ g₃ c
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  change Ideal.span (Set.range f) = I at hgen
  let F : ℕ → Ideal (MvPolynomial (Fin 4) ℂ) := fun j =>
    Ideal.span (Set.range (fun i : Fin (j + 1) × Fin r => D^[i.1.val] (f i.2)))
  have hc := (elliptic_extension_contact_ideal_structure g₂ g₃).1
  have hf (i : Fin r) : f i ∈ I := by
    rw [← hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hupper (a : ℕ) : F a ≤
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - a) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro v
    apply (hc c v.val (n v - a) _).mpr
    intro j hj
    rw [← Function.iterate_add_apply]
    have hi := i.1.isLt
    exact (hc c v.val (n v) _).mp ((Submodule.mem_iInf _).mp (hf i.2) v)
      (j + i.1.val) (by omega)
  have hbase : F 0 = I := by
    rw [← hgen]
    apply congrArg Ideal.span
    ext p
    constructor
    · rintro ⟨⟨i, a⟩, rfl⟩
      refine ⟨a, ?_⟩
      simp
    · rintro ⟨i, rfl⟩
      exact ⟨(0, i), rfl⟩
  have hF (a : ℕ) : F a =
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - a) := by
    induction a with
    | zero => simpa only [Nat.sub_zero] using hbase
    | succ a ih =>
      have hmono : F a ≤ F (a + 1) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨(⟨i.1.val, by have := i.1.isLt; omega⟩, i.2), rfl⟩
      have hDgen (p : MvPolynomial (Fin 4) ℂ)
          (hp : p ∈ Set.range (fun i : Fin (a + 1) × Fin r => D^[i.1.val] (f i.2))) :
          D p ∈ F (a + 1) := by
        obtain ⟨i, rfl⟩ := hp
        rw [← Function.iterate_succ_apply' D i.1.val]
        exact Ideal.subset_span ⟨(⟨i.1.val + 1, by have := i.1.isLt; omega⟩, i.2), rfl⟩
      have hstep := (finite_contact_iterated_differentiation
        g₂ g₃ c V (fun v => n v - a) 1).1
      rw [← ih] at hstep
      have hEq : F a ⊔ Ideal.span (D '' (F a : Set (MvPolynomial (Fin 4) ℂ))) =
          ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - (a + 1)) := by
        simpa only [Function.iterate_one, Nat.sub_sub] using hstep
      apply le_antisymm (hupper (a + 1))
      rw [← hEq]
      apply sup_le hmono
      apply Ideal.span_le.mpr
      rintro _ ⟨p, hp, rfl⟩
      exact generator_derivation_span _ D _ (F (a + 1)) hmono hDgen p hp
  have hdiff := finite_contact_iterated_differentiation g₂ g₃ c V n k
  dsimp only at hdiff
  have hEq : F k = I ⊔ Ideal.span (D^[k] '' (I : Set (MvPolynomial (Fin 4) ℂ))) :=
    (hF k).trans hdiff.1.symm
  dsimp only [F, D, I] at hEq
  rw [← hEq] at hdiff
  exact ⟨hEq, hdiff⟩

