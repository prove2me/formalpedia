-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_iterated_differentiation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T16:17:37.682895+00:00
-- url     : https://prove2.me/submissions/eb316349-0362-4f5b-a82c-ae6d1708d66c

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (k : ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let K := I ⊔ Ideal.span ((extensionChartDerivation g₂ g₃ c)^[k] ''
      (I : Set (MvPolynomial (Fin 4) ℂ)))
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
  let K := I ⊔ Ideal.span (D^[k] '' (I : Set (MvPolynomial (Fin 4) ℂ)))
  let E : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - k)
  have hc := (elliptic_extension_contact_ideal_structure g₂ g₃).1
  have hIE : I ≤ E := by
    intro p hp
    apply (Submodule.mem_iInf _).mpr
    intro v
    exact (hc c v.val (n v - k) p).mpr fun j hj =>
      (hc c v.val (n v) p).mp ((Submodule.mem_iInf _).mp hp v) j (by omega)
  have hDI (q : MvPolynomial (Fin 4) ℂ) (hq : q ∈ I) : D^[k] q ∈ E := by
    apply (Submodule.mem_iInf _).mpr
    intro v
    apply (hc c v.val (n v - k) _).mpr
    intro j hj
    rw [← Function.iterate_add_apply]
    exact (hc c v.val (n v) q).mp ((Submodule.mem_iInf _).mp hq v) (j + k) (by omega)
  have hKE : K ≤ E := by
    apply sup_le hIE
    apply Ideal.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    exact hDI q hq
  have hprimitive (p : MvPolynomial (Fin 4) ℂ) (hp : p ∈ E) :
      ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ I ∧ p - D^[k] q ∈ I := by
    let a : (v : V) → Fin (n v + k) → ℂ := fun v i =>
      if k ≤ i.val then MvPolynomial.eval v.val (D^[i.val - k] p) else 0
    obtain ⟨q, hq⟩ := (elliptic_extension_contact_quotient_dimension
      g₂ g₃ c V (fun v => n v + k)).2.2 a
    refine ⟨q, ?_, ?_⟩
    · apply (Submodule.mem_iInf _).mpr
      intro v
      apply (hc c v.val (n v) q).mpr
      intro j hj
      rw [hq v ⟨j, by omega⟩]
      by_cases hkj : k ≤ j
      · simp only [a, if_pos hkj]
        exact (hc c v.val (n v - k) p).mp ((Submodule.mem_iInf _).mp hp v)
          (j - k) (by omega)
      · simp only [a, if_neg hkj]
    · apply (Submodule.mem_iInf _).mpr
      intro v
      apply (hc c v.val (n v) _).mpr
      intro j hj
      have hqj := hq v ⟨j + k, Nat.add_lt_add_right hj k⟩
      have heq : MvPolynomial.eval v.val (D^[j] (D^[k] q)) =
          MvPolynomial.eval v.val (D^[j] p) := by
        rw [← Function.iterate_add_apply]
        simpa only [a, if_pos (Nat.le_add_left k j), Nat.add_sub_cancel] using hqj
      simpa only [Module.End.pow_apply] using!
        (show MvPolynomial.eval v.val ((D.toLinearMap ^ j) (p - D^[k] q)) = 0 by
          rw [map_sub, map_sub]
          simpa only [Module.End.pow_apply] using! sub_eq_zero.mpr heq.symm)
  have hIK : I ≤ K := le_sup_left
  have hspanK : Ideal.span (D^[k] '' (I : Set (MvPolynomial (Fin 4) ℂ))) ≤ K :=
    le_sup_right
  have hgen (q : MvPolynomial (Fin 4) ℂ) (hq : q ∈ I) : D^[k] q ∈ K :=
    hspanK (Ideal.subset_span ⟨q, hq, rfl⟩)
  have hEK : E ≤ K := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hprimitive p hp
    simpa only [sub_add_cancel] using K.add_mem (hIK hpq) (hgen q hq)
  have hEq : K = E := le_antisymm hKE hEK
  obtain ⟨hfinite, hdim, _⟩ :=
    elliptic_extension_contact_quotient_dimension g₂ g₃ c V (fun v => n v - k)
  refine ⟨hEq, ?_, ?_, ?_, ?_⟩
  · change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K)
    rw [hEq]
    exact hfinite
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = _
    rw [hEq]
    exact hdim
  · intro p
    constructor
    · intro hp
      exact hprimitive p (hKE hp)
    · rintro ⟨q, hq, hpq⟩
      change p - D^[k] q ∈ I at hpq
      simpa only [sub_add_cancel] using K.add_mem (hIK hpq) (hgen q hq)
  · change K = ⊤ ↔ _
    rw [hEq]
    constructor
    · intro htop v
      by_contra hn
      have hone : (1 : MvPolynomial (Fin 4) ℂ) ∈ E := by rw [htop]; trivial
      have hz := (hc c v.val (n v - k) 1).mp ((Submodule.mem_iInf _).mp hone v) 0 (by omega)
      simp at hz
    · intro hn
      apply top_unique
      intro p _
      apply (Submodule.mem_iInf _).mpr
      intro v
      apply (hc c v.val (n v - k) p).mpr
      intro j hj
      have := hn v
      omega

