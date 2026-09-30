-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_residual_intersection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T14:33:03.823897+00:00
-- url     : https://prove2.me/submissions/1c0d6436-dd16-4728-aae9-59d0fa2b0147

import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_colon
import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_sum
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
    let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    let K := J ⊓ R
    I ≤ K ∧ K ^ 2 ≤ I ∧
      K = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val
        (max (e v) (n v - e v))) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
        ∑ v : V, max (e v) (n v - e v) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
      (K = I ↔ J ⊔ R = ⊤) := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
  let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
  let K := J ⊓ R
  have hmono (v : V) (a b : ℕ) (hba : b ≤ a) :
      extensionChartContactIdeal g₂ g₃ c v.val a ≤
        extensionChartContactIdeal g₂ g₃ c v.val b :=
    Ideal.span_mono fun p hp j hj => hp j (hj.trans_le hba)
  have hIJ : I ≤ J := by
    intro p hp
    exact (Submodule.mem_iInf _).mpr fun v =>
      hmono v _ _ (he v) ((Submodule.mem_iInf _).mp hp v)
  have hIK : I ≤ K := le_inf hIJ Ideal.le_colon
  have hsq : K ^ 2 ≤ I := by
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro p hp q hq
    simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon.mp hq.2 p hp.1
  have hR : R = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)) :=
    (finite_contact_ideal_colon g₂ g₃ c V n e he).1
  have hK : K = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val
      (max (e v) (n v - e v))) := by
    change J ⊓ R = _
    rw [hR]
    apply le_antisymm
    · intro p hp
      apply (Submodule.mem_iInf _).mpr
      intro v
      by_cases hv : e v ≤ n v - e v
      · simpa only [max_eq_right hv] using (Submodule.mem_iInf _).mp hp.2 v
      · simpa only [max_eq_left (le_of_not_ge hv)] using (Submodule.mem_iInf _).mp hp.1 v
    · intro p hp
      exact ⟨(Submodule.mem_iInf _).mpr fun v =>
          hmono v _ _ (le_max_left _ _) ((Submodule.mem_iInf _).mp hp v),
        (Submodule.mem_iInf _).mpr fun v =>
          hmono v _ _ (le_max_right _ _) ((Submodule.mem_iInf _).mp hp v)⟩
  obtain ⟨hfinite, hdim, _⟩ := elliptic_extension_contact_quotient_dimension
    g₂ g₃ c V (fun v => max (e v) (n v - e v))
  have hKdim : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
      ∑ v : V, max (e v) (n v - e v) := by
    rw [hK]
    exact hdim
  have hIdim : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = ∑ v : V, n v :=
    (elliptic_extension_contact_quotient_dimension g₂ g₃ c V n).2.1
  have hsum := finite_contact_ideal_sum g₂ g₃ c V e (fun v => n v - e v)
  have hsumdim : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
      ∑ v : V, min (e v) (n v - e v) := by
    rw [hR]
    exact hsum.2.2.1
  have htop : J ⊔ R = ⊤ ↔ ∀ v : V, e v = 0 ∨ e v = n v := by
    rw [hR, hsum.2.2.2]
    apply forall_congr'
    intro v
    have hv := he v
    omega
  have hbalance : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) := by
    rw [hKdim, hsumdim, hIdim, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have hv := he v
    omega
  refine ⟨hIK, hsq, hK, ?_, hKdim, hbalance, ?_⟩
  · change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K)
    rw [hK]
    exact hfinite
  · change K = I ↔ J ⊔ R = ⊤
    rw [htop]
    constructor
    · intro hKI
      have hzero : ∑ v : V, min (e v) (n v - e v) = 0 := by
        rw [hKI, hsumdim] at hbalance
        omega
      intro v
      have hz := (Finset.sum_eq_zero_iff.mp hzero) v (Finset.mem_univ v)
      have hv := he v
      omega
    · intro hend
      rw [hK]
      apply iInf_congr
      intro v
      have hv : max (e v) (n v - e v) = n v := by
        rcases hend v with h | h <;> simp [h]
      rw [hv]

