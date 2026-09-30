-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_ideal_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T01:34:18.220791+00:00
-- url     : https://prove2.me/submissions/2db29786-2dbf-4623-9c49-b48dd1562823

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open WeierstrassEllipticZeta

private lemma ideal_eq_of_quotient_length
    (I J : Ideal (MvPolynomial (Fin 4) ℂ))
    [FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I)]
    [FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J)]
    (hle : I ≤ J)
    (hlen : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J)) : I = J := by
  let f : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₐ[ℂ] (MvPolynomial (Fin 4) ℂ ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id ℂ _) (by simpa using hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J q
    exact ⟨Ideal.Quotient.mkₐ ℂ I p, rfl⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hlen
      (f := f.toLinearMap)).mpr hsurj
  apply le_antisymm hle
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change Ideal.Quotient.mk J p = f 0
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2)
    (hcontact : ∀ (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v)
    (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ)
    (hvan : ∀ (v : V) (i : Fin K) (j : ℕ), j < e v →
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] (f i)) = 0)
    (hfinite : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸
      ((⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ⊔ Ideal.span (Set.range f))))
    (hlen : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
      ((⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ⊔ Ideal.span (Set.range f))) =
        ∑ v : V, e v) :
    (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ⊔ Ideal.span (Set.range f) =
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v) := by
  classical
  let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let J := I ⊔ Ideal.span (Set.range f)
  let E := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (e v)
  have hIE : I ≤ E := by
    intro p hp
    apply (Submodule.mem_iInf _).mpr
    intro v
    apply (hcontact v.val (e v) p).mpr
    intro j hj
    exact (hcontact v.val (n v) p).mp ((Submodule.mem_iInf _).mp hp v)
      j (hj.trans_le (he v))
  have hfE : Ideal.span (Set.range f) ≤ E := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro v
    exact (hcontact v.val (e v) (f i)).mpr (fun j hj => hvan v i j hj)
  obtain ⟨hEfinite, hElen, _⟩ := elliptic_extension_contact_quotient_dimension g₂ g₃ c V e
  have : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) := hfinite
  have : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ E) := hEfinite
  exact ideal_eq_of_quotient_length J E (sup_le hIE hfE) (hlen.trans hElen.symm)

