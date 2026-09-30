-- Prove2me | solution 1 for WeierstrassEllipticZeta.residual_contact_ideal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T03:11:40.198723+00:00
-- url     : https://prove2.me/submissions/9ae7f723-8331-41f2-b79a-60401be1b18c

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon

noncomputable section
open WeierstrassEllipticZeta

private lemma residual_ideal_eq_of_colength
    (I J : Ideal (MvPolynomial (Fin 4) ℂ))
    [FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I)]
    (hle : I ≤ J)
    (hlen : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J)) : I = J := by
  let f : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₐ[ℂ] (MvPolynomial (Fin 4) ℂ ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id ℂ _) (by simpa using hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J q
    exact ⟨Ideal.Quotient.mkₐ ℂ I p, rfl⟩
  have : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) :=
    FiniteDimensional.of_surjective f.toLinearMap hsurj
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

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n e : V → ℕ) (he : ∀ v : V, e v ≤ n v)
    (p : MvPolynomial (Fin 4) ℂ)
    (hvan : ∀ (v : V) (j : ℕ), j < e v →
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let R := I.colon {p}
    (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) + ∑ v : V, e v = ∑ v : V, n v) →
      R = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = ∑ v : V, (n v - e v) := by
  classical
  dsimp only
  intro hbalance
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let R := I.colon {p}
  let E : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - e v)
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  have hER : E ≤ R := by
    intro q hq
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    apply (Submodule.mem_iInf _).mpr
    intro v
    have hp := (hc.1 c v.val (e v) p).mpr (hvan v)
    have hm := hc.2.1 c v.val (n v - e v) (e v)
      (Ideal.mul_mem_mul ((Submodule.mem_iInf _).mp hq v) hp)
    simpa only [Nat.sub_add_cancel (he v)] using hm
  have hsum : (∑ v : V, (n v - e v)) + ∑ v : V, e v = ∑ v : V, n v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => Nat.sub_add_cancel (he v))
  have hlen : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = ∑ v : V, (n v - e v) :=
    Nat.add_right_cancel (hbalance.trans hsum.symm)
  obtain ⟨hEfinite, hEdim, _⟩ :=
    elliptic_extension_contact_quotient_dimension g₂ g₃ c V (fun v => n v - e v)
  have : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ E) := hEfinite
  have hEq : E = R := residual_ideal_eq_of_colength E R hER (hEdim.trans hlen.symm)
  refine ⟨hEq.symm, ?_, hlen⟩
  change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R)
  rw [← hEq]
  exact hEfinite

