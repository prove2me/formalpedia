-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_finite_contact_bezout_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T23:49:36.002059+00:00
-- url     : https://prove2.me/submissions/b2b09335-4ac1-466f-9298-d927a13bc636

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

noncomputable section
open WeierstrassEllipticZeta

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
    (hpower : ∀ v : V, RingHom.ker (MvPolynomial.eval v.val) ^ n v ≤
      extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (hcrt : ∀ p : V → MvPolynomial (Fin 4) ℂ,
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ)
    (hnonzero : ∀ v : V, 0 < n v → ∃ j : Fin K, MvPolynomial.eval v.val (f j) ≠ 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    ∃ a : Fin K → MvPolynomial (Fin 4) ℂ,
      1 - ∑ j : Fin K, a j * f j ∈ I ∧ I ⊔ Ideal.span (Set.range f) = ⊤ := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  have hlocal (v : V) : ∃ b : Fin K → MvPolynomial (Fin 4) ℂ,
      1 - ∑ j : Fin K, b j * f j ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
    by_cases hn : n v = 0
    · have htop : extensionChartContactIdeal g₂ g₃ c v.val (n v) = ⊤ := by
        apply top_unique
        simpa only [hn, pow_zero, Ideal.one_eq_top] using hpower v
      exact ⟨fun _ => 0, by rw [htop]; trivial⟩
    obtain ⟨j, hj⟩ := hnonzero v (Nat.pos_of_ne_zero hn)
    let u : MvPolynomial (Fin 4) ℂ :=
      1 - MvPolynomial.C ((MvPolynomial.eval v.val (f j))⁻¹) * f j
    have hu : u ∈ RingHom.ker (MvPolynomial.eval v.val) := by
      simp [u, RingHom.mem_ker, hj]
    let b : MvPolynomial (Fin 4) ℂ :=
      (∑ i ∈ Finset.range (n v), u ^ i) *
        MvPolynomial.C ((MvPolynomial.eval v.val (f j))⁻¹)
    have hb : 1 - b * f j = u ^ n v := by
      calc
        1 - b * f j = 1 - (∑ i ∈ Finset.range (n v), u ^ i) * (1 - u) := by
          dsimp [b, u]
          ring
        _ = u ^ n v := by rw [geom_sum_mul_neg, sub_sub_cancel]
    refine ⟨fun i => if i = j then b else 0, ?_⟩
    have hmem : 1 - b * f j ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
      rw [hb]
      exact hpower v (Ideal.pow_mem_pow hu (n v))
    simpa [ite_mul] using hmem
  choose b hb using hlocal
  choose a ha using fun j : Fin K => hcrt (fun v => b v j)
  have hcert : 1 - ∑ j : Fin K, a j * f j ∈ I := by
    apply (Submodule.mem_iInf _).mpr
    intro v
    have hsum : ∑ j : Fin K, (a j - b v j) * f j ∈
        extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
      exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (ha j v)
    have heq : 1 - ∑ j : Fin K, a j * f j =
        (1 - ∑ j : Fin K, b v j * f j) - ∑ j : Fin K, (a j - b v j) * f j := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact Ideal.sub_mem _ (hb v) hsum
  refine ⟨a, hcert, (Ideal.eq_top_iff_one _).mpr ?_⟩
  have hsum : ∑ j : Fin K, a j * f j ∈ Ideal.span (Set.range f) := by
    exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have h1 := (I ⊔ Ideal.span (Set.range f)).add_mem
    ((show I ≤ I ⊔ Ideal.span (Set.range f) from le_sup_left) hcert)
    ((show Ideal.span (Set.range f) ≤ I ⊔ Ideal.span (Set.range f) from le_sup_right) hsum)
  simpa using h1

