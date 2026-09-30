-- Prove2me | solution 1 for WeierstrassEllipticZeta.time_axis_jet_box_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T22:38:36.055554+00:00
-- url     : https://prove2.me/submissions/33046813-b633-401f-ac9c-f1ac694ec782

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_bounded_hermite_interpolation
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat

open WeierstrassEllipticZeta
open scoped Classical

noncomputable section

theorem solution
    (G : Frontier.Geometry) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (N : ℕ)
    (hinj : Function.Injective (fun v : V => v.val 0)) :
    let b : Fin 4 →₀ ℕ := Finsupp.single 0 (N * V.card)
    ∃ p : MvPolynomial (Fin 4) ℂ,
      p ≠ 0 ∧ (∀ i : Fin 4, p.degreeOf i ≤ b i) ∧
      (∑ i : Fin 4, p.degreeOf i *
        ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (b j + 1)) ≤ N * V.card ∧
      (∀ v : V, p ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c v.val N) ∧
      ∀ q : MvPolynomial (Fin 4) ℂ, ∃ r : MvPolynomial (Fin 4) ℂ,
        r.support ⊆ Finset.Iic b ∧
        ∀ (v : V) (k : Fin N), MvPolynomial.eval v.val
          ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] (q - r)) = 0 := by
  classical
  dsimp only
  let d := N * V.card
  let b : Fin 4 →₀ ℕ := Finsupp.single 0 d
  let M : Polynomial ℂ := ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ N
  have hMmonic : M.Monic := Polynomial.monic_prod_of_monic _ _ (fun v _ =>
    (Polynomial.monic_X_sub_C (v.val 0)).pow N)
  have hMdegree : M.natDegree = d := by
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun v _ =>
      (Polynomial.monic_X_sub_C (v.val 0)).pow N)]
    simp [d, Nat.mul_comm]
  have hsupport (w : Polynomial ℂ) (hw : w.natDegree ≤ d) :
      (w.toMvPolynomial (0 : Fin 4)).support ⊆ Finset.Iic b := by
    have hexpand : w.toMvPolynomial (0 : Fin 4) =
        ∑ k ∈ Finset.range (w.natDegree + 1),
          MvPolynomial.monomial (Finsupp.single 0 k) (w.coeff k) := by
      calc
        w.toMvPolynomial (0 : Fin 4) =
            (∑ k ∈ Finset.range (w.natDegree + 1),
              Polynomial.C (w.coeff k) * Polynomial.X ^ k).toMvPolynomial 0 :=
          congrArg (Polynomial.toMvPolynomial (0 : Fin 4)) w.as_sum_range_C_mul_X_pow
        _ = _ := by
          simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
            Polynomial.toMvPolynomial_X, MvPolynomial.C_mul_X_pow_eq_monomial]
    intro e he
    rw [hexpand] at he
    obtain ⟨k, hk, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
    have heq : e = Finsupp.single (0 : Fin 4) k :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    apply Finset.mem_Iic.mpr
    rw [heq]
    exact Finsupp.single_le_single.mpr ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hw)
  let p := M.toMvPolynomial (0 : Fin 4)
  have hfit (i : Fin 4) : p.degreeOf i ≤ b i := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Finset.mem_Iic.mp (hsupport M hMdegree.le he)) i
  refine ⟨p, ?_, hfit, ?_, ?_, ?_⟩
  · intro hp
    apply hMmonic.ne_zero
    apply Polynomial.toMvPolynomial_injective (0 : Fin 4)
    simpa only [map_zero] using hp
  · rw [Finset.sum_eq_single (0 : Fin 4)]
    · have hprod : (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase 0, (b j + 1)) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        have hj0 := Finset.ne_of_mem_erase hj
        simp [b, hj0]
      rw [hprod, mul_one]
      simpa [b] using hfit 0
    · intro i _ hi
      have hi0 : p.degreeOf i = 0 := by
        have h := hfit i
        simpa [b, Finsupp.single_apply, hi, Ne.symm hi] using h
      rw [hi0, zero_mul]
    · simp
  · intro v
    have hker : MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v.val 0) ∈
        RingHom.ker (MvPolynomial.eval v.val) := by simp
    have hfactor : ((Polynomial.X - Polynomial.C (v.val 0)) ^ N).toMvPolynomial
        (0 : Fin 4) ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c v.val N := by
      simpa only [map_pow, map_sub, Polynomial.toMvPolynomial_X, Polynomial.toMvPolynomial_C]
        using G.hcontact.2.2.1 c v.val N (Ideal.pow_mem_pow hker N)
    obtain ⟨q, hq⟩ : (Polynomial.X - Polynomial.C (v.val 0)) ^ N ∣ M :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
    change M.toMvPolynomial (0 : Fin 4) ∈ _
    rw [hq, map_mul]
    exact Ideal.mul_mem_right _ _ hfactor
  · intro q
    obtain ⟨w, hw, _⟩ := elliptic_extension_bounded_hermite_interpolation G.L.g₂ G.L.g₃
      c V (fun _ => N) hinj (fun v k => MvPolynomial.eval v.val
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] q))
    have hwdegree : w.natDegree ≤ d := by
      apply Polynomial.natDegree_le_of_degree_le
      simpa [d, Nat.mul_comm] using hw.1.le
    refine ⟨w.toMvPolynomial (0 : Fin 4), hsupport w hwdegree, ?_⟩
    intro v k
    have hsub (j : ℕ) :
        (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[j]
          (q - w.toMvPolynomial (0 : Fin 4)) =
        (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[j] q -
          (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[j]
            (w.toMvPolynomial (0 : Fin 4)) := by
      induction j with
      | zero => rfl
      | succ j ih => simp only [Function.iterate_succ_apply', ih, map_sub]
    rw [hsub k.val, map_sub]
    exact sub_eq_zero.mpr (hw.2 v k).symm
