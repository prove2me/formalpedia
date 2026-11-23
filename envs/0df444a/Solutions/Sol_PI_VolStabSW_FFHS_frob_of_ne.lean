-- Prove2me | solution 1 for PI.VolStabSW.FFHS.frob_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:55.991535+00:00
-- url     : https://prove2.me/submissions/f19caaa3-1247-4725-b687-41c865c2afe7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
private theorem card_le_natDegree_of_eval_eq_zero {L : Type} [Field L] (P : L[X]) (hP : P ≠ 0)
    (Z : Finset L) (hZ : ∀ z ∈ Z, P.eval z = 0) : Z.card ≤ P.natDegree := by
  have hsub : Z.val ⊆ P.roots := fun z hz =>
    (Polynomial.mem_roots hP).mpr (hZ z (Finset.mem_val.mp hz))
  exact (Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr hsub)).trans
    (Polynomial.card_roots' P)
private theorem card_le_of_pow_eq_mul_add {L : Type} [Field L] (n : ℕ) (hn : 1 < n) (b c : L)
    (Z : Finset L) (hZ : ∀ z ∈ Z, z ^ n = b * z + c) : Z.card ≤ n := by
  have hlt : (C b * X + C c : L[X]).natDegree < (X ^ n : L[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le hn
  have hdeg : (X ^ n - (C b * X + C c) : L[X]).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP0 : (X ^ n - (C b * X + C c) : L[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have := card_le_natDegree_of_eval_eq_zero _ hP0 Z fun z hz => by simp [hZ z hz]
  rwa [hdeg] at this
private theorem exists_algebraMap_eq_of_frobenius_fixed (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  by_contra hne
  push_neg at hne
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hdS : d ∉ Finset.univ.image (algebraMap k K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hc := card_le_of_pow_eq_mul_add (Fintype.card k) hq 1 0
    (Finset.cons d (Finset.univ.image (algebraMap k K)) hdS) (by
      intro z hz
      rw [Finset.mem_cons] at hz
      rcases hz with h | hz
      · rw [h, hd, one_mul, add_zero]
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
        rw [← map_pow, FiniteField.pow_card, one_mul, add_zero])
  rw [Finset.card_cons, Finset.card_image_of_injective _ (algebraMap k K).injective,
    Finset.card_univ] at hc
  omega
end field
end PI.VolStabSW.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabSW.FFHS
theorem _root_.solution (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  intro x
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  by_cases hx : ∃ a : k, algebraMap k K a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [AlgEquiv.commutes, ← map_pow, FiniteField.pow_card]
  push_neg at hx
  have hq : x ^ Fintype.card k ≠ x := fun h => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_frobenius_fixed x h
    exact hx a ha
  have hσx : σ x ≠ x := by
    intro hfix
    apply hne
    have hli : LinearIndependent k ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        exact ⟨by simpa using hst, rfl⟩
      · exfalso
        have htK : algebraMap k K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        apply hx (-s * t⁻¹)
        rw [map_mul, map_neg, map_inv₀, eq_comm, eq_mul_inv_iff_mul_eq₀ htK]
        linear_combination hst
    have hlin : σ.toLinearMap = LinearMap.id :=
      (basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])).ext fun i => by
        fin_cases i <;> simp [coe_basisOfLinearIndependentOfCardEqFinrank, hfix]
    ext y
    simpa using LinearMap.congr_fun hlin y
  have hint_r : IsIntegral k x := IsIntegral.of_finite k x
  have hP0 : (minpoly k x).map (algebraMap k K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint_r)
  have hroot : ∀ y, Polynomial.aeval y (minpoly k x) = 0 →
      ((minpoly k x).map (algebraMap k K)).eval y = 0 := fun y hy => by
    rw [Polynomial.eval_map_algebraMap]
    exact hy
  have r1 := hroot x (minpoly.aeval k x)
  have r2 := hroot (σ x) (by
    rw [show σ x = (σ : K →ₐ[k] K) x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero])
  have r3 := hroot (x ^ Fintype.card k) (by
    rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero])
  by_contra hne3
  have hcard : ({x, σ x, x ^ Fintype.card k} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, σ x, x ^ Fintype.card k, hσx.symm, hq.symm, hne3, rfl⟩
  have hle := card_le_natDegree_of_eval_eq_zero _ hP0 {x, σ x, x ^ Fintype.card k} (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption)
  rw [hcard, Polynomial.natDegree_map] at hle
  have hdeg : (minpoly k x).natDegree ≤ finrank k K := minpoly.natDegree_le x
  omega
end PI.VolStabSW.FFHS
