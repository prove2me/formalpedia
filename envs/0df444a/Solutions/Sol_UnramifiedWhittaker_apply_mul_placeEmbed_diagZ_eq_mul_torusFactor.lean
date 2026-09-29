-- Prove2me | solution 1 for UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d66317eb-8195-5fc3-898e-27343833517e

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField AdelicDock

noncomputable section

open Matrix

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "heckeRecursionSeq torusFactor unipotent diagZ repSome repInf scalarPi placeEmbed"
p2m_open "UnramifiedWhittaker"

section Algebra

variable (N lam om : ℂ)

@[scoped simp] private theorem heckeRecursionSeq_zero : heckeRecursionSeq N lam om 0 = 1 := rfl

@[scoped simp] private theorem heckeRecursionSeq_one : heckeRecursionSeq N lam om 1 = lam / N := rfl

private theorem heckeRecursionSeq_add_two (m : ℕ) :
    heckeRecursionSeq N lam om (m + 2) =
      (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N := rfl

variable {N lam om}

private theorem eq_mul_heckeRecursionSeq (hN : N ≠ 0) {c : ℕ → ℂ} (h1 : N * c 1 = lam * c 0)
    (h2 : ∀ m, N * c (m + 2) = lam * c (m + 1) - om * c m) (m : ℕ) :
    c m = c 0 * heckeRecursionSeq N lam om m := by
  suffices H : c m = c 0 * heckeRecursionSeq N lam om m ∧
      c (m + 1) = c 0 * heckeRecursionSeq N lam om (m + 1) from H.1
  induction m with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [zero_add, heckeRecursionSeq_one]
    field_simp
    linear_combination h1
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h := h2 m
    rw [ih.1, ih.2] at h
    rw [show m + 1 + 1 = m + 2 from rfl, heckeRecursionSeq_add_two]
    field_simp
    linear_combination h

private theorem norm_heckeRecursionSeq_le (hN : N ≠ 0) (m : ℕ) :
    ‖heckeRecursionSeq N lam om m‖ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ m := by
  have hC1 : (1 : ℝ) ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) := le_max_left _ _
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have hCN : ‖lam‖ + ‖om‖ ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) * ‖N‖ :=
    (div_le_iff₀ hNpos).mp (le_max_right _ _)
  suffices H : ‖heckeRecursionSeq N lam om m‖ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ m ∧
      ‖heckeRecursionSeq N lam om (m + 1)‖ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) from H.1
  induction m with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [zero_add, heckeRecursionSeq_one, pow_one, norm_div, div_le_iff₀ hNpos]
    exact le_trans (by linarith [norm_nonneg om]) hCN
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [show m + 1 + 1 = m + 2 from rfl, heckeRecursionSeq_add_two, norm_div, div_le_iff₀ hNpos]
    have hm : ‖heckeRecursionSeq N lam om m‖ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) :=
      ih.1.trans (pow_le_pow_right₀ hC1 (Nat.le_succ m))
    calc ‖lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m‖
        ≤ ‖lam‖ * ‖heckeRecursionSeq N lam om (m + 1)‖ + ‖om‖ * ‖heckeRecursionSeq N lam om m‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖lam‖ * (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) +
            ‖om‖ * (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) := by
          gcongr
          exact ih.2
      _ = (‖lam‖ + ‖om‖) * (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) := by ring
      _ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖) * ‖N‖) * (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 1) := by
          gcongr
      _ = (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ (m + 2) * ‖N‖ := by ring

private theorem tsum_heckeRecursionSeq_mul_heckePoly (hN : N ≠ 0) {Y : ℂ}
    (hs : Summable fun m => heckeRecursionSeq N lam om m * Y ^ m) :
    (∑' m, heckeRecursionSeq N lam om m * Y ^ m) * (N - lam * Y + om * Y ^ 2) = N := by
  have hs1 : Summable fun m => heckeRecursionSeq N lam om (m + 1) * Y ^ (m + 1) :=
    (summable_nat_add_iff (f := fun m => heckeRecursionSeq N lam om m * Y ^ m) 1).mpr hs
  have e1 : 1 + ∑' m, heckeRecursionSeq N lam om (m + 1) * Y ^ (m + 1) =
      ∑' m, heckeRecursionSeq N lam om m * Y ^ m := by
    have h := hs.sum_add_tsum_nat_add 1
    simpa [Finset.sum_range_one] using h
  have e2 : (1 + lam / N * Y) + ∑' m, heckeRecursionSeq N lam om (m + 2) * Y ^ (m + 2) =
      ∑' m, heckeRecursionSeq N lam om m * Y ^ m := by
    have h := hs.sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ] using h
  have e2' : N * ∑' m, heckeRecursionSeq N lam om (m + 2) * Y ^ (m + 2) =
      N * (∑' m, heckeRecursionSeq N lam om m * Y ^ m) - N - lam * Y := by
    rw [← e2]
    field_simp
    ring
  have e3 : N * ∑' m, heckeRecursionSeq N lam om (m + 2) * Y ^ (m + 2) =
      lam * Y * (∑' m, heckeRecursionSeq N lam om (m + 1) * Y ^ (m + 1)) -
        om * Y ^ 2 * ∑' m, heckeRecursionSeq N lam om m * Y ^ m := by
    calc N * ∑' m, heckeRecursionSeq N lam om (m + 2) * Y ^ (m + 2)
        = ∑' m, N * (heckeRecursionSeq N lam om (m + 2) * Y ^ (m + 2)) := tsum_mul_left.symm
      _ = ∑' m, (lam * Y * (heckeRecursionSeq N lam om (m + 1) * Y ^ (m + 1)) -
            om * Y ^ 2 * (heckeRecursionSeq N lam om m * Y ^ m)) := by
          refine tsum_congr fun m => ?_
          rw [heckeRecursionSeq_add_two]
          field_simp
          ring
      _ = lam * Y * (∑' m, heckeRecursionSeq N lam om (m + 1) * Y ^ (m + 1)) -
            om * Y ^ 2 * ∑' m, heckeRecursionSeq N lam om m * Y ^ m := by
          rw [(hs1.mul_left (lam * Y)).tsum_sub (hs.mul_left (om * Y ^ 2)), tsum_mul_left,
            tsum_mul_left]
  linear_combination lam * Y * e1 - e2' + e3

private theorem summable_heckeRecursionSeq (hN : N ≠ 0) {Y : ℂ}
    (hY : ‖Y‖ * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) < 1) :
    Summable (fun m => heckeRecursionSeq N lam om m * Y ^ m) ∧
      (∑' m, heckeRecursionSeq N lam om m * Y ^ m) * (N - lam * Y + om * Y ^ 2) = N ∧
      N - lam * Y + om * Y ^ 2 ≠ 0 := by
  have hsum : Summable fun m => heckeRecursionSeq N lam om m * Y ^ m := by
    refine Summable.of_norm_bounded (g := fun m => (‖Y‖ * max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ m)
      (summable_geometric_of_lt_one (by positivity) hY) fun m => ?_
    calc ‖heckeRecursionSeq N lam om m * Y ^ m‖
        = ‖heckeRecursionSeq N lam om m‖ * ‖Y‖ ^ m := by rw [norm_mul, norm_pow]
      _ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ m * ‖Y‖ ^ m := by
          gcongr
          exact norm_heckeRecursionSeq_le hN m
      _ = (‖Y‖ * max 1 ((‖lam‖ + ‖om‖) / ‖N‖)) ^ m := by rw [mul_pow]; ring
  refine ⟨hsum, tsum_heckeRecursionSeq_mul_heckePoly hN hsum, fun h0 => hN ?_⟩
  have h := tsum_heckeRecursionSeq_mul_heckePoly hN hsum
  rw [h0, mul_zero] at h
  exact h.symm

end Algebra

section Matrices

variable {K : Type*} [Field K]

variable (π : K) (hπ : π ≠ 0)

@[scoped simp] private theorem diagZ_zero : diagZ π hπ 0 = 1 := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagZ]

private theorem diagZ_mul_repSome (m : ℤ) (β : K) :
    diagZ π hπ m * repSome π hπ β = unipotent (π ^ m * β) * diagZ π hπ (m + 1) := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, repSome, unipotent, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

private theorem diagZ_succ_mul_repInf (m : ℤ) :
    diagZ π hπ (m + 1) * repInf π hπ = diagZ π hπ m * scalarPi π hπ := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, repInf, scalarPi, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

private theorem diagZ_mul_unipotent (m : ℤ) (x : K) :
    diagZ π hπ m * unipotent x = unipotent (π ^ m * x) * diagZ π hπ m := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, unipotent, Matrix.mul_apply, Fin.sum_univ_two]

end Matrices

section Torus

variable {R K G : Type*} [CommRing R] [Field K] [Algebra R K] [Group G]
variable (ι : GL (Fin 2) K →* G) (W : G → ℂ) (ψ : AddChar K ℂ) (ϖ : R)
  (hπ : algebraMap R K ϖ ≠ 0) (lam om : ℂ) (g₀ : G)

private def torusValue (m : ℤ) : ℂ := W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m))

variable {ι W ψ ϖ hπ lam om g₀}

private theorem torusValue_unipotent_mul
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℤ) (x : K) :
    W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) * ι (unipotent x)) =
      ψ (algebraMap R K ϖ ^ m * x) * torusValue ι W ϖ hπ g₀ m := by
  rw [torusValue, mul_assoc, ← map_mul, diagZ_mul_unipotent, map_mul, ← mul_assoc, hg₀,
    mul_assoc, hN]

private theorem torusValue_eq_zero_of_neg
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : R) (g : G), W (g * ι (unipotent (algebraMap R K r))) = W g)
    (hψ1 : ∃ r : R, ψ (algebraMap R K r / algebraMap R K ϖ) ≠ 1)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) {m : ℤ} (hm : m < 0) :
    torusValue ι W ϖ hπ g₀ m = 0 := by
  obtain ⟨r, hr⟩ := hψ1
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hm
  have h := hK (r * ϖ ^ k) (g₀ * ι (diagZ (algebraMap R K ϖ) hπ (Int.negSucc k)))
  rw [torusValue_unipotent_mul hN hg₀] at h
  have hx : algebraMap R K ϖ ^ (Int.negSucc k) * algebraMap R K (r * ϖ ^ k) =
      algebraMap R K r / algebraMap R K ϖ := by
    rw [zpow_negSucc, map_mul, map_pow]
    field_simp
    ring
  rw [hx] at h

  have hc : ψ (algebraMap R K r / algebraMap R K ϖ) * torusValue ι W ϖ hπ g₀ (Int.negSucc k) =
      torusValue ι W ϖ hπ g₀ (Int.negSucc k) := h
  have h' : (ψ (algebraMap R K r / algebraMap R K ϖ) - 1) * torusValue ι W ϖ hπ g₀ (Int.negSucc k)
      = 0 := by
    rw [sub_mul, one_mul, hc, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hr
  · exact h1

private theorem torusValue_recursion {I : Type*} [Fintype I] (b : I → R)
    (hψ0 : ∀ r : R, ψ (algebraMap R K r) = 1)
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hT : ∀ g : G, (∑ i, W (g * ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i))))) +
      W (g * ι (repInf (algebraMap R K ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : G, W (g * ι (scalarPi (algebraMap R K ϖ) hπ)) = om * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℕ) :
    lam * torusValue ι W ϖ hπ g₀ m =
      (Fintype.card I : ℂ) * torusValue ι W ϖ hπ g₀ (m + 1) +
        om * torusValue ι W ϖ hπ g₀ ((m : ℤ) - 1) := by
  have h := hT (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m))

  have hsome : ∀ i, W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) *
      ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i)))) = torusValue ι W ϖ hπ g₀ (m + 1) := by
    intro i
    rw [mul_assoc, ← map_mul, diagZ_mul_repSome, map_mul, ← mul_assoc, hg₀, mul_assoc, hN,
      zpow_natCast, ← map_pow, ← map_mul, hψ0, one_mul]
    rfl

  have hinf : W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) * ι (repInf (algebraMap R K ϖ) hπ)) =
      om * torusValue ι W ϖ hπ g₀ ((m : ℤ) - 1) := by
    have e : diagZ (algebraMap R K ϖ) hπ m = diagZ (algebraMap R K ϖ) hπ ((m : ℤ) - 1 + 1) := by
      rw [sub_add_cancel]
    rw [e, mul_assoc, ← map_mul, diagZ_succ_mul_repInf, map_mul, ← mul_assoc, hZ]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hsome i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hinf] at h
  exact h.symm

private theorem torusValue_eq_mul_heckeRecursionSeq {I : Type*} [Fintype I] [Nonempty I] (b : I → R)
    (hψ0 : ∀ r : R, ψ (algebraMap R K r) = 1)
    (hψ1 : ∃ r : R, ψ (algebraMap R K r / algebraMap R K ϖ) ≠ 1)
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : R) (g : G), W (g * ι (unipotent (algebraMap R K r))) = W g)
    (hT : ∀ g : G, (∑ i, W (g * ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i))))) +
      W (g * ι (repInf (algebraMap R K ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : G, W (g * ι (scalarPi (algebraMap R K ϖ) hπ)) = om * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℕ) :
    torusValue ι W ϖ hπ g₀ m =
      W g₀ * heckeRecursionSeq (Fintype.card I) lam om m := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h0 : torusValue ι W ϖ hπ g₀ ((0 : ℕ) : ℤ) = W g₀ := by
    simp [torusValue]
  have key := torusValue_recursion b hψ0 hN hT hZ hg₀
  have h := eq_mul_heckeRecursionSeq (N := (Fintype.card I : ℂ)) (lam := lam) (om := om) hcard
    (c := fun k : ℕ => torusValue ι W ϖ hπ g₀ k) ?_ ?_ m
  · rw [h0] at h
    exact h
  ·
    have k0 := key 0
    rw [torusValue_eq_zero_of_neg hN hK hψ1 hg₀ (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0), mul_zero,
      add_zero] at k0
    simpa using k0.symm
  · intro k
    have k1 := key (k + 1)
    have e1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
    have e2 : (((k + 1 : ℕ) : ℤ) + 1) = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at k1
    linear_combination -k1

end Torus

section Adelic

open IsDedekindDomain NumberField AdelicDock

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

variable {K}

private theorem placeEmbed_mul_placeEmbed_comm {v w : HeightOneSpectrum R} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion K)) (y : GL (Fin 2) (w.adicCompletion K)) :
    placeEmbed K v x * placeEmbed K w y = placeEmbed K w y * placeEmbed K v x := by
  simp only [placeEmbed, MonoidHom.comp_apply, ← map_mul]
  congr 1
  refine Units.ext ?_
  simp only [Units.val_mul, coe_localEmbed]
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun u => ?_
  rw [map_mul, map_mul]
  by_cases huv : u = v
  · subst huv
    rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K w _ hvw, mul_one, one_mul]
  · by_cases huw : u = w
    · subst huw
      rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K v _ huv, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne R K v _ huv, mapMatrix_localMat_of_ne R K w _ huw]

private theorem apply_mul_placeEmbed_diagZ_eq_mul_torusFactor (v : HeightOneSpectrum R)
    {W : GL (Fin 2) (AdeleRing R K) → ℂ} {ψ : AddChar (v.adicCompletion K) ℂ}
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) {lam om : ℂ}
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    {g₀ : GL (Fin 2) (AdeleRing R K)}
    (hg₀ : ∀ x : GL (Fin 2) (v.adicCompletion K), g₀ * placeEmbed K v x = placeEmbed K v x * g₀)
    (m : ℤ) :
    W (g₀ * placeEmbed K v (diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m)) =
      W g₀ * torusFactor (Fintype.card I) lam om m := by
  unfold torusFactor
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have hn : ((n : ℤ)).toNat = n := by simp
    rw [hn]
    exact torusValue_eq_mul_heckeRecursionSeq b hψ0 hψ1 hN hK hT hZ hg₀ n
  · rw [mul_zero]
    exact torusValue_eq_zero_of_neg hN hK hψ1 hg₀ (not_le.mp hm)
end Adelic

end UnramifiedWhittaker
p2m_reactivate "P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor.UnramifiedWhittaker"

end
p2m_reactivate "P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor.UnramifiedWhittaker"

p2m_open "UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor.UnramifiedWhittaker"

theorem solution
    {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R)
    {W : GL (Fin 2) (AdeleRing R K) → ℂ} {ψ : AddChar (v.adicCompletion K) ℂ}
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) {lam om : ℂ}
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    {g₀ : GL (Fin 2) (AdeleRing R K)}
    (hg₀ : ∀ x : GL (Fin 2) (v.adicCompletion K), g₀ * placeEmbed K v x = placeEmbed K v x * g₀)
    (m : ℤ) :
    W (g₀ * placeEmbed K v (diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m)) =
      W g₀ * torusFactor (Fintype.card I) lam om m :=
  apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hK hT hZ hg₀ m

end S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
end P2MW
export P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor (solution)
