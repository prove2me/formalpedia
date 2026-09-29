-- Prove2me | solution 1 for ResidualGaloisRep.exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bc123aa5-f001-56ce-95cc-aa14c153c4fb

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsUnramifiedAt baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ isAbsolutelyIrreducible_iff_span_eq_top"
namespace FrobeniusTraceResidue
p2m_open "ResidualGaloisRep"

section MatrixLemmas

open scoped Matrix

section

open Matrix

namespace EigenvalueAvoidance

variable {𝕜 : Type*} [Field 𝕜]

private def Tame (A : Matrix (Fin 2) (Fin 2) 𝕜) : Prop := A.det = 1 ∨ A.trace ^ 2 = (1 + A.det) ^ 2

private theorem det_sub_smul_one (A : Matrix (Fin 2) (Fin 2) 𝕜) (c : 𝕜) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det = A.det - c * A.trace + c ^ 2 := by
  simp [det_fin_two, trace_fin_two]
  ring

private theorem det_sub_one (A : Matrix (Fin 2) (Fin 2) 𝕜) : (A - 1).det = A.det - A.trace + 1 := by
  have h := det_sub_smul_one A 1
  rw [one_smul] at h
  rw [h]; ring

private theorem det_add_one (A : Matrix (Fin 2) (Fin 2) 𝕜) : (A + 1).det = A.det + A.trace + 1 := by
  have h := det_sub_smul_one A (-1)
  rw [neg_smul, one_smul, sub_neg_eq_add] at h
  rw [h]; ring

private theorem tame_iff (A : Matrix (Fin 2) (Fin 2) 𝕜) :
    Tame A ↔ A.det = 1 ∨ (A - 1).det = 0 ∨ (A + 1).det = 0 := by
  unfold Tame
  rw [det_sub_one, det_add_one, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linear_combination -h))
    · exact Or.inr (Or.inr (by linear_combination h))
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linear_combination -h))
    · exact Or.inr (Or.inr (by linear_combination h))

private theorem det_sub_smul_one_eq_zero_of_mulVec {A : Matrix (Fin 2) (Fin 2) 𝕜} {v : Fin 2 → 𝕜} (hv : v ≠ 0)
    {c : 𝕜} (h : A *ᵥ v = c • v) : (A - c • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, h, smul_mulVec, one_mulVec, sub_self]

private theorem exists_mulVec_eq_smul_of_det {A : Matrix (Fin 2) (Fin 2) 𝕜} {c : 𝕜}
    (h : (A - c • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det = 0) : ∃ v : Fin 2 → 𝕜, v ≠ 0 ∧ A *ᵥ v = c • v := by
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hAv
  exact hAv

private theorem neg_one_smul_one' : ((-1 : 𝕜) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = -1 := by
  rw [neg_smul, one_smul]

section Group

variable {G : Type*} [Group G] (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜)

private theorem det_ne_zero (g : G) : (ρ g).det ≠ 0 := by
  intro h
  have h1 : (ρ g * ρ g⁻¹).det = 1 := by rw [← map_mul, mul_inv_cancel, map_one, det_one]
  rw [det_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem det_inv_mul (g : G) : (ρ g⁻¹).det * (ρ g).det = 1 := by
  rw [← det_mul, ← map_mul, inv_mul_cancel, map_one, det_one]

private theorem field_core {δ ε x w : 𝕜} (h2 : (2 : 𝕜) ≠ 0) (hδ0 : δ ≠ 0) (hδ2 : δ ^ 2 ≠ 1) (hc3 : δ ^ 2 + δ + 1 ≠ 0)
    (hε : ε ^ 2 = 1)
    (e1 : (ε * x + ε * δ * w) ^ 2 = (1 + δ) ^ 2)
    (e2 : (ε * δ * x + ε * w) ^ 2 = (δ + 1) ^ 2)
    (e3 : (x + δ ^ 2 * w) ^ 2 = (1 + δ ^ 2) ^ 2) : x = w ∧ x ^ 2 = 1 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have h1δ : 1 + δ ≠ 0 := by
    intro h; apply hδ2; linear_combination (δ - 1) * h
  have h1mδ : 1 - δ ≠ 0 := by
    intro h; apply hδ2; linear_combination (-(1 + δ)) * h
  have hsq_of : ∀ t : 𝕜, ε * (1 - δ) * x = t → t ^ 2 = (1 + δ) ^ 2 → w = -x → False := by
    intro t ht ht2 hw
    subst hw
    have hsq : (1 - δ) ^ 2 * x ^ 2 = (1 + δ) ^ 2 := by
      have h' : (ε * (1 - δ) * x) ^ 2 = (1 + δ) ^ 2 := by rw [ht, ht2]
      rw [mul_pow, mul_pow, hε, one_mul] at h'
      exact h'
    have key : (2 * δ) * (2 * (δ ^ 2 + δ + 1)) = 0 := by
      linear_combination e3 - (1 + δ) ^ 2 * hsq
    rcases mul_eq_zero.mp key with h | h
    · exact mul_ne_zero h2 hδ0 h
    · rcases mul_eq_zero.mp h with h | h
      · exact h2 h
      · exact hc3 h
  rw [sq_eq_sq_iff_eq_or_eq_neg] at e1 e2
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  ·
    have hxw : ε * (1 - δ) * (x - w) = 0 := by linear_combination e1 - e2
    have hxw' : x = w := by
      rcases mul_eq_zero.mp hxw with h | h
      · exact absurd h (mul_ne_zero hε0 h1mδ)
      · exact sub_eq_zero.mp h
    refine ⟨hxw', ?_⟩
    rw [← hxw'] at e1
    have hεx : (ε * x - 1) * (1 + δ) = 0 := by linear_combination e1
    have hεx' : ε * x = 1 := by
      rcases mul_eq_zero.mp hεx with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h h1δ
    calc x ^ 2 = ε ^ 2 * x ^ 2 := by rw [hε, one_mul]
      _ = (ε * x) ^ 2 := by ring
      _ = 1 := by rw [hεx', one_pow]
  ·
    have hsum : ε * (1 + δ) * (x + w) = 0 := by linear_combination e1 + e2
    have hw : w = -x := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h (mul_ne_zero hε0 h1δ)
      · linear_combination h
    exact (hsq_of (1 + δ) (by rw [hw] at e1; linear_combination e1) rfl hw).elim
  ·
    have hsum : ε * (1 + δ) * (x + w) = 0 := by linear_combination e1 + e2
    have hw : w = -x := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h (mul_ne_zero hε0 h1δ)
      · linear_combination h
    exact (hsq_of (-(1 + δ)) (by rw [hw] at e1; linear_combination e1) (by ring) hw).elim
  ·
    have hxw : ε * (1 - δ) * (x - w) = 0 := by linear_combination e1 - e2
    have hxw' : x = w := by
      rcases mul_eq_zero.mp hxw with h | h
      · exact absurd h (mul_ne_zero hε0 h1mδ)
      · exact sub_eq_zero.mp h
    refine ⟨hxw', ?_⟩
    rw [← hxw'] at e1
    have hεx : (ε * x + 1) * (1 + δ) = 0 := by linear_combination e1
    have hεx' : ε * x = -1 := by
      rcases mul_eq_zero.mp hεx with h | h
      · linear_combination h
      · exact absurd h h1δ
    calc x ^ 2 = ε ^ 2 * x ^ 2 := by rw [hε, one_mul]
      _ = (ε * x) ^ 2 := by ring
      _ = 1 := by rw [hεx']; ring

private theorem eigen_det_ne_zero {D : Matrix (Fin 2) (Fin 2) 𝕜} {v w : Fin 2 → 𝕜} {a b : 𝕜} (hab : a ≠ b)
    (hv : v ≠ 0) (hw : w ≠ 0) (hDv : D *ᵥ v = a • v) (hDw : D *ᵥ w = b • w) :
    v 0 * w 1 - w 0 * v 1 ≠ 0 := by
  intro hQ
  have hv0 := congrFun hDv 0
  have hv1 := congrFun hDv 1
  have hw0 := congrFun hDw 0
  have hw1 := congrFun hDw 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at hv0 hv1 hw0 hw1

  have r0 : (a - b) * (w 0 * v 1) = 0 := by
    linear_combination (-(w 1)) * hv0 + v 1 * hw0 + (D 0 0 - a) * hQ
  have r1 : (a - b) * (v 0 * w 1) = 0 := by
    linear_combination (-(w 0)) * hv1 + v 0 * hw1 + (a - D 1 1) * hQ
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have p0 : w 0 * v 1 = 0 := (mul_eq_zero.mp r0).resolve_left hab'
  have p1 : v 0 * w 1 = 0 := (mul_eq_zero.mp r1).resolve_left hab'
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · right
      intro h1
      exact hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    · exact Or.inl h0
  have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_cases h0 : w 0 = 0
    · right
      intro h1
      exact hw (funext fun i => by fin_cases i <;> simp [h0, h1])
    · exact Or.inl h0
  rcases hv' with hv' | hv'
  · have hw1z : w 1 = 0 := (mul_eq_zero.mp p1).resolve_left hv'
    have hw0' : w 0 ≠ 0 := hw'.resolve_right (fun h => h hw1z)
    have hv1z : v 1 = 0 := (mul_eq_zero.mp p0).resolve_left hw0'
    rw [hv1z, mul_zero, add_zero] at hv0
    rw [hw1z, mul_zero, add_zero] at hw0

    have ha : D 0 0 = a := mul_right_cancel₀ hv' hv0
    have hb : D 0 0 = b := mul_right_cancel₀ hw0' hw0
    exact hab (ha.symm.trans hb)
  · have hw0z : w 0 = 0 := (mul_eq_zero.mp p0).resolve_right hv'
    have hw1' : w 1 ≠ 0 := hw'.resolve_left (fun h => h hw0z)
    have hv0z : v 0 = 0 := (mul_eq_zero.mp p1).resolve_right hw1'
    rw [hv0z, mul_zero, zero_add] at hv1
    rw [hw0z, mul_zero, zero_add] at hw1
    have ha : D 1 1 = a := mul_right_cancel₀ hv' hv1
    have hb : D 1 1 = b := mul_right_cancel₀ hw1' hw1
    exact hab (ha.symm.trans hb)

private def conjEntry (Qi Q : Matrix (Fin 2) (Fin 2) 𝕜) (i j : Fin 2) : Matrix (Fin 2) (Fin 2) 𝕜 →ₗ[𝕜] 𝕜 where
  toFun X := (Qi * X * Q) i j
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

private theorem conj_pow (Qi Q X : Matrix (Fin 2) (Fin 2) 𝕜) (hQQi : Q * Qi = 1) (hQiQ : Qi * Q = 1) (m : ℕ) :
    Qi * X ^ m * Q = (Qi * X * Q) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hQiQ]
  | succ m ih =>
      rw [pow_succ, pow_succ, ← ih]
      calc Qi * (X ^ m * X) * Q = Qi * X ^ m * (Q * Qi) * X * Q := by
            rw [hQQi, Matrix.mul_one, Matrix.mul_assoc Qi (X ^ m) X]
        _ = Qi * X ^ m * Q * (Qi * X * Q) := by simp only [Matrix.mul_assoc]

private theorem exists_not_tame_of_det_pow (h2 : (2 : 𝕜) ≠ 0) (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤) (g₀ : G)
    (hδ2 : (ρ g₀).det ^ 2 ≠ 1) (hc3 : (ρ g₀).det ^ 2 + (ρ g₀).det + 1 ≠ 0)
    (hgen : ∀ g : G, ∃ i : ℕ, (ρ g).det = (ρ g₀).det ^ i) : ∃ g : G, ¬ Tame (ρ g) := by
  by_contra hall'
  have hall : ∀ g : G, Tame (ρ g) := fun g => not_not.mp (fun h => hall' ⟨g, h⟩)
  obtain ⟨δ, hδ⟩ : ∃ δ : 𝕜, (ρ g₀).det = δ := ⟨_, rfl⟩
  rw [hδ] at hδ2 hc3
  have hδ0 : δ ≠ 0 := hδ ▸ det_ne_zero ρ g₀
  have hδ1 : δ ≠ 1 := fun h => hδ2 (by rw [h, one_pow])
  have hδinv : (ρ g₀⁻¹).det = δ⁻¹ := by
    have h := det_inv_mul ρ g₀
    rw [hδ] at h
    exact eq_inv_of_mul_eq_one_left h

  obtain ⟨ε, hε, hεD⟩ : ∃ ε : 𝕜, ε ^ 2 = 1 ∧ (ρ g₀ - ε • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det = 0 := by
    rcases (tame_iff (ρ g₀)).mp (hall g₀) with h | h | h
    · exact absurd (hδ.symm.trans h) hδ1
    · exact ⟨1, one_pow 2, by rw [one_smul]; exact h⟩
    · exact ⟨-1, by ring, by rw [neg_one_smul_one', sub_neg_eq_add]; exact h⟩
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hεε : ε * ε = 1 := by rw [← sq]; exact hε
  have htr : (ρ g₀).trace = ε * (1 + δ) := by
    rw [det_sub_smul_one, hδ] at hεD
    calc (ρ g₀).trace = ε ^ 2 * (ρ g₀).trace := by rw [hε, one_mul]
      _ = ε * (1 + δ) := by linear_combination (-ε) * hεD + ε * hε
  have hεδD : (ρ g₀ - (ε * δ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det = 0 := by
    rw [det_sub_smul_one, hδ, htr]
    linear_combination (-δ) * hε
  obtain ⟨v, hv, hDv⟩ := exists_mulVec_eq_smul_of_det hεD
  obtain ⟨w, hw, hDw⟩ := exists_mulVec_eq_smul_of_det hεδD
  have hab : ε ≠ ε * δ := by
    intro h
    apply hδ1
    calc δ = (ε * ε) * δ := by rw [hεε, one_mul]
      _ = ε * (ε * δ) := by ring
      _ = ε * ε := by rw [← h]
      _ = 1 := hεε

  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 2) (Fin 2) 𝕜, Q = Matrix.of ![![v 0, w 0], ![v 1, w 1]] := ⟨_, rfl⟩
  have hdetQ : Q.det ≠ 0 := by
    have key := eigen_det_ne_zero hab hv hw hDv hDw
    rw [det_fin_two, hQ]
    simpa using key
  have hQunit : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdetQ
  have hQQi : Q * Q⁻¹ = 1 := mul_nonsing_inv Q hQunit
  have hQiQ : Q⁻¹ * Q = 1 := nonsing_inv_mul Q hQunit

  have hDQ : ρ g₀ * Q = Q * diagonal ![ε, ε * δ] := by
    have hv0 := congrFun hDv 0
    have hv1 := congrFun hDv 1
    have hw0 := congrFun hDw 0
    have hw1 := congrFun hDw 1
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at hv0 hv1 hw0 hw1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination hv0
        | linear_combination hw0
        | linear_combination hv1
        | linear_combination hw1
  have hcD : Q⁻¹ * ρ g₀ * Q = diagonal ![ε, ε * δ] := by
    rw [Matrix.mul_assoc, hDQ, ← Matrix.mul_assoc, hQiQ, Matrix.one_mul]

  have hprod : ∀ i : Fin 2, (![ε, ε * δ] : Fin 2 → 𝕜) i * (![ε, ε * δ⁻¹] : Fin 2 → 𝕜) i = 1 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact hεε
    · simp only [Matrix.cons_val_one]
      calc ε * δ * (ε * δ⁻¹) = (ε * ε) * (δ * δ⁻¹) := by ring
        _ = 1 := by rw [hεε, mul_inv_cancel₀ hδ0, mul_one]
  have hdd' : diagonal (![ε, ε * δ] : Fin 2 → 𝕜) * diagonal (![ε, ε * δ⁻¹] : Fin 2 → 𝕜) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hprod i
  have hcDinv : Q⁻¹ * ρ g₀⁻¹ * Q = diagonal ![ε, ε * δ⁻¹] := by
    have h1 : (Q⁻¹ * ρ g₀⁻¹ * Q) * diagonal ![ε, ε * δ] = 1 := by
      rw [← hcD]
      calc Q⁻¹ * ρ g₀⁻¹ * Q * (Q⁻¹ * ρ g₀ * Q) = Q⁻¹ * (ρ g₀⁻¹ * (Q * Q⁻¹) * ρ g₀) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hQQi, Matrix.mul_one, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one, hQiQ]
    calc Q⁻¹ * ρ g₀⁻¹ * Q
        = Q⁻¹ * ρ g₀⁻¹ * Q * (diagonal ![ε, ε * δ] * diagonal ![ε, ε * δ⁻¹]) := by
          rw [hdd', Matrix.mul_one]
      _ = diagonal ![ε, ε * δ⁻¹] := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

  have hcmul : ∀ X Y : Matrix (Fin 2) (Fin 2) 𝕜, Q⁻¹ * (X * Y) * Q = (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) := by
    intro X Y
    calc Q⁻¹ * (X * Y) * Q = Q⁻¹ * (X * (Q * Q⁻¹) * Y) * Q := by rw [hQQi, Matrix.mul_one]
      _ = (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) := by simp only [Matrix.mul_assoc]
  have hcdet : ∀ X : Matrix (Fin 2) (Fin 2) 𝕜, (Q⁻¹ * X * Q).det = X.det := by
    intro X
    have hQQ : Q⁻¹.det * Q.det = 1 := by rw [← det_mul, hQiQ, det_one]
    rw [det_mul, det_mul, mul_comm Q⁻¹.det X.det, mul_assoc, hQQ, mul_one]
  have hctr : ∀ X : Matrix (Fin 2) (Fin 2) 𝕜, (Q⁻¹ * X * Q).trace = X.trace := by
    intro X
    rw [trace_mul_cycle, hQQi, Matrix.one_mul]

  have hdiag : ∀ n : G, (ρ n).det = 1 →
      (Q⁻¹ * ρ n * Q) 0 0 = (Q⁻¹ * ρ n * Q) 1 1 ∧ (Q⁻¹ * ρ n * Q) 0 0 ^ 2 = 1 := by
    intro n hn

    have t1 : (ε * (Q⁻¹ * ρ n * Q) 0 0 + ε * δ * (Q⁻¹ * ρ n * Q) 1 1) ^ 2 = (1 + δ) ^ 2 := by
      have hdet1 : (ρ (g₀ * n)).det = δ := by rw [map_mul, det_mul, hn, mul_one, hδ]
      rcases (hall (g₀ * n) : (ρ (g₀ * n)).det = 1 ∨
          (ρ (g₀ * n)).trace ^ 2 = (1 + (ρ (g₀ * n)).det) ^ 2) with h | h
      · exact absurd (hdet1.symm.trans h) hδ1
      · rw [hdet1, ← hctr (ρ (g₀ * n)), map_mul, hcmul, hcD, trace_fin_two, diagonal_mul, diagonal_mul] at h
        simpa using h

    have t2 : (ε * δ * (Q⁻¹ * ρ n * Q) 0 0 + ε * (Q⁻¹ * ρ n * Q) 1 1) ^ 2 = (δ + 1) ^ 2 := by
      have hdet2 : (ρ (g₀⁻¹ * n)).det = δ⁻¹ := by rw [map_mul, det_mul, hn, mul_one, hδinv]
      have hδinv1 : δ⁻¹ ≠ 1 := fun h => hδ1 (by rw [← inv_inv δ, h, inv_one])
      rcases (hall (g₀⁻¹ * n) : (ρ (g₀⁻¹ * n)).det = 1 ∨
          (ρ (g₀⁻¹ * n)).trace ^ 2 = (1 + (ρ (g₀⁻¹ * n)).det) ^ 2) with h | h
      · exact absurd (hdet2.symm.trans h) hδinv1
      · rw [hdet2, ← hctr (ρ (g₀⁻¹ * n)), map_mul, hcmul, hcDinv, trace_fin_two, diagonal_mul,
          diagonal_mul] at h
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
        have hδδ : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ0
        have e : ε * δ * (Q⁻¹ * ρ n * Q) 0 0 + ε * (Q⁻¹ * ρ n * Q) 1 1
            = δ * (ε * (Q⁻¹ * ρ n * Q) 0 0 + ε * δ⁻¹ * (Q⁻¹ * ρ n * Q) 1 1) := by
          linear_combination (-(ε * (Q⁻¹ * ρ n * Q) 1 1)) * hδδ
        have e' : δ + 1 = δ * (1 + δ⁻¹) := by linear_combination (-1 : 𝕜) * hδδ
        rw [e, e', mul_pow, mul_pow, h]

    have t3 : ((Q⁻¹ * ρ n * Q) 0 0 + δ ^ 2 * (Q⁻¹ * ρ n * Q) 1 1) ^ 2 = (1 + δ ^ 2) ^ 2 := by
      have hdet3 : (ρ (g₀ * (g₀ * n))).det = δ ^ 2 := by
        rw [map_mul, map_mul, det_mul, det_mul, hn, mul_one, hδ, sq]
      rcases (hall (g₀ * (g₀ * n)) : (ρ (g₀ * (g₀ * n))).det = 1 ∨
          (ρ (g₀ * (g₀ * n))).trace ^ 2 = (1 + (ρ (g₀ * (g₀ * n))).det) ^ 2) with h | h
      · exact absurd (hdet3.symm.trans h) hδ2
      · rw [hdet3, ← hctr (ρ (g₀ * (g₀ * n))), map_mul, hcmul, map_mul, hcmul, hcD, trace_fin_two,
          diagonal_mul, diagonal_mul, diagonal_mul, diagonal_mul] at h
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
        have e : ε * (ε * (Q⁻¹ * ρ n * Q) 0 0) + ε * δ * (ε * δ * (Q⁻¹ * ρ n * Q) 1 1)
            = (Q⁻¹ * ρ n * Q) 0 0 + δ ^ 2 * (Q⁻¹ * ρ n * Q) 1 1 := by
          linear_combination ((Q⁻¹ * ρ n * Q) 0 0 + δ ^ 2 * (Q⁻¹ * ρ n * Q) 1 1) * hεε
        rw [e] at h
        exact h
    exact field_core h2 hδ0 hδ2 hc3 hε t1 t2 t3

  have hoff : ∀ n : G, (ρ n).det = 1 → (Q⁻¹ * ρ n * Q) 0 1 = 0 ∨ (Q⁻¹ * ρ n * Q) 1 0 = 0 := by
    intro n hn
    obtain ⟨h00, hsq⟩ := hdiag n hn
    have hdet : (Q⁻¹ * ρ n * Q).det = 1 := by rw [hcdet, hn]
    rw [det_fin_two, ← h00] at hdet
    have : (Q⁻¹ * ρ n * Q) 0 1 * (Q⁻¹ * ρ n * Q) 1 0 = 0 := by linear_combination hsq - hdet
    exact mul_eq_zero.mp this
  have hside : (∀ n : G, (ρ n).det = 1 → (Q⁻¹ * ρ n * Q) 1 0 = 0) ∨
      (∀ n : G, (ρ n).det = 1 → (Q⁻¹ * ρ n * Q) 0 1 = 0) := by
    by_contra hcon
    revert hcon
    intro hcon
    obtain ⟨hP, hQ'⟩ := not_or.mp hcon
    obtain ⟨n₁, hn₁'⟩ := not_forall.mp hP
    obtain ⟨hn₁, h₁⟩ := Classical.not_imp.mp hn₁'
    obtain ⟨n₂, hn₂'⟩ := not_forall.mp hQ'
    obtain ⟨hn₂, h₂⟩ := Classical.not_imp.mp hn₂'
    have h₁' : (Q⁻¹ * ρ n₁ * Q) 0 1 = 0 := (hoff n₁ hn₁).resolve_right h₁
    have h₂' : (Q⁻¹ * ρ n₂ * Q) 1 0 = 0 := (hoff n₂ hn₂).resolve_left h₂
    have hn₂₁ : (ρ (n₂ * n₁)).det = 1 := by rw [map_mul, det_mul, hn₁, hn₂, mul_one]
    have hdg := (hdiag (n₂ * n₁) hn₂₁).1
    rw [map_mul, hcmul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, h₁', h₂',
      (hdiag n₁ hn₁).1, (hdiag n₂ hn₂).1] at hdg
    have : (Q⁻¹ * ρ n₂ * Q) 0 1 * (Q⁻¹ * ρ n₁ * Q) 1 0 = 0 := by linear_combination hdg
    exact (mul_ne_zero h₂ h₁) this

  have hspan : ∀ i j : Fin 2, (∀ n : G, (ρ n).det = 1 → (Q⁻¹ * ρ n * Q) i j = 0) → False := by
    intro i j hij
    have hall0 : ∀ g : G, (Q⁻¹ * ρ g * Q) i j = 0 := by
      intro g
      obtain ⟨m, hm⟩ := hgen g
      rw [hδ] at hm
      have hdpow : (ρ (g₀ ^ m)).det = δ ^ m := by rw [map_pow, det_pow, hδ]
      have hinvpow : (ρ (g₀ ^ m)⁻¹).det = (δ ^ m)⁻¹ := by
        have h := det_inv_mul ρ (g₀ ^ m)
        rw [hdpow] at h
        exact eq_inv_of_mul_eq_one_left h
      have hn : (ρ ((g₀ ^ m)⁻¹ * g)).det = 1 := by
        rw [map_mul, det_mul, hm, hinvpow, inv_mul_cancel₀ (pow_ne_zero m hδ0)]
      have hg : Q⁻¹ * ρ g * Q = Q⁻¹ * ρ (g₀ ^ m * ((g₀ ^ m)⁻¹ * g)) * Q := by
        rw [mul_inv_cancel_left]
      rw [hg, map_mul, hcmul, map_pow, conj_pow Q⁻¹ Q (ρ g₀) hQQi hQiQ, hcD, diagonal_pow, diagonal_mul,
        hij _ hn, mul_zero]
    have hle : (⊤ : Submodule 𝕜 (Matrix (Fin 2) (Fin 2) 𝕜)) ≤ LinearMap.ker (conjEntry Q⁻¹ Q i j) := by
      rw [← hρ]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact hall0 g
    have hE : Q * Matrix.single i j (1 : 𝕜) * Q⁻¹ ∈ LinearMap.ker (conjEntry Q⁻¹ Q i j) :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hE
    change (Q⁻¹ * (Q * Matrix.single i j (1 : 𝕜) * Q⁻¹) * Q) i j = 0 at hE
    have hconj : Q⁻¹ * (Q * Matrix.single i j (1 : 𝕜) * Q⁻¹) * Q = Matrix.single i j (1 : 𝕜) := by
      calc Q⁻¹ * (Q * Matrix.single i j (1 : 𝕜) * Q⁻¹) * Q
          = (Q⁻¹ * Q) * Matrix.single i j (1 : 𝕜) * (Q⁻¹ * Q) := by simp only [Matrix.mul_assoc]
        _ = Matrix.single i j (1 : 𝕜) := by rw [hQiQ, Matrix.one_mul, Matrix.mul_one]
    rw [hconj, Matrix.single_apply_same] at hE
    exact one_ne_zero hE
  rcases hside with h | h
  · exact hspan 1 0 h
  · exact hspan 0 1 h

end Group

end EigenvalueAvoidance

private theorem exists_det_ne_one_and_det_sub_one_ne_zero_of_span_eq_top
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜) (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (g₀ : G) (hc1 : (ρ g₀).det ^ 2 ≠ 1) (hc3 : (ρ g₀).det ^ 2 + (ρ g₀).det + 1 ≠ 0)
    (hgen : ∀ g : G, ∃ j : ℕ, (ρ g).det = (ρ g₀).det ^ j) :
    ∃ g : G, (ρ g).det ≠ 1 ∧ (ρ g - 1).det ≠ 0 ∧ (ρ g + 1).det ≠ 0 := by
  obtain ⟨g, hg⟩ := EigenvalueAvoidance.exists_not_tame_of_det_pow ρ h2 hρ g₀ hc1 hc3 hgen
  rw [EigenvalueAvoidance.tame_iff] at hg
  exact ⟨g, fun h => hg (Or.inl h), fun h => hg (Or.inr (Or.inl h)), fun h => hg (Or.inr (Or.inr h))⟩

end

section

open Matrix

namespace InvolutionLemma

private theorem det_sub_one_fin_two {𝕜 : Type*} [Field 𝕜] (X : Matrix (Fin 2) (Fin 2) 𝕜) :
    (X - 1).det = X.det - X.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

private theorem det_add_one_fin_two {𝕜 : Type*} [Field 𝕜] (X : Matrix (Fin 2) (Fin 2) 𝕜) :
    (X + 1).det = X.det + X.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

private theorem sq_eq_fin_two {𝕜 : Type*} [Field 𝕜] (X : Matrix (Fin 2) (Fin 2) 𝕜) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem sq_eq_one_of_det_eq_neg_one {𝕜 : Type*} [Field 𝕜] (X : Matrix (Fin 2) (Fin 2) 𝕜)
    (hX : X.det = -1) (h : (X - 1).det = 0 ∨ (X + 1).det = 0) : X * X = 1 := by
  have htr : X.trace = 0 := by
    rcases h with h | h
    · rw [det_sub_one_fin_two, hX] at h
      linear_combination -h
    · rw [det_add_one_fin_two, hX] at h
      linear_combination h
  rw [sq_eq_fin_two, htr, hX]
  simp

private theorem exists_eigenvector {K : Type*} [Field K] [IsAlgClosed K] (B : Matrix (Fin 2) (Fin 2) K) :
    ∃ (μ : K) (v : Fin 2 → K), v ≠ 0 ∧ B *ᵥ v = μ • v := by
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ 2 - B.trace * μ + B.det = 0 := by
    have hdeg : (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C (-B.trace) * Polynomial.X
        + Polynomial.C B.det).degree ≠ 0 := by
      rw [Polynomial.degree_quadratic one_ne_zero]
      decide
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨μ, ?_⟩
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hμ
    linear_combination hμ
  have hdet : (B - μ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hμ
    simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero,
      if_true, if_false, smul_eq_mul, mul_one, mul_zero, sub_zero]
    linear_combination hμ
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨μ, v, hv, ?_⟩
  rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hBv

private theorem eq_smul_one_of_mulVec_eq {K : Type*} [Field K] (B : Matrix (Fin 2) (Fin 2) K) (μ : K)
    (v w : Fin 2 → K) (hv : B *ᵥ v = μ • v) (hw : B *ᵥ w = μ • w)
    (hvw : w ∉ K ∙ v) (hv0 : v ≠ 0) : B = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hli : LinearIndependent K ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hv0, rfl⟩
    · exfalso
      apply hvw
      rw [Submodule.mem_span_singleton]
      refine ⟨-(s / t), ?_⟩
      have htw : t • w = -(s • v) := eq_neg_of_add_eq_zero_right hst
      calc (-(s / t)) • v = t⁻¹ • (-(s • v)) := by
            rw [neg_smul, div_eq_inv_mul, mul_smul, smul_neg]
        _ = t⁻¹ • (t • w) := by rw [htw]
        _ = w := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hspan : Submodule.span K (Set.range ![v, w]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp
  have hD : Matrix.toLin' (B - μ • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := by
    apply LinearMap.ext_on hspan
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp [Matrix.toLin'_apply, hv]
    · simp [Matrix.toLin'_apply, hw]
  exact sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff Matrix.toLin').mp hD)

end InvolutionLemma

private theorem exists_det_ne_one_and_det_sub_one_ne_zero_of_involutions
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜) (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (g₁ : G) (hg₁ : (ρ g₁).det = -1) (hdet2 : ∀ g : G, (ρ g).det = 1 ∨ (ρ g).det = -1)
    (hN : ∀ v : Fin 2 → AlgebraicClosure 𝕜, v ≠ 0 →
      ∃ g : G, (ρ g).det = 1 ∧ ((ρ g).map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) *ᵥ v ∉ (AlgebraicClosure 𝕜) ∙ v) :
    ∃ g : G, (ρ g).det ≠ 1 ∧ (ρ g - 1).det ≠ 0 ∧ (ρ g + 1).det ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ g : G, (ρ g).det ≠ 1 → (ρ g - 1).det ≠ 0 → (ρ g + 1).det = 0 :=
    fun g h1 h3 => by_contra fun h4 => hcon ⟨g, h1, h3, h4⟩
  have hne : (1 : 𝕜) ≠ -1 := by
    intro h
    apply h2
    linear_combination h

  have hinv : ∀ g : G, (ρ g).det = -1 → ρ g * ρ g = 1 := by
    intro g hg
    apply InvolutionLemma.sq_eq_one_of_det_eq_neg_one _ hg
    have hg' : (ρ g).det ≠ 1 := by
      rw [hg]
      exact hne.symm
    by_cases h : (ρ g - 1).det = 0
    · exact Or.inl h
    · exact Or.inr (hcon' g hg' h)
  have hA : ρ g₁ * ρ g₁ = 1 := hinv g₁ hg₁
  have hdet_inv : ∀ n : G, (ρ n).det = 1 → (ρ n⁻¹).det = 1 := by
    intro n hn
    have h : (ρ n⁻¹).det * (ρ n).det = 1 := by
      rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one]
    rwa [hn, mul_one] at h

  have hconj : ∀ n : G, (ρ n).det = 1 → ρ g₁ * ρ n * ρ g₁ = ρ n⁻¹ := by
    intro n hn
    have h1 : (ρ (g₁ * n)).det = -1 := by
      rw [map_mul, Matrix.det_mul, hg₁, hn, mul_one]
    have h2' := hinv (g₁ * n) h1
    rw [map_mul] at h2'
    have h3 : ρ n * ρ n⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g₁ * ρ n * ρ g₁ = ρ g₁ * ρ n * ρ g₁ * (ρ n * ρ n⁻¹) := by rw [h3, mul_one]
      _ = ρ g₁ * ρ n * (ρ g₁ * ρ n) * ρ n⁻¹ := by simp only [mul_assoc]
      _ = ρ n⁻¹ := by rw [h2', one_mul]

  have key : ∀ n m : G, (ρ n).det = 1 → (ρ m).det = 1 → ρ m⁻¹ * ρ n⁻¹ = ρ n⁻¹ * ρ m⁻¹ := by
    intro n m hn hm
    have hnm : (ρ (n * m)).det = 1 := by
      rw [map_mul, Matrix.det_mul, hn, hm, mul_one]
    have e1 : ρ g₁ * ρ (n * m) * ρ g₁ = ρ (n * m)⁻¹ := hconj _ hnm
    rw [_root_.mul_inv_rev, map_mul, map_mul] at e1
    have e2 : ρ g₁ * (ρ n * ρ m) * ρ g₁ = (ρ g₁ * ρ n * ρ g₁) * (ρ g₁ * ρ m * ρ g₁) := by
      calc ρ g₁ * (ρ n * ρ m) * ρ g₁ = ρ g₁ * ρ n * (ρ g₁ * ρ g₁) * ρ m * ρ g₁ := by
            rw [hA]
            simp only [mul_one, mul_assoc]
        _ = (ρ g₁ * ρ n * ρ g₁) * (ρ g₁ * ρ m * ρ g₁) := by simp only [mul_assoc]
    rw [e2, hconj n hn, hconj m hm] at e1
    exact e1.symm
  have hcomm : ∀ n m : G, (ρ n).det = 1 → (ρ m).det = 1 → ρ n * ρ m = ρ m * ρ n := by
    intro n m hn hm
    have h := key m⁻¹ n⁻¹ (hdet_inv m hm) (hdet_inv n hn)
    simpa only [inv_inv] using h
  by_cases hscalar : ∀ n : G, (ρ n).det = 1 → ∃ c : 𝕜, ρ n = c • (1 : Matrix (Fin 2) (Fin 2) 𝕜)
  ·
    classical
    have hdet_g₁inv : (ρ g₁⁻¹).det = -1 := by
      have h : (ρ g₁⁻¹).det * (ρ g₁).det = 1 := by
        rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one]
      rw [hg₁] at h
      linear_combination -h
    have hrange : Set.range ρ ⊆
        (Submodule.span 𝕜 ({(1 : Matrix (Fin 2) (Fin 2) 𝕜), ρ g₁} : Set (Matrix (Fin 2) (Fin 2) 𝕜)) :
          Set (Matrix (Fin 2) (Fin 2) 𝕜)) := by
      rintro _ ⟨g, rfl⟩
      rcases hdet2 g with hg | hg
      · obtain ⟨c, hc⟩ := hscalar g hg
        rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · have hg' : (ρ (g₁⁻¹ * g)).det = 1 := by
          rw [map_mul, Matrix.det_mul, hdet_g₁inv, hg]
          norm_num
        obtain ⟨c, hc⟩ := hscalar _ hg'
        have hgc : ρ g = c • ρ g₁ := by
          calc ρ g = ρ (g₁ * (g₁⁻¹ * g)) := by rw [mul_inv_cancel_left]
            _ = ρ g₁ * ρ (g₁⁻¹ * g) := map_mul _ _ _
            _ = c • ρ g₁ := by rw [hc, Matrix.mul_smul, mul_one]
        rw [hgc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hle : (⊤ : Submodule 𝕜 (Matrix (Fin 2) (Fin 2) 𝕜)) ≤
        Submodule.span 𝕜 ({(1 : Matrix (Fin 2) (Fin 2) 𝕜), ρ g₁} : Set (Matrix (Fin 2) (Fin 2) 𝕜)) := by
      rw [← hρ]
      exact Submodule.span_le.mpr hrange
    have h4 : Module.finrank 𝕜 (⊤ : Submodule 𝕜 (Matrix (Fin 2) (Fin 2) 𝕜)) = 4 := by
      rw [finrank_top, Module.finrank_matrix]
      simp
    have hle2 : Module.finrank 𝕜
        (Submodule.span 𝕜 ({(1 : Matrix (Fin 2) (Fin 2) 𝕜), ρ g₁} : Set (Matrix (Fin 2) (Fin 2) 𝕜))) ≤ 2 := by
      refine (finrank_span_le_card _).trans ?_
      simp only [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_le_two
    have hmono := Submodule.finrank_mono hle
    rw [h4] at hmono
    omega
  ·
    obtain ⟨n₀, hn⟩ := not_forall.mp hscalar
    obtain ⟨hn₀, hnotscalar⟩ := Classical.not_imp.mp hn
    obtain ⟨μ, v, hv0, hBv⟩ :=
      InvolutionLemma.exists_eigenvector ((ρ n₀).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)))
    obtain ⟨g, hg, hgv⟩ := hN v hv0
    have hcom : (ρ g).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) *
          (ρ n₀).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) =
        (ρ n₀).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) *
          (ρ g).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm g n₀ hg hn₀]
    have hw : (ρ n₀).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) *ᵥ
          ((ρ g).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) *ᵥ v) =
        μ • ((ρ g).map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← hcom, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul]
    have hscal := InvolutionLemma.eq_smul_one_of_mulVec_eq _ μ v _ hBv hw hgv hv0
    apply hnotscalar
    have hdiag : ∀ i : Fin 2, algebraMap 𝕜 (AlgebraicClosure 𝕜) ((ρ n₀) i i) = μ := by
      intro i
      have h := congrFun (congrFun hscal i) i
      simpa [Matrix.map_apply] using h
    have hoff : ∀ i j : Fin 2, i ≠ j → algebraMap 𝕜 (AlgebraicClosure 𝕜) ((ρ n₀) i j) = 0 := by
      intro i j hij
      have h := congrFun (congrFun hscal i) j
      simpa [Matrix.map_apply, Matrix.one_apply_ne hij] using h
    refine ⟨(ρ n₀) 0 0, ?_⟩
    ext i j
    apply (algebraMap 𝕜 (AlgebraicClosure 𝕜)).injective
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]

end

private theorem det_sub_one_mul_det_add_one {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    (X - 1).det * (X + 1).det = (X.det + 1) ^ 2 - X.trace ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

private theorem conj_sub_one {R : Type*} [Ring R] (P P' X : R) (h : P * P' = 1) :
    P * X * P' - 1 = P * (X - 1) * P' := by
  rw [mul_sub, sub_mul, mul_one, h]

private theorem conj_add_one {R : Type*} [Ring R] (P P' X : R) (h : P * P' = 1) :
    P * X * P' + 1 = P * (X + 1) * P' := by
  rw [mul_add, add_mul, mul_one, h]

end MatrixLemmas

section GaloisSide

open scoped Matrix TensorProduct

variable {k : Type} [Field k]

private noncomputable def matRep (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k where
  toFun σ := LinearMap.toMatrix b b (ρbar.ρ σ)
  map_one' := by simp only [map_one, LinearMap.toMatrix_one]
  map_mul' σ τ := by simp only [map_mul, LinearMap.toMatrix_mul]

private theorem matRep_apply (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    matRep ρbar b σ = LinearMap.toMatrix b b (ρbar.ρ σ) := rfl

private theorem det_matRep (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    (matRep ρbar b σ).det = LinearMap.det (ρbar.ρ σ) := by
  rw [matRep_apply, LinearMap.det_toMatrix]

private theorem matRep_mul_inv (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    matRep ρbar b σ * matRep ρbar b σ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem det_matRep_ne_zero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : (matRep ρbar b σ).det ≠ 0 := by
  apply left_ne_zero_of_mul_eq_one (b := (matRep ρbar b σ⁻¹).det)
  rw [← Matrix.det_mul, matRep_mul_inv, Matrix.det_one]

private theorem det_conj (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (X : Matrix (Fin 2) (Fin 2) k) : (matRep ρbar b c * X * matRep ρbar b c⁻¹).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, matRep_mul_inv, Matrix.det_one,
    one_mul]

private theorem span_matRep_eq_top (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (habs : ρbar.IsAbsolutelyIrreducible) : Submodule.span k (Set.range (matRep ρbar b)) = ⊤ := by
  have hspan : Submodule.span k (Set.range ⇑ρbar.ρ) = ⊤ :=
    (ρbar.isAbsolutelyIrreducible_iff_span_eq_top).mp habs
  apply top_unique
  have hsub : (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) ''
      Set.range ⇑ρbar.ρ ⊆ Set.range (matRep ρbar b) := by
    rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩
  calc (⊤ : Submodule k (Matrix (Fin 2) (Fin 2) k))
      = Submodule.map ((LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k]
          Matrix (Fin 2) (Fin 2) k) : Module.End k ρbar.V →ₗ[k] Matrix (Fin 2) (Fin 2) k) ⊤ := by
        rw [Submodule.map_top, LinearEquiv.range]
    _ = Submodule.span k ((LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k]
          Matrix (Fin 2) (Fin 2) k) '' Set.range ⇑ρbar.ρ) := by
        rw [← hspan, Submodule.map_span]; rfl
    _ ≤ Submodule.span k (Set.range (matRep ρbar b)) := Submodule.span_mono hsub

private theorem natCast_eq_zero (ρbar : ResidualGaloisRep k) {p : ℕ}
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) : (p : k) = 0 := by
  have h := hdet.1
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at h

private theorem det_eq_natCast_of_forall (ρbar : ResidualGaloisRep k) {p : ℕ}
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (a : ℕ)
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    LinearMap.det (ρbar.ρ σ) = (a : k) := by
  have h : LinearMap.det (ρbar.ρ σ) - (a : k) ∈ Ideal.span {((p ^ 1 : ℕ) : k)} :=
    hdet.2 1 σ a (fun μ hμ => ha μ (by rwa [pow_one] at hμ))
  rw [pow_one, natCast_eq_zero ρbar hdet, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot,
    sub_eq_zero] at h
  exact h

private theorem det_eq_natCast_of_isFrobeniusAt (ρbar : ResidualGaloisRep k) {p : ℕ} [Fact p.Prime]
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p) {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime r) {τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hτ : A.IsFrobeniusAt τ r) : LinearMap.det (ρbar.ρ τ) = (r : k) :=
  det_eq_natCast_of_forall ρbar hdet τ r
    (fun μ hμ => ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow Fact.out hr hrp A hA hτ μ hμ)

private theorem exists_det_eq_natCast (ρbar : ResidualGaloisRep k) {p : ℕ} [Fact p.Prime]
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ∃ a : ℕ, LinearMap.det (ρbar.ρ σ) = (a : k) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({p} : Set ℕ)) (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) (Set.mem_singleton p) (NeZero.ne p)
  have hσζ : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  refine ⟨a, det_eq_natCast_of_forall ρbar hdet σ a (fun μ hμ => ?_)⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [← hi, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

private theorem exists_seed_of_five_le (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    {p : ℕ} [Fact p.Prime] [CharP k p] (h2 : (2 : k) ≠ 0) (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (h5 : 5 ≤ p) :
    ∃ σ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (matRep ρbar b σ₀).det ≠ 1 ∧ (matRep ρbar b σ₀ - 1).det ≠ 0 ∧
      (matRep ρbar b σ₀ + 1).det ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf a₀ = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha₀, Nat.card_units, Nat.card_zmod]
  obtain ⟨ℓ₀, hℓ₀p, hℓ₀, hℓ₀a⟩ := Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit a₀) p
  obtain ⟨A₀, hA₀, τ₀, hτ₀⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ₀ hℓ₀
  have hdet₀ : (matRep ρbar b τ₀).det = (ℓ₀ : k) := by
    rw [det_matRep]
    exact det_eq_natCast_of_isFrobeniusAt ρbar hdet hℓ₀ (Nat.ne_of_gt hℓ₀p) hA₀ hτ₀
  let φ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hφ : Function.Injective φ := φ.injective
  have hφℓ : φ (a₀ : ZMod p) = (ℓ₀ : k) := by rw [← hℓ₀a, map_natCast]
  refine exists_det_ne_one_and_det_sub_one_ne_zero_of_span_eq_top h2 (matRep ρbar b)
    (span_matRep_eq_top ρbar b habs) τ₀ ?_ ?_ ?_
  · intro h
    rw [hdet₀, ← hφℓ, ← map_pow, ← Units.val_pow_eq_pow_val] at h
    have h1 : a₀ ^ 2 = 1 := Units.val_eq_one.mp (hφ (h.trans (map_one φ).symm))
    have := Nat.le_of_dvd two_pos (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  · intro h
    rw [hdet₀, ← hφℓ] at h
    have h3 : (a₀ : ZMod p) ^ 3 = 1 := by
      have h' : φ ((a₀ : ZMod p) ^ 2 + a₀ + 1) = φ 0 := by
        rw [map_add, map_add, map_pow, map_one, map_zero]; exact h
      have h'' := hφ h'
      calc (a₀ : ZMod p) ^ 3 = ((a₀ : ZMod p) - 1) * ((a₀ : ZMod p) ^ 2 + a₀ + 1) + 1 := by ring
        _ = 1 := by rw [h'', mul_zero, zero_add]
    rw [← Units.val_pow_eq_pow_val] at h3
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one (Units.val_eq_one.mp h3))
    omega
  · intro g
    obtain ⟨a, ha⟩ := exists_det_eq_natCast ρbar hdet g
    have hdg : (matRep ρbar b g).det = φ (a : ZMod p) := by rw [det_matRep, ha, map_natCast]
    have ha0 : (a : ZMod p) ≠ 0 := by
      intro h0
      apply det_matRep_ne_zero ρbar b g
      rw [hdg, h0, map_zero]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a₀ ^ j = Units.mk0 _ ha0 :=
      (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (ha₀ _))
    refine ⟨j, ?_⟩
    rw [hdg, hdet₀, ← hφℓ, ← map_pow, ← Units.val_pow_eq_pow_val, hj, Units.val_mk0]

private theorem exists_seed_three (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    [Fact (Nat.Prime 3)] [CharP k 3] (h2 : (2 : k) ≠ 0) (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic 3)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K],
      ∀ G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ v ∈ V, (ρbar.baseChange K).ρ σ v ∈ V) → (V = ⊥ ∨ V = ⊤)) :
    ∃ σ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (matRep ρbar b σ₀).det ≠ 1 ∧ (matRep ρbar b σ₀ - 1).det ≠ 0 ∧
      (matRep ρbar b σ₀ + 1).det ≠ 0 := by
  classical
  obtain ⟨ℓ₁, hℓ₁p, hℓ₁, hℓ₁a⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 3) (a := -1) isUnit_one.neg 3
  obtain ⟨A₁, hA₁, τ₁, hτ₁⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ₁ hℓ₁
  let φ : ZMod 3 →+* k := ZMod.castHom (dvd_refl 3) k
  have hdet₁ : (matRep ρbar b τ₁).det = -1 := by
    rw [det_matRep, det_eq_natCast_of_isFrobeniusAt ρbar hdet hℓ₁ (Nat.ne_of_gt hℓ₁p) hA₁ hτ₁,
      ← map_natCast φ, hℓ₁a, map_neg, map_one]
  have hdet2 : ∀ g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (matRep ρbar b g).det = 1 ∨ (matRep ρbar b g).det = -1 := by
    intro g
    obtain ⟨a, ha⟩ := exists_det_eq_natCast ρbar hdet g
    have hdg : (matRep ρbar b g).det = φ (a : ZMod 3) := by rw [det_matRep, ha, map_natCast]
    have ha0 : (a : ZMod 3) ≠ 0 := by
      intro h0
      apply det_matRep_ne_zero ρbar b g
      rw [hdg, h0, map_zero]
    have hcases : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
      intro x hx
      fin_cases x
      · exact absurd rfl hx
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases _ ha0 with h | h
    · left; rw [hdg, h, map_one]
    · right; rw [hdg, h, map_neg, map_one]
  refine exists_det_ne_one_and_det_sub_one_ne_zero_of_involutions h2 (matRep ρbar b)
    (span_matRep_eq_top ρbar b habs) τ₁ hdet₁ hdet2 ?_

  intro v hv
  by_contra hall
  push Not at hall
  set w : AlgebraicClosure k ⊗[k] ρbar.V :=
    (Algebra.TensorProduct.basis (AlgebraicClosure k) b).equivFun.symm v with hw_def
  have hw : ⇑((Algebra.TensorProduct.basis (AlgebraicClosure k) b).repr w) = v :=
    (Algebra.TensorProduct.basis (AlgebraicClosure k) b).equivFun.apply_symm_apply v
  have hw0 : w ≠ 0 := by
    intro h
    apply hv
    rw [← hw, h, map_zero, Finsupp.coe_zero]
  have hscale : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (matRep ρbar b σ).det = 1 →
      ∃ c : AlgebraicClosure k, (ρbar.ρ σ).baseChange (AlgebraicClosure k) w = c • w := by
    intro σ hσ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hall σ hσ)
    refine ⟨c, (Algebra.TensorProduct.basis (AlgebraicClosure k) b).repr.injective
      (DFunLike.coe_injective ?_)⟩
    change ⇑((Algebra.TensorProduct.basis (AlgebraicClosure k) b).repr
        (((ρbar.ρ σ).baseChange (AlgebraicClosure k)) w)) =
      ⇑((Algebra.TensorProduct.basis (AlgebraicClosure k) b).repr (c • w))
    rw [← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis (AlgebraicClosure k) b)
      (Algebra.TensorProduct.basis (AlgebraicClosure k) b) ((ρbar.ρ σ).baseChange (AlgebraicClosure k)) w,
      LinearMap.toMatrix_baseChange, hw, map_smul, Finsupp.coe_smul, hw]
    exact hc.symm
  set G' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).toHomUnits.ker
    with hG'_def
  have hmem : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ G' ↔ (matRep ρbar b σ).det = 1 := by
    intro σ
    rw [hG'_def, MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply,
      det_matRep]
  have hidx : G'.index = 2 := by
    rw [hG'_def, Subgroup.index_ker, Nat.card_eq_two_iff]
    refine ⟨⟨_, τ₁, rfl⟩, 1, ?_, ?_⟩
    · intro h
      rw [Subtype.ext_iff] at h
      have h' := congrArg Units.val h
      change ((((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).toHomUnits τ₁ : kˣ) : k) =
        ((1 : kˣ) : k) at h'
      rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, ← det_matRep ρbar b, hdet₁, Units.val_one] at h'
      apply h2
      calc (2 : k) = 1 - (-1) := by ring
        _ = 0 := by rw [h', sub_self]
    · apply Set.eq_univ_iff_forall.mpr
      rintro ⟨u, σ, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hdet2 σ with h | h
      · right
        apply Subtype.ext
        apply Units.ext
        change ((((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).toHomUnits σ : kˣ) : k) =
          ((1 : kˣ) : k)
        rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, ← det_matRep ρbar b, h, Units.val_one]
      · left
        apply Subtype.ext
        apply Units.ext
        change ((((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).toHomUnits σ : kˣ) : k) =
          ((((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).toHomUnits τ₁ : kˣ) : k)
        rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply,
          MonoidHom.comp_apply, ← det_matRep ρbar b, ← det_matRep ρbar b, h, hdet₁]
  have hstab : ∀ σ ∈ G', ∀ x ∈ (AlgebraicClosure k) ∙ w,
      (ρbar.baseChange (AlgebraicClosure k)).ρ σ x ∈ (AlgebraicClosure k) ∙ w := by
    intro σ hσ x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, hc⟩ := hscale σ ((hmem σ).mp hσ)
    show ((ρbar.ρ σ).baseChange (AlgebraicClosure k)) (t • w) ∈ _
    rw [map_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  rcases hTW (AlgebraicClosure k) G' hidx ((AlgebraicClosure k) ∙ w) hstab with h | h
  · exact hw0 (Submodule.span_singleton_eq_bot.mp h)
  · have h1 : Module.finrank (AlgebraicClosure k) ((AlgebraicClosure k) ∙ w) = 1 :=
      finrank_span_singleton hw0
    have hfr := (ρbar.baseChange (AlgebraicClosure k)).finrank_eq
    change Module.finrank (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] ρbar.V) = 2 at hfr
    rw [h, finrank_top, hfr] at h1
    exact absurd h1 (by norm_num)

private theorem main (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) (p : ℕ)
    [Fact p.Prime] [CharP k p] (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (σ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hd : (matRep ρbar b σ₀).det ≠ 1) (hm : (matRep ρbar b σ₀ - 1).det ≠ 0)
    (hpl : (matRep ρbar b σ₀ + 1).det ≠ 0)
    (Sram : Finset ℕ) (hram : ∀ q : ℕ, q.Prime → q ∉ Sram → ρbar.IsUnramifiedAt q) (T : Finset ℕ) :
    ∃ r : ℕ, r.Prime ∧ r ∉ T ∧ ¬ p ∣ r - 1 ∧ ρbar.IsUnramifiedAt r ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
          (LinearMap.trace k ρbar.V (ρbar.ρ σ)) ^ 2 ≠ ((r : k) + 1) ^ 2 := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hLfd
  have hopen : IsOpen ((ρbar.ρ.toHomUnits.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) _ (IntermediateField.fixingSubgroup_isOpen L)
    intro τ hτ
    rw [MonoidHom.mem_ker]
    ext1
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    exact hL τ ((IntermediateField.mem_fixingSubgroup_iff (K := L) τ).mp hτ)

  set M : ℕ := p * ∏ x ∈ (T ∪ Sram).erase 0, x with hM_def
  have hM : 0 < M :=
    Nat.mul_pos hp.pos (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hx))
  have hdvdM : ∀ x ∈ T ∪ Sram, x ≠ 0 → x ∣ M := fun x hx hx0 =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun x => x) (Finset.mem_erase.mpr ⟨hx0, hx⟩)) p

  obtain ⟨r, A, τ, g, n, -, hr, hrM, hA, hτ, hker, -⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen _ hopen σ₀ hM
  have hrp : r ≠ p := fun h => hrM (h ▸ ⟨_, hM_def⟩)
  have hrT : r ∉ T := fun h => hrM (hdvdM r (Finset.mem_union_left _ h) hr.ne_zero)
  have hrS : r ∉ Sram := fun h => hrM (hdvdM r (Finset.mem_union_right _ h) hr.ne_zero)
  have hunr : ρbar.IsUnramifiedAt r := hram r hr hrS

  have hconj : matRep ρbar b g * matRep ρbar b τ ^ n * matRep ρbar b g⁻¹ = matRep ρbar b σ₀ := by
    have h1 : ρbar.ρ (g * τ ^ n * g⁻¹) = ρbar.ρ σ₀ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
      have := congrArg Units.val hker
      rwa [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits] at this
    have h2 : matRep ρbar b (g * τ ^ n * g⁻¹) = matRep ρbar b σ₀ := by
      rw [matRep_apply, matRep_apply, h1]
    rwa [map_mul, map_mul, map_pow] at h2
  have hPP : matRep ρbar b g * matRep ρbar b g⁻¹ = 1 := matRep_mul_inv ρbar b g
  have hdetτ : (matRep ρbar b τ).det = (r : k) := by
    rw [det_matRep]; exact det_eq_natCast_of_isFrobeniusAt ρbar hdet hr hrp hA hτ

  have hτd : (matRep ρbar b τ).det ≠ 1 := by
    intro h1
    apply hd
    rw [← hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_pow, h1, one_pow, mul_one, ← Matrix.det_mul,
      hPP, Matrix.det_one]
  have hdiv : ∀ ε : Matrix (Fin 2) (Fin 2) k, Commute (matRep ρbar b τ) ε →
      (matRep ρbar b τ - ε).det = 0 → (matRep ρbar b τ ^ n - ε ^ n).det = 0 := by
    intro ε hc h0
    rw [← hc.geom_sum₂_mul n, Matrix.det_mul, h0, mul_zero]
  have hτm : (matRep ρbar b τ - 1).det ≠ 0 := by
    intro h0
    have h := hdiv 1 (Commute.one_right _) h0
    rw [one_pow] at h
    apply hm
    rw [← hconj, conj_sub_one _ _ _ hPP, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]
  have hτp : (matRep ρbar b τ + 1).det ≠ 0 := by
    intro h0
    have h := hdiv (-1) (Commute.neg_one_right _) (by rwa [sub_neg_eq_add])
    rcases neg_one_pow_eq_or (R := Matrix (Fin 2) (Fin 2) k) n with he | he
    · rw [he] at h
      apply hm
      rw [← hconj, conj_sub_one _ _ _ hPP, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]
    · rw [he, sub_neg_eq_add] at h
      apply hpl
      rw [← hconj, conj_add_one _ _ _ hPP, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]
  refine ⟨r, hr, hrT, ?_, hunr, ?_⟩
  ·
    intro hdvd
    apply hτd
    rw [hdetτ]
    have h : ((r - 1 : ℕ) : k) = 0 := (CharP.cast_eq_zero_iff k p _).mpr hdvd
    rwa [Nat.cast_sub hr.one_le, Nat.cast_one, sub_eq_zero] at h
  ·
    intro P hP φ hφ
    have hunr' : GlobalGaloisRep.IsUnramifiedAt ρbar.ρ.toHomUnits r := by
      intro A' hA' x hx
      rw [MonoidHom.mem_ker]
      ext1
      rw [MonoidHom.coe_toHomUnits, Units.val_one]
      exact hunr A' hA' x hx
    obtain ⟨c, hc⟩ := GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt hr hunr'
      hA hP hτ hφ
    have hcc : matRep ρbar b c * matRep ρbar b c⁻¹ = 1 := matRep_mul_inv ρbar b c
    have hc' : matRep ρbar b φ = matRep ρbar b c * matRep ρbar b τ * matRep ρbar b c⁻¹ := by
      have := congrArg Units.val hc
      rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits] at this
      rw [← map_mul, ← map_mul, matRep_apply, matRep_apply, this]
    have hφd : (matRep ρbar b φ).det = (r : k) := by rw [hc', det_conj, hdetτ]
    have hφm : (matRep ρbar b φ - 1).det ≠ 0 := by rw [hc', conj_sub_one _ _ _ hcc, det_conj]; exact hτm
    have hφp : (matRep ρbar b φ + 1).det ≠ 0 := by rw [hc', conj_add_one _ _ _ hcc, det_conj]; exact hτp
    rw [LinearMap.trace_eq_matrix_trace k b, ← matRep_apply]
    intro heq
    have hid := det_sub_one_mul_det_add_one (matRep ρbar b φ)
    rw [hφd, heq, sub_self] at hid
    rcases mul_eq_zero.mp hid with h | h
    · exact hφm h
    · exact hφp h

end GaloisSide

end ResidualGaloisRep.FrobeniusTraceResidue

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (Sram : Finset ℕ) (hram : ∀ q : ℕ, q.Prime → q ∉ Sram → ρbar.IsUnramifiedAt q)
    (T : Finset ℕ) :
    ∃ r : ℕ, r.Prime ∧ r ∉ T ∧ ¬ p ∣ r - 1 ∧ ρbar.IsUnramifiedAt r ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : k) + 1) ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have h0 : (p : k) = 0 := ResidualGaloisRep.FrobeniusTraceResidue.natCast_eq_zero ρbar hdet
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr h0
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by rw [Nat.cast_ofNat]; exact h
    rw [CharP.cast_eq_zero_iff k p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  let b : Module.Basis (Fin 2) k ρbar.V := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  have h35 : p = 3 ∨ 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · left
      have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
      have := hp.two_le
      omega
    · exact Or.inr h
  obtain ⟨σ₀, hd, hm, hpl⟩ : ∃ σ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (ResidualGaloisRep.FrobeniusTraceResidue.matRep ρbar b σ₀).det ≠ 1 ∧
      (ResidualGaloisRep.FrobeniusTraceResidue.matRep ρbar b σ₀ - 1).det ≠ 0 ∧
      (ResidualGaloisRep.FrobeniusTraceResidue.matRep ρbar b σ₀ + 1).det ≠ 0 := by
    rcases h35 with rfl | h5
    · exact ResidualGaloisRep.FrobeniusTraceResidue.exists_seed_three ρbar b h2 habs hdet hTW
    · exact ResidualGaloisRep.FrobeniusTraceResidue.exists_seed_of_five_le ρbar b h2 habs hdet h5
  exact ResidualGaloisRep.FrobeniusTraceResidue.main ρbar b p hdet σ₀ hd hm hpl Sram hram T

end S_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
end P2MW
export P2MW.S_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne (solution)
