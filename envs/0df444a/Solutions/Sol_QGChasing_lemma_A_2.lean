-- Prove2me | solution 1 for QGChasing.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-17T15:27:45.654103+00:00
-- url     : https://prove2.me/submissions/4da33cec-a842-4599-875e-645e15fc2db9

import Mathlib

set_option maxHeartbeats 1200000

private lemma key_ineq (A β p : ℝ) (hA : 0 ≤ A) (hp : 0 ≤ p) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    β * p + A * Real.sqrt (1 - β ^ 2) ≤ Real.sqrt (p ^ 2 + A ^ 2) := by
  have h1β : 0 ≤ 1 - β ^ 2 := by nlinarith
  rw [Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [sq_nonneg (p * Real.sqrt (1 - β ^ 2) - β * A), Real.sq_sqrt h1β]

theorem solution {d : ℕ} (y u v : EuclideanSpace ℝ (Fin d)) (A R γ η : ℝ) (hA : 0 < A)
    (hR : 0 < R) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : η = if y = v then γ else min γ (R / ‖y - v‖)) :
    min R (A * Real.sqrt (γ * (2 - γ))) ≤
      Real.sqrt (‖y - u‖ ^ 2 + A ^ 2) - (1 - η) * ‖y - u‖ + (γ - η) * ‖u - v‖ := by
  have hηγ : η ≤ γ := by
    rw [hη]
    split_ifs with h
    · exact le_rfl
    · exact min_le_left _ _
  have hγ2 : 0 ≤ γ * (2 - γ) := by nlinarith
  have hspos : 0 < Real.sqrt (γ * (2 - γ)) := Real.sqrt_pos.mpr (by nlinarith)
  set p : ℝ := ‖y - u‖ with hp
  set q : ℝ := ‖u - v‖ with hq
  set r : ℝ := ‖y - v‖ with hr
  set s : ℝ := Real.sqrt (γ * (2 - γ)) with hs
  set E : ℝ := Real.sqrt (p ^ 2 + A ^ 2) - (1 - η) * p + (γ - η) * q with hE
  have hs2 : s ^ 2 = γ * (2 - γ) := Real.sq_sqrt hγ2
  have hsnn : 0 ≤ s := le_of_lt hspos
  have hpnn : 0 ≤ p := norm_nonneg _
  have hqnn : 0 ≤ q := norm_nonneg _
  have hrnn : 0 ≤ r := norm_nonneg _
  have hδ : 0 ≤ γ - η := by linarith
  have htri : r ≤ p + q := by
    simpa [dist_eq_norm] using dist_triangle y u v
  have hsp : p ≤ Real.sqrt (p ^ 2 + A ^ 2) := by
    rw [Real.le_sqrt hpnn (by positivity)]
    nlinarith [sq_nonneg A]
  have hkey : (1 - γ) * p + A * s ≤ Real.sqrt (p ^ 2 + A ^ 2) := by
    have h := key_ineq A (1 - γ) p hA.le hpnn (by linarith) (by linarith)
    have hsq : 1 - (1 - γ) ^ 2 = γ * (2 - γ) := by ring
    rw [hsq] at h
    rwa [← hs] at h
  have hmain : min R (A * s) ≤ E := by
    by_cases heta : η = γ
    · have hq0 : (γ - η) * q = 0 := by rw [show γ - η = 0 by linarith]; ring
      have hp1 : (1 - η) * p = (1 - γ) * p := by rw [heta]
      have hEAs : A * s ≤ E := by
        rw [hE, hp1, hq0]
        simp only [add_zero]
        linarith [hkey]
      exact le_trans (min_le_right _ _) hEAs
    · have hηγ' : η < γ := lt_of_le_of_ne hηγ heta
      have hyv : y ≠ v := by
        intro h
        rw [h] at hη
        simp only [if_true] at hη
        exact heta hη
      have hηmin : η = min γ (R / r) := by
        have h := hη
        rw [if_neg hyv] at h
        exact h
      have hlt : R / r < γ := by
        have h2 : min γ (R / r) < γ := by rw [← hηmin]; exact hηγ'
        rw [min_lt_iff] at h2
        exact h2.resolve_left (lt_irrefl γ)
      have hηeq : η = R / r := by
        rw [hηmin]
        exact min_eq_right (le_of_lt hlt)
      have hrpos : 0 < r := by
        rw [hr]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hyv)
      have hηpos : 0 < η := by
        rw [hηeq]
        exact div_pos hR hrpos
      have hRη : R = η * r := by
        rw [hηeq]
        field_simp
      have hEbound : Real.sqrt (p ^ 2 + A ^ 2) - (1 + γ - 2 * η) * p + (γ - η) * r ≤ E := by
        rw [hE]
        have hqrp : r - p ≤ q := by linarith [htri]
        have hq' : (γ - η) * (r - p) ≤ (γ - η) * q := mul_le_mul_of_nonneg_left hqrp hδ
        have hexp : Real.sqrt (p ^ 2 + A ^ 2) - (1 - η) * p + (γ - η) * q =
            (Real.sqrt (p ^ 2 + A ^ 2) - (1 + γ - 2 * η) * p + (γ - η) * r) +
              (γ - η) * (q - (r - p)) := by ring
        rw [hexp]
        linarith [hq']
      by_cases hpr : r ≤ p
      · have h1 : η * p ≤ E := by
          have hδq : 0 ≤ (γ - η) * q := mul_nonneg hδ hqnn
          have h2 : η * p ≤ Real.sqrt (p ^ 2 + A ^ 2) - (1 - η) * p + (γ - η) * q := by
            nlinarith [hsp, hδq]
          rwa [hE]
        have hER : R ≤ E := by
          rw [hRη]
          calc η * r ≤ η * p := mul_le_mul_of_nonneg_left hpr hηpos.le
            _ ≤ E := h1
        exact le_trans (min_le_left _ _) hER
      · have hprlt : p < r := lt_of_not_ge hpr
        by_cases hnu : 2 * η ≤ γ
        · have hνnn : 2 * η - γ ≤ 0 := by linarith
          have hprod : (2 * η - γ) * (r - p) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hνnn (by linarith)
          have hER : R ≤ E := by
            rw [hRη]
            have hgl : η * r ≤ Real.sqrt (p ^ 2 + A ^ 2) - (1 + γ - 2 * η) * p + (γ - η) * r := by
              nlinarith [hsp, hprod]
            linarith [hEbound, hgl]
          exact le_trans (min_le_left _ _) hER
        · push_neg at hnu
          have hνpos : 0 < 2 * η - γ := by linarith
          have hνle : 2 * η - γ ≤ γ := by linarith
          have hβ0 : 0 ≤ 1 - (2 * η - γ) := by linarith
          have hβ1 : 1 - (2 * η - γ) ≤ 1 := by linarith
          have harg : 0 ≤ (2 * η - γ) * (2 - (2 * η - γ)) := by nlinarith
          have hB : 0 ≤ 2 * η ^ 2 - (2 - γ) * η + γ * (2 - γ) := by
            have hBν : 2 * η ^ 2 - (2 - γ) * η + γ * (2 - γ) =
                (2 * η - γ) ^ 2 / 2 + (2 * η - γ) * (3 * γ / 2 - 1) + γ := by ring
            rw [hBν]
            by_cases hc : 1 ≤ 3 * γ / 2
            · nlinarith [hνpos, hc, hγ0, sq_nonneg (2 * η - γ)]
            · push_neg at hc
              have h1 : (2 * η - γ) * (3 * γ / 2 - 1) ≥ γ * (3 * γ / 2 - 1) := by
                nlinarith [hνle, hc]
              nlinarith [h1, sq_nonneg (2 * η - γ)]
          have hD : 0 ≤ η ^ 2 * (2 - (2 * η - γ)) - γ * (2 - γ) * (2 * η - γ) := by
            have hfac : η ^ 2 * (2 - (2 * η - γ)) - γ * (2 - γ) * (2 * η - γ) =
                (γ - η) * (2 * η ^ 2 - (2 - γ) * η + γ * (2 - γ)) := by ring
            rw [hfac]
            exact mul_nonneg (by linarith) hB
          have hsq : (s * (2 * η - γ) / η) ^ 2 ≤ (2 * η - γ) * (2 - (2 * η - γ)) := by
            rw [div_pow, mul_pow, hs2, div_le_iff₀ (by positivity : (0 : ℝ) < η ^ 2)]
            nlinarith [hD, hνpos]
          have hstar : s * (2 * η - γ) / η ≤ Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) := by
            rw [Real.le_sqrt (by positivity) harg]
            exact hsq
          have hCS : A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) ≤
              Real.sqrt (p ^ 2 + A ^ 2) - (1 + γ - 2 * η) * p := by
            have h := key_ineq A (1 - (2 * η - γ)) p hA.le hpnn hβ0 hβ1
            have hsq : 1 - (1 - (2 * η - γ)) ^ 2 = (2 * η - γ) * (2 - (2 * η - γ)) := by ring
            rw [hsq] at h
            have hcoef : 1 - (2 * η - γ) = 1 + γ - 2 * η := by ring
            rw [hcoef] at h
            linarith [h]
          by_cases hAR : A * s ≤ R
          · have hrge : A * s / η ≤ r := by
              rw [hRη] at hAR
              exact (div_le_iff₀ hηpos).mpr (by linarith [hAR])
            have hEAs : A * s ≤ E := by
              have h1 : (A * s) * (2 * η - γ) / η ≤
                  A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) := by
                calc (A * s) * (2 * η - γ) / η = A * (s * (2 * η - γ) / η) := by ring
                  _ ≤ A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) :=
                      mul_le_mul_of_nonneg_left hstar hA.le
              have hid : (A * s) * (2 * η - γ) / η + (γ - η) * (A * s / η) = A * s := by
                field_simp
                ring
              have h3 : (γ - η) * (A * s / η) ≤ (γ - η) * r := mul_le_mul_of_nonneg_left hrge hδ
              linarith [hEbound, hCS, h1, h3, hid]
            exact le_trans (min_le_right _ _) hEAs
          · push_neg at hAR
            have hAle : η * r / s ≤ A := by
              rw [hRη] at hAR
              exact (div_le_iff₀ hspos).mpr (by linarith [hAR])
            have hER : R ≤ E := by
              rw [hRη]
              have hc : 0 ≤ s * (2 * η - γ) / η :=
                div_nonneg (mul_nonneg hsnn hνpos.le) hηpos.le
              have h1 : (2 * η - γ) * r ≤ A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) := by
                have h2 : (η * r / s) * (s * (2 * η - γ) / η) ≤
                    A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) := by
                  calc (η * r / s) * (s * (2 * η - γ) / η)
                      ≤ A * (s * (2 * η - γ) / η) := mul_le_mul_of_nonneg_right hAle hc
                    _ ≤ A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) :=
                        mul_le_mul_of_nonneg_left hstar hA.le
                have hid : (η * r / s) * (s * (2 * η - γ) / η) = (2 * η - γ) * r := by
                  field_simp
                linarith [hid, h2]
              have h2 : η * r ≤ A * Real.sqrt ((2 * η - γ) * (2 - (2 * η - γ))) + (γ - η) * r := by
                linarith
              linarith [hEbound, hCS, h2]
            exact le_trans (min_le_left _ _) hER
  exact hmain
