-- Prove2me | solution 1 for ShortBroadcastDom.sec_7_3_output_count_noninteger
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:30:22.147677+00:00
-- url     : https://prove2.me/submissions/f7cf2707-ee39-4a19-933f-25d01fcb6a19

import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData
import Theorems.Thm_ShortBroadcastDom_lemma_7_1_rounding_calculation

open ShortBroadcastDom

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℚ) (ha : 1 ≤ a) (hna : ∀ m : ℤ, 2 * a ≠ m) (hG : SubgraphDensityLE (a : ℝ) G)
    (x : V → ℝ) (hx : IsFeasibleOn G Finset.univ Finset.univ x) :
    (((uniformRounding (a : ℝ) x).D G).card : ℝ) ≤
      (a : ℝ) / (1 - ((2 * a : ℚ) - ⌊2 * a⌋ : ℝ)) *
          (((uniformRounding (a : ℝ) x).wCard : ℝ) + ((uniformRounding (a : ℝ) x).ell G : ℝ)) +
        ((⌊2 * a⌋ : ℝ) + 1) / ((2 * a : ℚ) - ⌊2 * a⌋ : ℝ) * (uniformRounding (a : ℝ) x).P G := by
  set d : RoundingData V := uniformRounding (a : ℝ) x
  have ha_real : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hset : IsRoundingSetting G d := by
    refine ⟨ha_real, Finset.Subset.refl _, ?_, hx⟩
    intro v _
    change 0 < 2 * (a : ℝ) + 1 ∧ 2 * (a : ℝ) + 1 ≤ 2 * (a : ℝ) + 1
    exact ⟨by linarith, le_rfl⟩
  have hH : ∀ v ∈ d.H G, d.c v = d.b := fun _ _ => rfl
  have hO_lt : ∀ v ∈ d.O G, (d.h G v : ℝ) < d.b := by
    intro v hvO
    rcases Finset.mem_sdiff.mp hvO with ⟨hvC, hvWH⟩
    have hvNotW : v ∉ d.W := fun h => hvWH (Finset.mem_union_left _ h)
    have hvNotH : v ∉ d.H G := fun h => hvWH (Finset.mem_union_right _ h)
    have hvCW : v ∈ d.C \ d.W := Finset.mem_sdiff.mpr ⟨hvC, hvNotW⟩
    by_contra hge
    exact hvNotH (Finset.mem_filter.mpr ⟨hvCW, le_of_not_gt hge⟩)
  have hO : ∀ v ∈ d.O G, (d.h G v : ℝ) ≤ d.c v := fun v hvO => le_of_lt (hO_lt v hvO)
  have h71 := lemma_7_1_rounding_calculation G d hset hG hH hO
  have hineq19 := h71.2.1
  have hineq20 := h71.2.2.1

  set k : ℤ := ⌊2 * a⌋
  set θ : ℝ := ((2 * a : ℚ) : ℝ) - (k : ℝ)
  have hk_lt_2a : (k : ℚ) < 2 * a :=
    lt_of_le_of_ne (Int.floor_le (2 * a)) (Ne.symm (hna k))
  have h2a_lt_k1 : 2 * a < (k : ℚ) + 1 := Int.lt_floor_add_one (2 * a)
  have hθ_pos : 0 < θ := by
    have hkr : (k : ℝ) < ((2 * a : ℚ) : ℝ) := by exact_mod_cast hk_lt_2a
    linarith
  have hθ_lt1 : θ < 1 := by
    have hkr : ((2 * a : ℚ) : ℝ) < (k : ℝ) + 1 := by exact_mod_cast h2a_lt_k1
    linarith
  have h1θ_pos : 0 < 1 - θ := by linarith
  have hb_eq : d.b = (k : ℝ) + 1 + θ := by
    have h2a_cast : ((2 * a : ℚ) : ℝ) = 2 * (a : ℝ) := by push_cast; ring
    change 2 * (a : ℝ) + 1 = (k : ℝ) + 1 + (((2 * a : ℚ) : ℝ) - (k : ℝ))
    linarith
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) + 1 := by
    have h2_le_2a : ((2 : ℤ) : ℚ) ≤ 2 * a := by push_cast; linarith
    have hk2 : (2 : ℤ) ≤ k := Int.le_floor.mpr h2_le_2a
    have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith

  -- Bound |H|
  have hH_each : ∀ v ∈ d.H G, 1 - θ ≤ (d.h G v : ℝ) - d.b := by
    intro v hvH
    have hbh : d.b ≤ (d.h G v : ℝ) := (Finset.mem_filter.mp hvH).2
    have hlt_int_r : ((k + 1 : ℤ) : ℝ) < ((d.h G v : ℤ) : ℝ) := by
      push_cast
      linarith [hb_eq]
    have hlt_int : k + 1 < (d.h G v : ℤ) := Int.cast_lt.mp hlt_int_r
    have hle_int : k + 2 ≤ (d.h G v : ℤ) := by omega
    have hle_r : ((k + 2 : ℤ) : ℝ) ≤ ((d.h G v : ℤ) : ℝ) := Int.cast_le.mpr hle_int
    push_cast at hle_r
    linarith [hb_eq]
  have hH_sum : (1 - θ) * ((d.H G).card : ℝ) ≤ (a : ℝ) * (d.ell G : ℝ) := by
    have h1 : (1 - θ) * ((d.H G).card : ℝ) ≤ ∑ v ∈ d.H G, ((d.h G v : ℝ) - d.b) := by
      calc (1 - θ) * ((d.H G).card : ℝ) = ∑ _v ∈ d.H G, (1 - θ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ v ∈ d.H G, ((d.h G v : ℝ) - d.b) := Finset.sum_le_sum hH_each
    have h2 : (0 : ℝ) ≤ (d.a + 1) * (((d.H G \ d.R G).card : ℝ)) := by
      change (0 : ℝ) ≤ ((a : ℝ) + 1) * _
      positivity
    change _ ≤ d.a * (d.ell G : ℝ)
    linarith [h1, h2, hineq19]
  have hH_bound : ((d.H G).card : ℝ) ≤ ((a : ℝ) / (1 - θ)) * (d.ell G : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1θ_pos]
    linarith [hH_sum]

  -- Bound |U|
  have hU_each : ∀ v ∈ d.O G, θ * ((d.h G v : ℝ) * d.x v) ≤
      ((k : ℝ) + 1) * ((d.c v - (d.h G v : ℝ)) * d.x v) := by
    intro v hvO
    have hlt_b : (d.h G v : ℝ) < d.b := hO_lt v hvO
    have hlt_int_r : ((d.h G v : ℤ) : ℝ) < ((k + 2 : ℤ) : ℝ) := by
      push_cast
      linarith [hb_eq, hθ_lt1]
    have hlt_int : (d.h G v : ℤ) < k + 2 := Int.cast_lt.mp hlt_int_r
    have hle_int : (d.h G v : ℤ) ≤ k + 1 := by omega
    have hle_r : ((d.h G v : ℤ) : ℝ) ≤ ((k + 1 : ℤ) : ℝ) := Int.cast_le.mpr hle_int
    push_cast at hle_r
    have hch_ge : θ ≤ d.c v - (d.h G v : ℝ) := by
      have hcv : d.c v = d.b := rfl
      linarith [hcv, hb_eq, hle_r]
    have hx0 : 0 ≤ d.x v := (hx.1 v (Finset.mem_univ v)).1
    have hstep1 : θ * ((d.h G v : ℝ) * d.x v) ≤ θ * (((k : ℝ) + 1) * d.x v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_r hx0) (le_of_lt hθ_pos)
    have hstep2 : ((k : ℝ) + 1) * (θ * d.x v) ≤
        ((k : ℝ) + 1) * ((d.c v - (d.h G v : ℝ)) * d.x v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hch_ge hx0) hk_nonneg
    linarith [hstep1, hstep2]
  have hU_sum : θ * ((d.U G).card : ℝ) ≤ ((k : ℝ) + 1) * d.P G := by
    calc θ * ((d.U G).card : ℝ) ≤ θ * (∑ v ∈ d.O G, (d.h G v : ℝ) * d.x v) :=
          mul_le_mul_of_nonneg_left hineq20 (le_of_lt hθ_pos)
      _ = ∑ v ∈ d.O G, θ * ((d.h G v : ℝ) * d.x v) := Finset.mul_sum _ _ _
      _ ≤ ∑ v ∈ d.O G, ((k : ℝ) + 1) * ((d.c v - (d.h G v : ℝ)) * d.x v) :=
          Finset.sum_le_sum hU_each
      _ = ((k : ℝ) + 1) * d.P G := (Finset.mul_sum _ _ _).symm
  have hU_bound : ((d.U G).card : ℝ) ≤ (((k : ℝ) + 1) / θ) * d.P G := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ_pos]
    linarith [hU_sum]

  -- Combine |D| ≤ w + |H| + |U|
  have hD_card_nat : (d.D G).card ≤ d.wCard + (d.H G).card + (d.U G).card := by
    change (d.W ∪ d.H G ∪ d.U G).card ≤ d.W.card + (d.H G).card + (d.U G).card
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hD_card : ((d.D G).card : ℝ) ≤ (d.wCard : ℝ) + ((d.H G).card : ℝ) + ((d.U G).card : ℝ) := by
    exact_mod_cast hD_card_nat
  have hM_ge1 : 1 ≤ (a : ℝ) / (1 - θ) := by
    rw [le_div_iff₀ h1θ_pos]
    linarith [ha_real, hθ_pos]
  have hw_nonneg : (0 : ℝ) ≤ (d.wCard : ℝ) := Nat.cast_nonneg _
  have hw_bound : (d.wCard : ℝ) ≤ ((a : ℝ) / (1 - θ)) * (d.wCard : ℝ) := by
    nlinarith
  linarith [hD_card, hw_bound, hH_bound, hU_bound]
