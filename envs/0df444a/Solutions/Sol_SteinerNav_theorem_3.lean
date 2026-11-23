-- Prove2me | solution 1 for SteinerNav.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:05:47.281034+00:00
-- url     : https://prove2.me/submissions/3350a086-810a-407a-b071-53611a9d95ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_annularCandidates
import Definitions.Def_SteinerNav_constructionEdges
import Theorems.Thm_SteinerNav_corollary_4_2
import Theorems.Thm_SteinerNav_construction_navigable
import Theorems.Thm_SteinerNav_construction_edge_count
import Theorems.Thm_SteinerNav_expected_type3_edges

open SteinerNav

namespace AuxThm3

lemma rpow_three_halves_mul_sqrt {n : ℝ} (hn : 0 < n) :
    n ^ (3 / 2 : ℝ) * Real.sqrt n = n ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  norm_num

lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) * x ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have h1r : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  by_cases hx2 : x < 2
  · linarith
  · have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith

lemma coversSet_mono {d : ℕ} {α : ℝ} {s : Pt d} {B₁ B₂ T : Finset (Pt d)}
    (hsub : B₁ ⊆ B₂) (hcov : CoversSet α s B₁ T) : CoversSet α s B₂ T := by
  intro t ht hts
  obtain ⟨v, hv, hcv⟩ := hcov t ht hts
  exact ⟨v, hsub hv, hcv⟩

lemma dense_case {d : ℕ} {C' : ℝ} (hC' : 0 < C') (hd : 1 ≤ d)
    (P : Finset (Pt d)) (hn : 2 ≤ P.card) (a : ℕ)
    (ha_ge : P.card ≤ a)
    (ha_le_C' : (a : ℝ) ≤ C' * ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) :
    let n : ℝ := (P.card : ℝ)
    let L : ℝ := (annulusCount P : ℝ)
    let C₁ : ℝ := Real.sqrt C'
    let C₂ : ℝ := max 11 (11 * Real.sqrt C')
    ∃ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
      IsSteinerNavigable (1 + 1 / (d : ℝ)) P R E ∧
      NoSteinerToSteiner R P E ∧
      (∀ x, (x, x) ∉ E) ∧
      R.card ≤ P.card ∧
      (R.card : ℝ) ≤ C₁ * Real.sqrt (n * L * Real.log n) ∧
      (E.card : ℝ) ≤ C₂ * min (n ^ 2) (n ^ (3 / 2 : ℝ) * Real.sqrt (L * Real.log n)) := by
  dsimp only
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hα_pos : 0 < 1 + 1 / (d : ℝ) := by positivity
  refine ⟨∅, (P ×ˢ P).filter (fun e => e.1 ≠ e.2), ?_, ?_, ?_, Nat.zero_le _, ?_, ?_⟩
  · refine ⟨Finset.disjoint_empty_left P, ?_, ?_⟩
    · intro x y hxy
      obtain ⟨hxP, hyP⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hxy).1
      exact ⟨Finset.mem_union_left _ hxP, Finset.mem_union_left _ hyP⟩
    · intro s hs t ht hts
      have hsP : s ∈ P := by simpa using hs
      refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsP, ht⟩, hts.symm⟩, ?_⟩
      unfold Covers
      rw [dist_self]
      exact div_pos (dist_pos.mpr hts.symm) hα_pos
  · intro x y _ hx
    exact absurd hx (Finset.notMem_empty x)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2 rfl
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hE_nat : ((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card ≤ P.card * P.card :=
      le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product P P))
    have hE_n2 : (((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
      have hc : (((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card : ℝ) ≤ (P.card : ℝ) * (P.card : ℝ) := by
        exact_mod_cast hE_nat
      linarith [sq (P.card : ℝ)]
    have hn_pos : 0 < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
    have hn_le_a : (P.card : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_ge
    have hn_le_C' : (P.card : ℝ) ≤ C' * ((annulusCount P : ℝ) * Real.log (P.card : ℝ)) :=
      le_trans hn_le_a ha_le_C'
    have hsqrtn : Real.sqrt (P.card : ℝ) ≤
        Real.sqrt C' * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ)) := by
      calc Real.sqrt (P.card : ℝ)
          ≤ Real.sqrt (C' * ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) :=
            Real.sqrt_le_sqrt hn_le_C'
        _ = Real.sqrt C' * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ)) :=
            Real.sqrt_mul (le_of_lt hC') _
    have hC2_pos : 0 < max (11 : ℝ) (11 * Real.sqrt C') :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hC2_1 : (1 : ℝ) ≤ max (11 : ℝ) (11 * Real.sqrt C') :=
      le_trans (by norm_num : (1 : ℝ) ≤ 11) (le_max_left _ _)
    have hC2_sqrt : Real.sqrt C' ≤ max (11 : ℝ) (11 * Real.sqrt C') := by
      have h11 : Real.sqrt C' ≤ 11 * Real.sqrt C' := by
        have hs0 : 0 ≤ Real.sqrt C' := Real.sqrt_nonneg C'
        linarith
      exact le_trans h11 (le_max_right _ _)
    have hb1 : (((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card : ℝ) ≤
        max 11 (11 * Real.sqrt C') * (P.card : ℝ) ^ 2 := by nlinarith
    have hb2 : (((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card : ℝ) ≤
        max 11 (11 * Real.sqrt C') *
          ((P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) := by
      calc (((P ×ˢ P).filter (fun e => e.1 ≠ e.2)).card : ℝ)
          ≤ (P.card : ℝ) ^ 2 := hE_n2
        _ = (P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (P.card : ℝ) :=
            (rpow_three_halves_mul_sqrt hn_pos).symm
        _ ≤ (P.card : ℝ) ^ (3 / 2 : ℝ) *
            (Real.sqrt C' * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) := by gcongr
        _ = Real.sqrt C' *
            ((P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) := by
            ring
        _ ≤ max 11 (11 * Real.sqrt C') *
            ((P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) := by
            gcongr
    rw [mul_min_of_nonneg _ _ (le_of_lt hC2_pos)]
    exact le_min hb1 hb2

lemma card_Algebra_bounds {n a m C' L logn : ℝ}
    (hn_pos : 0 < n) (ha_pos : 0 < a) (hC' : 0 < C') (ha_lt : a < n)
    (ha_le_C' : a ≤ C' * (L * logn))
    (hm_upper : m ≤ Real.sqrt (n / a))
    (hm_lower : (1 / 2 : ℝ) * Real.sqrt (n / a) ≤ m) :
    m * a ≤ Real.sqrt (n * a) ∧
    m * a ≤ n ∧
    m * a ≤ Real.sqrt C' * Real.sqrt (n * L * logn) ∧
    3 * (n * m * a) + 4 * n ^ 2 / m ≤
      max 11 (11 * Real.sqrt C') * min (n ^ 2) (n ^ (3 / 2 : ℝ) * Real.sqrt (L * logn)) := by
  have hsqn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqa_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
  have hma_le : m * a ≤ Real.sqrt (n * a) := by
    calc m * a ≤ Real.sqrt (n / a) * a := mul_le_mul_of_nonneg_right hm_upper (le_of_lt ha_pos)
      _ = (Real.sqrt n / Real.sqrt a) * (Real.sqrt a * Real.sqrt a) := by
          rw [Real.sqrt_div (le_of_lt hn_pos), Real.mul_self_sqrt (le_of_lt ha_pos)]
      _ = Real.sqrt n * Real.sqrt a := by
          have hne : Real.sqrt a ≠ 0 := ne_of_gt hsqa_pos
          field_simp
      _ = Real.sqrt (n * a) := (Real.sqrt_mul (le_of_lt hn_pos) a).symm
  have hma_n : m * a ≤ n := by
    have hna : n * a ≤ n ^ 2 := by nlinarith
    calc m * a ≤ Real.sqrt (n * a) := hma_le
      _ ≤ Real.sqrt (n ^ 2) := Real.sqrt_le_sqrt hna
      _ = n := Real.sqrt_sq (le_of_lt hn_pos)
  have hma_C' : m * a ≤ Real.sqrt C' * Real.sqrt (n * L * logn) := by
    have hprod : n * a ≤ C' * (n * L * logn) := by
      calc n * a ≤ n * (C' * (L * logn)) := mul_le_mul_of_nonneg_left ha_le_C' (le_of_lt hn_pos)
        _ = C' * (n * L * logn) := by ring
    calc m * a ≤ Real.sqrt (n * a) := hma_le
      _ ≤ Real.sqrt (C' * (n * L * logn)) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt C' * Real.sqrt (n * L * logn) := Real.sqrt_mul (le_of_lt hC') _
  have hterm1 : 3 * (n * m * a) ≤ 3 * n ^ (3 / 2 : ℝ) * Real.sqrt a := by
    have h1 : n * (m * a) ≤ n * Real.sqrt (n * a) :=
      mul_le_mul_of_nonneg_left hma_le (le_of_lt hn_pos)
    have h2 : n * Real.sqrt (n * a) = n ^ (3 / 2 : ℝ) * Real.sqrt a := by
      calc n * Real.sqrt (n * a)
          = (n ^ (1 : ℝ) * Real.sqrt n) * Real.sqrt a := by
            rw [Real.rpow_one, Real.sqrt_mul (le_of_lt hn_pos), mul_assoc]
        _ = n ^ (3 / 2 : ℝ) * Real.sqrt a := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
            norm_num
    linarith
  have hterm2 : 4 * n ^ 2 / m ≤ 8 * n ^ (3 / 2 : ℝ) * Real.sqrt a := by
    have hhalf_pos : 0 < (1 / 2 : ℝ) * Real.sqrt (n / a) := by positivity
    have hdiv_le : 4 * n ^ 2 / m ≤ 4 * n ^ 2 / ((1 / 2 : ℝ) * Real.sqrt (n / a)) :=
      div_le_div_of_nonneg_left (by positivity) hhalf_pos hm_lower
    have hn2 : n ^ 2 = n ^ (3 / 2 : ℝ) * Real.sqrt n := (rpow_three_halves_mul_sqrt hn_pos).symm
    have hsimp : 4 * n ^ 2 / ((1 / 2 : ℝ) * Real.sqrt (n / a)) =
        8 * n ^ (3 / 2 : ℝ) * Real.sqrt a := by
      rw [Real.sqrt_div (le_of_lt hn_pos), hn2]
      field_simp
      ring
    linarith
  have hsum11 : 3 * (n * m * a) + 4 * n ^ 2 / m ≤ 11 * n ^ (3 / 2 : ℝ) * Real.sqrt a := by linarith
  have hC2_pos : 0 < max (11 : ℝ) (11 * Real.sqrt C') :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb1 : 3 * (n * m * a) + 4 * n ^ 2 / m ≤ max 11 (11 * Real.sqrt C') * n ^ 2 := by
    have hsqa_le : Real.sqrt a ≤ Real.sqrt n := Real.sqrt_le_sqrt (le_of_lt ha_lt)
    have hC2_11 : (11 : ℝ) ≤ max 11 (11 * Real.sqrt C') := le_max_left _ _
    calc 3 * (n * m * a) + 4 * n ^ 2 / m
        ≤ 11 * n ^ (3 / 2 : ℝ) * Real.sqrt a := hsum11
      _ ≤ 11 * n ^ (3 / 2 : ℝ) * Real.sqrt n := by gcongr
      _ = 11 * (n ^ (3 / 2 : ℝ) * Real.sqrt n) := by ring
      _ = 11 * n ^ 2 := by rw [rpow_three_halves_mul_sqrt hn_pos]
      _ ≤ max 11 (11 * Real.sqrt C') * n ^ 2 := by gcongr
  have hb2 : 3 * (n * m * a) + 4 * n ^ 2 / m ≤
      max 11 (11 * Real.sqrt C') * (n ^ (3 / 2 : ℝ) * Real.sqrt (L * logn)) := by
    have hsqa_le : Real.sqrt a ≤ Real.sqrt C' * Real.sqrt (L * logn) := by
      calc Real.sqrt a ≤ Real.sqrt (C' * (L * logn)) := Real.sqrt_le_sqrt ha_le_C'
        _ = Real.sqrt C' * Real.sqrt (L * logn) := Real.sqrt_mul (le_of_lt hC') _
    have hC2_11s : 11 * Real.sqrt C' ≤ max 11 (11 * Real.sqrt C') := le_max_right _ _
    calc 3 * (n * m * a) + 4 * n ^ 2 / m
        ≤ 11 * n ^ (3 / 2 : ℝ) * Real.sqrt a := hsum11
      _ ≤ 11 * n ^ (3 / 2 : ℝ) * (Real.sqrt C' * Real.sqrt (L * logn)) := by gcongr
      _ = (11 * Real.sqrt C') * (n ^ (3 / 2 : ℝ) * Real.sqrt (L * logn)) := by ring
      _ ≤ max 11 (11 * Real.sqrt C') * (n ^ (3 / 2 : ℝ) * Real.sqrt (L * logn)) := by gcongr
  refine ⟨hma_le, hma_n, hma_C', ?_⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt hC2_pos)]
  exact le_min hb1 hb2

end AuxThm3

open scoped Classical in
theorem solution : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (d : ℕ), 1 ≤ d →
    ∀ P : Finset (Pt d), 2 ≤ P.card →
      let n : ℝ := (P.card : ℝ)
      let L : ℝ := (annulusCount P : ℝ)
      ∃ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
        IsSteinerNavigable (1 + 1 / (d : ℝ)) P R E ∧
        NoSteinerToSteiner R P E ∧
        (∀ x, (x, x) ∉ E) ∧
        R.card ≤ P.card ∧
        (R.card : ℝ) ≤ C₁ * Real.sqrt (n * L * Real.log n) ∧
        (E.card : ℝ) ≤ C₂ * min (n ^ 2) (n ^ (3 / 2 : ℝ) * Real.sqrt (L * Real.log n)) := by
  obtain ⟨C, C', hC, hC', hcor⟩ := SteinerNav.corollary_4_2 1 zero_lt_one
  refine ⟨Real.sqrt C', max 11 (11 * Real.sqrt C'), Real.sqrt_pos.mpr hC',
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11) (le_max_left _ _), ?_⟩
  intro d hd P hn
  have hn_ge2 : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (P.card : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (P.card : ℝ) := Real.log_pos (by linarith)
  have hK_pos : 1 ≤ ⌈C * Real.log (P.card : ℝ)⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hL_pos : 1 ≤ annulusCount P := by
    unfold annulusCount
    omega
  have ha_pos : 1 ≤ ⌈C * Real.log (P.card : ℝ)⌉₊ * annulusCount P := Nat.mul_pos hK_pos hL_pos
  obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
  have ha_le_C' : ((⌈C * Real.log (P.card : ℝ)⌉₊ * annulusCount P : ℕ) : ℝ) ≤
      C' * ((annulusCount P : ℝ) * Real.log (P.card : ℝ)) := by
    have hc1 := (hcor d hd P hn s₀ hs₀).1
    simpa [Nat.cast_mul] using hc1
  by_cases ha_ge : P.card ≤ ⌈C * Real.log (P.card : ℝ)⌉₊ * annulusCount P
  · exact AuxThm3.dense_case hC' hd P hn _ ha_ge ha_le_C'
  · dsimp only
    set K : ℕ := ⌈C * Real.log (P.card : ℝ)⌉₊
    set L_nat : ℕ := annulusCount P
    set a : ℕ := K * L_nat
    have ha_lt : a < P.card := Nat.lt_of_not_ge ha_ge
    have ha_lt_real : (a : ℝ) < (P.card : ℝ) := by exact_mod_cast ha_lt
    have ha_real_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
    have hna_ge1 : 1 ≤ (P.card : ℝ) / (a : ℝ) :=
      (one_le_div ha_real_pos).mpr (le_of_lt ha_lt_real)
    have hsqrt_ge1 : 1 ≤ Real.sqrt ((P.card : ℝ) / (a : ℝ)) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hna_ge1
    have hsqrt_le_n : Real.sqrt ((P.card : ℝ) / (a : ℝ)) ≤ (P.card : ℝ) := by
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
      have hdiv_le : (P.card : ℝ) / (a : ℝ) ≤ (P.card : ℝ) ^ 2 := by
        calc (P.card : ℝ) / (a : ℝ)
            ≤ (P.card : ℝ) / 1 := div_le_div_of_nonneg_left (le_of_lt hn_pos) zero_lt_one ha1
          _ = (P.card : ℝ) := div_one _
          _ ≤ (P.card : ℝ) ^ 2 := by nlinarith
      calc Real.sqrt ((P.card : ℝ) / (a : ℝ))
          ≤ Real.sqrt ((P.card : ℝ) ^ 2) := Real.sqrt_le_sqrt hdiv_le
        _ = (P.card : ℝ) := Real.sqrt_sq (le_of_lt hn_pos)
    set m : ℕ := ⌊Real.sqrt ((P.card : ℝ) / (a : ℝ))⌋₊
    have hm_ge1 : 1 ≤ m := (Nat.one_le_floor_iff _).mpr hsqrt_ge1
    have hm_le_n : m ≤ P.card := Nat.floor_le_of_le hsqrt_le_n
    have hm_upper : (m : ℝ) ≤ Real.sqrt ((P.card : ℝ) / (a : ℝ)) := Nat.floor_le (by positivity)
    have hm_lower : (1 / 2 : ℝ) * Real.sqrt ((P.card : ℝ) / (a : ℝ)) ≤ (m : ℝ) :=
      AuxThm3.half_le_floor hsqrt_ge1
    have htype3 := (SteinerNav.expected_type3_edges P hn m hm_ge1 hm_le_n).2.2
    have hpcard_pos : (0 : ℝ) < ((P.powersetCard m).card : ℝ) := by
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_pos hm_le_n
    have hfilt_pos : 0 < ((P.powersetCard m).filter fun Q =>
        ((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)).card := by
      have hpos_real : (0 : ℝ) < (((P.powersetCard m).filter fun Q =>
          ((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)).card : ℝ) := by linarith
      exact_mod_cast hpos_real
    obtain ⟨Q, hQ_filt⟩ := Finset.card_pos.mp hfilt_pos
    obtain ⟨hQ_mem, hQ_type3⟩ := Finset.mem_filter.mp hQ_filt
    obtain ⟨hQP, hQcard⟩ := Finset.mem_powersetCard.mp hQ_mem
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    have hexists_u : ∀ q ∈ Q, ∃ u : Fin L_nat × Fin K → Pt d,
        CoversSet (1 + 1 / (d : ℝ)) q (annularCandidates (1 + 1 / (d : ℝ)) P q K L_nat u) P := by
      intro q hq
      have hprob := (hcor d hd P hn q (hQP hq)).2.2
      have hn_inv : (P.card : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, inv_le_comm₀ hn_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      have hpos_ofReal : (0 : ENNReal) < ENNReal.ofReal (1 - (P.card : ℝ) ^ (-1 : ℝ)) :=
        ENNReal.ofReal_pos.mpr (by linarith)
      have hmeas_pos := lt_of_lt_of_le hpos_ofReal hprob
      by_contra hnone
      have hempty : {u : Fin L_nat × Fin K → Pt d |
          CoversSet (1 + 1 / (d : ℝ)) q (annularCandidates (1 + 1 / (d : ℝ)) P q K L_nat u) P} = ∅ := by
        ext u
        simp only [Set.mem_setOf, Set.mem_empty_iff_false, iff_false]
        exact fun hu => hnone ⟨u, hu⟩
      rw [hempty, MeasureTheory.measure_empty] at hmeas_pos
      exact lt_irrefl _ hmeas_pos
    let candOf : Pt d → Finset (Pt d) := fun q =>
      if hq : q ∈ Q then
        annularCandidates (1 + 1 / (d : ℝ)) P q K L_nat (Classical.choose (hexists_u q hq))
      else ∅
    let S : Finset (Pt d) := Q.biUnion candOf
    have hS_cov : ∀ q ∈ Q, CoversSet (1 + 1 / (d : ℝ)) q S P := by
      intro q hq
      have hcov_q : CoversSet (1 + 1 / (d : ℝ)) q (candOf q) P := by
        dsimp [candOf]
        rw [dif_pos hq]
        exact Classical.choose_spec (hexists_u q hq)
      exact AuxThm3.coversSet_mono (Finset.subset_biUnion_of_mem candOf hq) hcov_q
    have hS_card : S.card ≤ m * a := by
      calc S.card ≤ ∑ q ∈ Q, (candOf q).card := Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ Q, a := by
            refine Finset.sum_le_sum fun q hq => ?_
            dsimp [candOf]
            rw [dif_pos hq]
            exact (hcor d hd P hn q (hQP hq)).2.1 _
        _ = Q.card * a := by rw [Finset.sum_const, smul_eq_mul]
        _ = m * a := by rw [hQcard]
    have hα : 1 < 1 + 1 / (d : ℝ) := by
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      linarith [one_div_pos.mpr hd_pos]
    obtain ⟨hG, hnoloop, hN⟩ :=
      SteinerNav.construction_navigable (1 + 1 / (d : ℝ)) hα P Q S hQne hQP hS_cov
    obtain ⟨_, hma_n, hma_C', hE_alg⟩ :=
      AuxThm3.card_Algebra_bounds hn_pos ha_real_pos hC' ha_lt_real ha_le_C' hm_upper hm_lower
    have hR_le_S : (S \ P).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
    have hR_le_ma_real : ((S \ P).card : ℝ) ≤ (m : ℝ) * (a : ℝ) := by
      exact_mod_cast le_trans hR_le_S hS_card
    have hR_le_P : (S \ P).card ≤ P.card := by
      exact_mod_cast le_trans hR_le_ma_real hma_n
    have hR_bound : ((S \ P).card : ℝ) ≤
        Real.sqrt C' * Real.sqrt ((P.card : ℝ) * (L_nat : ℝ) * Real.log (P.card : ℝ)) :=
      le_trans hR_le_ma_real hma_C'
    have hedge_cnt := SteinerNav.construction_edge_count P Q S
    have h12_nat : P.card * (S \ P).card + P.card * (Q.card + S.card) ≤ 3 * (P.card * m * a) := by
      obtain ⟨hc2_1, hc2_2⟩ := hedge_cnt.2 m a hQcard hS_card
      rw [hQcard]
      exact le_trans hc2_1 (hc2_2 ha_pos)
    have hE_nat : (constructionEdges P Q S).card ≤ 3 * (P.card * m * a) + (type3Edges P Q).card :=
      le_trans hedge_cnt.1 (Nat.add_le_add_right h12_nat _)
    have hE_cast : ((constructionEdges P Q S).card : ℝ) ≤
        3 * ((P.card : ℝ) * (m : ℝ) * (a : ℝ)) + ((type3Edges P Q).card : ℝ) := by
      exact_mod_cast hE_nat
    have hE_final : ((constructionEdges P Q S).card : ℝ) ≤
        max 11 (11 * Real.sqrt C') *
          min ((P.card : ℝ) ^ 2)
            ((P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((L_nat : ℝ) * Real.log (P.card : ℝ))) :=
      le_trans (by linarith) hE_alg
    exact ⟨S \ P, constructionEdges P Q S, hG, hN, hnoloop, hR_le_P, hR_bound, hE_final⟩
