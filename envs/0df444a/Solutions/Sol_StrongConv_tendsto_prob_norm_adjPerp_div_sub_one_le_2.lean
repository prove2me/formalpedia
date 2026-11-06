-- Prove2me | solution 2 for StrongConv.tendsto_prob_norm_adjPerp_div_sub_one_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:38:31.660189+00:00
-- url     : https://prove2.me/submissions/bdd9e37a-83c3-4128-9b3e-453f9e261d70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_le
import Theorems.Thm_StrongConv_norm_adjPerp_ge_alonBoppana
import Theorems.Thm_StrongConv_tendsto_prob_norm_adjPerp_ge_highDegree
import Theorems.Thm_StrongConv_prob_norm_adjPerp_le_highDegree_ge

open Filter Topology

namespace StrongConv

section prob

variable {X : Type*} [Fintype X]

lemma cor35_card_pos [Nonempty X] : (0 : ℝ) < Fintype.card X := by
  exact_mod_cast Fintype.card_pos

lemma cor35_prob_le_one (E : X → Prop) : uniformProb E ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_univ _

lemma cor35_prob_mono (E F : X → Prop) (h : ∀ x, E x → F x) : uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

lemma cor35_prob_of_forall (E : X → Prop) [Nonempty X] (h : ∀ x, E x) : uniformProb E = 1 := by
  classical
  unfold uniformProb
  have : Finset.univ.filter E = Finset.univ := by
    ext x; simp [h x]
  rw [this, Finset.card_univ]
  exact div_self cor35_card_pos.ne'

lemma cor35_prob_cover (E F : X → Prop) [Nonempty X] (h : ∀ x, E x ∨ F x) :
    1 ≤ uniformProb E + uniformProb F := by
  classical
  unfold uniformProb
  rw [← add_div, le_div_iff₀ cor35_card_pos, one_mul]
  have : Finset.univ ⊆ Finset.univ.filter E ∪ Finset.univ.filter F := by
    intro x _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x
  have h2 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ] at h2
  exact_mod_cast h2

lemma cor35_prob_and (E F : X → Prop) [Nonempty X] :
    uniformProb E + uniformProb F - 1 ≤ uniformProb (fun x => E x ∧ F x) := by
  classical
  unfold uniformProb
  have hpos := cor35_card_pos (X := X)
  have h1 := Finset.card_union_add_card_inter (Finset.univ.filter E) (Finset.univ.filter F)
  have h2 : (Finset.univ.filter E ∪ Finset.univ.filter F).card ≤ Fintype.card X :=
    (Finset.card_le_univ _).trans (by simp)
  have h3 : Finset.univ.filter E ∩ Finset.univ.filter F = Finset.univ.filter (fun x => E x ∧ F x) := by
    ext x; simp
  rw [h3] at h1
  have : ((Finset.univ.filter E).card : ℝ) + (Finset.univ.filter F).card
      ≤ Fintype.card X + (Finset.univ.filter (fun x => E x ∧ F x)).card := by
    exact_mod_cast (by omega : (Finset.univ.filter E).card + (Finset.univ.filter F).card
      ≤ Fintype.card X + (Finset.univ.filter (fun x => E x ∧ F x)).card)
  rw [← add_div, div_sub_one hpos.ne']
  exact div_le_div_of_nonneg_right (by convert sub_le_iff_le_add'.2 this; rfl) hpos.le

end prob

lemma cor35_norm_permOpPerp_le {N : ℕ} (σ : Equiv.Perm (Fin N)) : ‖permOpPerp σ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul]
  apply le_of_eq
  show ‖(permOp σ) (x : EuclideanSpace ℂ (Fin N))‖ = ‖(x : EuclideanSpace ℂ (Fin N))‖
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).norm_map _

lemma cor35_norm_star {N : ℕ} (T : OnesPerp N →L[ℂ] OnesPerp N) : ‖star T‖ = ‖T‖ := norm_star T

lemma cor35_norm_adjPerp_le {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖adjPerp σ‖ ≤ 2 * d := by
  unfold adjPerp
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i : Fin d, ‖sModel σ i + star (sModel σ i)‖ ≤ 2 := fun i => by
    refine (norm_add_le _ _).trans ?_
    have hs : ‖star (sModel σ i)‖ = ‖sModel σ i‖ := by
      exact cor35_norm_star _
    rw [hs]
    have := cor35_norm_permOpPerp_le (σ i)
    change ‖permOpPerp (σ i)‖ + ‖permOpPerp (σ i)‖ ≤ 2
    linarith
  calc _ ≤ ∑ _i : Fin d, (2 : ℝ) := Finset.sum_le_sum (fun i _ => this i)
    _ = 2 * d := by simp [mul_comm]

/-- Lower-tail event probability. -/
noncomputable def cor35_pL (δ : ℝ) (m N : ℕ) : ℝ :=
  uniformProb (fun σ : Fin m → Equiv.Perm (Fin N) =>
    (1 - δ) * (2 * Real.sqrt (2 * m - 1)) ≤ ‖adjPerp σ‖)

/-- Upper-tail event probability. -/
noncomputable def cor35_pU (δ : ℝ) (m N : ℕ) : ℝ :=
  uniformProb (fun σ : Fin m → Equiv.Perm (Fin N) =>
    ‖adjPerp σ‖ ≤ (1 + δ) * (2 * Real.sqrt (2 * m - 1)))

lemma cor35_tendsto_log : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma cor35_logN_pos : ∀ᶠ N : ℕ in atTop, 0 < Real.log N :=
  cor35_tendsto_log.eventually_gt_atTop 0

lemma cor35_tendsto_loglog : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.comp_tendsto cor35_tendsto_log).tendsto_div_nhds_zero

lemma cor35_tendsto_const_div_log (c : ℝ) : Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop cor35_tendsto_log

lemma cor35_lower (d : ℕ → ℕ) (hd : ∀ N, 1 ≤ d N) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => cor35_pL δ (d N) N) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := norm_adjPerp_ge_alonBoppana
  set d' : ℕ → ℕ := fun N => max (d N) ⌈Real.log N ^ 5⌉₊ with hd'
  have hd'1 : Tendsto (fun N : ℕ => (d' N : ℝ) / Real.log N ^ 4) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ cor35_tendsto_log
    filter_upwards [cor35_logN_pos] with N hN
    rw [le_div_iff₀ (by positivity)]
    have : Real.log N ^ 5 ≤ (d' N : ℝ) := by
      calc Real.log N ^ 5 ≤ (⌈Real.log N ^ 5⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d' N : ℝ) := by exact_mod_cast le_max_right _ _
    nlinarith [this]
  have hsib := tendsto_prob_norm_adjPerp_ge_highDegree d' hd'1 δ hδ
  have hL : Tendsto (fun N : ℕ => |C| * (Real.log 2 + 5 * Real.log (Real.log N)) / Real.log N)
      atTop (𝓝 0) := by
    have := ((cor35_tendsto_const_div_log (|C| * Real.log 2)).add
      (cor35_tendsto_loglog.const_mul (5 * |C|)))
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [cor35_logN_pos] with N hN
    field_simp
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h1 := (tendsto_order.1 hsib).1 a ha
    have h2 := (tendsto_order.1 hL).2 δ hδ
    filter_upwards [h1, h2, cor35_logN_pos, eventually_ge_atTop 2] with N h1 h2 hN hN2
    by_cases hcase : (d N : ℝ) ≤ Real.log N ^ 5
    · have : cor35_pL δ (d N) N = 1 := by
        apply cor35_prob_of_forall
        intro σ
        have hab := hC (d N) N (hd N) hN2 σ
        have hdpos : (1 : ℝ) ≤ d N := by exact_mod_cast hd N
        have hlog : Real.log (2 * d N) ≤ Real.log 2 + 5 * Real.log (Real.log N) := by
          calc Real.log (2 * d N) ≤ Real.log (2 * Real.log N ^ 5) :=
                Real.log_le_log (by positivity) (by linarith)
            _ = Real.log 2 + 5 * Real.log (Real.log N) := by
                rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
        have hx : C * Real.log (2 * d N) / Real.log N ≤ δ := by
          refine le_trans ?_ h2.le
          rw [div_le_div_iff_of_pos_right hN]
          calc C * Real.log (2 * d N) ≤ |C| * Real.log (2 * d N) :=
                mul_le_mul_of_nonneg_right (le_abs_self C)
                  (Real.log_nonneg (by linarith))
            _ ≤ _ := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
        have hs : 0 ≤ 2 * Real.sqrt (2 * (d N : ℝ) - 1) := by positivity
        refine le_trans ?_ hab
        exact mul_le_mul_of_nonneg_right (by linarith) hs
      rw [this]; exact ha
    · rw [not_le] at hcase
      have hdd : d' N = d N := by
        apply max_eq_left
        exact Nat.ceil_le.2 hcase.le
      have : cor35_pL δ (d' N) N = cor35_pL δ (d N) N := by rw [hdd]
      rw [← this]
      exact h1
  · exact Eventually.of_forall fun N => lt_of_le_of_lt (cor35_prob_le_one _) ha

/-- Mid-degree case: `2 ≤ d ≤ (log N)^5`, pointwise bound from Theorem 3.4. -/
lemma cor35_mid_bound (C : ℝ)
    (hC : ∀ d N : ℕ, 2 ≤ d → 1 ≤ N → ∀ ε : ℝ, 0 < ε →
      ε < 2 * d - 2 * Real.sqrt (2 * d - 1) →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖) ≤
        C * (1 / N) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε))
    (δ : ℝ) (hδ : 0 < δ) (N d : ℕ) (hN : 2 ≤ N) (hd2 : 2 ≤ d)
    (hdl : (d : ℝ) ≤ Real.log N ^ 5) :
    1 - |C| * (2 * Real.exp 1) / (min (3 * δ) (1 / 5)) ^ 9 * Real.log N ^ 85 / N
      ≤ cor35_pU δ d N := by
  set c := min (3 * δ) (1 / 5) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by norm_num)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set l := Real.log N with hl
  set r := Real.sqrt (2 * (d : ℝ) - 1) with hr
  have hr2 : r ^ 2 = 2 * d - 1 := Real.sq_sqrt (by linarith)
  have hr17 : (17 / 10 : ℝ) ≤ r := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hs : 2 * d - 2 * r = (r - 1) ^ 2 := by nlinarith
  set ε := min (δ * (2 * r)) ((2 * d - 2 * r) / 2) with hε
  have hpos2 : 0 < 2 * (d : ℝ) - 2 * r := by rw [hs]; nlinarith
  have hεc : c ≤ ε := by
    refine le_min ?_ ?_
    · calc c ≤ 3 * δ := min_le_left _ _
        _ ≤ δ * (2 * r) := by nlinarith
    · calc c ≤ 1 / 5 := min_le_right _ _
        _ ≤ (2 * d - 2 * r) / 2 := by rw [hs]; nlinarith
  have hεpos : 0 < ε := lt_of_lt_of_le hcpos hεc
  have hε1 : ε ≤ δ * (2 * r) := min_le_left _ _
  have hε2 : ε ≤ (2 * d - 2 * r) / 2 := min_le_right _ _
  have hb := hC d N hd2 (by omega) ε hεpos (by linarith)
  have hcov := cor35_prob_cover
    (fun σ : Fin d → Equiv.Perm (Fin N) => ‖adjPerp σ‖ ≤ (1 + δ) * (2 * r))
    (fun σ : Fin d → Equiv.Perm (Fin N) => 2 * r + ε ≤ ‖adjPerp σ‖) (by
      intro σ
      by_cases h : 2 * r + ε ≤ ‖adjPerp σ‖
      · exact Or.inr h
      · left; push Not at h; nlinarith)
  have hl2 : 0 ≤ l := by rw [hl]; exact Real.log_nonneg (by linarith)
  have hdl1 : (1 : ℝ) ≤ d := by linarith
  -- bound the RHS
  have hT1 : 0 ≤ d * Real.log d / ε := by
    have := Real.log_nonneg hdl1
    positivity
  have hT1' : (d : ℝ) * Real.log d / ε ≤ l ^ 10 / c := by
    have hlogd : Real.log d ≤ d := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < d); linarith
    have h1 : (d : ℝ) * Real.log d ≤ l ^ 10 := by
      calc (d : ℝ) * Real.log d ≤ d * d :=
            mul_le_mul_of_nonneg_left hlogd (by linarith)
        _ ≤ l ^ 5 * l ^ 5 := mul_le_mul hdl hdl (by linarith) (by positivity)
        _ = l ^ 10 := by ring
    calc (d : ℝ) * Real.log d / ε ≤ (d * Real.log d) / c :=
          div_le_div_of_nonneg_left (by have := Real.log_nonneg hdl1; positivity) hcpos hεc
      _ ≤ l ^ 10 / c := div_le_div_of_nonneg_right h1 hcpos.le
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hT2arg : 1 ≤ 2 * Real.exp 1 * d / ε := by
    rw [le_div_iff₀ hεpos]; nlinarith
  have hT2 : 0 ≤ Real.log (2 * Real.exp 1 * d / ε) := Real.log_nonneg hT2arg
  have hT2' : Real.log (2 * Real.exp 1 * d / ε) ≤ 2 * Real.exp 1 * l ^ 5 / c := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 * Real.exp 1 * d / ε)
    have h2 : 2 * Real.exp 1 * (d : ℝ) / ε ≤ 2 * Real.exp 1 * l ^ 5 / c := by
      calc 2 * Real.exp 1 * (d : ℝ) / ε ≤ 2 * Real.exp 1 * d / c :=
            div_le_div_of_nonneg_left (by positivity) hcpos hεc
        _ ≤ _ := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdl (by positivity)) hcpos.le
    linarith
  have hfin : C * (1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)
      ≤ |C| * (2 * Real.exp 1) / c ^ 9 * l ^ 85 / N := by
    have hNpos : (0 : ℝ) < N := by linarith
    have hX : 0 ≤ (1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε) := by
      positivity
    calc C * (1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)
        = C * ((1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) := by
          ring
      _ ≤ |C| * ((1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hX
      _ ≤ |C| * ((1 / (N : ℝ)) * (l ^ 10 / c) ^ 8 * (2 * Real.exp 1 * l ^ 5 / c)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          have h8 : (d * Real.log d / ε) ^ 8 ≤ (l ^ 10 / c) ^ 8 := pow_le_pow_left₀ hT1 hT1' 8
          have h8' : 0 ≤ (d * Real.log d / ε) ^ 8 := by positivity
          have hq : 0 ≤ 2 * Real.exp 1 * l ^ 5 / c := by positivity
          calc (1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)
              ≤ (1 / (N : ℝ)) * (d * Real.log d / ε) ^ 8 * (2 * Real.exp 1 * l ^ 5 / c) :=
                mul_le_mul_of_nonneg_left hT2' (by positivity)
            _ ≤ (1 / (N : ℝ)) * (l ^ 10 / c) ^ 8 * (2 * Real.exp 1 * l ^ 5 / c) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h8 (by positivity)) hq
      _ = |C| * (2 * Real.exp 1) / c ^ 9 * l ^ 85 / N := by
          field_simp
  have : cor35_pU δ d N = uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ‖adjPerp σ‖ ≤ (1 + δ) * (2 * r)) := rfl
  rw [this]
  linarith

/-- High-degree case, pointwise inequality of the thresholds. -/
lemma cor35_high_pt (C : ℝ) (hCpos : 0 < C) (δ : ℝ) (N d : ℕ) (hN : 2 ≤ N)
    (hl1 : 1 ≤ Real.log N) (hd : Real.log N ^ 5 < d)
    (hψ : (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4)
        + 2 * C * Real.log N ^ (-(1 : ℝ) / 6)) * (1 + Real.log N ^ (-(1 : ℝ) / 6)) ≤ 1 + δ) :
    (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))
      ≤ (1 + δ) * (2 * Real.sqrt (2 * d - 1)) := by
  set l := Real.log N with hl
  have hl0 : 0 < l := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set η := l ^ (-(1 : ℝ) / 6) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hl0 _
  have hd0 : (0 : ℝ) < d := lt_of_le_of_lt (by positivity) hd
  have hd1 : (1 : ℝ) ≤ d := by
    have : 1 ≤ l ^ 5 := one_le_pow₀ hl1
    linarith
  -- d^(1/6) ≥ l^(5/6)
  have h6 : l ^ ((5 : ℝ) / 6) ≤ (d : ℝ) ^ ((1 : ℝ) / 6) := by
    have : (l ^ 5) ^ ((1 : ℝ) / 6) ≤ (d : ℝ) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (by positivity) hd.le (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, Nat.cast_ofNat, show (5 : ℝ) * (1 / 6) = 5 / 6 by norm_num] at this
  have h2 : (d : ℝ) ^ ((1 : ℝ) / 2) ≥ l ^ ((5 : ℝ) / 2) := by
    have : (l ^ 5) ^ ((1 : ℝ) / 2) ≤ (d : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hd.le (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, Nat.cast_ofNat, show (5 : ℝ) * (1 / 2) = 5 / 2 by norm_num] at this
  have e2 : C * l ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) ≤ C * η := by
    have : l ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) ≤ η := by
      calc l ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6)
          ≤ l ^ ((2 : ℝ) / 3) / l ^ ((5 : ℝ) / 6) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h6
        _ = η := by
            rw [← Real.rpow_sub hl0, hη]; norm_num
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hCpos.le
  have e3 : C * l / (d : ℝ) ^ ((1 : ℝ) / 2) ≤ C * η := by
    have : l / (d : ℝ) ^ ((1 : ℝ) / 2) ≤ η := by
      calc l / (d : ℝ) ^ ((1 : ℝ) / 2) ≤ l / l ^ ((5 : ℝ) / 2) :=
            div_le_div_of_nonneg_left hl0.le (by positivity) h2
        _ = l ^ (-(3 : ℝ) / 2) := by
            calc l / l ^ ((5 : ℝ) / 2) = l ^ (1 : ℝ) / l ^ ((5 : ℝ) / 2) := by rw [Real.rpow_one]
              _ = _ := by rw [← Real.rpow_sub hl0]; norm_num
        _ ≤ η := Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hCpos.le
  have hsq : Real.sqrt (2 * d) ≤ (1 + η) * Real.sqrt (2 * d - 1) := by
    have hηl : 1 ≤ η * l ^ 5 := by
      have : η * l ^ 5 = l ^ (-(1 : ℝ) / 6 + 5) := by
        rw [hη, Real.rpow_add hl0]; norm_num
      rw [this]
      exact Real.one_le_rpow hl1 (by norm_num)
    have hηd : 1 ≤ η * d := by nlinarith
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + η), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith
  set e1 := C * l ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) with he1
  have he10 : 0 ≤ e1 := by positivity
  have hsq0 : 0 ≤ Real.sqrt (2 * (d : ℝ) - 1) := Real.sqrt_nonneg _
  calc (1 + e1 + C * l ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) + C * l / (d : ℝ) ^ ((1 : ℝ) / 2))
        * (2 * Real.sqrt (2 * d))
      ≤ (1 + e1 + 2 * C * η) * (2 * ((1 + η) * Real.sqrt (2 * d - 1))) := by
        apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = (1 + e1 + 2 * C * η) * (1 + η) * (2 * Real.sqrt (2 * d - 1)) := by ring
    _ ≤ (1 + δ) * (2 * Real.sqrt (2 * d - 1)) :=
        mul_le_mul_of_nonneg_right hψ (by positivity)

lemma cor35_tendsto_mid (K : ℝ) :
    Tendsto (fun N : ℕ => K * Real.log N ^ 85 / N) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 85 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.const_mul K
  simp only [mul_zero] at h2
  refine h2.congr (fun N => ?_)
  simp [Function.comp, mul_div_assoc]

lemma cor35_tendsto_e1 (C : ℝ) :
    Tendsto (fun N : ℕ => C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4))
      atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (3 / 4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.const_mul C
  simp only [mul_zero] at h2
  refine h2.congr (fun N => ?_)
  simp [Function.comp, mul_div_assoc]

lemma cor35_tendsto_eta :
    Tendsto (fun N : ℕ => Real.log N ^ (-(1 : ℝ) / 6)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp cor35_tendsto_log
  refine h.congr (fun N => ?_)
  simp only [Function.comp]
  congr 1; ring

lemma cor35_upper (d : ℕ → ℕ) (hd : ∀ N, 1 ≤ d N) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => cor35_pU δ (d N) N) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := prob_norm_adjPerp_ge_le
  obtain ⟨C2, hC2pos, hC2⟩ := prob_norm_adjPerp_le_highDegree_ge 1 one_pos
  set K := |C| * (2 * Real.exp 1) / (min (3 * δ) (1 / 5)) ^ 9 with hK
  have hψ : Tendsto (fun N : ℕ => (1 + C2 * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4)
        + 2 * C2 * Real.log N ^ (-(1 : ℝ) / 6)) * (1 + Real.log N ^ (-(1 : ℝ) / 6))) atTop (𝓝 1) := by
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add (cor35_tendsto_e1 C2)
    have h2 := h1.add (cor35_tendsto_eta.const_mul (2 * C2))
    have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add cor35_tendsto_eta
    have := h2.mul h3
    simpa using this
  have hinv : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hA := (tendsto_order.1 (cor35_tendsto_mid K)).2 (1 - a) (by linarith)
    have hB := (tendsto_order.1 hψ).2 (1 + δ) (by linarith)
    have hD := (tendsto_order.1 hinv).2 (1 - a) (by linarith)
    filter_upwards [hA, hB, hD, cor35_tendsto_log.eventually_ge_atTop 1, eventually_ge_atTop 2]
      with N hA hB hD hl1 hN2
    by_cases h1 : d N = 1
    · have : cor35_pU δ (d N) N = 1 := by
        apply cor35_prob_of_forall
        intro σ
        have := cor35_norm_adjPerp_le σ
        have hc : (d N : ℝ) = 1 := by exact_mod_cast h1
        rw [hc] at this ⊢
        norm_num at this ⊢
        nlinarith
      rw [this]; exact ha
    · have hd2 : 2 ≤ d N := by have := hd N; omega
      by_cases hcase : (d N : ℝ) ≤ Real.log N ^ 5
      · have := cor35_mid_bound C hC δ hδ N (d N) hN2 hd2 hcase
        linarith
      · rw [not_le] at hcase
        have hpt : ∀ σ : Fin (d N) → Equiv.Perm (Fin N),
            ‖adjPerp σ‖ ≤ (1 + C2 * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
              C2 * Real.log N ^ ((2 : ℝ) / 3) / (d N : ℝ) ^ ((1 : ℝ) / 6) +
              C2 * Real.log N / (d N : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * (d N : ℝ))) →
            ‖adjPerp σ‖ ≤ (1 + δ) * (2 * Real.sqrt (2 * (d N : ℝ) - 1)) := fun σ h =>
          h.trans (cor35_high_pt C2 hC2pos δ N (d N) hN2 hl1 hcase hB.le)
        have hm := cor35_prob_mono _ _ hpt
        have hs := hC2 N (d N) (by omega) (hd N)
        have : cor35_pU δ (d N) N = uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
            ‖adjPerp σ‖ ≤ (1 + δ) * (2 * Real.sqrt (2 * (d N : ℝ) - 1))) := rfl
        rw [this]
        linarith
  · exact Eventually.of_forall fun N => lt_of_le_of_lt (cor35_prob_le_one _) ha

theorem tendsto_prob_norm_adjPerp_div_sub_one_le_dev (d : ℕ → ℕ) (hd : ∀ N, 1 ≤ d N) (δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      |‖adjPerp σ‖ / (2 * Real.sqrt (2 * d N - 1)) - 1| ≤ δ)) atTop (𝓝 1) := by
  have hlow := cor35_lower d hd δ hδ
  have hup := cor35_upper d hd δ hδ
  have hsum : Tendsto (fun N : ℕ => cor35_pL δ (d N) N + cor35_pU δ (d N) N - 1) atTop (𝓝 1) := by
    simpa using hlow.add hup |>.sub_const 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hsum tendsto_const_nhds (fun N => ?_)
    (fun N => cor35_prob_le_one _)
  have hs : 0 < 2 * Real.sqrt (2 * (d N : ℝ) - 1) := by
    have : (1 : ℝ) ≤ d N := by exact_mod_cast hd N
    have : 0 < Real.sqrt (2 * (d N : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
    positivity
  have h := cor35_prob_and (X := Fin (d N) → Equiv.Perm (Fin N))
    (fun σ => (1 - δ) * (2 * Real.sqrt (2 * (d N : ℝ) - 1)) ≤ ‖adjPerp σ‖)
    (fun σ => ‖adjPerp σ‖ ≤ (1 + δ) * (2 * Real.sqrt (2 * (d N : ℝ) - 1)))
  refine h.trans (cor35_prob_mono _ _ (fun σ ⟨h1, h2⟩ => ?_))
  rw [abs_le]
  have e1 : 1 - δ ≤ ‖adjPerp σ‖ / (2 * Real.sqrt (2 * (d N : ℝ) - 1)) := by
    rw [le_div_iff₀ hs]; exact h1
  have e2 : ‖adjPerp σ‖ / (2 * Real.sqrt (2 * (d N : ℝ) - 1)) ≤ 1 + δ := by
    rw [div_le_iff₀ hs]; exact h2
  constructor <;> linarith

end StrongConv

theorem solution : type_of% @StrongConv.tendsto_prob_norm_adjPerp_div_sub_one_le_dev := @StrongConv.tendsto_prob_norm_adjPerp_div_sub_one_le_dev
