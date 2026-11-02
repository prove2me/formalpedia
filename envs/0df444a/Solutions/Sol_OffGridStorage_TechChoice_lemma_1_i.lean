-- Prove2me | solution 1 for OffGridStorage.TechChoice.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:16:54.480918+00:00
-- url     : https://prove2.me/submissions/3f65bc1e-fd38-45c0-b748-1ab748032580

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model
import Theorems.Thm_OffGridStorage_TechChoice_theorem_4_i
import Theorems.Thm_OffGridStorage_TechChoice_eq_20_closed_form
import Theorems.Thm_OffGridStorage_TechChoice_tracking_eq_full
import Theorems.Thm_OffGridStorage_TechChoice_eq_25_marginal_storage
import Theorems.Thm_OffGridStorage_TechChoice_eq_19_threshold_ratio
import Theorems.Thm_OffGridStorage_TechChoice_lemma_1_ii

open MeasureTheory OffGridStorage.TechChoice

namespace OffGridLemma1Aux

lemma pos_nonneg' (a : ℝ) : 0 ≤ pos a := le_max_left _ _

lemma charge_nonneg (p : Params) (K : ℝ) (q : Fin p.T → ℝ) (n : ℕ) : 0 ≤ charge p K q n := by
  cases n with
  | zero => exact le_refl _
  | succ n => exact le_max_left _ _

lemma qn_cont (p : Params) (n : ℕ) :
    Continuous (fun q : Fin p.T → ℝ => if h : n < p.T then q ⟨n, h⟩ else 0) := by
  by_cases h : n < p.T
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const

lemma charge_cont (p : Params) (n : ℕ) :
    Continuous (fun z : ℝ × (Fin p.T → ℝ) => charge p z.1 z.2 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hq : Continuous (fun z : ℝ × (Fin p.T → ℝ) => if h : n < p.T then z.2 ⟨n, h⟩ else 0) :=
      (qn_cont p n).comp continuous_snd
    show Continuous (fun z : ℝ × (Fin p.T → ℝ) => max 0 (min (max 0 (charge p z.1 z.2 n +
      p.e * max 0 ((if h : n < p.T then z.2 ⟨n, h⟩ else 0) - p.DH) -
      max 0 (p.DH - (if h : n < p.T then z.2 ⟨n, h⟩ else 0)))) z.1 - p.DL))
    fun_prop

lemma rev_cont (p : Params) :
    Continuous (fun z : (ℝ × ℝ) × (Fin p.T → ℝ) => revenueTR p z.1.2 (fun t => z.1.1 * z.2 t)) := by
  unfold revenueTR periodRevenueTR afterDay pos
  have hc : ∀ t : Fin p.T, Continuous
      (fun z : (ℝ × ℝ) × (Fin p.T → ℝ) => charge p z.1.2 (fun t => z.1.1 * z.2 t) t.val) := by
    intro t
    have hm : Continuous (fun z : (ℝ × ℝ) × (Fin p.T → ℝ) => (z.1.2, fun t => z.1.1 * z.2 t)) := by
      fun_prop
    exact (charge_cont p t.val).comp hm
  fun_prop

lemma profit_cont (p : Params) : Continuous (fun z : ℝ × ℝ => profitTR p z.1 z.2) := by
  unfold profitTR
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin p.T → ℝ)))
    (f := fun (z : ℝ × ℝ) (u : Fin p.T → ℝ) => revenueTR p z.2 (fun t => z.1 * u t))
    (rev_cont p) (s := unitCube p.T) (isCompact_univ_pi (fun _ => isCompact_Icc))
  fun_prop


lemma afterDay_le (p : Params) (hp : Standing p) (Q x q : ℝ) (hx : 0 ≤ x) (hq0 : 0 ≤ q)
    (hqQ : q ≤ Q) : afterDay p x q ≤ x + p.e * Q := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  unfold afterDay pos
  have h1 : max 0 (q - p.DH) ≤ Q := max_le (by linarith) (by linarith)
  have h2 : 0 ≤ max 0 (p.DH - q) := le_max_left _ _
  have h3 : p.e * max 0 (q - p.DH) ≤ p.e * Q := mul_le_mul_of_nonneg_left h1 he0.le
  have h4 : 0 ≤ x + p.e * Q := by nlinarith [le_max_left 0 (q - p.DH)]
  exact max_le h4 (by linarith)

lemma afterDay_nonneg (p : Params) (x q : ℝ) : 0 ≤ afterDay p x q := le_max_left _ _

lemma charge_sat (p : Params) (hp : Standing p) (Q : ℝ) (hQ : 0 ≤ Q) (K1 K2 : ℝ)
    (h1 : (p.T : ℝ) * p.e * Q ≤ K1) (h2 : (p.T : ℝ) * p.e * Q ≤ K2) (u : Fin p.T → ℝ)
    (hu : ∀ t, u t ∈ Set.Icc (0:ℝ) 1) :
    ∀ n : ℕ, n ≤ p.T → charge p K1 (fun t => Q * u t) n = charge p K2 (fun t => Q * u t) n ∧
      charge p K1 (fun t => Q * u t) n ≤ (n : ℝ) * p.e * Q := by
  have he0 := hp.2.2.1
  have hDL := hp.2.1
  intro n
  induction n with
  | zero => intro _; simp [charge]
  | succ n ih =>
    intro hn
    have hlt : n < p.T := by omega
    obtain ⟨heq, hle⟩ := ih hlt.le
    set x := charge p K1 (fun t => Q * u t) n
    have hx : 0 ≤ x := charge_nonneg _ _ _ _
    have hqn0 : 0 ≤ Q * u ⟨n, hlt⟩ := mul_nonneg hQ (hu _).1
    have hqnQ : Q * u ⟨n, hlt⟩ ≤ Q := mul_le_of_le_one_right hQ (hu _).2
    have ha := afterDay_le p hp Q x _ hx hqn0 hqnQ
    have ha0 := afterDay_nonneg p x (Q * u ⟨n, hlt⟩)
    have hTn : ((n:ℝ) + 1) ≤ p.T := by exact_mod_cast hn
    have hB : (n + 1 : ℝ) * p.e * Q ≤ p.T * p.e * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ
      exact mul_le_mul_of_nonneg_right hTn he0.le
    have haB : afterDay p x (Q * u ⟨n, hlt⟩) ≤ (n + 1 : ℝ) * p.e * Q := by nlinarith
    simp only [charge, dif_pos hlt, nextCharge]
    rw [← heq, min_eq_left (by linarith), min_eq_left (by linarith)]
    refine ⟨rfl, ?_⟩
    push_cast
    unfold pos
    exact max_le (by nlinarith) (by linarith)

lemma rev_sat (p : Params) (hp : Standing p) (Q : ℝ) (hQ : 0 ≤ Q) (K1 K2 : ℝ)
    (h1 : (p.T : ℝ) * p.e * Q ≤ K1) (h2 : (p.T : ℝ) * p.e * Q ≤ K2) (u : Fin p.T → ℝ)
    (hu : ∀ t, u t ∈ Set.Icc (0:ℝ) 1) :
    revenueTR p K1 (fun t => Q * u t) = revenueTR p K2 (fun t => Q * u t) := by
  have he0 := hp.2.2.1
  unfold revenueTR
  apply Finset.sum_congr rfl
  intro t _
  obtain ⟨heq, hle⟩ := charge_sat p hp Q hQ K1 K2 h1 h2 u hu t.val t.isLt.le
  rw [← heq]
  set x := charge p K1 (fun t => Q * u t) t.val
  have hx : 0 ≤ x := charge_nonneg _ _ _ _
  have ha := afterDay_le p hp Q x (Q * u t) hx (mul_nonneg hQ (hu t).1)
    (mul_le_of_le_one_right hQ (hu t).2)
  have hTn : ((t.val:ℝ) + 1) ≤ p.T := by exact_mod_cast t.isLt
  have hB : (t.val + 1 : ℝ) * p.e * Q ≤ p.T * p.e * Q := by
    apply mul_le_mul_of_nonneg_right _ hQ
    exact mul_le_mul_of_nonneg_right hTn he0.le
  have e1 : ∀ K : ℝ, (p.T : ℝ) * p.e * Q ≤ K →
      min (afterDay p x (Q * u t)) (min K p.DL) = min (afterDay p x (Q * u t)) p.DL := by
    intro K hK
    rw [← min_assoc, min_eq_left (show afterDay p x (Q * u t) ≤ K by nlinarith)]
  unfold periodRevenueTR
  beta_reduce
  rw [e1 K1 h1, e1 K2 h2]

lemma measurableSet_cube (n : ℕ) : MeasurableSet (unitCube n) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma volume_cube (n : ℕ) : volume (unitCube n) = 1 := by
  unfold unitCube
  rw [volume_pi_pi]
  simp [Real.volume_Icc]

lemma rev_nonneg (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (u : Fin p.T → ℝ) (hu : ∀ t, u t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ revenueTR p K (fun t => Q * u t) := by
  unfold revenueTR
  apply Finset.sum_nonneg
  intro t _
  unfold periodRevenueTR
  have hx := charge_nonneg p K (fun t => Q * u t) t.val
  have hq := mul_nonneg hQ (hu t).1
  have := afterDay_nonneg p (charge p K (fun t => Q * u t) t.val) (Q * u t)
  have hDH := hp.1
  have hDL := hp.2.1
  have : 0 ≤ min (Q * u t + charge p K (fun t => Q * u t) t.val) p.DH := le_min (by linarith) hDH.le
  have : 0 ≤ min (afterDay p (charge p K (fun t => Q * u t) t.val) (Q * u t)) (min K p.DL) :=
    le_min (by assumption) (le_min hK hDL.le)
  rw [add_comm (charge p K _ _)]
  linarith

lemma rev_le (p : Params) (K : ℝ) (q : Fin p.T → ℝ) :
    revenueTR p K q ≤ p.T * (p.DH + p.DL) := by
  unfold revenueTR
  have : ∀ t ∈ (Finset.univ : Finset (Fin p.T)),
      periodRevenueTR p K (charge p K q t.val) (q t) ≤ p.DH + p.DL := by
    intro t _
    unfold periodRevenueTR
    have := min_le_right (charge p K q t.val + q t) p.DH
    have := min_le_right (afterDay p (charge p K q t.val) (q t)) (min K p.DL)
    have := min_le_right K p.DL
    linarith
  calc _ ≤ ∑ t : Fin p.T, (p.DH + p.DL) := Finset.sum_le_sum this
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma int_le (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    ∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t) ≤ p.T * (p.DH + p.DL) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin p.T → ℝ)))
    (s := unitCube p.T) (C := p.T * (p.DH + p.DL)) (f := fun u => revenueTR p K (fun t => Q * u t))
    (by rw [volume_cube]; exact ENNReal.one_lt_top) (by
      intro u hu
      have hu' : ∀ t, u t ∈ Set.Icc (0:ℝ) 1 := fun t => hu t (Set.mem_univ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (rev_nonneg p hp Q K hQ hK u hu')]
      exact rev_le p K _)
  rw [measureReal_def, volume_cube] at h
  simp only [ENNReal.toReal_one, mul_one] at h
  exact le_trans (le_abs_self _) (by simpa using h)

lemma int_nonneg (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    0 ≤ ∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t) := by
  apply setIntegral_nonneg (measurableSet_cube _)
  intro u hu
  exact rev_nonneg p hp Q K hQ hK u (fun t => hu t (Set.mem_univ _))

lemma profit_sat (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q)
    (hK : (p.T : ℝ) * p.e * Q ≤ K) :
    profitTR p Q K ≤ profitTR p Q ((p.T : ℝ) * p.e * Q) := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  have hint : ∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t) =
      ∫ u in unitCube p.T, revenueTR p ((p.T : ℝ) * p.e * Q) (fun t => Q * u t) := by
    apply setIntegral_congr_fun (measurableSet_cube _)
    intro u hu
    exact rev_sat p ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ Q hQ _ _ hK le_rfl u
      (fun t => hu t (Set.mem_univ _))
  unfold profitTR
  rw [hint]
  have : 0 ≤ p.cK / p.e := div_nonneg hcK he0.le
  have hT0 : (0:ℝ) ≤ p.T := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hK (mul_nonneg hT0 this)
  nlinarith

theorem exists_opt (p : Params) (hp : Standing p) : ∃ Q K : ℝ, IsOptimalTR p Q K := by
  have hp' := hp
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp'
  have hg0 : 0 < p.g := by linarith
  set Qm := p.g * (p.DH + p.DL) / p.cQ with hQm
  have hQm0 : 0 ≤ Qm := by positivity
  set S : Set (ℝ × ℝ) := Set.Icc 0 Qm ×ˢ Set.Icc 0 ((p.T : ℝ) * p.e * Qm)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hT0 : (0:ℝ) ≤ p.T := Nat.cast_nonneg _
  have h00 : ((0:ℝ), (0:ℝ)) ∈ S := ⟨⟨le_rfl, hQm0⟩, ⟨le_rfl, by positivity⟩⟩
  obtain ⟨x, hxS, hx⟩ := hS.exists_isMaxOn ⟨_, h00⟩ (profit_cont p).continuousOn
  refine ⟨x.1, x.2, hxS.1.1, hxS.2.1, ?_⟩
  intro Q' K' hQ' hK'
  have hmax : ∀ y ∈ S, profitTR p y.1 y.2 ≤ profitTR p x.1 x.2 := fun y hy => hx hy
  by_cases hQb : Qm < Q'
  · have hP0 : 0 ≤ profitTR p 0 0 := by
      unfold profitTR
      have := int_nonneg p hp 0 0 le_rfl le_rfl
      simp only [mul_zero, sub_zero]
      positivity
    have h1 := int_le p hp Q' K' hQ' hK'
    have hT1 : (1:ℝ) ≤ p.T := by exact_mod_cast hT
    have hcost : 0 ≤ (p.T : ℝ) * (p.cK / p.e) * K' := by
      have := div_nonneg hcK he0.le; positivity
    have hQ'' : p.g * (p.DH + p.DL) < p.cQ * Q' := by
      rw [hQm, div_lt_iff₀ hcQ] at hQb; linarith
    have : profitTR p Q' K' < 0 := by
      unfold profitTR
      have := mul_le_mul_of_nonneg_left h1 hg0.le
      have := mul_lt_mul_of_pos_left hQ'' (by linarith : (0:ℝ) < p.T)
      nlinarith
    linarith [hmax _ h00]
  · rw [not_lt] at hQb
    have hle : profitTR p Q' K' ≤ profitTR p Q' (min K' ((p.T : ℝ) * p.e * Q')) := by
      rcases le_total K' ((p.T : ℝ) * p.e * Q') with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]; exact profit_sat p hp Q' K' hQ' h
    refine le_trans hle (hmax (Q', min K' ((p.T : ℝ) * p.e * Q')) ⟨⟨hQ', hQb⟩, ?_, ?_⟩)
    · exact le_min hK' (by positivity)
    · refine le_trans (min_le_right _ _) ?_
      apply mul_le_mul_of_nonneg_left hQb
      positivity

end OffGridLemma1Aux

open OffGridLemma1Aux Filter Topology in
theorem solution (p : Params) (hp : Standing p) :
    OptimalStoragePos p ↔ g0 p < p.g := by
  have hp' := hp
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp'
  constructor
  · intro hpos
    by_contra hle
    rw [not_lt] at hle
    have h4 := (theorem_4_i p hp hle).2.1
    exact lt_irrefl _ (hpos.2 _ _ h4)
  · intro hlt
    refine ⟨exists_opt p hp, ?_⟩
    intro Q K hopt
    rcases (lt_or_eq_of_le hopt.2.1) with hK | hK
    · exact hK
    exfalso
    subst hK
    -- the marginal value of storage at (Q0, 0) is positive
    have hr : 0 ≤ p.cK / p.e := div_nonneg hcK he0.le
    have hδ : p.cK / p.e < p.g - Real.sqrt (2 * p.cQ * p.g) := by
      rw [lemma_1_ii.1] at hlt
      exact (eq_19_threshold_ratio p.cQ _ p.g hcQ hr hg).2.mp hlt
    obtain ⟨⟨hQ00, hQ0max⟩, -, hderiv⟩ := eq_25_marginal_storage p hp
    have hT1 : (0:ℝ) < p.T := by exact_mod_cast hT
    have hdpos : 0 < (p.T : ℝ) * (-Real.sqrt (2 * p.cQ * p.g) + p.g - p.cK / p.e) := by
      apply mul_pos hT1; linarith
    -- Q0 > D_H
    have hQ0DH : p.DH < Q0 p := by
      unfold Q0
      have : 1 < Real.sqrt (p.g / (2 * p.cQ)) := by
        rw [Real.lt_sqrt (by norm_num), one_pow, lt_div_iff₀ (by linarith)]; linarith
      nlinarith
    -- choose a small k > 0
    have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
    have hslope' : Tendsto (slope (fun K' => closedFormF p (Q0 p) K') 0) (𝓝[>] 0)
        (𝓝 ((p.T : ℝ) * (-Real.sqrt (2 * p.cQ * p.g) + p.g - p.cK / p.e))) :=
      hslope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
    have ev1 : ∀ᶠ k in 𝓝[>] (0:ℝ), 0 < slope (fun K' => closedFormF p (Q0 p) K') 0 k :=
      hslope'.eventually (lt_mem_nhds hdpos)
    have hε : 0 < min p.DL (p.e * (Q0 p - p.DH)) := lt_min hDL (mul_pos he0 (by linarith))
    have ev2 : ∀ᶠ k in 𝓝[>] (0:ℝ), k < min p.DL (p.e * (Q0 p - p.DH)) :=
      nhdsWithin_le_nhds (gt_mem_nhds hε)
    have ev3 : ∀ᶠ k in 𝓝[>] (0:ℝ), 0 < k := self_mem_nhdsWithin
    obtain ⟨k, hk1, hk2, hk3⟩ := (ev1.and (ev2.and ev3)).exists
    have hkDL : k ≤ p.DL := le_trans hk2.le (min_le_left _ _)
    have hkQ : p.DH + k / p.e ≤ Q0 p := by
      have := lt_of_lt_of_le hk2 (min_le_right _ _)
      have : k / p.e < Q0 p - p.DH := by rw [div_lt_iff₀ he0]; linarith
      linarith
    have hinc : closedFormF p (Q0 p) 0 < closedFormF p (Q0 p) k := by
      rw [slope_def_field] at hk1
      have := (div_pos_iff.mp hk1)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    have e0 : profitF p (Q0 p) 0 = closedFormF p (Q0 p) 0 :=
      eq_20_closed_form p hp (Q0 p) 0 le_rfl (by simp; linarith)
    have ek : profitF p (Q0 p) k = closedFormF p (Q0 p) k :=
      eq_20_closed_form p hp (Q0 p) k hk3.le hkQ
    have tk : profitTR p (Q0 p) k = profitF p (Q0 p) k :=
      tracking_eq_full p hp (Q0 p) k hQ00 hk3.le hkDL
    have tQ : profitTR p Q 0 = profitF p Q 0 :=
      tracking_eq_full p hp Q 0 hopt.1 le_rfl hDL.le
    have hopt' := hopt.2.2 (Q0 p) k hQ00 hk3.le
    have := hQ0max Q hopt.1
    linarith
