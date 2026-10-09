-- Prove2me | solution 1 for TeschlODE.IntervalMaps.tentRepellor_dimH
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:43:09.463193+00:00
-- url     : https://prove2.me/submissions/63633a3f-ae05-433d-a0ff-e0017fec8ebf

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_IntervalMaps_IsStrangeRepellor

set_option autoImplicit false

open TeschlODE.Shared in
noncomputable def t5e_code (μ x : ℝ) : ℕ → Fin 2 :=
  fun i => if 1 / 2 < (tentMap μ)^[i] x then 1 else 0

open TeschlODE.Shared in
theorem t5e_T_left (μ x : ℝ) (hx : x ≤ 1 / 2) : tentMap μ x = μ * x := by
  unfold tentMap
  rw [abs_of_nonpos (by linarith)]; ring

open TeschlODE.Shared in
theorem t5e_T_right (μ x : ℝ) (hx : 1 / 2 ≤ x) : tentMap μ x = μ * (1 - x) := by
  unfold tentMap
  rw [abs_of_nonneg (by linarith)]; ring

open TeschlODE.Shared in
theorem t5e_T_cont (μ : ℝ) : Continuous (tentMap μ) := by
  unfold tentMap; fun_prop

open TeschlODE.Shared in
theorem t5e_code_shift (μ x : ℝ) (k i : ℕ) :
    t5e_code μ ((tentMap μ)^[k] x) i = t5e_code μ x (i + k) := by
  simp only [t5e_code, ← Function.iterate_add_apply]

open TeschlODE.Shared in
theorem t5e_T_dist (μ a b : ℝ) (hμ : 0 ≤ μ) (h : (1 / 2 < a ↔ 1 / 2 < b)) :
    |tentMap μ a - tentMap μ b| = μ * |a - b| := by
  by_cases ha : 1 / 2 < a
  · have hb := h.mp ha
    rw [t5e_T_right μ a ha.le, t5e_T_right μ b hb.le, ← mul_sub, abs_mul, abs_of_nonneg hμ,
      show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg]
  · have hb : ¬ 1 / 2 < b := fun hb => ha (h.mpr hb)
    push Not at ha hb
    rw [t5e_T_left μ a ha, t5e_T_left μ b hb, ← mul_sub, abs_mul, abs_of_nonneg hμ]

open TeschlODE.Shared in
theorem t5e_code_eq_iff (μ x y : ℝ) (i : ℕ) : t5e_code μ x i = t5e_code μ y i ↔
    (1 / 2 < (tentMap μ)^[i] x ↔ 1 / 2 < (tentMap μ)^[i] y) := by
  unfold t5e_code
  split_ifs with h1 h2 h2
  · exact ⟨fun _ => ⟨fun _ => h2, fun _ => h1⟩, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (h.mp h1) h2⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (h.mpr h2) h1⟩
  · exact ⟨fun _ => ⟨fun h => absurd h h1, fun h => absurd h h2⟩, fun _ => rfl⟩

open TeschlODE.Shared in
theorem t5e_iter_dist (μ : ℝ) (hμ : 0 ≤ μ) : ∀ (n : ℕ) (x y : ℝ),
    (∀ i < n, t5e_code μ x i = t5e_code μ y i) →
    |(tentMap μ)^[n] x - (tentMap μ)^[n] y| = μ ^ n * |x - y| := by
  intro n
  induction n with
  | zero => intro x y _; simp
  | succ n ih =>
    intro x y h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      t5e_T_dist μ _ _ hμ ((t5e_code_eq_iff μ x y n).mp (h n (by omega))),
      ih x y (fun i hi => h i (by omega)), pow_succ]
    ring

open TeschlODE.Shared in
theorem t5e_iter_mem (μ x : ℝ) (hx : x ∈ tentRepellor μ) (k : ℕ) :
    (tentMap μ)^[k] x ∈ tentRepellor μ := by
  intro n
  rw [← Function.iterate_add_apply]
  exact hx (n + k)

open TeschlODE.Shared in
theorem t5e_isClosed (μ : ℝ) : IsClosed (tentRepellor μ) := by
  have : tentRepellor μ = ⋂ n : ℕ, (tentMap μ)^[n] ⁻¹' Set.Icc 0 1 := by
    ext x; simp [tentRepellor]
  rw [this]
  exact isClosed_iInter fun n => isClosed_Icc.preimage ((t5e_T_cont μ).iterate n)

open TeschlODE.Shared in
theorem t5e_isCompact (μ : ℝ) : IsCompact (tentRepellor μ) :=
  isCompact_Icc.of_isClosed_subset (t5e_isClosed μ) (fun x hx => hx 0)

open TeschlODE.Shared in
theorem t5e_gap (μ : ℝ) (hμ : 2 < μ) (x : ℝ) (hx : x ∈ tentRepellor μ) :
    (x ≤ μ⁻¹ ∧ t5e_code μ x 0 = 0) ∨ (1 - μ⁻¹ ≤ x ∧ t5e_code μ x 0 = 1) := by
  have h0 := hx 0
  have h1 := hx 1
  simp only [Function.iterate_zero, id, Function.iterate_one, Set.mem_Icc] at h0 h1
  have hμ0 : 0 < μ := by linarith
  have hi : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0.ne'
  by_cases h : 1 / 2 < x
  · right
    refine ⟨?_, by unfold t5e_code; exact if_pos (by simpa using h)⟩
    rw [t5e_T_right μ x h.le] at h1
    have := mul_le_mul_of_nonneg_left h1.2 (inv_nonneg.mpr hμ0.le)
    rw [← mul_assoc, hi, one_mul, mul_one] at this
    linarith
  · left
    push Not at h
    refine ⟨?_, by unfold t5e_code; exact if_neg (by simpa using h)⟩
    rw [t5e_T_left μ x h] at h1
    have := mul_le_mul_of_nonneg_left h1.2 (inv_nonneg.mpr hμ0.le)
    rw [← mul_assoc, hi, one_mul, mul_one] at this
    linarith

theorem t5e_inv_lt_half (μ : ℝ) (hμ : 2 < μ) : μ⁻¹ < 1 / 2 := by
  rw [one_div]
  exact inv_strictAnti₀ (by norm_num) hμ

open TeschlODE.Shared in
theorem t5e_close (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (n : ℕ) (h : ∀ i < n, t5e_code μ x i = t5e_code μ y i) :
    |x - y| ≤ μ⁻¹ ^ n := by
  have hμ0 : 0 < μ := by linarith
  have hd := t5e_iter_dist μ hμ0.le n x y h
  have hb : |(tentMap μ)^[n] x - (tentMap μ)^[n] y| ≤ 1 := by
    have h1 := hx n
    have h2 := hy n
    simp only [Set.mem_Icc] at h1 h2
    rw [abs_le]; constructor <;> linarith
  rw [hd] at hb
  calc |x - y| = μ⁻¹ ^ n * (μ ^ n * |x - y|) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ0.ne', one_pow, one_mul]
    _ ≤ μ⁻¹ ^ n * 1 := by gcongr
    _ = μ⁻¹ ^ n := mul_one _

open TeschlODE.Shared in
theorem t5e_far (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (k : ℕ) (h : ∀ i < k, t5e_code μ x i = t5e_code μ y i)
    (hk : t5e_code μ x k ≠ t5e_code μ y k) :
    (1 - 2 * μ⁻¹) * μ⁻¹ ^ k ≤ |x - y| := by
  have hμ0 : 0 < μ := by linarith
  have hd := t5e_iter_dist μ hμ0.le k x y h
  have hgx := t5e_gap μ hμ _ (t5e_iter_mem μ x hx k)
  have hgy := t5e_gap μ hμ _ (t5e_iter_mem μ y hy k)
  rw [t5e_code_shift, zero_add] at hgx hgy
  have hh := t5e_inv_lt_half μ hμ
  have hg : 1 - 2 * μ⁻¹ ≤ |(tentMap μ)^[k] x - (tentMap μ)^[k] y| := by
    rcases hgx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hgy with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact absurd (a2.trans b2.symm) hk
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · exact absurd (a2.trans b2.symm) hk
  rw [hd] at hg
  calc (1 - 2 * μ⁻¹) * μ⁻¹ ^ k ≤ (μ ^ k * |x - y|) * μ⁻¹ ^ k := by gcongr
    _ = |x - y| := by
        rw [mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ0.ne', one_pow, one_mul]

open TeschlODE.Shared in
theorem t5e_eq_of_code (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (h : t5e_code μ x = t5e_code μ y) : x = y := by
  have hμ0 : 0 < μ := by linarith
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ (by linarith : (1:ℝ) < μ))
  have := t5e_close μ hμ x y hx hy n (fun i _ => by rw [h])
  linarith

/-- inverse branches -/
noncomputable def t5e_g (μ : ℝ) (b : Fin 2) (y : ℝ) : ℝ := if b = 0 then y / μ else 1 - y / μ

open TeschlODE.Shared in
theorem t5e_g_spec (μ : ℝ) (hμ : 2 < μ) (b : Fin 2) (y : ℝ) (hy : y ∈ tentRepellor μ) :
    t5e_g μ b y ∈ tentRepellor μ ∧ tentMap μ (t5e_g μ b y) = y ∧ t5e_code μ (t5e_g μ b y) 0 = b ∧
      ∀ i, t5e_code μ (t5e_g μ b y) (i + 1) = t5e_code μ y i := by
  have hμ0 : 0 < μ := by linarith
  have hy0 := hy 0
  simp only [Function.iterate_zero, id, Set.mem_Icc] at hy0
  have hq0 : 0 ≤ y / μ := div_nonneg hy0.1 hμ0.le
  have hq1 : y / μ < 1 / 2 := by rw [div_lt_iff₀ hμ0]; linarith
  have hT : tentMap μ (t5e_g μ b y) = y := by
    unfold t5e_g
    split_ifs
    · rw [t5e_T_left μ _ hq1.le]; field_simp
    · rw [t5e_T_right μ _ (by linarith)]; field_simp; ring
  have hc : t5e_code μ (t5e_g μ b y) 0 = b := by
    unfold t5e_g t5e_code
    split_ifs with h1 h2 h2 <;> simp only [Function.iterate_zero, id] at h2
    · linarith
    · exact h1.symm
    · exact (Fin.eq_one_of_ne_zero b h1).symm
    · exact absurd (by linarith) h2
  have hI : t5e_g μ b y ∈ Set.Icc (0:ℝ) 1 := by
    unfold t5e_g
    split_ifs <;> constructor <;> linarith
  refine ⟨fun n => ?_, hT, hc, fun i => ?_⟩
  · cases n with
    | zero => simpa using hI
    | succ n => rw [Function.iterate_succ_apply, hT]; exact hy n
  · rw [← t5e_code_shift, Function.iterate_one, hT]

noncomputable def t5e_P (μ : ℝ) : ℕ → (ℕ → Fin 2) → ℝ
  | 0, _ => 0
  | n + 1, a => t5e_g μ (a 0) (t5e_P μ n (fun i => a (i + 1)))

open TeschlODE.Shared in
theorem t5e_zero_mem (μ : ℝ) : (0:ℝ) ∈ tentRepellor μ := by
  intro n
  have h0 : tentMap μ 0 = 0 := by simp [tentMap]
  rw [Function.iterate_fixed h0 n]
  simp

open TeschlODE.Shared in
theorem t5e_P_spec (μ : ℝ) (hμ : 2 < μ) : ∀ (n : ℕ) (a : ℕ → Fin 2),
    t5e_P μ n a ∈ tentRepellor μ ∧ ∀ i < n, t5e_code μ (t5e_P μ n a) i = a i := by
  intro n
  induction n with
  | zero => intro a; exact ⟨t5e_zero_mem μ, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro a
    obtain ⟨hm, hc⟩ := ih (fun i => a (i + 1))
    obtain ⟨g1, -, g3, g4⟩ := t5e_g_spec μ hμ (a 0) _ hm
    refine ⟨g1, fun i hi => ?_⟩
    cases i with
    | zero => exact g3
    | succ i => rw [t5e_P, g4]; exact hc i (by omega)

open TeschlODE.Shared in
theorem t5e_exists_code (μ : ℝ) (hμ : 2 < μ) (a : ℕ → Fin 2) :
    ∃ x ∈ tentRepellor μ, t5e_code μ x = a := by
  have hμ0 : 0 < μ := by linarith
  have hr : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hcs : CauchySeq (fun n => t5e_P μ n a) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => μ⁻¹ ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hμ0.le) hr)
    rw [Real.dist_eq]
    exact t5e_close μ hμ _ _ (t5e_P_spec μ hμ n a).1 (t5e_P_spec μ hμ m a).1 N (fun i hi => by
      rw [(t5e_P_spec μ hμ n a).2 i (by omega), (t5e_P_spec μ hμ m a).2 i (by omega)])
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  have hxm : x ∈ tentRepellor μ := (t5e_isClosed μ).mem_of_tendsto hx
    (Filter.Eventually.of_forall fun n => (t5e_P_spec μ hμ n a).1)
  refine ⟨x, hxm, funext fun i => ?_⟩
  have hti := (((t5e_T_cont μ).iterate i).tendsto x).comp hx
  have hside : ∀ n, i < n → ((tentMap μ)^[i] (t5e_P μ n a) ≤ μ⁻¹ ∧ a i = 0) ∨
      (1 - μ⁻¹ ≤ (tentMap μ)^[i] (t5e_P μ n a) ∧ a i = 1) := by
    intro n hn
    have hg := t5e_gap μ hμ _ (t5e_iter_mem μ _ (t5e_P_spec μ hμ n a).1 i)
    rw [t5e_code_shift, zero_add, (t5e_P_spec μ hμ n a).2 i hn] at hg
    exact hg
  have hhalf := t5e_inv_lt_half μ hμ
  by_cases hai : a i = 0
  · have hle : (tentMap μ)^[i] x ≤ μ⁻¹ := by
      refine le_of_tendsto hti (Filter.eventually_atTop.mpr ⟨i + 1, fun n hn => ?_⟩)
      rcases hside n (by omega) with h | h
      · exact h.1
      · rw [hai] at h; exact absurd h.2 (by decide)
    rw [hai]
    simp only [t5e_code]
    rw [if_neg (by linarith)]
  · have hai1 : a i = 1 := Fin.eq_one_of_ne_zero _ hai
    have hge : 1 - μ⁻¹ ≤ (tentMap μ)^[i] x := by
      refine ge_of_tendsto hti (Filter.eventually_atTop.mpr ⟨i + 1, fun n hn => ?_⟩)
      rcases hside n (by omega) with h | h
      · exact absurd h.2 hai
      · exact h.1
    rw [hai1]
    simp only [t5e_code]
    rw [if_pos (by linarith)]


theorem t5e_s_facts (μ : ℝ) (hμ : 2 < μ) :
    0 < Real.log 2 / Real.log μ ∧ Real.log 2 / Real.log μ < 1 ∧
      μ ^ (Real.log 2 / Real.log μ) = 2 := by
  have hμ0 : 0 < μ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlμ : Real.log 2 < Real.log μ := Real.log_lt_log (by norm_num) hμ
  have hlμ0 : 0 < Real.log μ := by linarith
  refine ⟨div_pos hl2 hlμ0, (div_lt_one hlμ0).mpr hlμ, ?_⟩
  rw [Real.rpow_def_of_pos hμ0,
    show Real.log μ * (Real.log 2 / Real.log μ) = Real.log 2 by field_simp,
    Real.exp_log (by norm_num)]

theorem t5e_pow_s (μ : ℝ) (hμ : 2 < μ) (n : ℕ) :
    (μ⁻¹ ^ n) ^ (Real.log 2 / Real.log μ) = ((2:ℝ) ^ n)⁻¹ := by
  have hμ0 : 0 < μ := by linarith
  rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hμ0.le,
    mul_comm, Real.rpow_mul hμ0.le, (t5e_s_facts μ hμ).2.2, Real.rpow_natCast]

open TeschlODE.Shared in
def t5e_cyl (μ : ℝ) (n : ℕ) (w : Fin n → Fin 2) : Set ℝ :=
  {x | x ∈ tentRepellor μ ∧ ∀ i : Fin n, t5e_code μ x i = w i}

open TeschlODE.Shared in
theorem t5e_dim_le (μ : ℝ) (hμ : 2 < μ) :
    dimH (tentRepellor μ) ≤ ENNReal.ofReal (Real.log 2 / Real.log μ) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hs0, -, -⟩ := t5e_s_facts μ hμ
  set s : NNReal := (Real.log 2 / Real.log μ).toNNReal with hsdef
  have hs : (s : ℝ) = Real.log 2 / Real.log μ := Real.coe_toNNReal _ hs0.le
  show dimH (tentRepellor μ) ≤ (s : ENNReal)
  apply dimH_le_of_hausdorffMeasure_ne_top
  have hr : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdiam : ∀ n w, Metric.ediam (t5e_cyl μ n w) ≤ ENNReal.ofReal (μ⁻¹ ^ n) := by
    intro n w
    apply Metric.ediam_le
    rintro x ⟨hx, hxw⟩ y ⟨hy, hyw⟩
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (t5e_close μ hμ x y hx hy n (fun i hi => by
      rw [hxw ⟨i, hi⟩, hyw ⟨i, hi⟩]))
  have htend : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (μ⁻¹ ^ n)) Filter.atTop (nhds 0) := by
    have := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hμ0.le) hr)
    simpa using this
  have key := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (s : ℝ) (tentRepellor μ)
    (l := Filter.atTop) (fun n : ℕ => ENNReal.ofReal (μ⁻¹ ^ n)) htend
    (t5e_cyl μ) (Filter.Eventually.of_forall hdiam)
    (Filter.Eventually.of_forall fun n x hx => by
      simp only [Set.mem_iUnion]
      exact ⟨fun i => t5e_code μ x i, hx, fun i => rfl⟩)
  have hsum : ∀ n : ℕ, ∑ w : Fin n → Fin 2, Metric.ediam (t5e_cyl μ n w) ^ (s:ℝ) ≤ 1 := by
    intro n
    calc ∑ w : Fin n → Fin 2, Metric.ediam (t5e_cyl μ n w) ^ (s:ℝ)
        ≤ ∑ _w : Fin n → Fin 2, ENNReal.ofReal (((2:ℝ) ^ n)⁻¹) := by
          gcongr with w
          calc Metric.ediam (t5e_cyl μ n w) ^ (s:ℝ) ≤ ENNReal.ofReal (μ⁻¹ ^ n) ^ (s:ℝ) :=
                ENNReal.rpow_le_rpow (hdiam n w) s.2
            _ = ENNReal.ofReal ((μ⁻¹ ^ n) ^ (s:ℝ)) :=
                ENNReal.ofReal_rpow_of_nonneg (by positivity) s.2
            _ = _ := by rw [hs, t5e_pow_s μ hμ n]
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_ofNat]
          exact ENNReal.mul_inv_cancel (by simp) (by simp)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (key.trans (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hsum)))

open TeschlODE.Shared in
theorem t5e_holder (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) :
    |Real.ofDigits (t5e_code μ x) - Real.ofDigits (t5e_code μ y)| ≤
      ((1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ))⁻¹ * |x - y| ^ (Real.log 2 / Real.log μ) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hs0, -, -⟩ := t5e_s_facts μ hμ
  have hh := t5e_inv_lt_half μ hμ
  have hc0 : 0 < 1 - 2 * μ⁻¹ := by linarith
  by_cases hxy : t5e_code μ x = t5e_code μ y
  · rw [hxy, sub_self, abs_zero]; positivity
  · have hex : ∃ k, t5e_code μ x k ≠ t5e_code μ y k := by
      by_contra hc; push Not at hc; exact hxy (funext hc)
    classical
    have hk : t5e_code μ x (Nat.find hex) ≠ t5e_code μ y (Nat.find hex) := Nat.find_spec hex
    have hlt : ∀ i < Nat.find hex, t5e_code μ x i = t5e_code μ y i := fun i hi => by
      have := Nat.find_min hex hi; push Not at this; exact this
    have h1 : |Real.ofDigits (t5e_code μ x) - Real.ofDigits (t5e_code μ y)| ≤
        ((2:ℝ) ^ Nat.find hex)⁻¹ := by
      have := Real.abs_ofDigits_sub_ofDigits_le hlt
      simpa using this
    have h2 := t5e_far μ hμ x y hx hy _ hlt hk
    have hcs : 0 < (1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ) := Real.rpow_pos_of_pos hc0 _
    calc _ ≤ ((2:ℝ) ^ Nat.find hex)⁻¹ := h1
      _ = ((1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ))⁻¹ *
            ((1 - 2 * μ⁻¹) * μ⁻¹ ^ Nat.find hex) ^ (Real.log 2 / Real.log μ) := by
          rw [Real.mul_rpow hc0.le (by positivity), t5e_pow_s μ hμ, ← mul_assoc,
            inv_mul_cancel₀ hcs.ne', one_mul]
      _ ≤ ((1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ))⁻¹ * |x - y| ^ (Real.log 2 / Real.log μ) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcs.le)
          exact Real.rpow_le_rpow (mul_nonneg hc0.le (by positivity)) h2 hs0.le

open TeschlODE.Shared in
theorem t5e_dim_ge (μ : ℝ) (hμ : 2 < μ) :
    ENNReal.ofReal (Real.log 2 / Real.log μ) ≤ dimH (tentRepellor μ) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hs0, -, -⟩ := t5e_s_facts μ hμ
  set s : NNReal := (Real.log 2 / Real.log μ).toNNReal with hsdef
  have hs : (s : ℝ) = Real.log 2 / Real.log μ := Real.coe_toNNReal _ hs0.le
  have hspos : 0 < s := by rw [← NNReal.coe_pos, hs]; exact hs0
  have hc : 0 ≤ ((1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (by linarith [t5e_inv_lt_half μ hμ]) _)
  have hH : HolderOnWith (((1 - 2 * μ⁻¹) ^ (Real.log 2 / Real.log μ))⁻¹).toNNReal s
      (fun x => Real.ofDigits (t5e_code μ x)) (tentRepellor μ) := by
    intro x hx y hy
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs0.le]
    show _ ≤ ENNReal.ofReal _ * _
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal (t5e_holder μ hμ x y hx hy)
  have himg : Set.Icc (0:ℝ) 1 ⊆ (fun x => Real.ofDigits (t5e_code μ x)) '' tentRepellor μ := by
    intro t ht
    obtain ⟨d, -, hd⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) ht
    obtain ⟨x, hx, hxc⟩ := t5e_exists_code μ hμ d
    exact ⟨x, hx, by simp only [hxc, hd]⟩
  have h1 : (1 : ENNReal) ≤ dimH (tentRepellor μ) / s := by
    calc (1:ENNReal) = dimH (Set.Icc (0:ℝ) 1) := by
          rw [Real.dimH_of_nonempty_interior (by
            rw [interior_Icc]; exact Set.nonempty_Ioo.mpr one_pos), Module.finrank_self,
            Nat.cast_one]
      _ ≤ _ := dimH_mono himg
      _ ≤ _ := hH.dimH_image_le hspos
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hspos.ne'))
    (Or.inl ENNReal.coe_ne_top), one_mul] at h1
  exact h1

open TeschlODE.Shared in
theorem t5e_mapsTo (μ : ℝ) : Set.MapsTo (tentMap μ) (tentRepellor μ) (tentRepellor μ) :=
  fun x hx => by simpa using t5e_iter_mem μ x hx 1

open TeschlODE.Shared in
theorem t5e_shadow (μ : ℝ) (hμ : 2 < μ) (u v : ℝ) (hu : u ∈ tentRepellor μ)
    (hv : v ∈ tentRepellor μ) (m : ℕ) :
    ∃ x ∈ tentRepellor μ, |x - u| ≤ μ⁻¹ ^ m ∧ (tentMap μ)^[m] x = v := by
  obtain ⟨x, hx, hxc⟩ := t5e_exists_code μ hμ
    (fun i => if i < m then t5e_code μ u i else t5e_code μ v (i - m))
  refine ⟨x, hx, t5e_close μ hμ x u hx hu m (fun i hi => by rw [hxc]; simp [hi]), ?_⟩
  apply t5e_eq_of_code μ hμ _ _ (t5e_iter_mem μ x hx m) hv
  funext i
  rw [t5e_code_shift, hxc]
  show (if i + m < m then _ else _) = _
  rw [if_neg (by omega), Nat.add_sub_cancel]

open TeschlODE.Shared in
theorem t5e_escape_neg (μ : ℝ) (hμ : 2 < μ) (w : ℝ) (hw : w < 0) :
    ∀ j : ℕ, (tentMap μ)^[j] w = μ ^ j * w := by
  have hμ0 : 0 < μ := by linarith
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hneg := mul_neg_of_pos_of_neg (pow_pos hμ0 j) hw
    rw [Function.iterate_succ_apply', ih, t5e_T_left μ _ (by linarith), pow_succ]
    ring

open TeschlODE.Shared TeschlODE.IntervalMaps in
theorem t5e_repelling (μ : ℝ) (hμ : 2 < μ) : IsRepelling (tentMap μ) (tentRepellor μ) := by
  have hμ0 : 0 < μ := by linarith
  refine ⟨t5e_isCompact μ, ?_, Set.Ioo (-1) 2, ?_, ?_⟩
  · apply Set.Subset.antisymm (t5e_mapsTo μ).image_subset
    intro y hy
    obtain ⟨g1, g2, -, -⟩ := t5e_g_spec μ hμ 0 y hy
    exact ⟨_, g1, g2⟩
  · exact isOpen_Ioo.mem_nhdsSet.mpr (fun x hx => by
      have h0 := hx 0
      simp only [Function.iterate_zero, id, Set.mem_Icc] at h0
      exact ⟨by linarith, by linarith⟩)
  · rintro x ⟨-, hxΛ⟩
    have hex : ∃ m, (tentMap μ)^[m] x ∉ Set.Icc (0:ℝ) 1 := by
      by_contra hc; push Not at hc; exact hxΛ hc
    obtain ⟨m, hm⟩ := hex
    have hneg : ∃ m', (tentMap μ)^[m'] x < 0 := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hm
      rcases hm with hm | hm
      · exact ⟨m, hm⟩
      · refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply', t5e_T_right μ _ (by linarith)]
        nlinarith
    obtain ⟨m', hm'⟩ := hneg
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (-((tentMap μ)^[m'] x))⁻¹ (by linarith : (1:ℝ) < μ)
    refine ⟨j + m', fun hmem => ?_⟩
    rw [Function.iterate_add_apply, t5e_escape_neg μ hμ _ hm' j] at hmem
    have h1 : 1 < μ ^ j * (-((tentMap μ)^[m'] x)) := by
      have := mul_lt_mul_of_pos_right hj (neg_pos.mpr hm')
      rwa [inv_mul_cancel₀ (by linarith)] at this
    have h2 := hmem.1
    nlinarith

open TeschlODE.Shared in
theorem t5e_transitive (μ : ℝ) (hμ : 2 < μ) :
    IsTopTransitive ((t5e_mapsTo μ).restrict (tentMap μ) (tentRepellor μ) (tentRepellor μ)) := by
  have hr : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hμ0 : 0 < μ := by linarith
  intro U V hU _ hUne hVne
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU u hu
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hr
  obtain ⟨x, hx, hxu, hxv⟩ := t5e_shadow μ hμ (u : ℝ) (v : ℝ) u.2 v.2 (k + 1)
  refine ⟨k + 1, by omega, v, ⟨⟨x, hx⟩, hball ?_, ?_⟩, hv⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    calc |x - (u : ℝ)| ≤ μ⁻¹ ^ (k + 1) := hxu
      _ ≤ μ⁻¹ ^ k := pow_le_pow_of_le_one (by positivity) hr.le (by omega)
      _ < ε := hk
  · rw [Set.MapsTo.iterate_restrict]
    exact Subtype.ext hxv

open TeschlODE.Shared in
theorem t5e_chaotic (μ : ℝ) (hμ : 2 < μ) :
    IsChaotic ((t5e_mapsTo μ).restrict (tentMap μ) (tentRepellor μ) (tentRepellor μ)) := by
  have hμ0 : 0 < μ := by linarith
  have hr : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  refine ⟨Continuous.subtype_mk ((t5e_T_cont μ).comp continuous_subtype_val) _, ?_,
    t5e_transitive μ hμ, ?_⟩
  · classical
    choose f hf1 hf2 using fun n : ℕ =>
      t5e_exists_code μ hμ (fun i => if i = n then (1 : Fin 2) else 0)
    have hinj : Function.Injective f := by
      intro n m h
      have e : t5e_code μ (f n) = t5e_code μ (f m) := by rw [h]
      rw [hf2, hf2] at e
      have := congrFun e n
      by_contra hnm
      simp [hnm] at this
    exact (Set.infinite_of_injective_forall_mem hinj hf1).to_subtype
  · rw [Metric.dense_iff]
    intro u ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hr
    obtain ⟨x, hx, hxc⟩ := t5e_exists_code μ hμ (fun i => t5e_code μ u (i % (k + 1)))
    refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      calc |x - (u : ℝ)| ≤ μ⁻¹ ^ (k + 1) :=
            t5e_close μ hμ x u hx u.2 (k + 1) (fun i hi => by
              simp only [hxc]; rw [Nat.mod_eq_of_lt hi])
        _ ≤ μ⁻¹ ^ k := pow_le_pow_of_le_one (by positivity) hr.le (by omega)
        _ < ε := hk
    · refine Function.mk_mem_periodicPts (n := k + 1) (by omega) ?_
      unfold Function.IsPeriodicPt Function.IsFixedPt
      rw [Set.MapsTo.iterate_restrict]
      apply Subtype.ext
      show (tentMap μ)^[k + 1] x = x
      apply t5e_eq_of_code μ hμ _ _ (t5e_iter_mem μ x hx (k + 1)) hx
      funext i
      rw [t5e_code_shift, hxc]
      simp only [Nat.add_mod_right]

open TeschlODE.Shared TeschlODE.IntervalMaps in
theorem t5e_strange (μ : ℝ) (hμ : 2 < μ)
    (hdim : dimH (tentRepellor μ) = ENNReal.ofReal (Real.log 2 / Real.log μ)) :
    IsStrangeRepellor (tentMap μ) (tentRepellor μ) := by
  obtain ⟨hs0, hs1, -⟩ := t5e_s_facts μ hμ
  refine ⟨⟨t5e_repelling μ hμ, t5e_mapsTo μ, t5e_transitive μ hμ⟩,
    ⟨t5e_mapsTo μ, t5e_chaotic μ hμ⟩, ?_, ?_⟩
  · rw [hdim]; exact ENNReal.ofReal_ne_top
  · intro k hk
    rw [hdim] at hk
    have e := congrArg ENNReal.toReal hk
    rw [ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_natCast] at e
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [Nat.cast_zero] at e; linarith
    · have h' : (1:ℝ) ≤ k := by exact_mod_cast h
      linarith

open TeschlODE.IntervalMaps in
theorem solution (μ : ℝ) (hμ : 2 ≤ μ) :
    dimH (TeschlODE.Shared.tentRepellor μ) = ENNReal.ofReal (Real.log 2 / Real.log μ) ∧
      (2 < μ → IsStrangeRepellor (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ)) := by
  rcases hμ.lt_or_eq with h | h
  · have hd := le_antisymm (t5e_dim_le μ h) (t5e_dim_ge μ h)
    exact ⟨hd, fun _ => t5e_strange μ h hd⟩
  · subst h
    refine ⟨?_, fun h => absurd h (lt_irrefl _)⟩
    have hT : ∀ x ∈ Set.Icc (0:ℝ) 1, TeschlODE.Shared.tentMap 2 x ∈ Set.Icc (0:ℝ) 1 := by
      intro x hx
      unfold TeschlODE.Shared.tentMap
      have h1 : |2 * x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have h2 := abs_nonneg (2 * x - 1)
      constructor <;> nlinarith
    have hΛ : TeschlODE.Shared.tentRepellor 2 = Set.Icc 0 1 := by
      ext x
      constructor
      · intro hx; simpa using hx 0
      · intro hx n
        induction n with
        | zero => simpa using hx
        | succ n ih => rw [Function.iterate_succ_apply']; exact hT _ ih
    rw [hΛ, Real.dimH_of_nonempty_interior (by
      rw [interior_Icc]; exact Set.nonempty_Ioo.mpr one_pos), Module.finrank_self,
      div_self (Real.log_pos one_lt_two).ne', ENNReal.ofReal_one, Nat.cast_one]
