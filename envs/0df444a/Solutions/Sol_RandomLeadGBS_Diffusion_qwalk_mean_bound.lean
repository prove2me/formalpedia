-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.qwalk_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:00:52.383257+00:00
-- url     : https://prove2.me/submissions/5b2ac79d-2c80-481b-98e5-7f82275001a0

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSMarkov

variable {S : Type*}

/-- A stochastic kernel on a countable type. -/
structure Kern (K : S → S → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ K x y
  summ : ∀ x, Summable (K x)
  one : ∀ x, ∑' y, K x y = 1

/-- One-step push-forward of a mass function. -/
noncomputable def push (K : S → S → ℝ) (μ : S → ℝ) : S → ℝ := fun y => ∑' x, μ x * K x y

lemma prod_summable {K : S → S → ℝ} (hK : Kern K) (μ : S → ℝ) (h0 : ∀ x, 0 ≤ μ x)
    (hs : Summable μ) : Summable (fun z : S × S => μ z.1 * K z.1 z.2) := by
  refine (summable_prod_of_nonneg (f := fun z : S × S => μ z.1 * K z.1 z.2)
    (fun z => mul_nonneg (h0 _) (hK.nonneg _ _))).mpr
    ⟨fun x => by show Summable (fun y => μ x * K x y); exact (hK.summ x).mul_left _, ?_⟩
  have : (fun x => ∑' y, μ (x, y).1 * K (x, y).1 (x, y).2) = μ := by
    funext x
    show ∑' y, μ x * K x y = μ x
    rw [tsum_mul_left, hK.one, mul_one]
  rw [this]; exact hs

lemma push_props {K : S → S → ℝ} (hK : Kern K) (μ : S → ℝ) (h0 : ∀ x, 0 ≤ μ x)
    (hs : Summable μ) :
    (∀ y, 0 ≤ push K μ y) ∧ Summable (push K μ) ∧ ∑' y, push K μ y = ∑' x, μ x := by
  have hF := prod_summable hK μ h0 hs
  refine ⟨fun y => tsum_nonneg (fun x => mul_nonneg (h0 x) (hK.nonneg x y)), ?_, ?_⟩
  · have hF' : Summable (fun z : S × S => μ z.2 * K z.2 z.1) :=
      (Equiv.prodComm S S).summable_iff.mpr hF
    exact ((summable_prod_of_nonneg (fun z => mul_nonneg (h0 _) (hK.nonneg _ _))).mp hF').2
  · unfold push
    rw [Summable.tsum_comm (f := fun x y => μ x * K x y) hF]
    congr 1; funext x
    rw [tsum_mul_left, hK.one, mul_one]

lemma push_V {K : S → S → ℝ} (hK : Kern K) (μ : S → ℝ) (h0 : ∀ x, 0 ≤ μ x)
    (V : S → ℝ) (hV0 : ∀ x, 0 ≤ V x) (hKV : ∀ x, Summable (fun y => K x y * V y))
    (hμV : Summable (fun x => μ x * ∑' y, K x y * V y)) :
    Summable (fun y => push K μ y * V y) ∧
      ∑' y, push K μ y * V y = ∑' x, μ x * ∑' y, K x y * V y := by
  have hnn : ∀ z : S × S, 0 ≤ μ z.1 * K z.1 z.2 * V z.2 :=
    fun z => mul_nonneg (mul_nonneg (h0 _) (hK.nonneg _ _)) (hV0 _)
  have hF : Summable (fun z : S × S => μ z.1 * K z.1 z.2 * V z.2) := by
    refine (summable_prod_of_nonneg hnn).mpr ⟨fun x => ?_, ?_⟩
    · simpa [mul_assoc] using (hKV x).mul_left (μ x)
    · have : (fun x => ∑' y, μ (x, y).1 * K (x, y).1 (x, y).2 * V (x, y).2) =
          fun x => μ x * ∑' y, K x y * V y := by
        funext x; simp only [mul_assoc]; rw [tsum_mul_left]
      rw [this]; exact hμV
  have e : ∀ y, push K μ y * V y = ∑' x, μ x * K x y * V y := by
    intro y; unfold push; rw [tsum_mul_right]
  have hF' : Summable (fun z : S × S => μ z.2 * K z.2 z.1 * V z.1) :=
    (Equiv.prodComm S S).summable_iff.mpr hF
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact ((summable_prod_of_nonneg (fun z => hnn (z.2, z.1))).mp hF').2
  · simp only [e]
    rw [Summable.tsum_comm (f := fun x y => μ x * K x y * V y) hF]
    congr 1; funext x
    simp only [mul_assoc]; rw [tsum_mul_left]

lemma K_le_one {K : S → S → ℝ} (hK : Kern K) (x y : S) : K x y ≤ 1 := by
  rw [← hK.one x]; exact (hK.summ x).le_tsum y (fun j _ => hK.nonneg x j)

lemma col_summable {K : S → S → ℝ} (hK : Kern K) (μ : S → ℝ) (h0 : ∀ x, 0 ≤ μ x)
    (hs : Summable μ) (y : S) : Summable (fun x => μ x * K x y) :=
  Summable.of_nonneg_of_le (fun x => mul_nonneg (h0 x) (hK.nonneg x y))
    (fun x => by have := K_le_one hK x y; nlinarith [h0 x]) hs

/-- A stationary distribution of a discrete-time chain (same shape as the platform's
`IsDTMCStationary`). -/
def Stat (K : S → S → ℝ) (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ Summable p ∧ ∑' s, p s = 1 ∧ ∀ s', ∑' s, p s * K s s' = p s'

/-- Foster–Lyapunov criterion: a drift condition with a finite exceptional set gives a stationary
distribution (Krylov–Bogolyubov averaging along an ultrafilter). -/
theorem exists_stat [Countable S] [DecidableEq S] {K : S → S → ℝ} (hK : Kern K) (x₀ : S) (V : S → ℝ)
    (hV0 : ∀ x, 0 ≤ V x) (F : Finset S) (b : ℝ) (hb : 0 < b)
    (hKV : ∀ x, Summable (fun y => K x y * V y))
    (hdrift : ∀ x, ∑' y, K x y * V y ≤ V x - 1 + (if x ∈ F then b else 0)) :
    ∃ p, Stat K p := by
  classical
  -- iterates
  let μs : ℕ → S → ℝ := fun n => Nat.rec (fun x => if x = x₀ then 1 else 0)
    (fun _ μ => push K μ) n
  have μs_zero : μs 0 = fun x => if x = x₀ then 1 else 0 := rfl
  have μs_succ : ∀ n, μs (n + 1) = push K (μs n) := fun n => rfl
  have hKVle : ∀ x, ∑' y, K x y * V y ≤ V x + b := by
    intro x; have := hdrift x; split_ifs at this <;> linarith
  have hKV0 : ∀ x, 0 ≤ ∑' y, K x y * V y :=
    fun x => tsum_nonneg (fun y => mul_nonneg (hK.nonneg _ _) (hV0 _))
  -- invariants
  have inv : ∀ n, (∀ x, 0 ≤ μs n x) ∧ Summable (μs n) ∧ ∑' x, μs n x = 1 ∧
      Summable (fun x => μs n x * V x) ∧
      ∑' x, μs n x * V x ≤ V x₀ - n + b * ∑ t ∈ Finset.range n, ∑ x ∈ F, μs t x := by
    intro n
    induction n with
    | zero =>
      have hfin : ∀ f : S → ℝ, Summable (fun x => (if x = x₀ then (1 : ℝ) else 0) * f x) :=
        fun f => summable_of_ne_finset_zero (s := {x₀}) (by intro x hx; simp_all)
      refine ⟨fun x => by
        show 0 ≤ (if x = x₀ then (1 : ℝ) else 0); split_ifs <;> norm_num, ?_, ?_, ?_, ?_⟩
      · rw [μs_zero]; exact summable_of_ne_finset_zero (s := {x₀}) (by intro x hx; simp_all)
      · rw [μs_zero, tsum_ite_eq]
      · rw [μs_zero]; exact hfin V
      · rw [μs_zero]
        have : (fun x => (if x = x₀ then (1 : ℝ) else 0) * V x) =
            fun x => if x = x₀ then V x₀ else 0 := by
          funext x; split_ifs with h <;> simp [h]
        rw [this, tsum_ite_eq]; simp
    | succ n ih =>
      obtain ⟨h0, hs, h1, hsV, hEV⟩ := ih
      obtain ⟨p0, ps, p1⟩ := push_props hK (μs n) h0 hs
      have hμKV : Summable (fun x => μs n x * ∑' y, K x y * V y) := by
        refine Summable.of_nonneg_of_le (fun x => mul_nonneg (h0 x) (hKV0 x))
          (fun x => mul_le_mul_of_nonneg_left (hKVle x) (h0 x)) ?_
        simpa [mul_add] using hsV.add (hs.mul_right b)
      obtain ⟨pV, pVe⟩ := push_V hK (μs n) h0 V hV0 hKV hμKV
      rw [μs_succ]
      refine ⟨p0, ps, by rw [p1, h1], pV, ?_⟩
      rw [pVe]
      have hle : ∑' x, μs n x * ∑' y, K x y * V y ≤
          ∑' x, (μs n x * V x - μs n x + (if x ∈ F then b * μs n x else 0)) := by
        refine Summable.tsum_le_tsum (fun x => ?_) hμKV
          ((hsV.sub hs).add (summable_of_ne_finset_zero (s := F) (by intro x hx; simp [hx])))
        have := mul_le_mul_of_nonneg_left (hdrift x) (h0 x)
        split_ifs at this ⊢ <;> nlinarith
      rw [Summable.tsum_add (hsV.sub hs) (summable_of_ne_finset_zero (s := F)
        (by intro x hx; simp [hx])), Summable.tsum_sub hsV hs, h1,
        tsum_eq_sum (f := fun x => if x ∈ F then b * μs n x else 0) (s := F)
          (by intro x hx; simp [hx])] at hle
      rw [Finset.sum_range_succ]
      have : ∑ x ∈ F, (if x ∈ F then b * μs n x else 0) = b * ∑ x ∈ F, μs n x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x hx => by simp [hx])
      rw [this] at hle
      push_cast
      nlinarith
  have μ_le_one : ∀ n x, μs n x ≤ 1 := by
    intro n x
    obtain ⟨h0, hs, h1, -⟩ := inv n
    rw [← h1]
    exact hs.le_tsum x (fun j _ => h0 j)
  -- Cesàro averages
  let ν : ℕ → S → ℝ := fun n x => (∑ t ∈ Finset.range n, μs t x) / n
  have ν0 : ∀ n x, 0 ≤ ν n x := fun n x =>
    div_nonneg (Finset.sum_nonneg (fun t _ => (inv t).1 x)) (Nat.cast_nonneg _)
  have νsum : ∀ n, 1 ≤ n → Summable (ν n) ∧ ∑' x, ν n x = 1 := by
    intro n hn
    have hsum : Summable (fun x => ∑ t ∈ Finset.range n, μs t x) :=
      summable_sum (fun t _ => (inv t).2.1)
    refine ⟨hsum.div_const _, ?_⟩
    simp only [ν]
    rw [tsum_div_const, Summable.tsum_finsetSum (fun t _ => (inv t).2.1)]
    simp only [fun t => (inv t).2.2.1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have νle1 : ∀ n x, ν n x ≤ 1 := by
    intro n x
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [ν, h]
    · obtain ⟨hs, h1⟩ := νsum n h
      rw [← h1]; exact hs.le_tsum x (fun j _ => ν0 n j)
  -- ultrafilter limit
  let U : Ultrafilter ℕ := hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
  have hlim : ∀ x, ∃ a ∈ Set.Icc (0 : ℝ) 1, Tendsto (fun n => ν n x) U (𝓝 a) := by
    intro x
    have := isCompact_Icc.ultrafilter_le_nhds (U.map (fun n => ν n x)) (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact univ_mem' (fun n => ⟨ν0 n x, νle1 n x⟩))
    obtain ⟨a, ha, hle⟩ := this
    exact ⟨a, ha, by rw [Ultrafilter.coe_map] at hle; exact hle⟩
  choose L hL0 hLt using hlim
  have L0 : ∀ x, 0 ≤ L x := fun x => (hL0 x).1
  have hfin : ∀ A : Finset S, Tendsto (fun n => ∑ x ∈ A, ν n x) U (𝓝 (∑ x ∈ A, L x)) :=
    fun A => tendsto_finsetSum _ (fun x _ => hLt x)
  have hev1 : ∀ᶠ n in (U : Filter ℕ), 1 ≤ n := hU (eventually_ge_atTop 1)
  have Lsum_le : ∀ A : Finset S, ∑ x ∈ A, L x ≤ 1 := by
    intro A
    refine le_of_tendsto (hfin A) ?_
    filter_upwards [hev1] with n hn
    obtain ⟨hs, h1⟩ := νsum n hn
    rw [← h1]; exact hs.sum_le_tsum A (fun j _ => ν0 n j)
  have Ls : Summable L := summable_of_sum_le L0 Lsum_le
  -- lower bound on the mass of F
  have LF : 1 / (2 * b) ≤ ∑ x ∈ F, L x := by
    refine ge_of_tendsto (hfin F) ?_
    filter_upwards [hU (eventually_ge_atTop (max 1 ⌈2 * V x₀⌉₊))] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 2 * V x₀ ≤ n := by
      have := le_trans (le_max_right _ _) hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
    obtain ⟨-, -, -, -, hEV⟩ := inv n
    have hEV0 : 0 ≤ ∑' x, μs n x * V x := tsum_nonneg (fun x => mul_nonneg ((inv n).1 x) (hV0 x))
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have key : (n : ℝ) / 2 ≤ b * ∑ t ∈ Finset.range n, ∑ x ∈ F, μs t x := by linarith
    simp only [ν]
    rw [← Finset.sum_div, Finset.sum_comm]
    rw [div_le_div_iff₀ (by positivity) hnpos]
    nlinarith
  have Lpos : 0 < ∑' x, L x := by
    have := Ls.sum_le_tsum F (fun j _ => L0 j)
    have : 0 < 1 / (2 * b) := by positivity
    linarith
  -- superinvariance
  have push_ν : ∀ n, 1 ≤ n → ∀ y, push K (ν n) y = ν n y + (μs n y - μs 0 y) / n := by
    intro n hn y
    unfold push
    simp only [ν]
    have : (fun x => (∑ t ∈ Finset.range n, μs t x) / n * K x y) =
        fun x => (∑ t ∈ Finset.range n, μs t x * K x y) / n := by
      funext x; rw [div_mul_eq_mul_div, Finset.sum_mul]
    rw [this, tsum_div_const,
      Summable.tsum_finsetSum (fun t _ => col_summable hK (μs t) (inv t).1 (inv t).2.1 y)]
    have e1 : ∑ t ∈ Finset.range n, ∑' x, μs t x * K x y = ∑ t ∈ Finset.range n, μs (t + 1) y :=
      Finset.sum_congr rfl (fun t _ => by rw [μs_succ]; rfl)
    have e2 := Finset.sum_range_succ' (fun t => μs t y) n
    have e3 := Finset.sum_range_succ (fun t => μs t y) n
    rw [e1]
    have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                             linarith
    field_simp
    linarith
  have super : ∀ y, Summable (fun x => L x * K x y) ∧ ∑' x, L x * K x y ≤ L y := by
    intro y
    have hA : ∀ A : Finset S, ∑ x ∈ A, L x * K x y ≤ L y := by
      intro A
      have ht : Tendsto (fun n => ∑ x ∈ A, ν n x * K x y) U (𝓝 (∑ x ∈ A, L x * K x y)) :=
        tendsto_finsetSum _ (fun x _ => (hLt x).mul_const _)
      have h2 : Tendsto (fun n : ℕ => (μs n y - μs 0 y) / n) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat 2)
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos]
        apply div_le_div_of_nonneg_right _ hnpos.le
        have a1 := (inv n).1 y
        have a2 := μ_le_one n y
        have a3 := (inv 0).1 y
        have a4 := μ_le_one 0 y
        rw [abs_le]; constructor <;> linarith
      have hr : Tendsto (fun n => ν n y + (μs n y - μs 0 y) / n) U (𝓝 (L y)) := by
        simpa using (hLt y).add (h2.mono_left hU)
      refine le_of_tendsto_of_tendsto ht hr ?_
      filter_upwards [hev1] with n hn
      rw [← push_ν n hn y]
      exact (col_summable hK (ν n) (ν0 n) (νsum n hn).1 y).sum_le_tsum A
        (fun j _ => mul_nonneg (ν0 n j) (hK.nonneg j y))
    exact ⟨summable_of_sum_le (fun x => mul_nonneg (L0 x) (hK.nonneg x y)) hA,
      Real.tsum_le_of_sum_le (fun x => mul_nonneg (L0 x) (hK.nonneg x y)) hA⟩
  obtain ⟨-, pLs, pL1⟩ := push_props hK L L0 Ls
  have heq : ∀ y, ∑' x, L x * K x y = L y := by
    have hd0 : ∀ y, 0 ≤ L y - push K L y := fun y => by
      have := (super y).2; unfold push; linarith
    have hds : HasSum (fun y => L y - push K L y) 0 := by
      have := (Ls.sub pLs).hasSum
      rwa [Summable.tsum_sub Ls pLs, pL1, sub_self] at this
    have := (hasSum_zero_iff_of_nonneg hd0).mp hds
    intro y
    have := congrFun this y
    simp only [Pi.zero_apply] at this
    unfold push at this
    linarith
  set Z := ∑' x, L x with hZ
  refine ⟨fun x => L x / Z, fun x => div_nonneg (L0 x) Lpos.le, Ls.div_const _, ?_, ?_⟩
  · rw [tsum_div_const]; exact div_self Lpos.ne'
  · intro y
    have : (fun x => L x / Z * K x y) = fun x => L x * K x y / Z := by
      funext x; ring
    rw [this, tsum_div_const, heq y]

lemma push_lin {K : S → S → ℝ} (hK : Kern K) (μ ν : S → ℝ) (hμ : Summable μ) (hν : Summable ν)
    (a b : ℝ) (y : S) :
    push K (fun x => a * μ x + b * ν x) y = a * push K μ y + b * push K ν y := by
  have hs : ∀ w : S → ℝ, Summable w → Summable (fun x => w x * K x y) := by
    intro w hw
    refine Summable.of_norm_bounded hw.abs (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK.nonneg x y)]
    have := K_le_one hK x y
    have := abs_nonneg (w x)
    nlinarith
  unfold push
  have : (fun x => (a * μ x + b * ν x) * K x y) = fun x => a * (μ x * K x y) + b * (ν x * K x y) := by
    funext x; ring
  rw [this, Summable.tsum_add ((hs μ hμ).mul_left a) ((hs ν hν).mul_left b), tsum_mul_left,
    tsum_mul_left]

/-- Uniqueness of the stationary distribution when one state is accessible from every state. -/
theorem unique_stat {K : S → S → ℝ} (hK : Kern K) (x₀ : S)
    (hreach : ∀ x, Relation.ReflTransGen (fun a b => 0 < K a b) x x₀)
    (p p' : S → ℝ) (hp : Stat K p) (hp' : Stat K p') : p = p' := by
  obtain ⟨p0, ps, p1, pb⟩ := hp
  obtain ⟨q0, qs, q1, qb⟩ := hp'
  set ν : S → ℝ := fun x => p x - p' x with hν
  have νs : Summable ν := ps.sub qs
  have νas : Summable (fun x => |ν x|) := νs.abs
  have hs : ∀ w : S → ℝ, Summable w → ∀ y, Summable (fun x => w x * K x y) := by
    intro w hw y
    refine Summable.of_norm_bounded hw.abs (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK.nonneg x y)]
    have := K_le_one hK x y
    have := abs_nonneg (w x)
    nlinarith
  have νb : ∀ y, push K ν y = ν y := by
    intro y
    have := push_lin hK p p' ps qs 1 (-1) y
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
    unfold push at this ⊢
    rw [this, pb y, qb y]
  -- |ν| is superinvariant, hence invariant
  have hA : ∀ y, |ν y| ≤ push K (fun x => |ν x|) y := by
    intro y
    rw [← νb y]
    unfold push
    calc |∑' x, ν x * K x y| ≤ ∑' x, |ν x * K x y| := by
          have := norm_tsum_le_tsum_norm (f := fun x => ν x * K x y)
            ((hs _ νas y).congr (fun x => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK.nonneg x y)]))
          simpa [Real.norm_eq_abs] using this
      _ = ∑' x, |ν x| * K x y := by
          congr 1; funext x; rw [abs_mul, abs_of_nonneg (hK.nonneg x y)]
  obtain ⟨-, pas, pa1⟩ := push_props hK (fun x => |ν x|) (fun x => abs_nonneg _) νas
  have habs : ∀ y, push K (fun x => |ν x|) y = |ν y| := by
    have hd0 : ∀ y, 0 ≤ push K (fun x => |ν x|) y - |ν y| := fun y => by linarith [hA y]
    have hds : HasSum (fun y => push K (fun x => |ν x|) y - |ν y|) 0 := by
      have := (pas.sub νas).hasSum
      rwa [Summable.tsum_sub pas νas, pa1, sub_self] at this
    have := (hasSum_zero_iff_of_nonneg hd0).mp hds
    intro y
    have := congrFun this y
    simp only [Pi.zero_apply] at this
    linarith
  -- positive and negative parts are invariant
  have inv_part : ∀ c : ℝ, (c = 1 ∨ c = -1) → ∀ y,
      push K (fun x => (1 / 2) * |ν x| + (c / 2) * ν x) y = (1 / 2) * |ν y| + (c / 2) * ν y := by
    intro c _ y
    rw [push_lin hK _ _ νas νs, habs y, νb y]
  have closure : ∀ w : S → ℝ, (∀ x, 0 ≤ w x) → Summable w → (∀ y, push K w y = w y) →
      ∀ x, 0 < w x → 0 < w x₀ := by
    intro w w0 ws wb x hx
    have step : ∀ a b, 0 < K a b → 0 < w a → 0 < w b := by
      intro a b hab ha
      rw [← wb b]
      unfold push
      have := (hs w ws b).le_tsum a (fun j _ => mul_nonneg (w0 j) (hK.nonneg j b))
      have : 0 < w a * K a b := mul_pos ha hab
      linarith
    have hrx := hreach x
    clear hreach
    induction hrx with
    | refl => exact hx
    | tail _ hbc ih => exact step _ _ hbc ih
  have hpos := closure (fun x => (1 / 2) * |ν x| + (1 / 2) * ν x)
    (fun x => by have := neg_abs_le (ν x); linarith)
    ((νas.mul_left _).add (νs.mul_left _)) (fun y => by
      have := inv_part 1 (Or.inl rfl) y; simpa using this)
  have hneg := closure (fun x => (1 / 2) * |ν x| + (-1 / 2) * ν x)
    (fun x => by have := le_abs_self (ν x); linarith)
    ((νas.mul_left _).add (νs.mul_left _)) (fun y => by
      have := inv_part (-1) (Or.inr rfl) y; simpa using this)
  have νsum : ∑' x, ν x = 0 := by rw [Summable.tsum_sub ps qs, p1, q1, sub_self]
  -- one of the parts vanishes identically
  have key : (∀ x, 0 ≤ ν x) ∨ (∀ x, ν x ≤ 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ := hcon
    have a : 0 < (1 / 2) * |ν x₀| + (-1 / 2) * ν x₀ := hneg x1 (by
      show 0 < (1 / 2) * |ν x1| + (-1 / 2) * ν x1
      rw [abs_of_neg hx1]; linarith)
    have b : 0 < (1 / 2) * |ν x₀| + (1 / 2) * ν x₀ := hpos x2 (by
      show 0 < (1 / 2) * |ν x2| + (1 / 2) * ν x2
      rw [abs_of_pos hx2]; linarith)
    rcases le_total 0 (ν x₀) with h | h
    · rw [abs_of_nonneg h] at a; linarith
    · rw [abs_of_nonpos h] at b; linarith
  funext x
  rcases key with h | h
  · have := (hasSum_zero_iff_of_nonneg h).mp (by rw [← νsum]; exact νs.hasSum)
    have := congrFun this x
    simp only [hν, Pi.zero_apply] at this
    linarith
  · have h' : ∀ x, 0 ≤ -ν x := fun x => by linarith [h x]
    have := (hasSum_zero_iff_of_nonneg h').mp (by
      have := νs.neg.hasSum
      rwa [tsum_neg, νsum, neg_zero] at this)
    have := congrFun this x
    simp only [hν, Pi.zero_apply] at this
    linarith

end GBSMarkov

namespace GBSQwalk

open GBSMarkov

lemma qrow (γ : ℕ) (ε : ℝ) (f : ℕ → ℝ) (q : ℕ) :
    Summable (fun q' => qKernel γ ε q q' * f q') ∧
    ∑' q', qKernel γ ε q q' * f q' = (1 / 2 + ε) * f (q + (γ - 1)) + (1 / 2 - ε) * f (q - γ) := by
  have e : (fun q' => qKernel γ ε q q' * f q') = fun q' =>
      (if q' = q + (γ - 1) then (1 / 2 + ε) * f (q + (γ - 1)) else 0) +
        (if q' = q - γ then (1 / 2 - ε) * f (q - γ) else 0) := by
    funext q'
    simp only [qKernel]
    rw [add_mul]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · split_ifs with h
      · subst h; rfl
      · simp
  have s1 : Summable (fun q' : ℕ => if q' = q + (γ - 1) then (1 / 2 + ε) * f (q + (γ - 1)) else 0) :=
    summable_of_ne_finset_zero (s := {q + (γ - 1)}) (by intro j hj; simp_all)
  have s2 : Summable (fun q' : ℕ => if q' = q - γ then (1 / 2 - ε) * f (q - γ) else 0) :=
    summable_of_ne_finset_zero (s := {q - γ}) (by intro j hj; simp_all)
  rw [e]
  exact ⟨s1.add s2, by rw [Summable.tsum_add s1 s2, tsum_ite_eq, tsum_ite_eq]⟩

lemma kern (γ : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) : Kern (qKernel γ ε) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold qKernel
    apply add_nonneg <;> split_ifs <;> linarith
  · simpa using (qrow γ ε (fun _ => 1) x).1
  · have := (qrow γ ε (fun _ => 1) x).2
    simp only [mul_one] at this
    rw [this]; ring

end GBSQwalk

open GBSMarkov GBSQwalk

theorem solution (γ : ℕ) (hγ : 1 ≤ γ) (ε : ℝ) (hε : 0 < ε)
    (hδ : 0 < (1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1)) :
    (∃! p : ℕ → ℝ, IsDTMCStationary (qKernel γ ε) p) ∧
    ∀ p : ℕ → ℝ, IsDTMCStationary (qKernel γ ε) p →
      Summable (fun k : ℕ => p k * (k : ℝ)) ∧
      ∑' k : ℕ, p k * (k : ℝ) ≤
        (2 * ((γ : ℝ) - 1 + ((1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1))) * ((γ : ℝ) - 1)
            + (γ : ℝ) ^ 2) /
          (2 * ((1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1))) := by
  set δ := (1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1) with hδdef
  have hγr : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hε2 : ε < 1 / 2 := by nlinarith
  have hK := kern γ ε hε hε2
  have cast1 : ∀ q : ℕ, ((q + (γ - 1) : ℕ) : ℝ) = q + γ - 1 := by
    intro q; push_cast [Nat.cast_sub hγ]; ring
  have castsub : ∀ q : ℕ, γ ≤ q → ((q - γ : ℕ) : ℝ) = q - γ := by
    intro q hq; push_cast [Nat.cast_sub hq]; ring
  have castsub0 : ∀ q : ℕ, q < γ → ((q - γ : ℕ) : ℝ) = 0 := by
    intro q hq; rw [Nat.sub_eq_zero_of_le hq.le]; simp
  have hstat : ∀ p, IsDTMCStationary (qKernel γ ε) p ↔ Stat (qKernel γ ε) p := fun p => Iff.rfl
  -- existence
  have hex : ∃ p, Stat (qKernel γ ε) p := by
    refine exists_stat hK 0 (fun q => (q : ℝ) / δ) (fun q => by positivity) (Finset.range γ)
      (γ / δ + 1) (by positivity) (fun q => (qrow γ ε _ q).1) (fun q => ?_)
    rw [(qrow γ ε _ q).2, cast1]
    by_cases hq : γ ≤ q
    · rw [castsub q hq, if_neg (by simp; omega)]
      field_simp
      nlinarith
    · push Not at hq
      rw [castsub0 q hq, if_pos (Finset.mem_range.mpr hq)]
      field_simp
      nlinarith
  -- uniqueness
  have hreach : ∀ x, Relation.ReflTransGen (fun a b => 0 < qKernel γ ε a b) x 0 := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ q ih =>
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h]
      · have hlt : q - γ < q := by omega
        refine Relation.ReflTransGen.head ?_ (ih _ hlt)
        unfold qKernel
        rw [if_pos rfl]
        have : 0 ≤ (if q - γ = q + (γ - 1) then 1 / 2 + ε else 0) := by split_ifs <;> linarith
        linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := hex
    exact ⟨p, hp, fun p' hp' => (unique_stat hK 0 hreach p p' hp hp').symm⟩
  -- mean bound
  intro p hp
  obtain ⟨p0, ps, p1, pb⟩ := hp
  set c₀ : ℝ := (1 / 2 + ε) * ((γ : ℝ) - 1) ^ 2 + (1 / 2 - ε) * (γ : ℝ) ^ 2 with hc₀
  have hc0 : 0 ≤ c₀ := by
    rw [hc₀]
    have : 0 ≤ (γ : ℝ) - 1 := by linarith
    have : 0 ≤ 1 / 2 - ε := by linarith
    positivity
  set V : ℕ → ℝ := fun q => (q : ℝ) ^ 2 with hV
  set g : ℕ → ℝ := fun q => 2 * δ * q - c₀ with hg
  have hKV : ∀ q, (1 / 2 + ε) * V (q + (γ - 1)) + (1 / 2 - ε) * V (q - γ) ≤ V q - g q := by
    intro q
    simp only [hV, hg, hc₀, cast1]
    have h2 : ((q - γ : ℕ) : ℝ) ^ 2 ≤ ((q : ℝ) - γ) ^ 2 := by
      by_cases hq : γ ≤ q
      · rw [castsub q hq]
      · push Not at hq; rw [castsub0 q hq]; nlinarith [sq_nonneg ((q : ℝ) - γ)]
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 / 2 - ε)
    nlinarith
  have hA : ∀ A : Finset ℕ, ∑ q ∈ A, p q * (q : ℝ) ≤ c₀ / (2 * δ) := by
    intro A
    -- truncation level
    set N : ℝ := ∑ q ∈ A, ((V q) + |V q - g q|) + 1 with hN
    have hNA : ∀ q ∈ A, V q ≤ N ∧ V q - g q ≤ N := by
      intro q hq
      have hle : V q + |V q - g q| ≤ ∑ q ∈ A, ((V q) + |V q - g q|) :=
        Finset.single_le_sum (f := fun q => V q + |V q - g q|)
          (fun i _ => by simp only [hV]; positivity) hq
      have := abs_nonneg (V q - g q)
      have := le_abs_self (V q - g q)
      have : 0 ≤ V q := by simp only [hV]; positivity
      constructor <;> linarith
    set VN : ℕ → ℝ := fun q => min (V q) N with hVN
    have hVN0 : ∀ q, 0 ≤ VN q := fun q => le_min (by simp only [hV]; positivity)
      (by have := hNA; simp only [hN]; positivity)
    have hVNle : ∀ q, VN q ≤ N := fun q => min_le_right _ _
    have hN0 : 0 ≤ N := le_trans (hVN0 0) (hVNle 0)
    -- K VN ≤ min(V - g, N)
    have hKVN : ∀ q, ∑' q', qKernel γ ε q q' * VN q' ≤ min (V q - g q) N := by
      intro q
      rw [(qrow γ ε VN q).2]
      apply le_min
      · have := hKV q
        have a1 : VN (q + (γ - 1)) ≤ V (q + (γ - 1)) := min_le_left _ _
        have a2 : VN (q - γ) ≤ V (q - γ) := min_le_left _ _
        nlinarith
      · have a1 := hVNle (q + (γ - 1))
        have a2 := hVNle (q - γ)
        nlinarith
    have hKVN0 : ∀ q, 0 ≤ ∑' q', qKernel γ ε q q' * VN q' := fun q =>
      tsum_nonneg (fun q' => mul_nonneg (hK.nonneg _ _) (hVN0 _))
    have hpKVN : Summable (fun q => p q * ∑' q', qKernel γ ε q q' * VN q') :=
      Summable.of_nonneg_of_le (fun q => mul_nonneg (p0 q) (hKVN0 q))
        (fun q => mul_le_mul_of_nonneg_left (le_trans (hKVN q) (min_le_right _ _)) (p0 q))
        (ps.mul_right N)
    obtain ⟨-, hpush⟩ := push_V hK p p0 VN hVN0 (fun q => (qrow γ ε VN q).1) hpKVN
    have hpp : push (qKernel γ ε) p = p := funext pb
    rw [hpp] at hpush
    -- h_N = VN − min(V − g, N) has nonpositive mean and h_N + c₀ ≥ 0
    set h : ℕ → ℝ := fun q => VN q - min (V q - g q) N with hh
    have hmin_lb : ∀ q, -(c₀ + δ ^ 2) ≤ min (V q - g q) N := by
      intro q
      apply le_min
      · simp only [hV, hg]
        nlinarith [sq_nonneg ((q : ℝ) - δ), hc0]
      · nlinarith [sq_nonneg δ]
    have hs_min : Summable (fun q => p q * min (V q - g q) N) := by
      refine Summable.of_norm_bounded ((ps.mul_right (N + (c₀ + δ ^ 2)))) (fun q => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p0 q)]
      apply mul_le_mul_of_nonneg_left _ (p0 q)
      rw [abs_le]; constructor
      · linarith [hmin_lb q]
      · nlinarith [min_le_right (V q - g q) N, sq_nonneg δ]
    have hs_VN : Summable (fun q => p q * VN q) :=
      Summable.of_nonneg_of_le (fun q => mul_nonneg (p0 q) (hVN0 q))
        (fun q => mul_le_mul_of_nonneg_left (hVNle q) (p0 q)) (ps.mul_right N)
    have hmean : ∑' q, p q * h q ≤ 0 := by
      have e : (fun q => p q * h q) = fun q => p q * VN q - p q * min (V q - g q) N := by
        funext q; simp only [hh]; ring
      rw [e, Summable.tsum_sub hs_VN hs_min, hpush]
      have := Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left (hKVN q) (p0 q))
        hpKVN hs_min
      linarith
    have hhc : ∀ q, 0 ≤ h q + c₀ := by
      intro q
      simp only [hh, hVN]
      by_cases hgq : 0 ≤ g q
      · have : min (V q - g q) N ≤ min (V q) N := min_le_min (by linarith) le_rfl
        linarith
      · push Not at hgq
        have : min (V q - g q) N ≤ min (V q) N - g q := by
          rcases le_total (V q) N with h1 | h1
          · rw [min_eq_left h1]; exact min_le_left _ _
          · rw [min_eq_right h1]; linarith [min_le_right (V q - g q) N]
        have : -c₀ ≤ g q := by
          simp only [hg]
          have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          nlinarith
        linarith
    have hs_h : Summable (fun q => p q * (h q + c₀)) := by
      have e : (fun q => p q * (h q + c₀)) =
          fun q => (p q * VN q - p q * min (V q - g q) N) + p q * c₀ := by
        funext q; simp only [hh]; ring
      rw [e]; exact (hs_VN.sub hs_min).add (ps.mul_right c₀)
    have hsumA : ∑ q ∈ A, p q * (h q + c₀) ≤ c₀ := by
      have := hs_h.sum_le_tsum A (fun q _ => mul_nonneg (p0 q) (hhc q))
      have e : ∑' q, p q * (h q + c₀) = ∑' q, p q * h q + c₀ := by
        have : (fun q => p q * (h q + c₀)) = fun q => p q * h q + p q * c₀ := by
          funext q; ring
        rw [this, Summable.tsum_add (by
          have e2 : (fun q => p q * h q) = fun q => p q * VN q - p q * min (V q - g q) N := by
            funext q; simp only [hh]; ring
          rw [e2]; exact hs_VN.sub hs_min) (ps.mul_right c₀), tsum_mul_right, p1, one_mul]
      linarith
    have hAeq : ∀ q ∈ A, h q + c₀ = 2 * δ * q := by
      intro q hq
      obtain ⟨a1, a2⟩ := hNA q hq
      simp only [hh, hVN]
      rw [min_eq_left a1, min_eq_left a2]
      simp only [hg]
      ring
    rw [Finset.sum_congr rfl (fun q hq => by rw [hAeq q hq])] at hsumA
    rw [le_div_iff₀ (by positivity), Finset.sum_mul]
    have : ∑ q ∈ A, p q * (2 * δ * q) = ∑ q ∈ A, p q * q * (2 * δ) :=
      Finset.sum_congr rfl (fun q _ => by ring)
    linarith
  have hsum : Summable (fun k : ℕ => p k * (k : ℝ)) :=
    summable_of_sum_le (fun k => mul_nonneg (p0 k) (Nat.cast_nonneg k)) hA
  refine ⟨hsum, ?_⟩
  have h1 := Real.tsum_le_of_sum_le (fun k => mul_nonneg (p0 k) (Nat.cast_nonneg k)) hA
  refine le_trans h1 ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ (γ : ℝ) - 1 := by linarith
  simp only [hc₀]
  nlinarith
