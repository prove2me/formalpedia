-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.theorem_1_stability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:14:17.701631+00:00
-- url     : https://prove2.me/submissions/5e3379cf-5efa-41fd-b524-8169ed6965f1

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

namespace GBSStab

open GBSMarkov

/-- Row sums of the rate matrix against a test function. -/
lemma row (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    (fun s' => rate P r s s' * h s') =
      fun s' => (if s' = afterCustomer P r s then r * h (afterCustomer P r s) else 0) +
        (if s' = afterItem P r s then P.β * (s.2 : ℝ) * h (afterItem P r s) else 0) := by
  funext s'
  simp only [rate, add_mul]
  congr 1
  · split_ifs with h1
    · subst h1; rfl
    · simp
  · by_cases h1 : s' = afterItem P r s
    · subst h1
      by_cases hz : 1 ≤ s.2
      · simp [hz]
      · have : s.2 = 0 := by omega
        simp [this]
    · simp [h1]

lemma row_summable (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    Summable (fun s' => rate P r s s' * h s') := by
  rw [row]
  exact (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all)).add
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all))

lemma row_tsum (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    ∑' s', rate P r s s' * h s' =
      r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s) := by
  rw [row, Summable.tsum_add
    (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all))
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all)),
    tsum_ite_eq, tsum_ite_eq]

lemma rate_nonneg (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (s s' : State) :
    0 ≤ rate P r s s' := by
  unfold rate
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs
    · positivity
    · rfl


lemma os_eq (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ((orderStep P r y z : ℕ) : ℤ) = max (z : ℤ) ⌈truncTarget P r y⌉ := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  push_cast
  rcases le_total ⌈truncTarget P r y⌉ (z : ℤ) with h | h
  · rw [Int.toNat_eq_zero.mpr (by omega), max_eq_left h]; simp
  · rw [Int.toNat_of_nonneg (by omega), max_eq_right h]; ring

section Fixed

variable (P : Params) (r : ℝ)

/-- The cap `M = X∗ + f`. -/
noncomputable def capM : ℝ := Xstar P r + P.f r
/-- `m = ⌈M⌉`. -/
noncomputable def mcap : ℕ := ⌈capM P r⌉₊
/-- Lower threshold: below it the truncated target equals the cap. -/
noncomputable def yL : ℤ := ⌊P.xs r - P.f r / P.γ⌋
/-- Upper threshold: from `yH - 1` on the truncated target is `0`. -/
noncomputable def yH : ℤ := ⌈P.xs r + Xstar P r / P.γ⌉ + 1

variable {P r}

lemma capM_pos (hP : P.Standing) (hr : 0 < r) : 0 < capM P r := by
  have := hP.2.2.1 r
  unfold capM Xstar
  have := hP.1
  positivity

lemma mcap_int (hP : P.Standing) (hr : 0 < r) : ((mcap P r : ℕ) : ℤ) = ⌈capM P r⌉ :=
  Int.natCast_ceil_eq_ceil (capM_pos hP hr).le

lemma mcap_ge (hP : P.Standing) (hr : 0 < r) : capM P r ≤ (mcap P r : ℝ) := Nat.le_ceil _

lemma one_le_mcap (hP : P.Standing) (hr : 0 < r) : 1 ≤ mcap P r := by
  have := capM_pos hP hr
  unfold mcap
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma T_le_cap (hP : P.Standing) (hr : 0 < r) (y : ℤ) : truncTarget P r y ≤ capM P r :=
  max_le (min_le_right _ _) (capM_pos hP hr).le

lemma ceilT_le (hP : P.Standing) (hr : 0 < r) (y : ℤ) :
    ⌈truncTarget P r y⌉ ≤ ((mcap P r : ℕ) : ℤ) := by
  rw [mcap_int hP hr]; exact Int.ceil_mono (T_le_cap hP hr y)

lemma ceilT_nonneg (y : ℤ) : 0 ≤ ⌈truncTarget P r y⌉ :=
  Int.ceil_nonneg (le_max_right _ _)

lemma ceilT_low (hP : P.Standing) (hr : 0 < r) (y : ℤ) (hy : y ≤ yL P r) :
    ⌈truncTarget P r y⌉ = ((mcap P r : ℕ) : ℤ) := by
  rw [mcap_int hP hr]
  congr 1
  have hγ : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have h1 : (y : ℝ) ≤ P.xs r - P.f r / P.γ := by
    have := Int.floor_le (P.xs r - P.f r / P.γ)
    have : (y : ℝ) ≤ (yL P r : ℝ) := by exact_mod_cast hy
    unfold yL at this; linarith
  have h2 : P.f r ≤ -((P.γ : ℝ) * ((y : ℝ) - P.xs r)) := by
    have : P.f r / P.γ ≤ P.xs r - y := by linarith
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith
  have hc := capM_pos hP hr
  unfold truncTarget target
  unfold capM at hc ⊢
  rw [min_eq_right (by linarith), max_eq_left hc.le]

lemma ceilT_high (hP : P.Standing) (hr : 0 < r) (y : ℤ) (hy : yH P r - 1 ≤ y) :
    ⌈truncTarget P r y⌉ = 0 := by
  have hγ : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have h1 : P.xs r + Xstar P r / P.γ ≤ (y : ℝ) := by
    have := Int.le_ceil (P.xs r + Xstar P r / P.γ)
    have : ((yH P r - 1 : ℤ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    unfold yH at this; push_cast at this; linarith
  have h2 : Xstar P r ≤ (P.γ : ℝ) * ((y : ℝ) - P.xs r) := by
    have : Xstar P r / P.γ ≤ y - P.xs r := by linarith
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have : truncTarget P r y = 0 := by
    unfold truncTarget target
    exact max_eq_right (le_trans (min_le_left _ _) (by linarith))
  rw [this, Int.ceil_zero]

lemma yL_lt_yH (hP : P.Standing) (hr : 0 < r) : yL P r < yH P r - 1 := by
  have hγ : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hf := hP.2.2.1 r
  have hX : 0 < Xstar P r := by unfold Xstar; have := hP.1; positivity
  have a : (yL P r : ℝ) ≤ P.xs r - P.f r / P.γ := Int.floor_le _
  have b : P.xs r + Xstar P r / P.γ ≤ ((yH P r - 1 : ℤ) : ℝ) := by
    unfold yH; push_cast; linarith [Int.le_ceil (P.xs r + Xstar P r / P.γ)]
  have c : 0 < P.f r / P.γ := by positivity
  have d : 0 < Xstar P r / P.γ := by positivity
  have : (yL P r : ℝ) < ((yH P r - 1 : ℤ) : ℝ) := by linarith
  exact_mod_cast this

/-! ### Reachability -/

lemma step_cust (hr : 0 < r) (hβ : 0 < P.β) (s : State) : Step P r s (afterCustomer P r s) := by
  unfold Step rate
  rw [if_pos rfl]
  have : 0 ≤ (if 1 ≤ s.2 ∧ afterCustomer P r s = afterItem P r s then P.β * (s.2 : ℝ) else 0) := by
    split_ifs <;> first | positivity | exact le_rfl
  linarith

lemma step_item (hr : 0 < r) (hβ : 0 < P.β) (s : State) (hz : 1 ≤ s.2) :
    Step P r s (afterItem P r s) := by
  unfold Step rate
  rw [if_pos (show 1 ≤ s.2 ∧ afterItem P r s = afterItem P r s from ⟨hz, rfl⟩)]
  have : 0 ≤ (if afterItem P r s = afterCustomer P r s then r else 0) := by
    split_ifs <;> linarith
  have : (0 : ℝ) < P.β * (s.2 : ℝ) := by
    have : (1 : ℝ) ≤ s.2 := by exact_mod_cast hz
    positivity
  linarith

lemma aC_low (hP : P.Standing) (hr : 0 < r) (s : State) (hy : s.1 ≤ yL P r) :
    afterCustomer P r s = (s.1 - 1, max s.2 (mcap P r)) := by
  have h := os_eq P r (s.1 - 1) s.2
  rw [ceilT_low hP hr _ (by omega)] at h
  ext
  · rfl
  · show orderStep P r (s.1 - 1) s.2 = max s.2 (mcap P r)
    have : ((orderStep P r (s.1 - 1) s.2 : ℕ) : ℤ) = ((max s.2 (mcap P r) : ℕ) : ℤ) := by
      rw [h]; push_cast; rfl
    exact_mod_cast this

lemma aI_low (hP : P.Standing) (hr : 0 < r) (s : State) (hy : s.1 + 1 ≤ yL P r) :
    afterItem P r s = (s.1 + 1, max (s.2 - 1) (mcap P r)) := by
  have h := os_eq P r (s.1 + 1) (s.2 - 1)
  rw [ceilT_low hP hr _ hy] at h
  ext
  · rfl
  · show orderStep P r (s.1 + 1) (s.2 - 1) = max (s.2 - 1) (mcap P r)
    have : ((orderStep P r (s.1 + 1) (s.2 - 1) : ℕ) : ℤ) = ((max (s.2 - 1) (mcap P r) : ℕ) : ℤ) := by
      rw [h]; push_cast; rfl
    exact_mod_cast this

lemma aC_high (hP : P.Standing) (hr : 0 < r) (s : State) (hy : yH P r ≤ s.1) :
    afterCustomer P r s = (s.1 - 1, s.2) := by
  have h := os_eq P r (s.1 - 1) s.2
  rw [ceilT_high hP hr _ (by omega)] at h
  ext
  · rfl
  · show orderStep P r (s.1 - 1) s.2 = s.2
    have : ((orderStep P r (s.1 - 1) s.2 : ℕ) : ℤ) = ((s.2 : ℕ) : ℤ) := by
      rw [h]; exact max_eq_left (by positivity)
    exact_mod_cast this

lemma aI_high (hP : P.Standing) (hr : 0 < r) (s : State) (hy : yH P r - 1 ≤ s.1 + 1) :
    afterItem P r s = (s.1 + 1, s.2 - 1) := by
  have h := os_eq P r (s.1 + 1) (s.2 - 1)
  rw [ceilT_high hP hr _ hy] at h
  ext
  · rfl
  · show orderStep P r (s.1 + 1) (s.2 - 1) = s.2 - 1
    have : ((orderStep P r (s.1 + 1) (s.2 - 1) : ℕ) : ℤ) = ((s.2 - 1 : ℕ) : ℤ) := by
      rw [h]; exact max_eq_left (by positivity)
    exact_mod_cast this

/-- Every state reaches `(yL - 1, m)`. -/
theorem reach (hP : P.Standing) (hr : 0 < r) :
    ∀ s : State, Relation.ReflTransGen (Step P r) s (yL P r - 1, mcap P r) := by
  have hβ := hP.1
  have hm1 := one_le_mcap hP hr
  set m := mcap P r
  set L := yL P r
  -- (C) from (y, m) with y ≤ L - 1 to (L - 1, m)
  have stepC : ∀ n : ℕ, ∀ y : ℤ, y = L - 1 - n →
      Relation.ReflTransGen (Step P r) (y, m) (L - 1, m) := by
    intro n
    induction n with
    | zero => intro y hy; simp at hy; rw [hy]
    | succ n ih =>
      intro y hy
      have h1 : afterItem P r (y, m) = (y + 1, m) := by
        rw [aI_low hP hr (y, m) (by simp; omega)]
        simp only
        congr 1
        omega
      refine Relation.ReflTransGen.head ?_ (ih (y + 1) (by push_cast at hy ⊢; omega))
      rw [← h1]; exact step_item hr hβ _ hm1
  -- (B) from (y, z) with y ≤ L - 1, z ≥ m, to (y, m)
  have stepB : ∀ n : ℕ, ∀ y : ℤ, ∀ z : ℕ, y ≤ L - 1 → z = m + n →
      Relation.ReflTransGen (Step P r) (y, z) (y, m) := by
    intro n
    induction n with
    | zero => intro y z _ hz; rw [hz]; rfl
    | succ n ih =>
      intro y z hy hz
      have h1 : afterItem P r (y, z) = (y + 1, z - 1) := by
        rw [aI_low hP hr (y, z) (by simp; omega)]
        simp only
        congr 1
        omega
      have h2 : afterCustomer P r (y + 1, z - 1) = (y, z - 1) := by
        rw [aC_low hP hr (y + 1, z - 1) (by simp; omega)]
        simp only
        congr 1
        · ring
        · omega
      have e1 : Step P r (y, z) (y + 1, z - 1) := by
        rw [← h1]; exact step_item hr hβ _ (by show 1 ≤ z; omega)
      have e2 : Step P r (y + 1, z - 1) (y, z - 1) := by
        rw [← h2]; exact step_cust hr hβ _
      exact Relation.ReflTransGen.head e1 (Relation.ReflTransGen.head e2 (ih y (z - 1) hy (by omega)))
  -- (A) from any state to one with y ≤ L - 1 and z ≥ m
  have stepA : ∀ n : ℕ, ∀ s : State, s.1 = L - 1 + n →
      ∃ s' : State, s'.1 ≤ L - 1 ∧ m ≤ s'.2 ∧ Relation.ReflTransGen (Step P r) s s' := by
    intro n
    induction n with
    | zero =>
      intro s hs
      refine ⟨afterCustomer P r s, ?_, ?_, Relation.ReflTransGen.single (step_cust hr hβ s)⟩
      · show s.1 - 1 ≤ L - 1; omega
      · rw [aC_low hP hr s (by omega)]; exact le_max_right _ _
    | succ n ih =>
      intro s hs
      obtain ⟨s', h1, h2, h3⟩ := ih (afterCustomer P r s) (by show s.1 - 1 = _; push_cast at hs; omega)
      exact ⟨s', h1, h2, Relation.ReflTransGen.head (step_cust hr hβ s) h3⟩
  intro s
  -- reduce to y ≥ L - 1 by first going up? No: if s.1 < L - 1, one customer step suffices.
  obtain ⟨s', h1, h2, h3⟩ : ∃ s' : State, s'.1 ≤ L - 1 ∧ m ≤ s'.2 ∧
      Relation.ReflTransGen (Step P r) s s' := by
    by_cases hs : L - 1 ≤ s.1
    · exact stepA (s.1 - (L - 1)).toNat s (by rw [Int.toNat_of_nonneg (by omega)]; ring)
    · push Not at hs
      refine ⟨afterCustomer P r s, ?_, ?_, Relation.ReflTransGen.single (step_cust hr hβ s)⟩
      · show s.1 - 1 ≤ L - 1; omega
      · rw [aC_low hP hr s (by omega)]; exact le_max_right _ _
  have hB := stepB (s'.2 - m) s'.1 s'.2 h1 (by omega)
  have hC := stepC (L - 1 - s'.1).toNat s'.1 (by rw [Int.toNat_of_nonneg (by omega)]; ring)
  exact h3.trans (hB.trans hC)


/-! ### Lyapunov function for the jump chain -/

variable (P r)

noncomputable def alph : ℝ := (r + P.β * mcap P r) / (P.β * mcap P r - r)
noncomputable def cst : ℝ := (alph P r + 1) * (mcap P r + 1)
noncomputable def Acoef : ℝ := 2 * (cst P r + 1)

noncomputable def Yp (y : ℤ) : ℝ :=
  alph P r * max ((yL P r - y : ℤ) : ℝ) 0 + max ((y - (yH P r - 1) : ℤ) : ℝ) 0
noncomputable def Zp (y : ℤ) (z : ℕ) : ℝ :=
  if y ≤ yL P r then (alph P r + 1) * ((mcap P r : ℝ) - min (z : ℝ) (mcap P r))
  else 2 * min (z : ℝ) (mcap P r)
noncomputable def Ap (z : ℕ) : ℝ := Acoef P r * max ((z : ℝ) - mcap P r) 0
noncomputable def Vly (s : State) : ℝ := Yp P r s.1 + Zp P r s.1 s.2 + Ap P r s.2

variable {P r}

lemma rate_lt_bm (hP : P.Standing) (hr : 0 < r) : r < P.β * mcap P r := by
  have h1 := mcap_ge hP hr
  have hβ := hP.1
  have hf := hP.2.2.1 r
  have : P.β * capM P r = r + P.β * P.f r := by
    unfold capM Xstar; field_simp
  have : P.β * capM P r ≤ P.β * mcap P r := mul_le_mul_of_nonneg_left h1 hβ.le
  nlinarith

lemma alph_ge (hP : P.Standing) (hr : 0 < r) : 1 ≤ alph P r := by
  have h := rate_lt_bm hP hr
  unfold alph
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma alph_eq (hP : P.Standing) (hr : 0 < r) :
    alph P r * (P.β * mcap P r - r) = r + P.β * mcap P r := by
  have h := rate_lt_bm hP hr
  unfold alph
  field_simp [show P.β * mcap P r - r ≠ 0 by linarith]

lemma Yp_dn (hP : P.Standing) (hr : 0 < r) (y : ℤ) : Yp P r (y - 1) ≤ Yp P r y + (alph P r + 1) := by
  have ha := alph_ge hP hr
  unfold Yp
  have h1 : max ((yL P r - (y - 1) : ℤ) : ℝ) 0 ≤ max ((yL P r - y : ℤ) : ℝ) 0 + 1 := by
    push_cast
    apply max_le
    · linarith [le_max_left ((yL P r : ℝ) - y) 0]
    · linarith [le_max_right ((yL P r : ℝ) - y) 0]
  have h2 : max ((y - 1 - (yH P r - 1) : ℤ) : ℝ) 0 ≤ max ((y - (yH P r - 1) : ℤ) : ℝ) 0 := by
    push_cast
    apply max_le_max _ le_rfl
    linarith
  nlinarith

lemma Yp_up (hP : P.Standing) (hr : 0 < r) (y : ℤ) : Yp P r (y + 1) ≤ Yp P r y + (alph P r + 1) := by
  have ha := alph_ge hP hr
  unfold Yp
  have h1 : max ((yL P r - (y + 1) : ℤ) : ℝ) 0 ≤ max ((yL P r - y : ℤ) : ℝ) 0 := by
    push_cast
    apply max_le_max _ le_rfl
    linarith
  have h2 : max ((y + 1 - (yH P r - 1) : ℤ) : ℝ) 0 ≤ max ((y - (yH P r - 1) : ℤ) : ℝ) 0 + 1 := by
    push_cast
    apply max_le
    · linarith [le_max_left ((y : ℝ) - (yH P r - 1)) 0]
    · linarith [le_max_right ((y : ℝ) - (yH P r - 1)) 0]
  nlinarith

lemma Yp_nonneg (hP : P.Standing) (hr : 0 < r) (y : ℤ) : 0 ≤ Yp P r y := by
  have ha := alph_ge hP hr
  unfold Yp
  have := le_max_right ((yL P r - y : ℤ) : ℝ) 0
  have := le_max_right ((y - (yH P r - 1) : ℤ) : ℝ) 0
  nlinarith

lemma Zp_bounds (hP : P.Standing) (hr : 0 < r) (y : ℤ) (z : ℕ) :
    0 ≤ Zp P r y z ∧ Zp P r y z ≤ (alph P r + 1) * mcap P r := by
  have ha := alph_ge hP hr
  have hm0 : (0 : ℝ) ≤ mcap P r := Nat.cast_nonneg _
  have h1 : min (z : ℝ) (mcap P r) ≤ mcap P r := min_le_right _ _
  have h2 : 0 ≤ min (z : ℝ) (mcap P r) := le_min (Nat.cast_nonneg _) hm0
  unfold Zp
  split_ifs
  · constructor <;> nlinarith
  · constructor <;> nlinarith

lemma Ap_nonneg (hP : P.Standing) (hr : 0 < r) (z : ℕ) : 0 ≤ Ap P r z := by
  have ha := alph_ge hP hr
  have : 0 ≤ cst P r := by unfold cst; positivity
  unfold Ap Acoef
  have := le_max_right ((z : ℝ) - mcap P r) 0
  positivity

lemma Vly_nonneg (hP : P.Standing) (hr : 0 < r) (s : State) : 0 ≤ Vly P r s := by
  unfold Vly
  linarith [Yp_nonneg hP hr s.1, (Zp_bounds hP hr s.1 s.2).1, Ap_nonneg hP hr s.2]

lemma aC_snd_real (hP : P.Standing) (hr : 0 < r) (s : State) :
    max (((afterCustomer P r s).2 : ℕ) : ℝ) (mcap P r) = max (s.2 : ℝ) (mcap P r) := by
  have h := os_eq P r (s.1 - 1) s.2
  have hc := ceilT_le hP hr (s.1 - 1)
  have hc0 := ceilT_nonneg (P := P) (r := r) (s.1 - 1)
  have : (((afterCustomer P r s).2 : ℕ) : ℤ) = max (s.2 : ℤ) ⌈truncTarget P r (s.1 - 1)⌉ := h
  have h' : (((afterCustomer P r s).2 : ℕ) : ℝ) =
      max (s.2 : ℝ) ((⌈truncTarget P r (s.1 - 1)⌉ : ℤ) : ℝ) := by
    have := congrArg (fun t : ℤ => (t : ℝ)) this
    push_cast at this
    exact this
  have hc' : ((⌈truncTarget P r (s.1 - 1)⌉ : ℤ) : ℝ) ≤ (mcap P r : ℝ) := by exact_mod_cast hc
  rw [h', max_assoc, max_eq_right hc']

lemma aI_snd_real (hP : P.Standing) (hr : 0 < r) (s : State) (hz : 1 ≤ s.2) :
    max (((afterItem P r s).2 : ℕ) : ℝ) (mcap P r) = max ((s.2 : ℝ) - 1) (mcap P r) := by
  have h := os_eq P r (s.1 + 1) (s.2 - 1)
  have hc := ceilT_le hP hr (s.1 + 1)
  have this : (((afterItem P r s).2 : ℕ) : ℤ) = max ((s.2 - 1 : ℕ) : ℤ) ⌈truncTarget P r (s.1 + 1)⌉ := h
  have h' : (((afterItem P r s).2 : ℕ) : ℝ) =
      max ((s.2 : ℝ) - 1) ((⌈truncTarget P r (s.1 + 1)⌉ : ℤ) : ℝ) := by
    have := congrArg (fun t : ℤ => (t : ℝ)) this
    push_cast [Nat.cast_sub hz] at this
    exact this
  have hc' : ((⌈truncTarget P r (s.1 + 1)⌉ : ℤ) : ℝ) ≤ (mcap P r : ℝ) := by exact_mod_cast hc
  rw [h', max_assoc, max_eq_right hc']

lemma Ap_eq (z : ℝ) : Acoef P r * max (z - mcap P r) 0 = Acoef P r * (max z (mcap P r) - mcap P r) := by
  congr 1
  rcases le_total z (mcap P r) with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]

lemma Ap_cust (hP : P.Standing) (hr : 0 < r) (s : State) :
    Ap P r (afterCustomer P r s).2 = Ap P r s.2 := by
  unfold Ap
  rw [Ap_eq, Ap_eq, aC_snd_real hP hr]

lemma Ap_item (hP : P.Standing) (hr : 0 < r) (s : State) (hz : 1 ≤ s.2) :
    Ap P r (afterItem P r s).2 = Ap P r s.2 - (if mcap P r < s.2 then Acoef P r else 0) := by
  unfold Ap
  rw [Ap_eq, Ap_eq, aI_snd_real hP hr s hz]
  split_ifs with h
  · have : (mcap P r : ℝ) + 1 ≤ s.2 := by exact_mod_cast h
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · push Not at h
    have : (s.2 : ℝ) ≤ mcap P r := by exact_mod_cast h
    rw [max_eq_right (by linarith), max_eq_right this]; ring

lemma V_cust_le (hP : P.Standing) (hr : 0 < r) (s : State) :
    Vly P r (afterCustomer P r s) ≤ Vly P r s + cst P r := by
  unfold Vly cst
  have h1 := Yp_dn hP hr s.1
  have h2 := Zp_bounds hP hr (afterCustomer P r s).1 (afterCustomer P r s).2
  have h3 := Zp_bounds hP hr s.1 s.2
  have h4 := Ap_cust hP hr s
  have e : (afterCustomer P r s).1 = s.1 - 1 := rfl
  rw [e] at h2 ⊢
  rw [h4]
  have ha := alph_ge hP hr
  nlinarith

lemma V_item_le (hP : P.Standing) (hr : 0 < r) (s : State) (hz : 1 ≤ s.2) :
    Vly P r (afterItem P r s) ≤ Vly P r s + cst P r - (if mcap P r < s.2 then Acoef P r else 0) := by
  unfold Vly cst
  have h1 := Yp_up hP hr s.1
  have h2 := Zp_bounds hP hr (afterItem P r s).1 (afterItem P r s).2
  have h3 := Zp_bounds hP hr s.1 s.2
  have h4 := Ap_item hP hr s hz
  have e : (afterItem P r s).1 = s.1 + 1 := rfl
  rw [e] at h2 ⊢
  rw [h4]
  have ha := alph_ge hP hr
  nlinarith


lemma Vly_low (hP : P.Standing) (hr : 0 < r) (y : ℤ) (z : ℕ) (hy : y ≤ yL P r) (hz : z ≤ mcap P r) :
    Vly P r (y, z) = alph P r * ((yL P r : ℝ) - y) + (alph P r + 1) * ((mcap P r : ℝ) - z) := by
  have hLH := yL_lt_yH hP hr
  have hz' : (z : ℝ) ≤ mcap P r := by exact_mod_cast hz
  have hyr : (y : ℝ) ≤ yL P r := by exact_mod_cast hy
  have hLHr : (yL P r : ℝ) < (yH P r : ℝ) - 1 := by
    have : ((yL P r : ℤ) : ℝ) < ((yH P r - 1 : ℤ) : ℝ) := by exact_mod_cast hLH
    push_cast at this; linarith
  have e1 : max (((yL P r - y : ℤ)) : ℝ) 0 = (yL P r : ℝ) - y := by
    push_cast; exact max_eq_left (by linarith)
  have e2 : max (((y - (yH P r - 1)) : ℤ) : ℝ) 0 = 0 := by
    push_cast; exact max_eq_right (by linarith)
  unfold Vly Yp Zp Ap
  simp only
  rw [if_pos hy, e1, e2, min_eq_left hz', max_eq_right (by linarith)]
  ring

lemma Vly_high (hP : P.Standing) (hr : 0 < r) (y : ℤ) (z : ℕ) (hy : yH P r - 1 ≤ y)
    (hz : z ≤ mcap P r) :
    Vly P r (y, z) = ((y : ℝ) - (yH P r - 1)) + 2 * (z : ℝ) := by
  have hLH := yL_lt_yH hP hr
  have hz' : (z : ℝ) ≤ mcap P r := by exact_mod_cast hz
  have hy' : ((yH P r - 1 : ℤ) : ℝ) ≤ y := by exact_mod_cast hy
  have hLH' : (yL P r : ℝ) < ((yH P r - 1 : ℤ) : ℝ) := by exact_mod_cast hLH
  unfold Vly Yp Zp Ap
  simp only
  rw [if_neg (by omega), max_eq_right (by push_cast at hy' hLH' ⊢; linarith),
    max_eq_left (by push_cast at hy' ⊢; linarith),
    min_eq_left hz', max_eq_right (by linarith)]
  push_cast; ring

noncomputable def Fset (P : Params) (r : ℝ) : Finset State :=
  (Finset.Icc (yL P r) (yH P r - 1)) ×ˢ (Finset.range (mcap P r + 1))

theorem drift (hP : P.Standing) (hr : 0 < r) (s : State) :
    r * Vly P r (afterCustomer P r s) + P.β * (s.2 : ℝ) * Vly P r (afterItem P r s) ≤
      (r + P.β * (s.2 : ℝ)) * (Vly P r s - 1 + (if s ∈ Fset P r then cst P r + 1 else 0)) := by
  have hβ := hP.1
  have hbm := rate_lt_bm hP hr
  have ha := alph_ge hP hr
  have hc : 0 ≤ cst P r := by unfold cst; positivity
  have hz0 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
  have hext : 0 ≤ (if s ∈ Fset P r then cst P r + 1 else 0) := by split_ifs <;> linarith
  have hrz : 0 < r + P.β * (s.2 : ℝ) := by positivity
  by_cases hzm : mcap P r < s.2
  · -- many items in transit: the item rate dominates
    have hz1 : 1 ≤ s.2 := by omega
    have h1 := V_cust_le hP hr s
    have h2 := V_item_le hP hr s hz1
    rw [if_pos hzm] at h2
    have hzr : (mcap P r : ℝ) < s.2 := by exact_mod_cast hzm
    have hbz : r < P.β * s.2 := lt_trans hbm (by nlinarith)
    have hA : Acoef P r = 2 * (cst P r + 1) := rfl
    have hbz0 : 0 ≤ P.β * (s.2 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hr.le
    have := mul_le_mul_of_nonneg_left h2 hbz0
    nlinarith
  push Not at hzm
  by_cases hF : s ∈ Fset P r
  · rw [if_pos hF]
    have h1 := V_cust_le hP hr s
    have hbz0 : 0 ≤ P.β * (s.2 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hr.le
    rcases Nat.eq_zero_or_pos s.2 with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      nlinarith
    · have h2 := V_item_le hP hr s h0
      rw [if_neg (by omega)] at h2
      have := mul_le_mul_of_nonneg_left h2 hbz0
      nlinarith
  · rw [if_neg hF]
    have hLH := yL_lt_yH hP hr
    have hFc : ¬ (yL P r ≤ s.1 ∧ s.1 ≤ yH P r - 1) := by
      intro h
      apply hF
      simp only [Fset, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      exact ⟨h, by omega⟩
    rcases lt_or_ge s.1 (yL P r) with hlo | hhi
    · -- low region
      have eC := aC_low hP hr s (by omega)
      have eI := aI_low hP hr s (by omega)
      rw [eC, eI, max_eq_right hzm, max_eq_right (by omega),
        Vly_low hP hr _ _ (by omega) le_rfl, Vly_low hP hr _ _ (by omega) le_rfl]
      have eS : Vly P r s = alph P r * ((yL P r : ℝ) - s.1) + (alph P r + 1) * ((mcap P r : ℝ) - s.2) := by
        have := Vly_low hP hr s.1 s.2 (by omega) hzm
        simpa using this
      rw [eS]
      have hae := alph_eq hP hr
      push_cast
      rcases eq_or_lt_of_le hzm with heq | hlt
      · have : (s.2 : ℝ) = mcap P r := by exact_mod_cast heq
        rw [this]
        nlinarith
      · have : (s.2 : ℝ) + 1 ≤ mcap P r := by exact_mod_cast hlt
        have hbz0 : 0 ≤ P.β * (s.2 : ℝ) := by positivity
        have k1 : 0 ≤ (alph P r + 1) * ((mcap P r : ℝ) - s.2) - 1 - alph P r := by nlinarith
        have k2 := mul_nonneg hrz.le k1
        have k3 := mul_nonneg hbz0 (by linarith : (0 : ℝ) ≤ alph P r)
        nlinarith
    · -- high region
      have hhi' : yH P r ≤ s.1 := by
        by_contra h; push Not at h; exact hFc ⟨hhi, by omega⟩
      have eC := aC_high hP hr s hhi'
      have eI := aI_high hP hr s (by omega)
      rw [eC, eI, Vly_high hP hr _ _ (by omega) hzm, Vly_high hP hr _ _ (by omega) (by omega)]
      have eS : Vly P r s = ((s.1 : ℝ) - (yH P r - 1)) + 2 * (s.2 : ℝ) := by
        have := Vly_high hP hr s.1 s.2 (by omega) hzm
        simpa using this
      rw [eS]
      rcases Nat.eq_zero_or_pos s.2 with h0 | h0
      · rw [h0]; push_cast; nlinarith
      · push_cast [Nat.cast_sub h0]
        nlinarith

/-! ### The jump chain -/

noncomputable def Jk (P : Params) (r : ℝ) (s s' : State) : ℝ := rate P r s s' / exitRate P r s

lemma exit_pos (hP : P.Standing) (hr : 0 < r) (s : State) : 0 < exitRate P r s := by
  unfold exitRate; have := hP.1; positivity

lemma rate_tsum (P : Params) (r : ℝ) (s : State) : ∑' s', rate P r s s' = exitRate P r s := by
  have := row_tsum P r s (fun _ => 1)
  simp only [mul_one] at this
  rw [this, exitRate]

lemma Jk_kern (hP : P.Standing) (hr : 0 < r) : Kern (Jk P r) := by
  refine ⟨fun x y => div_nonneg (rate_nonneg P r hr hP.1 x y) (exit_pos hP hr x).le,
    fun x => ?_, fun x => ?_⟩
  · refine ((row_summable P r x (fun _ => 1)).div_const (exitRate P r x)).congr (fun y => ?_)
    simp [Jk]
  · simp only [Jk]
    rw [tsum_div_const, rate_tsum]
    exact div_self (exit_pos hP hr x).ne'

lemma Jk_V (hP : P.Standing) (hr : 0 < r) (s : State) :
    Summable (fun s' => Jk P r s s' * Vly P r s') ∧
    ∑' s', Jk P r s s' * Vly P r s' =
      (r * Vly P r (afterCustomer P r s) + P.β * (s.2 : ℝ) * Vly P r (afterItem P r s)) /
        exitRate P r s := by
  have e : (fun s' => Jk P r s s' * Vly P r s') = fun s' => rate P r s s' * Vly P r s' / exitRate P r s := by
    funext s'; simp only [Jk]; ring
  rw [e]
  exact ⟨(row_summable P r s _).div_const _, by rw [tsum_div_const, row_tsum]⟩

/-- CTMC stationary laws ↦ stationary laws of the jump chain. -/
lemma to_jump (hP : P.Standing) (hr : 0 < r) (p : State → ℝ) (hp : IsStationary P r p) :
    0 < ∑' s, p s * exitRate P r s ∧
    Stat (Jk P r) (fun s => p s * exitRate P r s / ∑' s, p s * exitRate P r s) := by
  obtain ⟨p0, ps, p1, pxs, pb⟩ := hp
  set Z := ∑' s, p s * exitRate P r s with hZ
  have hZ : r ≤ Z := by
    have := Summable.tsum_le_tsum (fun s => (by
      have : r ≤ exitRate P r s := by
        unfold exitRate; exact le_add_of_nonneg_right (by have := hP.1; positivity)
      nlinarith [p0 s] : p s * r ≤ p s * exitRate P r s)) (ps.mul_right r) pxs
    rw [tsum_mul_right, p1, one_mul] at this
    exact this
  have hZpos : 0 < Z := lt_of_lt_of_le hr hZ
  refine ⟨hZpos, fun s => div_nonneg (mul_nonneg (p0 s) (exit_pos hP hr s).le) hZpos.le,
    pxs.div_const _, by rw [tsum_div_const]; exact div_self hZpos.ne', fun s' => ?_⟩
  have e : (fun s => p s * exitRate P r s / Z * Jk P r s s') = fun s => p s * rate P r s s' / Z := by
    funext s; simp only [Jk]; field_simp [(exit_pos hP hr s).ne']
  rw [e, tsum_div_const, pb s']

lemma reachJ (hP : P.Standing) (hr : 0 < r) (s : State) :
    Relation.ReflTransGen (fun a b => 0 < Jk P r a b) s (yL P r - 1, mcap P r) :=
  Relation.ReflTransGen.mono (fun a b h => div_pos h (exit_pos hP hr a)) _ _ (reach hP hr s)

end Fixed

end GBSStab

open GBSMarkov GBSStab

theorem solution (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ s₀ : State, ∀ s : State, Relation.ReflTransGen (Step P r) s s₀) ∧
    (∃ r₀ : ℝ, ∀ r ≥ r₀, ∃! p : State → ℝ, IsStationary P r p) := by
  refine ⟨fun r hr => ⟨_, reach hP hr⟩, ⟨1, fun r hr1 => ?_⟩⟩
  have hr : 0 < r := lt_of_lt_of_le one_pos hr1
  have hK := Jk_kern hP hr
  -- existence through the jump chain
  obtain ⟨π, π0, πs, π1, πb⟩ := exists_stat hK ((0 : ℤ), (0 : ℕ)) (Vly P r) (Vly_nonneg hP hr)
    (Fset P r) (cst P r + 1) (by have := alph_ge hP hr; unfold cst; positivity)
    (fun s => (Jk_V hP hr s).1) (fun s => by
      rw [(Jk_V hP hr s).2, div_le_iff₀ (exit_pos hP hr s)]
      have := drift hP hr s
      unfold exitRate
      linarith)
  have hex : ∀ s, 0 < exitRate P r s := exit_pos hP hr
  have hrle : ∀ s, r ≤ exitRate P r s := fun s => by
    unfold exitRate; exact le_add_of_nonneg_right (by have := hP.1; positivity)
  have hs1 : Summable (fun s => π s / exitRate P r s) :=
    Summable.of_nonneg_of_le (fun s => div_nonneg (π0 s) (hex s).le)
      (fun s => div_le_div_of_nonneg_left (π0 s) hr (hrle s)) (πs.div_const r)
  set W := ∑' s, π s / exitRate P r s with hW
  have hWpos : 0 < W := by
    by_contra hcon
    push Not at hcon
    have hW0 : W = 0 := le_antisymm hcon (tsum_nonneg (fun s => div_nonneg (π0 s) (hex s).le))
    have hall := (hasSum_zero_iff_of_nonneg (fun s => div_nonneg (π0 s) (hex s).le)).mp
      (by rw [← hW0]; exact hs1.hasSum)
    have : ∀ s, π s = 0 := by
      intro s
      have := congrFun hall s
      simp only [Pi.zero_apply] at this
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h (hex s).ne'
    simp [this] at π1
  refine ⟨fun s => π s / exitRate P r s / W, ?_, ?_⟩
  · refine ⟨fun s => div_nonneg (div_nonneg (π0 s) (hex s).le) hWpos.le, hs1.div_const _,
      by rw [tsum_div_const]; exact div_self hWpos.ne', ?_, fun s' => ?_⟩
    · have : (fun s => π s / exitRate P r s / W * exitRate P r s) = fun s => π s / W := by
        funext s; field_simp [(hex s).ne']
      rw [this]; exact πs.div_const _
    · have : (fun s => π s / exitRate P r s / W * rate P r s s') = fun s => π s * Jk P r s s' / W := by
        funext s; simp only [Jk]; field_simp [(hex s).ne']
      rw [this, tsum_div_const, πb s']
      field_simp [(hex s').ne']
  -- uniqueness
  intro p' hp'
  have hp : IsStationary P r (fun s => π s / exitRate P r s / W) := by
    refine ⟨fun s => div_nonneg (div_nonneg (π0 s) (hex s).le) hWpos.le, hs1.div_const _,
      by rw [tsum_div_const]; exact div_self hWpos.ne', ?_, fun s' => ?_⟩
    · have : (fun s => π s / exitRate P r s / W * exitRate P r s) = fun s => π s / W := by
        funext s; field_simp [(hex s).ne']
      rw [this]; exact πs.div_const _
    · have : (fun s => π s / exitRate P r s / W * rate P r s s') = fun s => π s * Jk P r s s' / W := by
        funext s; simp only [Jk]; field_simp [(hex s).ne']
      rw [this, tsum_div_const, πb s']
      field_simp [(hex s').ne']
  set p := fun s => π s / exitRate P r s / W with hpdef
  obtain ⟨Zp, hJp⟩ := to_jump hP hr p hp
  obtain ⟨Zq, hJq⟩ := to_jump hP hr p' hp'
  have heq := unique_stat hK _ (reachJ hP hr) _ _ hJp hJq
  set A := ∑' s, p s * exitRate P r s
  set B := ∑' s, p' s * exitRate P r s
  have hpt : ∀ s, p' s = p s * (B / A) := by
    intro s
    have := congrFun heq s
    field_simp [(hex s).ne', Zp.ne', Zq.ne'] at this
    field_simp [Zp.ne']
    nlinarith [hex s]
  have hsum1 : ∑' s, p' s = 1 := hp'.2.2.1
  have hsum2 : ∑' s, p s = 1 := hp.2.2.1
  have hBA : B / A = 1 := by
    have : ∑' s, p' s = (∑' s, p s) * (B / A) := by
      rw [← tsum_mul_right]; exact tsum_congr hpt
    rw [hsum1, hsum2, one_mul] at this
    exact this.symm
  funext s
  rw [hpt s, hBA, mul_one]
