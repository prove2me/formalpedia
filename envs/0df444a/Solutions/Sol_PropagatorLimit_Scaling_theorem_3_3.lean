-- Prove2me | solution 1 for PropagatorLimit.Scaling.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:10:40.168052+00:00
-- url     : https://prove2.me/submissions/c702f581-9f60-4994-b182-55961da66a2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Model
import Theorems.Thm_PropagatorLimit_Scaling_explicit_solution
import Theorems.Thm_PropagatorLimit_Scaling_rescaled_convergence

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling.Thm33Red

lemma recD (x : ℕ → ℝ) (q β Δ K : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hβ : 0 ≤ β)
    (hΔ : 0 ≤ Δ) : ∀ n : ℕ,
    (∀ k < n, |∑ m ∈ Finset.Icc 1 k, Real.exp (β * (m * Δ)) * x m| ≤ K) →
    |∑ m ∈ Finset.Icc 1 n, q ^ (n - m) * x m -
        Real.exp (-(β * (n * Δ))) * ∑ m ∈ Finset.Icc 1 n, Real.exp (β * (m * Δ)) * x m|
      ≤ n * (|q - Real.exp (-(β * Δ))| * K) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hK
    have hKn := hK n (Nat.lt_succ_self n)
    have ih' := ih (fun k hk => hK k (Nat.lt_succ_of_lt hk))
    set U := ∑ m ∈ Finset.Icc 1 n, q ^ (n - m) * x m with hUdef
    set B := ∑ m ∈ Finset.Icc 1 n, Real.exp (β * (m * Δ)) * x m with hBdef
    have hU : ∑ m ∈ Finset.Icc 1 (n+1), q ^ (n + 1 - m) * x m = q * U + x (n+1) := by
      rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul, hUdef,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]; ring
    have hB : ∑ m ∈ Finset.Icc 1 (n+1), Real.exp (β * (m * Δ)) * x m
        = B + Real.exp (β * (((n+1 : ℕ) : ℝ) * Δ)) * x (n+1) := by
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hU, hB]
    have e1 : Real.exp (-(β * (((n+1 : ℕ) : ℝ) * Δ))) *
        Real.exp (β * (((n+1 : ℕ) : ℝ) * Δ)) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(β * (((n+1 : ℕ) : ℝ) * Δ))) =
        Real.exp (-(β * Δ)) * Real.exp (-(β * ((n : ℝ) * Δ))) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have key : q * U + x (n+1) - Real.exp (-(β * (((n+1 : ℕ) : ℝ) * Δ))) *
        (B + Real.exp (β * (((n+1 : ℕ) : ℝ) * Δ)) * x (n+1)) =
        q * (U - Real.exp (-(β * ((n : ℝ) * Δ))) * B) +
          (q - Real.exp (-(β * Δ))) * (Real.exp (-(β * ((n : ℝ) * Δ))) * B) := by
      linear_combination (-x (n+1)) * e1 - B * e2
    rw [key]
    have hexp : |Real.exp (-(β * ((n : ℝ) * Δ)))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg hβ (mul_nonneg (Nat.cast_nonneg n) hΔ)
      linarith
    have hK0 : 0 ≤ K := (abs_nonneg _).trans hKn
    calc _ ≤ |q * (U - Real.exp (-(β * ((n : ℝ) * Δ))) * B)| +
          |(q - Real.exp (-(β * Δ))) * (Real.exp (-(β * ((n : ℝ) * Δ))) * B)| := abs_add_le _ _
      _ = q * |U - Real.exp (-(β * ((n : ℝ) * Δ))) * B| +
          |q - Real.exp (-(β * Δ))| * (|Real.exp (-(β * ((n : ℝ) * Δ)))| * |B|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0]
      _ ≤ 1 * (n * (|q - Real.exp (-(β * Δ))| * K)) +
          |q - Real.exp (-(β * Δ))| * (1 * K) := by
          gcongr
      _ = _ := by push_cast; ring

lemma exp_neg_lip (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · have h1 := Real.add_one_le_exp (-(b - a))
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h5 := Real.exp_pos (-a)
    rw [abs_of_nonneg (by rw [h2]; nlinarith), abs_of_nonpos (by linarith), h2]
    nlinarith
  · have h1 := Real.add_one_le_exp (-(a - b))
    have h2 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : Real.exp (-(a - b)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h5 := Real.exp_pos (-b)
    rw [abs_of_nonpos (by rw [h2]; nlinarith), abs_of_nonneg (by linarith), h2]
    nlinarith

/-- The rescaled sum of `rescaled_convergence`. -/
noncomputable def Sres {Ω : Type} (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ)
    (N : ℕ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  Real.sqrt (dt T N) * ∑ m ∈ Finset.Icc 1 (nsteps T N t),
    Real.exp (beta * (m * dt T N)) * g (incr T N F m ω / Real.sqrt (dt T N))

lemma nsteps_grid (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    nsteps T N (grid T N k) = k := by
  unfold nsteps grid dt
  have hT' : (0 : ℝ) < T := hT
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((((k : ℝ≥0) * T / N : ℝ≥0)) : ℝ) / ((T : ℝ) / N) = k := by
    push_cast; field_simp
  rw [this, Nat.ceil_natCast, min_eq_right hk]

lemma grid_le (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) : grid T N k ≤ T := by
  unfold grid
  rw [← NNReal.coe_le_coe]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  push_cast
  rw [div_le_iff₀ hN']
  nlinarith [T.2]

lemma estE {Ω : Type} (beta : ℝ) (hbeta : 0 < beta) (T : ℝ≥0) (hT : 0 < T) (g : ℝ → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (N : ℕ) (hN : 1 ≤ N) (hsmall : beta * dt T N ≤ 1) (ω : Ω) (K : ℝ)
    (hK : ∀ k ≤ N, |Sres beta T g F N ω (grid T N k)| ≤ K) (t : ℝ≥0) (ht : t ≤ T) :
    |INpath beta T g F N ω t - Real.exp (-(beta * t)) * Sres beta T g F N ω t|
      ≤ ((beta ^ 2 * (T : ℝ) ^ 2 + beta * T) / N) * K := by
  have hT' : (0 : ℝ) < T := hT
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set Δ := dt T N with hΔdef
  have hΔ : 0 < Δ := div_pos hT' hN'
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (Nat.zero_le _))
  set x : ℕ → ℝ := fun m => Real.sqrt Δ * g (incr T N F m ω / Real.sqrt Δ) with hx
  have hS : ∀ s, Sres beta T g F N ω s =
      ∑ m ∈ Finset.Icc 1 (nsteps T N s), Real.exp (beta * (m * Δ)) * x m := by
    intro s; unfold Sres; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  set n := nsteps T N t with hndef
  have hIN : INpath beta T g F N ω t = ∑ m ∈ Finset.Icc 1 n, (1 - beta * Δ) ^ (n - m) * x m :=
    (explicit_solution beta T g F N n ω).1
  -- properties of n
  have htΔ : (t : ℝ) / Δ ≤ N := by
    rw [div_le_iff₀ hΔ, hΔdef, dt]; field_simp; exact_mod_cast ht
  have hnc : n = ⌈(t : ℝ) / Δ⌉₊ := by
    rw [hndef, nsteps, ← hΔdef]; exact min_eq_right (Nat.ceil_le.mpr htΔ)
  have hnN : n ≤ N := min_le_left _ _
  have hn1 : (t : ℝ) ≤ n * Δ := by
    have : (t : ℝ) / Δ ≤ n := by rw [hnc]; exact Nat.le_ceil _
    rwa [div_le_iff₀ hΔ] at this
  have hn2 : (n : ℝ) * Δ ≤ t + Δ := by
    have : (n : ℝ) < (t : ℝ) / Δ + 1 := by
      rw [hnc]; exact Nat.ceil_lt_add_one (div_nonneg t.2 hΔ.le)
    have h' : (n : ℝ) * Δ < ((t : ℝ) / Δ + 1) * Δ := mul_lt_mul_of_pos_right this hΔ
    rw [add_mul, div_mul_cancel₀ _ hΔ.ne'] at h'; linarith
  have hq0 : 0 ≤ 1 - beta * Δ := by linarith
  have hq1 : 1 - beta * Δ ≤ 1 := by nlinarith
  have hrec := recD x (1 - beta * Δ) beta Δ K hq0 hq1 hbeta.le hΔ.le n
    (fun k hk => by
      have := hK k (by omega)
      rwa [hS, nsteps_grid T hT N hN k (by omega)] at this)
  have hqp : |1 - beta * Δ - Real.exp (-(beta * Δ))| ≤ (beta * Δ) ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -(beta * Δ))
      (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hsmall)
    have e : 1 - beta * Δ - Real.exp (-(beta * Δ)) = -(Real.exp (-(beta * Δ)) - 1 - -(beta * Δ)) := by ring
    rw [e, abs_neg]; convert h using 1; ring
  have hB : |∑ m ∈ Finset.Icc 1 n, Real.exp (beta * (m * Δ)) * x m| ≤ K := by
    have := hK n hnN; rwa [hS, nsteps_grid T hT N hN n hnN] at this
  have hexpd : |Real.exp (-(beta * (n * Δ))) - Real.exp (-(beta * t))| ≤ beta * Δ := by
    refine (exp_neg_lip _ _ (by positivity) (by positivity)).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos hbeta]
    apply mul_le_mul_of_nonneg_left _ hbeta.le
    rw [abs_le]; constructor <;> linarith
  rw [hIN, hS t, ← hndef]
  set B := ∑ m ∈ Finset.Icc 1 n, Real.exp (beta * (m * Δ)) * x m
  set U := ∑ m ∈ Finset.Icc 1 n, (1 - beta * Δ) ^ (n - m) * x m
  have hsplit : U - Real.exp (-(beta * t)) * B = (U - Real.exp (-(beta * (n * Δ))) * B) +
      (Real.exp (-(beta * (n * Δ))) - Real.exp (-(beta * t))) * B := by ring
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hfin : (N : ℝ) * (beta * Δ) ^ 2 + beta * Δ = (beta ^ 2 * (T : ℝ) ^ 2 + beta * T) / N := by
    rw [hΔdef, dt]; field_simp
  rw [hsplit, ← hfin]
  calc _ ≤ |U - Real.exp (-(beta * (n * Δ))) * B| +
        |(Real.exp (-(beta * (n * Δ))) - Real.exp (-(beta * t))) * B| := abs_add_le _ _
    _ ≤ n * ((beta * Δ) ^ 2 * K) + beta * Δ * K := by
        rw [abs_mul]
        gcongr
        · exact hrec.trans (by gcongr)
    _ ≤ N * ((beta * Δ) ^ 2 * K) + beta * Δ * K := by gcongr
    _ = _ := by ring

end PropagatorLimit.Scaling.Thm33Red

namespace PropagatorLimit.Scaling.Thm33Red

lemma isTest_of (T : ℝ≥0) (φ : (ℝ≥0 → ℝ) → ℝ) (C c : ℝ) (hC : ∀ x, |φ x| ≤ C) (hc : 0 ≤ c)
    (hL : ∀ x y : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ r) →
      |φ x - φ y| ≤ c * r) : IsTestFunctional T φ := by
  refine ⟨⟨C, hC⟩, ⟨(c + 1).toNNReal, fun x y => ?_⟩⟩
  by_cases htop : supEDist T x y = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · simp; linarith
  · set r := (supEDist T x y).toReal
    have hr : ∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ r := by
      intro t ht
      have h1 : edist (x t) (y t) ≤ supEDist T x y :=
        le_iSup₂ (f := fun t (_ : t ∈ Set.Icc 0 T) => edist (x t) (y t)) t ht
      rw [edist_dist, Real.dist_eq] at h1
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
    have h := hL x y r ENNReal.toReal_nonneg hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    rw [edist_dist, Real.dist_eq]
    calc ENNReal.ofReal |φ x - φ y| ≤ ENNReal.ofReal ((c + 1) * r) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ((c + 1).toNNReal : ℝ≥0∞) * supEDist T x y := by
          rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal htop]; rfl

lemma test_bound {T : ℝ≥0} {f : (ℝ≥0 → ℝ) → ℝ} (hf : IsTestFunctional T f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r →
      (∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ r) → |f x - f y| ≤ L * r := by
  obtain ⟨_, L, hL⟩ := hf
  refine ⟨L, NNReal.coe_nonneg L, fun x y r hr h => ?_⟩
  have hs : supEDist T x y ≤ ENNReal.ofReal r := iSup₂_le fun t ht => by
    rw [edist_dist, Real.dist_eq]; exact ENNReal.ofReal_le_ofReal (h t ht)
  have h2 : edist (f x) (f y) ≤ (L : ℝ≥0∞) * ENNReal.ofReal r := (hL x y).trans (by gcongr)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)] at h2
  have := (edist_le_ofReal (mul_nonneg (NNReal.coe_nonneg L) hr)).mp h2
  rwa [Real.dist_eq] at this

lemma INdisc_meas {Ω : Type} [MeasurableSpace Ω] (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ)
    (hg : Continuous g) (F : ℝ≥0 → Ω → ℝ) (hF : ∀ t, Measurable (F t)) (N : ℕ) :
    ∀ n, Measurable (INdisc beta T g F N n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable (fun ω => INdisc beta T g F N n ω - beta * INdisc beta T g F N n ω * dt T N +
        gN T N g (incr T N F (n + 1) ω))
    unfold gN incr
    exact (ih.sub ((measurable_const.mul ih).mul measurable_const)).add
      (measurable_const.mul (hg.measurable.comp
        (((hF _).sub (hF _)).div_const _)))

lemma meas_comp {Ω : Type} [MeasurableSpace Ω] (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ)
    (hg : Continuous g) (F : ℝ≥0 → Ω → ℝ) (hF : ∀ t, Measurable (F t)) (N : ℕ)
    {f : (ℝ≥0 → ℝ) → ℝ} (hf : IsTestFunctional T f) :
    Measurable (fun ω => f (INpath beta T g F N ω)) := by
  obtain ⟨L, hL0, hL⟩ := test_bound hf
  let V : Ω → (Fin (N + 1) → ℝ) := fun ω i => INdisc beta T g F N i ω
  have hV : Measurable V := measurable_pi_lambda _ (fun i => INdisc_meas beta T g hg F hF N i)
  let Φ : (Fin (N + 1) → ℝ) → ℝ := fun v =>
    f (fun t => v ⟨nsteps T N t, Nat.lt_succ_of_le (min_le_left _ _)⟩)
  have hΦ : Continuous Φ := by
    apply (LipschitzWith.of_dist_le_mul (K := L.toNNReal) ?_).continuous
    intro v w
    rw [Real.dist_eq, Real.coe_toNNReal _ hL0]
    apply hL _ _ _ dist_nonneg
    intro t _
    rw [← Real.dist_eq]
    exact dist_le_pi_dist v w _
  exact hΦ.measurable.comp hV

/-- The tightness functional `x ↦ sup_{t ∈ [0,T]} min(1, |x_t| / K)`. -/
noncomputable def hK (T : ℝ≥0) (K : ℝ) (x : ℝ≥0 → ℝ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ≥0) T, min 1 (|x t| / K)

lemma hK_bdd (T : ℝ≥0) (K : ℝ) (x : ℝ≥0 → ℝ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ≥0) T => min 1 (|x t| / K)) :=
  ⟨1, by rintro _ ⟨t, rfl⟩; exact min_le_left _ _⟩

instance (T : ℝ≥0) : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩

lemma le_hK (T : ℝ≥0) (K : ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : t ∈ Set.Icc 0 T) :
    min 1 (|x t| / K) ≤ hK T K x :=
  le_ciSup (f := fun t : Set.Icc (0 : ℝ≥0) T => min 1 (|x t| / K)) (hK_bdd T K x) ⟨t, ht⟩

lemma hK_le_one (T : ℝ≥0) (K : ℝ) (x : ℝ≥0 → ℝ) : hK T K x ≤ 1 :=
  ciSup_le fun _ => min_le_left _ _

lemma hK_nonneg (T : ℝ≥0) (K : ℝ) (hK0 : 0 < K) (x : ℝ≥0 → ℝ) : 0 ≤ hK T K x :=
  (le_min zero_le_one (div_nonneg (abs_nonneg _) hK0.le)).trans
    (le_hK T K x 0 ⟨le_rfl, bot_le⟩)

lemma hK_le (T : ℝ≥0) (K : ℝ) (hK0 : 0 < K) (x : ℝ≥0 → ℝ) (B : ℝ)
    (hB : ∀ t ∈ Set.Icc 0 T, |x t| ≤ B) : hK T K x ≤ B / K :=
  ciSup_le fun t => (min_le_right _ _).trans (div_le_div_of_nonneg_right (hB t t.2) hK0.le)

lemma hK_test (T : ℝ≥0) (K : ℝ) (hK0 : 0 < K) : IsTestFunctional T (hK T K) := by
  refine isTest_of T (hK T K) 1 (1 / K) (fun x => ?_) (by positivity) ?_
  · rw [abs_of_nonneg (hK_nonneg T K hK0 x)]; exact hK_le_one T K x
  · intro x y r hr h
    have key : ∀ x y : ℝ≥0 → ℝ, (∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ r) →
        hK T K x ≤ hK T K y + 1 / K * r := by
      intro x y h
      apply ciSup_le
      intro t
      have h1 : |x t| / K ≤ |y t| / K + 1 / K * r := by
        have : |x t| ≤ |y t| + r := by
          have := h t t.2
          have := abs_sub_abs_le_abs_sub (x t) (y t)
          linarith
        have h5 : |x t| / K ≤ (|y t| + r) / K := div_le_div_of_nonneg_right this hK0.le
        have h6 : (|y t| + r) / K = |y t| / K + 1 / K * r := by ring
        linarith
      have h2 : min 1 (|x t| / K) ≤ min 1 (|y t| / K) + 1 / K * r := by
        have : 0 ≤ 1 / K * r := by positivity
        rcases le_total 1 (|y t| / K) with h3 | h3
        · rw [min_eq_left h3]; exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_right h3]; exact (min_le_right _ _).trans h1
      exact h2.trans (by linarith [le_hK T K y t t.2])
    rw [abs_le]
    constructor
    · have := key y x (fun t ht => by rw [abs_sub_comm]; exact h t ht); linarith
    · have := key x y h; linarith

end PropagatorLimit.Scaling.Thm33Red

namespace PropagatorLimit.Scaling.Thm33Red

lemma pointwise {Ω : Type} (beta : ℝ) (hbeta : 0 < beta) (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ) (N : ℕ) (hN : 1 ≤ N) (hsmall : beta * dt T N ≤ 1)
    (ω : Ω) (K : ℝ) (hK0 : 0 < K) (f : (ℝ≥0 → ℝ) → ℝ) (Cf L : ℝ)
    (hCf : ∀ x, |f x| ≤ Cf) (hL0 : 0 ≤ L)
    (hL : ∀ x y : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r →
      (∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ r) → |f x - f y| ≤ L * r) :
    |f (INpath beta T g F N ω) -
        f (fun t => Real.exp (-(beta * t)) * Sres beta T g F N ω t)|
      ≤ 2 * Cf * hK T K (Sres beta T g F N ω) +
        L * (((beta ^ 2 * (T : ℝ) ^ 2 + beta * T) / N) * K) := by
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hδ : 0 ≤ ((beta ^ 2 * (T : ℝ) ^ 2 + beta * T) / N) * K := by positivity
  have hh0 := hK_nonneg T K hK0 (Sres beta T g F N ω)
  by_cases hall : ∀ k ≤ N, |Sres beta T g F N ω (grid T N k)| ≤ K
  · have := hL _ _ _ hδ (fun t ht =>
      estE beta hbeta T hT g F N hN hsmall ω K hall t ht.2)
    nlinarith
  · push_neg at hall
    obtain ⟨k, hk, hkK⟩ := hall
    have h1 := le_hK T K (Sres beta T g F N ω) (grid T N k) ⟨bot_le, grid_le T N hN k hk⟩
    have h2 : min 1 (|Sres beta T g F N ω (grid T N k)| / K) = 1 :=
      min_eq_left ((one_lt_div hK0).mpr hkK).le
    have h3 : hK T K (Sres beta T g F N ω) = 1 := le_antisymm (hK_le_one _ _ _) (h2 ▸ h1)
    rw [h3]
    have := abs_sub (f (INpath beta T g F N ω))
      (f (fun t => Real.exp (-(beta * t)) * Sres beta T g F N ω t))
    have := hCf (INpath beta T g F N ω)
    have := hCf (fun t => Real.exp (-(beta * t)) * Sres beta T g F N ω t)
    have := mul_nonneg hL0 hδ
    linarith

lemma transfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (T : ℝ≥0) (hT : 0 < T) (E : Extension Ω P 𝓕)
    (hP' : IsProbabilityMeasure E.P')
    (beta : ℝ) (hbeta : 0 < beta) (g : ℝ → ℝ) (hg : Continuous g) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, Measurable (F t)) (I : ℝ≥0 → E.Ω' → ℝ) (hI : ∀ ω', Continuous (I · ω'))
    (hconv : StablyConverges P T (fun N ω t => Sres beta T g F N ω t) E
      (fun ω' t => Real.exp (beta * t) * I t ω')) :
    StablyConverges P T (fun N ω => INpath beta T g F N ω) E (fun ω' t => I t ω') := by
  intro Y hY hYb f hf
  obtain ⟨CY, hCY⟩ := hYb
  have hf' := hf
  obtain ⟨⟨Cf, hCf⟩, -⟩ := hf'
  obtain ⟨L, hL0, hL⟩ := test_bound hf
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  set CY' := max CY 0 with hCY'
  have hCY'0 : 0 ≤ CY' := le_max_right _ _
  have hYle : ∀ ω, |Y ω| ≤ CY' := fun ω => (hCY ω).trans (le_max_left _ _)
  set f₁ : (ℝ≥0 → ℝ) → ℝ := fun x => f (fun t => Real.exp (-(beta * t)) * x t) with hf₁def
  have hf₁ : IsTestFunctional T f₁ := by
    refine isTest_of T f₁ Cf L (fun x => hCf _) hL0 (fun x y r hr h =>
      hL (fun t => Real.exp (-(beta * t)) * x t) (fun t => Real.exp (-(beta * t)) * y t) r hr ?_)
    intro t ht
    have he : Real.exp (-(beta * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := mul_nonneg hbeta.le (NNReal.coe_nonneg t); linarith)
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ 1 * |x t - y t| := by gcongr
      _ ≤ r := by rw [one_mul]; exact h t ht
  obtain ⟨hint1, hint1', hlim1⟩ := hconv Y hY ⟨CY, hCY⟩ f₁ hf₁
  have hfI : (fun ω' => Y (E.π ω') * f₁ (fun t => Real.exp (beta * t) * I t ω')) =
      fun ω' => Y (E.π ω') * f (fun t => I t ω') := by
    funext ω'
    congr 1
    show f (fun t => Real.exp (-(beta * t)) * (Real.exp (beta * t) * I t ω')) = f (fun t => I t ω')
    congr 1
    funext t
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [hfI] at hint1' hlim1
  have hintN : ∀ N, Integrable (fun ω => Y ω * f (INpath beta T g F N ω)) P := by
    intro N
    refine (integrable_const (CY' * Cf)).mono'
      (hY.mul (meas_comp beta T g hg F hF N hf)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hYle ω) (hCf _) (abs_nonneg _) hCY'0
  refine ⟨hintN, hint1', ?_⟩
  -- tightness functionals
  have hψ : ∀ K : ℝ, 0 < K →
      (∀ N, Integrable (fun ω => hK T K (Sres beta T g F N ω)) P) ∧
      Integrable (fun ω' => hK T K (fun t => Real.exp (beta * t) * I t ω')) E.P' ∧
      Tendsto (fun N => ∫ ω, hK T K (Sres beta T g F N ω) ∂P) atTop
        (𝓝 (∫ ω', hK T K (fun t => Real.exp (beta * t) * I t ω') ∂E.P')) := by
    intro K hK0
    obtain ⟨a, b, c⟩ := hconv (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
      (hK T K) (hK_test T K hK0)
    simp only [one_mul] at a b c
    exact ⟨a, b, c⟩
  -- a(K) → 0
  have hA : Tendsto (fun k : ℕ =>
      ∫ ω', hK T ((k : ℝ) + 1) (fun t => Real.exp (beta * t) * I t ω') ∂E.P') atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := E.P')
      (F := fun (k : ℕ) ω' => hK T ((k : ℝ) + 1) (fun t => Real.exp (beta * t) * I t ω'))
      (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun k => (hψ _ (by positivity)).2.1.aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun ω' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hK_nonneg _ _ (by positivity) _)]
        exact hK_le_one _ _ _)
      (ae_of_all _ fun ω' => by
        obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
          (f := fun t : ℝ≥0 => Real.exp (beta * t) * I t ω')
          ((Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).mul
            (hI ω')).continuousOn
        have hup : Tendsto (fun k : ℕ => B * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun k => hK_nonneg _ _ (by positivity) _) (fun k => ?_)
        have := hK_le T ((k : ℝ) + 1) (by positivity)
          (fun t => Real.exp (beta * t) * I t ω') B (fun t ht => by
            have := hB t ht; rwa [Real.norm_eq_abs] at this)
        rw [mul_one_div]; exact this)
    simpa using this
  -- the difference tends to zero
  set c0 : ℝ := beta ^ 2 * (T : ℝ) ^ 2 + beta * T with hc0
  suffices hd : Tendsto (fun N => ∫ ω, Y ω * f (INpath beta T g F N ω) ∂P -
      ∫ ω, Y ω * f₁ (Sres beta T g F N ω) ∂P) atTop (𝓝 0) by
    have := hd.add hlim1
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := 2 * CY' * Cf + 1 with hM
  have hMpos : 0 < M := by positivity
  set η := ε / (4 * M) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨k, hk⟩ := ((hA.eventually (gt_mem_nhds hηpos)).exists)
  set K : ℝ := (k : ℝ) + 1 with hKdef
  have hK0 : 0 < K := by positivity
  obtain ⟨hψint, -, hψlim⟩ := hψ K hK0
  have ev1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have ev2 : ∀ᶠ N : ℕ in atTop, beta * dt T N ≤ 1 := by
    have : Tendsto (fun N : ℕ => beta * ((T : ℝ) / N)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).const_mul beta
    exact (this.eventually (gt_mem_nhds zero_lt_one)).mono fun N h => h.le
  have ev3 : ∀ᶠ N : ℕ in atTop, CY' * (L * ((c0 / N) * K)) < ε / 2 := by
    have : Tendsto (fun N : ℕ => CY' * (L * ((c0 / N) * K))) atTop (𝓝 0) := by
      simpa using (((tendsto_const_div_atTop_nhds_zero_nat c0).mul_const K).const_mul L).const_mul CY'
    exact this.eventually (gt_mem_nhds (by positivity))
  have ev4 : ∀ᶠ N : ℕ in atTop, ∫ ω, hK T K (Sres beta T g F N ω) ∂P < 2 * η :=
    hψlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hN1, hNs, hN3, hN4⟩ := hN0 N hN
  rw [Real.dist_eq, sub_zero, ← integral_sub (hintN N) (hint1 N)]
  have hbound : ∀ ω, |Y ω * f (INpath beta T g F N ω) - Y ω * f₁ (Sres beta T g F N ω)| ≤
      CY' * (2 * Cf * hK T K (Sres beta T g F N ω) + L * ((c0 / N) * K)) := by
    intro ω
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hYle ω)
      (pointwise beta hbeta T hT g F N hN1 hNs ω K hK0 f Cf L hCf hL0 hL)
      (abs_nonneg _) hCY'0
  have hRint : Integrable (fun ω => CY' * (2 * Cf * hK T K (Sres beta T g F N ω) +
      L * ((c0 / N) * K))) P :=
    (((hψint N).const_mul (2 * Cf)).add (integrable_const _)).const_mul CY'
  calc |∫ ω, (Y ω * f (INpath beta T g F N ω) - Y ω * f₁ (Sres beta T g F N ω)) ∂P|
      ≤ ∫ ω, |Y ω * f (INpath beta T g F N ω) - Y ω * f₁ (Sres beta T g F N ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, CY' * (2 * Cf * hK T K (Sres beta T g F N ω) + L * ((c0 / N) * K)) ∂P :=
        integral_mono ((hintN N).sub (hint1 N)).abs hRint hbound
    _ = CY' * (2 * Cf * ∫ ω, hK T K (Sres beta T g F N ω) ∂P) + CY' * (L * ((c0 / N) * K)) := by
        rw [integral_const_mul, integral_add ((hψint N).const_mul _) (integrable_const _),
          integral_const_mul, integral_const]
        simp; ring
    _ < ε := by
        have h1 : CY' * (2 * Cf * ∫ ω, hK T K (Sres beta T g F N ω) ∂P) ≤
            (2 * CY' * Cf) * (2 * η) := by
          have := mul_le_mul_of_nonneg_left hN4.le (mul_nonneg (mul_nonneg zero_le_two hCY'0) hCf0)
          nlinarith
        have h2 : (2 * CY' * Cf) * (2 * η) < ε / 2 := by
          rw [hη]
          have : (2 * CY' * Cf) * (2 * (ε / (4 * M))) = ε / 2 * ((2 * CY' * Cf) / M) := by
            field_simp; ring
          rw [this]
          have : (2 * CY' * Cf) / M < 1 := by rw [div_lt_one hMpos]; linarith
          nlinarith
        linarith

end PropagatorLimit.Scaling.Thm33Red

open PropagatorLimit.Scaling in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W Wperp : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianPair P 𝓕 W Wperp)
    (T : ℝ≥0) (hT : 0 < T) (fl : Flow Ω) (hfl : IsFlow P 𝓕 W Wperp T fl)
    (beta : ℝ) (hbeta : 0 < beta) (g : ℝ → ℝ) (hg : IsImpactFn g) :
    ∃ (E : Extension Ω P 𝓕) (Wp : ℝ≥0 → E.Ω' → ℝ) (I : ℝ≥0 → E.Ω' → ℝ),
      E.IsVeryGood ∧ IsFBrownian E.P' E.𝓖 Wp ∧
      EthierKurtz.HasCrossVariation E.P' (fun t ω' => W t (E.π ω')) Wp
        (fun t ω' => ∫ u in (0 : ℝ)..t.val, rho g (fl.v u.toNNReal (E.π ω'))) ∧
      SolvesLinearImpact beta g W fl E Wp I ∧
      StablyConverges P T (fun N ω => INpath beta T g fl.F N ω) E (fun ω' t => I t ω') := by
  obtain ⟨E, Wp, I, hE, hWp, hcv, hsol, hconv⟩ :=
    rescaled_convergence P 𝓕 W Wperp hW T hT fl hfl beta hbeta g hg
  refine ⟨E, Wp, I, hE, hWp, hcv, hsol, ?_⟩
  have hF : ∀ t, Measurable (fl.F t) := fun t =>
    (hfl.1.1 t).mono (𝓕.le t) le_rfl
  exact Thm33Red.transfer P T hT E hE.1 beta hbeta g hg.2.1.continuous fl.F hF I hsol.1 hconv
