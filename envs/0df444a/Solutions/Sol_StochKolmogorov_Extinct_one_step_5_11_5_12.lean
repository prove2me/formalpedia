-- Prove2me | solution 1 for StochKolmogorov.Extinct.one_step_5_11_5_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T19:22:40.829216+00:00
-- url     : https://prove2.me/submissions/1a409fd6-36b4-455a-a8fa-2c6aa20bcbbf

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Theorems.Thm_EthierKurtz_sde_markov_property_fd_conditional
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Theorems.Thm_StochKolmogorov_Extinct_weighted_lyapunov_dynkin

set_option linter.all false
set_option Elab.async false


-- ===== module K34min =====
section Mod_K34min
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- the path read at rational times (negative rationals read time 0) -/
def rpath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω) : ℚ → SDEState n :=
  fun q => X x (q : ℝ).toNNReal ω

theorem measurable_rpath [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (hm : ∀ t, Measurable (X x t)) : Measurable (rpath X x) :=
  measurable_pi_lambda _ (fun q => hm _)

end StochKolmogorov.Classify.K3

namespace StochKolmogorov.Classify.K4

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- the rational-time path after time `t` -/
def shiftPath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    ℚ → SDEState n :=
  fun q => X x (t + (q : ℝ).toNNReal) ω

open Classical in
/-- the rational-time path from `y` (a constant path off the orthant, where `X y` is unconstrained) -/
noncomputable def Zf (X : SDEState n → ℝ≥0 → Ω → SDEState n) (y : SDEState n) (ω : Ω) :
    ℚ → SDEState n :=
  if y ∈ orthant n then K3.rpath X y ω else fun _ => y

/-- PM1, the finite-dimensional Markov identity (open child). -/
def FDMarkov [MeasurableSpace Ω] (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0),
    (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
    Measurable (fun y => ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P) ∧
    ∫⁻ ω, (F (s.restrict (shiftPath X x t ω)) : ℝ≥0∞) ∂P =
      ∫⁻ y, ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P ∂(trans P X t x)


end StochKolmogorov.Classify.K4

end Mod_K34min

-- ===== module FDM =====
section Mod_FDM

/-! PM1 glue of K4b (8f909832): `K4.FDMarkov` (finite-dimensional Markov identity of the rational
path after time `t`, for Lipschitz test functions bounded by 1) from the child theorem
`EthierKurtz.sde_markov_property_fd_conditional` (case q = 0), applied to Lipschitz truncations of the Kolmogorov
coefficients (copied from the accepted `Persist.markov_property` reduction, namespace renamed). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDM

open StochKolmogorov.Classify EthierKurtz

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {d : ℕ}
theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩


/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and have truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

variable {n : ℕ}

theorem fdMarkov_of {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    K4.FDMarkov P X := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s G hGL hG1
  obtain ⟨KG, hGL⟩ := hGL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let F : (Fin s.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous F :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ F v := fun v => (G _).2
  have hFK : ∀ v, |F v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hG1 _
  have hFL : ∀ v v', |F v - F v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM'⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KG.2 hFL
  have hgM := fun x hx s' hD => by
    have h1 := hgM' x hx s' hD 0 (fun j => j.elim0) (fun j => j.elim0) (fun _ => (1 : ℝ))
      measurable_const 1 0 (fun v => by simp) le_rfl (fun v v' => by simp)
    simpa only [one_mul] using h1
  have hGF : ∀ f : ℚ → SDEState n, ((G (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (F (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (F (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, F (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((G (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hhm : Measurable h := by
    refine Measurable.piecewise orthant_isClosed.measurableSet (ENNReal.measurable_ofReal.comp hgm) ?_
    exact measurable_coe_nnreal_ennreal.comp
      (G.continuous.comp (continuous_pi fun j => continuous_id)).measurable
  have hheq : ∀ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hGF]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hgI : Integrable (fun ω => g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hgm.comp ((hXs x hxo).1 t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK _)
  have hg0 : 0 ≤ᵐ[P] fun ω => g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    show (0 : ℝ) ≤ g (X x t ω)
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  refine ⟨?_, ?_⟩
  · have : (fun y => ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P) = h := funext hheq
    rw [this]; exact hhm
  calc ∫⁻ ω, ((G (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (F (fun i => K4.shiftPath X x t ω (e i))) ∂P :=
          lintegral_congr fun ω => hGF _
    _ = ENNReal.ofReal (∫ ω, F (fun i => X x (t + τ i) ω) ∂P) :=
          hlin (fun ω i => X x (t + τ i) ω) (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
    _ = ENNReal.ofReal (∫ ω, g (X x t ω) ∂P) := by rw [hgM x hxo t (hinv x hxo t)]
    _ = ∫⁻ ω, ENNReal.ofReal (g (X x t ω)) ∂P := ofReal_integral_eq_lintegral_ofReal hgI hg0
    _ = ∫⁻ ω, h (X x t ω) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]
    _ = ∫⁻ y, h y ∂(trans P X t x) := by
          rw [trans, lintegral_map hhm ((hXs x hxo).1 t)]
    _ = ∫⁻ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P ∂(trans P X t x) :=
          lintegral_congr fun y => (hheq y).symm

end StochKolmogorov.Classify.FDM

end Mod_FDM

-- ===== module FDMC =====
section Mod_FDMC

/-! K2-mc step 1 (8f909832): conditional finite-dimensional Markov identity, tested against a
Lipschitz functional `G` of finitely many past rational times in `(0, t]`, from child C
(`EthierKurtz.sde_markov_property_fd_conditional`) with `q = s'.card`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- past rational times `q ∈ (0, t]` -/
def Past (t : ℝ≥0) : Type := {q : ℚ // 0 < q ∧ (q : ℝ) ≤ t}

/-- the past rational path up to time `t` -/
def past (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    Past t → SDEState n :=
  fun q => X x ((q.1 : ℚ) : ℝ).toNNReal ω

theorem measurable_past [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (t : ℝ≥0) (hm : ∀ s, Measurable (X x s)) : Measurable (past X x t) :=
  measurable_pi_lambda _ fun _ => hm _

theorem fdMarkovCond_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s' : Finset (Past t)) (G : (∀ i : s', SDEState n) →ᵇ ℝ≥0),
      (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := FDM.kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s' G hGL hG1 s F hFL hF1
  obtain ⟨KG, hGL⟩ := hGL
  obtain ⟨KF, hFL⟩ := hFL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  -- the future functional
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let Fr : (Fin s.card → SDEState n) → ℝ := fun v => ((F (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous Fr :=
    NNReal.continuous_coe.comp (F.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ Fr v := fun v => (F _).2
  have hFK : ∀ v, |Fr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hF1 _
  have hFLr : ∀ v v', |Fr v - Fr v'| ≤ (KF : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hFL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KF.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  -- the past functional
  let e' : Fin s'.card ≃ s' := s'.equivFin.symm
  let u : Fin s'.card → ℝ≥0 := fun j => ((((e' j).1).1 : ℚ) : ℝ).toNNReal
  have hu : ∀ j, 0 < u j ∧ u j ≤ t := fun j =>
    ⟨Real.toNNReal_pos.2 (by exact_mod_cast ((e' j).1).2.1),
      Real.toNNReal_le_iff_le_coe.2 ((e' j).1).2.2⟩
  let Gr : (Fin s'.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e'.symm j)) : ℝ≥0) : ℝ)
  have hGc : Continuous Gr :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hG0 : ∀ v, 0 ≤ Gr v := fun v => (G _).2
  have hGK : ∀ v, |Gr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hG0 v)]; exact_mod_cast hG1 _
  have hGLr : ∀ v v', |Gr v - Gr v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e'.symm j)) (fun j => v' (e'.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e'.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KF.2 hFLr
  have key := hgM x hxo t (hinv x hxo t) s'.card u hu Gr hGc.measurable 1 KG hGK KG.2 hGLr
  have hFeq : ∀ f : ℚ → SDEState n, ((F (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Fr (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hGeq : ∀ ω, ((G (s'.restrict (past X x t ω)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Gr (fun j => X x (u j) ω)) := by
    intro ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [u, past, Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (Fr (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, Fr (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((F (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hheq : ∀ y, ∫⁻ ω, ((F (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hFeq]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hGm : Measurable fun ω => Gr (fun j => X x (u j) ω) :=
    hGc.measurable.comp (f := fun ω j => X x (u j) ω) (measurable_pi_lambda _ fun j => (hXs x hxo).1 _)
  have hFm : Measurable fun ω => Fr (fun i => X x (t + τ i) ω) :=
    hFc.measurable.comp (f := fun ω i => X x (t + τ i) ω)
      (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
  have hgXm : Measurable fun ω => g (X x t ω) := hgm.comp ((hXs x hxo).1 t)
  have hI1 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hFK (fun i => X x (t + τ i) ω)))
  have hI2 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hgXm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hgK (X x t ω)))
  have hg0 : ∀ᵐ ω ∂P, 0 ≤ g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  calc ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hGeq, hFeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          rfl
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hI1
            (Eventually.of_forall fun ω => mul_nonneg (hG0 (fun j => X x (u j) ω))
              (hF0 (fun i => X x (t + τ i) ω)))).symm
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * g (X x t ω) ∂P) := by rw [key]
    _ = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * g (X x t ω)) ∂P :=
          ofReal_integral_eq_lintegral_ofReal hI2
            (hg0.mono fun ω hω => mul_nonneg (hG0 (fun j => X x (u j) ω)) hω)
    _ = ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          rw [hheq, hGeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]

end StochKolmogorov.Classify.FDMC

end Mod_FDMC

-- ===== module PathMix2 =====
section Mod_PathMix2

/-! K2-mc (8f909832): two-measure version of PathMix. `Q` (finite; e.g. `P` weighted by a past
functional) governs `Y`, the probability `P` governs `Z y`, and `κ` (finite, same mass as `Q`)
mixes: `Q(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)`. Used for the conditional (past-weighted) path Markov
identity: `Q = P.withDensity (G ∘ past)`, `κ = Q.map (X x s)`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix2

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def MixQ {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W) (Z : E → Ω → W)
    (κ : Measure E) (Γ : Set W) : Prop :=
  Measurable (fun y => P (Z y ⁻¹' Γ)) ∧ Q (Y ⁻¹' Γ) = ∫⁻ y, P (Z y ⁻¹' Γ) ∂κ

theorem mixQ_compl {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (t : Set W) (htm : MeasurableSet t) (hmix : MixQ Q P Y Z κ t) : MixQ Q P Y Z κ tᶜ := by
  obtain ⟨hm, heq⟩ := hmix
  have hc : ∀ y, P (Z y ⁻¹' tᶜ) = 1 - P (Z y ⁻¹' t) := fun y => by
    rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage (hZ y))]
  refine ⟨?_, ?_⟩
  · simp_rw [hc]; exact hm.const_sub 1
  · rw [Set.preimage_compl, measure_compl (htm.preimage hY) (measure_ne_top _ _), heq, hmass]
    simp_rw [hc]
    have hle : (fun y => P (Z y ⁻¹' t)) ≤ᵐ[κ] fun _ => (1 : ℝ≥0∞) :=
      Eventually.of_forall fun y => prob_le_one
    have hfin : ∫⁻ y, P (Z y ⁻¹' t) ∂κ ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂κ) ?_ (lintegral_mono fun y => prob_le_one)
      simp
    rw [lintegral_sub hm hfin hle]
    simp

theorem mixQ_iUnion {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W)
    (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    (f : ℕ → Set W) (hd : Pairwise (Function.onFun Disjoint f)) (hfm : ∀ i, MeasurableSet (f i))
    (hmix : ∀ i, MixQ Q P Y Z κ (f i)) : MixQ Q P Y Z κ (⋃ i, f i) := by
  have hZd : ∀ y, P (Z y ⁻¹' ⋃ i, f i) = ∑' i, P (Z y ⁻¹' f i) := fun y => by
    rw [Set.preimage_iUnion]
    exact measure_iUnion (fun i j hij => (hd hij).preimage _) (fun i => (hfm i).preimage (hZ y))
  refine ⟨?_, ?_⟩
  · simp_rw [hZd]; exact Measurable.tsum fun i => (hmix i).1
  · rw [Set.preimage_iUnion, measure_iUnion (fun i j hij => (hd hij).preimage _)
      (fun i => (hfm i).preimage hY)]
    simp_rw [hZd]
    rw [lintegral_tsum fun i => (hmix i).1.aemeasurable]
    exact tsum_congr fun i => (hmix i).2

theorem mixQ_of_pi {W : Type*} [mW : MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ]
    (hmass : Q Set.univ = κ Set.univ) {𝒮 : Set (Set W)} (hgen : mW = generateFrom 𝒮)
    (hpi : IsPiSystem 𝒮) (hS : ∀ t ∈ 𝒮, MixQ Q P Y Z κ t) :
    ∀ Γ : Set W, MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  intro Γ hΓ
  refine MeasurableSpace.induction_on_inter (C := fun Γ _ => MixQ Q P Y Z κ Γ)
    hgen hpi ?_ ?_ ?_ ?_ Γ hΓ
  · refine ⟨by simp, by simp⟩
  · intro t ht
    exact hS t ht
  · intro t htm hmix
    exact mixQ_compl Q P Y hY Z hZ κ hmass t htm hmix
  · intro f hd hfm hmix
    exact mixQ_iUnion Q P Y hY Z hZ κ f hd hfm hmix

theorem mixQ_closed {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [OpensMeasurableSpace W]
    (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsFiniteMeasure κ]
    (hF : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (Y ω) : ℝ≥0∞) ∂Q = ∫⁻ y, ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P ∂κ)
    (C : Set W) (hC : IsClosed C) : MixQ Q P Y Z κ C := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → W →ᵇ ℝ≥0 := fun k => thickenedIndicator (δpos k) C
  have hF' := fun k => hF (F k) ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
    (fun w => thickenedIndicator_le_one (δpos k) C w)
  have hFm : ∀ k, Measurable fun w => ((F k w : ℝ≥0) : ℝ≥0∞) :=
    fun k => measurable_coe_nnreal_ennreal.comp (F k).continuous.measurable
  have hlim : ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → W), Measurable V →
      Tendsto (fun k => ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ) atTop (𝓝 (μ (V ⁻¹' C))) := by
    intro μ _ V hV
    have e : ∀ k, ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ = ∫⁻ w, (F k w : ℝ≥0∞) ∂(μ.map V) :=
      fun k => (lintegral_map (hFm k) hV).symm
    simp_rw [e]
    rw [← Measure.map_apply hV hC.measurableSet]
    haveI : IsFiniteMeasure (μ.map V) := Measure.isFiniteMeasure_map μ V
    exact tendsto_lintegral_thickenedIndicator_of_isClosed (μ.map V) hC δpos δlim
  have hmeas : Measurable fun y => P (Z y ⁻¹' C) :=
    measurable_of_tendsto_metrizable (fun k => (hF' k).1)
      (tendsto_pi_nhds.2 fun y => hlim P _ (hZ y))
  refine ⟨hmeas, ?_⟩
  have h1 := hlim Q Y hY
  have h2 : Tendsto (fun k => ∫⁻ y, ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ∂κ) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun k => (hF' k).1)
      (fun k => Eventually.of_forall fun y => ?_) (by simp)
      (Eventually.of_forall fun y => hlim P _ (hZ y))
    calc ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono fun ω => by
            exact ENNReal.coe_le_one_iff.mpr (thickenedIndicator_le_one (δpos k) C (Z y ω))
      _ = 1 := by simp
  have h3 : Tendsto (fun k => ∫⁻ ω, (F k (Y ω) : ℝ≥0∞) ∂Q) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    simp_rw [(hF' _).2]; exact h2
  exact tendsto_nhds_unique h1 h3

theorem mixQ_cylinders (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hcyl : ∀ (s : Finset ι) (S : Set (∀ i : s, E)), MeasurableSet S →
      MixQ Q P Y Z κ (cylinder s S)) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_of_pi Q P Y hY Z hZ κ hmass generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders fun t ht => ?_
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  exact hcyl s S hS

/-- two-measure PM2: finite-dimensional Lipschitz test functions to the path σ-algebra. -/
theorem mixQ_all [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_cylinders Q P Y hY Z hZ κ hmass fun s S hS => ?_
  have hYs : Measurable fun ω => s.restrict (Y ω) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hY
  have hZs : ∀ y, Measurable fun ω => s.restrict (Z y ω) :=
    fun y => measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (hZ y)
  have hgen : (inferInstance : MeasurableSpace (∀ i : s, E)) = generateFrom {C | IsClosed C} :=
    BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  exact mixQ_of_pi Q P _ hYs _ hZs κ hmass hgen isPiSystem_isClosed
    (fun C hC => mixQ_closed Q P _ hYs _ hZs κ (hFD s) C hC) S hS

end StochKolmogorov.Classify.PathMix2

end Mod_PathMix2

-- ===== module CondMix =====
section Mod_CondMix

/-! K2-mc steps 2-3 (8f909832), generic: from the conditional finite-dimensional Markov identity
(Lipschitz tests `G` of the past path `V`, `F` of the future path `Y`) to the conditional path
identity `P(Y ∈ Γ, V ∈ A) = ∫_{V ∈ A} P(Z (Xt ω) ∈ Γ) dP(ω)` for all measurable `A`, `Γ`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.CondMix

/-- Two finite Borel measures on a pseudo-emetric space agree if they agree on Lipschitz
bounded continuous functions with values in `[0, 1]`. -/
theorem ext_lip {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F w : ℝ≥0∞) ∂μ = ∫⁻ w, (F w : ℝ≥0∞) ∂ν) : μ = ν := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcl : ∀ C : Set W, IsClosed C → μ C = ν C := by
    intro C hC
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed μ hC δpos δlim
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ν hC δpos δlim
    have e : ∀ k : ℕ, ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂μ =
        ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂ν := fun k =>
      h _ ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
        (fun w => thickenedIndicator_le_one (δpos k) C w)
    simp_rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun C hC => hcl C hC)
    (hcl _ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := W), borel_eq_generateFrom_isClosed]

/-- Two finite measures on a path space `ι → E` agree if they agree on Lipschitz `[0,1]`-valued
tests of finitely many coordinates. -/
theorem pi_ext_lip {ι E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ ν : Measure (ι → E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂μ = ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂ν) : μ = ν := by
  have hmap : ∀ s : Finset ι, μ.map s.restrict = ν.map s.restrict := by
    intro s
    refine ext_lip _ _ fun F hF hF1 => ?_
    have hFm : Measurable fun w : (∀ i : s, E) => ((F w : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp F.continuous.measurable
    rw [lintegral_map hFm (Finset.measurable_restrict s),
      lintegral_map hFm (Finset.measurable_restrict s)]
    exact h s F hF hF1
  have hcyl : ∀ t ∈ measurableCylinders (fun _ : ι => E), μ t = ν t := by
    intro t ht
    rw [mem_measurableCylinders] at ht
    obtain ⟨s, S, hS, rfl⟩ := ht
    have e : cylinder (α := fun _ : ι => E) s S = s.restrict ⁻¹' S := rfl
    rw [e, ← Measure.map_apply (Finset.measurable_restrict s) hS,
      ← Measure.map_apply (Finset.measurable_restrict s) hS, hmap s]
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders hcyl ?_
  have := hcyl _ (cylinder_mem_measurableCylinders (∅ : Finset ι) Set.univ MeasurableSet.univ)
  simpa using this

variable {Ω E ι ι' : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The conditional path identity. -/
theorem condMix [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → (ι' → E)) (hV : Measurable V) (Y : Ω → (ι → E)) (hY : Measurable Y)
    (Xt : Ω → E) (hXt : Measurable Xt) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P))
    (hC : ∀ (s' : Finset ι') (G : (∀ i : s', E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) * (F (s.restrict (Y ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (Z (Xt ω) ω')) : ℝ≥0∞) ∂P ∂P)
    (A : Set (ι' → E)) (hA : MeasurableSet A) (Γ : Set (ι → E)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (Z y ⁻¹' Γ)) ∧
      P (Y ⁻¹' Γ ∩ V ⁻¹' A) = ∫⁻ ω in V ⁻¹' A, P (Z (Xt ω) ⁻¹' Γ) ∂P := by
  set Q : Measure Ω := P.restrict (V ⁻¹' A) with hQ
  set κ : Measure E := Q.map Xt with hκ
  haveI hQfin : IsFiniteMeasure Q := by rw [hQ]; infer_instance
  haveI : IsFiniteMeasure κ := Measure.isFiniteMeasure_map Q Xt
  have hmass : Q Set.univ = κ Set.univ := by
    rw [hκ, Measure.map_apply hXt MeasurableSet.univ, Set.preimage_univ]
  -- the finite-dimensional identity under `Q`
  have hFDQ : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) →
      (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ := by
    intro s F hF hF1
    have hHm := hFD s F hF hF1
    refine ⟨hHm, ?_⟩
    set H : E → ℝ≥0∞ := fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P with hH
    have hFYm : Measurable fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp
        (F.continuous.measurable.comp ((Finset.measurable_restrict s).comp hY))
    have hHXm : Measurable fun ω => H (Xt ω) := hHm.comp hXt
    have hH1 : ∀ y, H y ≤ 1 := fun y => by
      calc H y ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
            lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
        _ = 1 := by simp
    -- two measures on the past path space
    set μ1 : Measure (ι' → E) :=
      (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)).map V with hμ1
    set μ2 : Measure (ι' → E) := (P.withDensity fun ω => H (Xt ω)).map V with hμ2
    have hfin1 : IsFiniteMeasure (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
    have hfin2 : IsFiniteMeasure (P.withDensity fun ω => H (Xt ω)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => hH1 _
    haveI : IsFiniteMeasure μ1 := Measure.isFiniteMeasure_map _ V
    haveI : IsFiniteMeasure μ2 := Measure.isFiniteMeasure_map _ V
    have hμ : μ1 = μ2 := by
      refine pi_ext_lip μ1 μ2 fun s' G hG hG1 => ?_
      have hGm : Measurable fun w : (ι' → E) => ((G (s'.restrict w) : ℝ≥0) : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp
          (G.continuous.measurable.comp (Finset.measurable_restrict s'))
      have hGVm : Measurable fun ω => ((G (s'.restrict (V ω)) : ℝ≥0) : ℝ≥0∞) := hGm.comp hV
      rw [hμ1, hμ2, lintegral_map hGm hV, lintegral_map hGm hV,
        lintegral_withDensity_eq_lintegral_mul _ hFYm hGVm,
        lintegral_withDensity_eq_lintegral_mul _ hHXm hGVm]
      have := hC s' G hG hG1 s F hF hF1
      simp only [Pi.mul_apply]
      rw [lintegral_congr fun ω => mul_comm _ _, this]
      exact lintegral_congr fun ω => mul_comm _ _
    have hA1 : μ1 A = ∫⁻ ω in V ⁻¹' A, ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) ∂P := by
      rw [hμ1, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    have hA2 : μ2 A = ∫⁻ ω in V ⁻¹' A, H (Xt ω) ∂P := by
      rw [hμ2, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    rw [hκ, lintegral_map hHm hXt, hQ, ← hA1, ← hA2, hμ]
  have hmix := PathMix2.mixQ_all Q P Y hY Z hZ κ hmass hFDQ Γ hΓ
  refine ⟨hmix.1, ?_⟩
  have h2 := hmix.2
  rw [hQ, Measure.restrict_apply (hY hΓ)] at h2
  rw [h2, hκ, lintegral_map hmix.1 hXt]

end StochKolmogorov.Classify.CondMix

end Mod_CondMix

-- ===== module FDMC2 =====
section Mod_FDMC2

/-! K2-mc (8f909832): the conditional path Markov identity for the Kolmogorov solution family:
`P(shiftPath_t ∈ Γ, past_t ∈ A) = ∫_{past_t ∈ A} P(Zf (X x t ω) ∈ Γ) dP(ω)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem measurable_Zf [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (y : SDEState n) : Measurable (K4.Zf X y) := by
  unfold K4.Zf
  split_ifs with h
  · exact K3.measurable_rpath X y (hX.2.2 y h).1
  · exact measurable_const

theorem condPath_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (x : SDEState n) (hx : x ∈ openOrthant n) (t : ℝ≥0)
    (A : Set (Past t → SDEState n)) (hA : MeasurableSet A)
    (Γ : Set (ℚ → SDEState n)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (K4.Zf X y ⁻¹' Γ)) ∧
      P (K4.shiftPath X x t ⁻¹' Γ ∩ past X x t ⁻¹' A) =
        ∫⁻ ω in past X x t ⁻¹' A, P (K4.Zf X (X x t ω) ⁻¹' Γ) ∂P := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hFD := FDM.fdMarkov_of P C B X hX hC hinv
  exact CondMix.condMix P (past X x t) (measurable_past X x t hsol.1)
    (K4.shiftPath X x t) (measurable_pi_lambda _ fun q => hsol.1 _) (X x t) (hsol.1 t)
    (K4.Zf X) (measurable_Zf P C B X hX)
    (fun s F hF hF1 => (hFD x hx t s F hF hF1).1)
    (fdMarkovCond_of P C B X hX hC hinv x hx t) A hA Γ hΓ

end StochKolmogorov.Classify.FDMC

end Mod_FDMC2

-- ===== ef9e0740 glue (far case, Markov transfer, top) =====

/-! ef9e0740 glue G (far case), abstract pure measure theory. Session 2 (opus55).
Part 1: grid Dynkin telescoping, partition identity, the min/weight inequality, the
pathwise lower bound of the clock. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace OSEG

variable {Ω : Type*} [MeasurableSpace Ω]

/-- alive at index `k`: no stop before `k` -/
def aliveS (stop : ℕ → Set Ω) (k : ℕ) : Set Ω := {ω | ∀ j < k, ω ∉ stop j}

theorem aliveS_zero (stop : ℕ → Set Ω) : aliveS stop 0 = univ := by
  ext ω; simp [aliveS]

theorem aliveS_succ (stop : ℕ → Set Ω) (k : ℕ) :
    aliveS stop (k + 1) = aliveS stop k \ stop k := by
  ext ω; simp only [aliveS, mem_setOf_eq, mem_diff]
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact h1 j h
    · subst h; exact h2

theorem measurableSet_aliveS {m : MeasurableSpace Ω} (stop : ℕ → Set Ω) (k : ℕ)
    (hs : ∀ j < k, MeasurableSet[m] (stop j)) : MeasurableSet[m] (aliveS stop k) := by
  have : aliveS stop k = ⋂ j ∈ (Finset.range k : Set ℕ), (stop j)ᶜ := by
    ext ω; simp [aliveS]
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet _)
    fun j hj => (hs j (Finset.mem_range.1 hj)).compl

theorem indicator_split (stop : ℕ → Set Ω) (g : Ω → ℝ≥0∞) (k : ℕ) (ω : Ω) :
    (aliveS stop k).indicator g ω =
      (aliveS stop k ∩ stop k).indicator g ω + (aliveS stop (k + 1)).indicator g ω := by
  rw [aliveS_succ]
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_diff]
  split_ifs <;> simp_all

theorem partition_sum (stop : ℕ → Set Ω) (g : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range N, (aliveS stop j ∩ stop j).indicator g ω) +
      (aliveS stop N).indicator g ω = g ω := by
  induction N with
  | zero => simp [aliveS_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← indicator_split, ih]

theorem dynkin_grid (P : Measure Ω) (N : ℕ) (W : ℕ → Ω → ℝ≥0∞) (stop : ℕ → Set Ω)
    (hW : ∀ k, Measurable (W k)) (hS : ∀ k, MeasurableSet (stop k))
    (hstep : ∀ k < N, ∫⁻ ω, (aliveS stop (k + 1)).indicator (W (k + 1)) ω ∂P ≤
      ∫⁻ ω, (aliveS stop (k + 1)).indicator (W k) ω ∂P) :
    ∫⁻ ω, ((∑ j ∈ Finset.range N, (aliveS stop j ∩ stop j).indicator (W j) ω) +
      (aliveS stop N).indicator (W N) ω) ∂P ≤ ∫⁻ ω, W 0 ω ∂P := by
  have hA : ∀ k, MeasurableSet (aliveS stop k) := fun k =>
    measurableSet_aliveS stop k (fun j _ => hS j)
  have key : ∀ k ≤ N, ∫⁻ ω, ((∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω) +
      (aliveS stop k).indicator (W k) ω) ∂P ≤ ∫⁻ ω, W 0 ω ∂P := by
    intro k
    induction k with
    | zero => intro _; simp [aliveS_zero]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hmS : Measurable fun ω =>
          ∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω :=
        Finset.measurable_sum _ fun j _ => (hW j).indicator ((hA j).inter (hS j))
      have hm1 : Measurable fun ω =>
          (∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω) +
            (aliveS stop k ∩ stop k).indicator (W k) ω :=
        hmS.add ((hW k).indicator ((hA k).inter (hS k)))
      calc ∫⁻ ω, ((∑ j ∈ Finset.range (k + 1), (aliveS stop j ∩ stop j).indicator (W j) ω) +
              (aliveS stop (k + 1)).indicator (W (k + 1)) ω) ∂P
          = ∫⁻ ω, ((∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω) +
              (aliveS stop k ∩ stop k).indicator (W k) ω) ∂P +
            ∫⁻ ω, (aliveS stop (k + 1)).indicator (W (k + 1)) ω ∂P := by
            simp_rw [Finset.sum_range_succ]
            exact lintegral_add_left hm1 _
        _ ≤ ∫⁻ ω, ((∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω) +
              (aliveS stop k ∩ stop k).indicator (W k) ω) ∂P +
            ∫⁻ ω, (aliveS stop (k + 1)).indicator (W k) ω ∂P :=
            add_le_add le_rfl (hstep k (by omega))
        _ = ∫⁻ ω, ((∑ j ∈ Finset.range k, (aliveS stop j ∩ stop j).indicator (W j) ω) +
              (aliveS stop k).indicator (W k) ω) ∂P := by
            rw [← lintegral_add_left hm1]
            congr 1; funext ω; rw [indicator_split stop (W k) k ω, add_assoc]
        _ ≤ _ := ih'
  exact key N le_rfl

/-- `min(ς,u) ≤ e^A u + ς (e^{cD} - 1)` when `A ≥ -cD`. -/
theorem min_le_weighted (ς u A D c : ℝ) (hς : 0 ≤ ς) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hA : -(c * D) ≤ A) :
    ENNReal.ofReal (min ς u) ≤ ENNReal.ofReal (Real.exp A * u) +
      ENNReal.ofReal ς * ENNReal.ofReal (Real.exp (c * D) - 1) := by
  rcases le_or_gt u 0 with hu | hu
  · rw [ENNReal.ofReal_of_nonpos (le_trans (min_le_right _ _) hu)]; exact bot_le
  have he1 : 0 ≤ Real.exp (c * D) - 1 := by
    have := Real.one_le_exp (mul_nonneg hc hD); linarith
  have hEu : 0 ≤ Real.exp A * u := mul_nonneg (Real.exp_pos _).le hu.le
  rw [← ENNReal.ofReal_mul hς, ← ENNReal.ofReal_add hEu (mul_nonneg hς he1)]
  apply ENNReal.ofReal_le_ofReal
  rcases le_or_gt ς (Real.exp A * u) with h | h
  · have : 0 ≤ ς * (Real.exp (c * D) - 1) := mul_nonneg hς he1
    linarith [min_le_left ς u]
  · have hprod : 1 ≤ Real.exp (c * D) * Real.exp A := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h1 : u ≤ Real.exp (c * D) * (Real.exp A * u) := by
      calc u = 1 * u := (one_mul u).symm
        _ ≤ (Real.exp (c * D) * Real.exp A) * u := mul_le_mul_of_nonneg_right hprod hu.le
        _ = _ := by ring
    have h2 : (Real.exp (c * D) - 1) * (Real.exp A * u) ≤ (Real.exp (c * D) - 1) * ς :=
      mul_le_mul_of_nonneg_left h.le he1
    have h3 : Real.exp (c * D) * (Real.exp A * u) =
        Real.exp A * u + (Real.exp (c * D) - 1) * (Real.exp A * u) := by ring
    linarith [min_le_right ς u]

/-- pathwise lower bound of the clock: `∫₀ᵗ ρ ≥ a t - (a+L)·|{ℓ < M} ∩ (0,t]|`. -/
theorem integral_lower (ρ ℓ : ℝ → ℝ) (hρ : Continuous ρ) (hℓ : Continuous ℓ)
    (a L M t : ℝ) (ht : 0 ≤ t)
    (h1 : ∀ s, M ≤ ℓ s → a ≤ ρ s) (h2 : ∀ s, -L ≤ ρ s) :
    a * t - (a + L) * (volume ({s | ℓ s < M} ∩ Ioc 0 t)).toReal ≤ ∫ s in (0 : ℝ)..t, ρ s := by
  set S : Set ℝ := {s | ℓ s < M} with hSdef
  have hS : MeasurableSet S := (isOpen_lt hℓ continuous_const).measurableSet
  have hpt : ∀ s, a - (a + L) * S.indicator (1 : ℝ → ℝ) s ≤ ρ s := by
    intro s
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs]; simp only [Pi.one_apply, mul_one]; linarith [h2 s]
    · rw [Set.indicator_of_notMem hs]; simp only [mul_zero, sub_zero]
      exact h1 s (not_lt.1 hs)
  have hind : IntervalIntegrable (S.indicator (1 : ℝ → ℝ)) volume 0 t := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
      ((measurable_const.indicator hS).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ S
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hint1 : IntervalIntegrable (fun s => a - (a + L) * S.indicator (1 : ℝ → ℝ) s) volume 0 t :=
    intervalIntegrable_const.sub (hind.const_mul _)
  have hmono := intervalIntegral.integral_mono_on ht hint1 (hρ.intervalIntegrable _ _)
    (fun s _ => hpt s)
  have hcomp : ∫ s in (0 : ℝ)..t, (a - (a + L) * S.indicator (1 : ℝ → ℝ) s) =
      a * t - (a + L) * (volume (S ∩ Ioc 0 t)).toReal := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hind.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_of_le ht, integral_indicator_one hS]
    simp [Measure.real, Measure.restrict_apply hS, smul_eq_mul]
    ring
  linarith

section MeasInt
variable {Ω : Type*}

/-- the clock is measurable for any σ-algebra seeing the rate up to time `t` -/
theorem meas_integral [m : MeasurableSpace Ω] (ρ : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hc : ∀ ω, Continuous fun s => ρ s ω) (hm : ∀ s, s ≤ t → Measurable (ρ s)) :
    Measurable (fun ω => ∫ s in (0 : ℝ)..t, ρ s ω) := by
  set ρ' : ℝ → Ω → ℝ := fun s ω => ρ (min s t) ω with hρ'
  have hj : Measurable (Function.uncurry ρ') :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hc ω).comp (continuous_id.min continuous_const))
      (fun s => hm _ (min_le_right _ _))
  have hs : StronglyMeasurable fun ω => ∫ s, ρ' s ω ∂(volume.restrict (Ioc 0 t)) :=
    hj.stronglyMeasurable.integral_prod_left
  have heq : (fun ω => ∫ s in (0 : ℝ)..t, ρ s ω) =
      fun ω => ∫ s, ρ' s ω ∂(volume.restrict (Ioc 0 t)) := by
    funext ω
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp [hρ', min_eq_left hs.2]
  rw [heq]; exact hs.measurable

end MeasInt

/-- grid time `k T / 2^m` -/
noncomputable def tg (T : ℝ≥0) (m k : ℕ) : ℝ≥0 := (k : ℝ≥0) * (T / 2 ^ m)

theorem tg_coe (T : ℝ≥0) (m k : ℕ) : ((tg T m k : ℝ≥0) : ℝ) = k * ((T : ℝ) / 2 ^ m) := by
  simp [tg]

theorem tg_succ (T : ℝ≥0) (m k : ℕ) : tg T m k + T / 2 ^ m = tg T m (k + 1) := by
  apply NNReal.eq; simp only [NNReal.coe_add, tg_coe, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat]; push_cast; ring

theorem tg_zero (T : ℝ≥0) (m : ℕ) : tg T m 0 = 0 := by simp [tg]

theorem tg_top (T : ℝ≥0) (m : ℕ) : tg T m (2 ^ m) = T := by
  apply NNReal.eq; rw [tg_coe]; push_cast; field_simp

theorem tg_two_mul (T : ℝ≥0) (m i : ℕ) : tg T (m + 1) (2 * i) = tg T m i := by
  apply NNReal.eq; rw [tg_coe, tg_coe]; push_cast; rw [pow_succ]; field_simp

theorem lt_of_tg_lt (T : ℝ≥0) (hT : 0 < T) (m i j : ℕ)
    (h : ((tg T m i : ℝ≥0) : ℝ) < tg T m j) : i < j := by
  rw [tg_coe, tg_coe] at h
  have hh : 0 < (T : ℝ) / 2 ^ m := by positivity
  exact_mod_cast lt_of_mul_lt_mul_right h hh.le

theorem tg_le_T (T : ℝ≥0) (m i : ℕ) (hi : i ≤ 2 ^ m) : ((tg T m i : ℝ≥0) : ℝ) ≤ T := by
  rw [tg_coe]
  have hh : 0 ≤ (T : ℝ) / 2 ^ m := by positivity
  calc (i : ℝ) * ((T : ℝ) / 2 ^ m) ≤ (2 ^ m : ℕ) * ((T : ℝ) / 2 ^ m) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
    _ = T := by push_cast; field_simp

theorem tg_mono (T : ℝ≥0) (m i j : ℕ) (h : i ≤ j) : ((tg T m i : ℝ≥0) : ℝ) ≤ tg T m j := by
  rw [tg_coe, tg_coe]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)

section Bad
variable {Ω : Type*}

/-- times `s ∈ (0,T]` with `ℓ s < M` such that every grid point before `s` is far -/
def Sm (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) : Set ℝ :=
  {s | s ∈ Ioc 0 (T : ℝ) ∧ ℓ s ω < M ∧
    ∀ i ≤ 2 ^ m, ((tg T m i : ℝ≥0) : ℝ) < s → M < ℓ (tg T m i) ω}

theorem Sm_succ_subset (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    Sm ℓ M T (m + 1) ω ⊆ Sm ℓ M T m ω := by
  rintro s ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun i hi hlt => ?_⟩
  have := h3 (2 * i) (by rw [pow_succ]; omega) (by rw [tg_two_mul]; exact hlt)
  rwa [tg_two_mul] at this

theorem Sm_iInter (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (hT : 0 < T) (ω : Ω)
    (hc : Continuous fun s => ℓ s ω) : ⋂ m, Sm ℓ M T m ω = ∅ := by
  ext s
  simp only [mem_iInter, mem_empty_iff_false, iff_false]
  intro hs
  obtain ⟨⟨hs0, hsT⟩, hlt, -⟩ := hs 0
  have hev : ∀ᶠ y in 𝓝 s, ℓ y ω < M := (hc.tendsto s).eventually (Iio_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hδ : 0 < min ε s := lt_min hε hs0
  obtain ⟨m, hm⟩ := exists_nat_gt ((T : ℝ) / min ε s)
  have h2m : (m : ℝ) < 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set h := (T : ℝ) / 2 ^ m with hhdef
  have hpos : 0 < h := by positivity
  have hsmall : h < min ε s := by
    rw [hhdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hm
    nlinarith
  set q := s / h with hqdef
  have hq0 : 0 < q := div_pos hs0 hpos
  have hceil : 1 ≤ ⌈q⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hq0).ne'
  set i := ⌈q⌉₊ - 1 with hidef
  have hi1 : (i : ℝ) + 1 = ⌈q⌉₊ := by
    rw [hidef, Nat.cast_sub hceil]; push_cast; ring
  have hlt_q : (i : ℝ) < q := by have := Nat.ceil_lt_add_one hq0.le; linarith
  have hge_q : q ≤ (i : ℝ) + 1 := by rw [hi1]; exact Nat.le_ceil q
  have hti : ((tg T m i : ℝ≥0) : ℝ) = i * h := by rw [tg_coe]
  have hqh : q * h = s := by rw [hqdef]; field_simp
  have hti_lt : ((tg T m i : ℝ≥0) : ℝ) < s := by
    rw [hti, ← hqh]; exact mul_lt_mul_of_pos_right hlt_q hpos
  have hti_ge : s - h ≤ ((tg T m i : ℝ≥0) : ℝ) := by
    rw [hti]; nlinarith
  have hi_le : i ≤ 2 ^ m := by
    have h1 : (i : ℝ) * h < 2 ^ m * h := by
      have : (2 : ℝ) ^ m * h = T := by rw [hhdef]; field_simp
      rw [this]; rw [← hti]; linarith
    have : (i : ℝ) < 2 ^ m := lt_of_mul_lt_mul_right h1 hpos.le
    exact_mod_cast this.le
  have hfar := (hs m).2.2 i hi_le hti_lt
  have hnear := hball (y := ((tg T m i : ℝ≥0) : ℝ)) (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : h < ε := lt_of_lt_of_le hsmall (min_le_left _ _)
    linarith)
  linarith

variable [MeasurableSpace Ω]

theorem measurableSet_Sprod (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (m : ℕ)
    (hc : ∀ ω, Continuous fun s => ℓ s ω) (hℓm : ∀ s, Measurable (ℓ s)) :
    MeasurableSet {p : ℝ × Ω | p.1 ∈ Sm ℓ M T m p.2} := by
  have hj : Measurable (fun p : ℝ × Ω => ℓ p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hℓm
  have hQ : ∀ i : ℕ, MeasurableSet {p : ℝ × Ω | i ≤ 2 ^ m →
      ((tg T m i : ℝ≥0) : ℝ) < p.1 → M < ℓ (tg T m i) p.2} := by
    intro i
    by_cases hi : i ≤ 2 ^ m
    · simp only [hi, true_implies]
      have e : {p : ℝ × Ω | ((tg T m i : ℝ≥0) : ℝ) < p.1 → M < ℓ (tg T m i) p.2} =
          {p | p.1 ≤ ((tg T m i : ℝ≥0) : ℝ)} ∪ {p | M < ℓ (tg T m i) p.2} := by
        ext p; simp only [mem_setOf_eq, mem_union]; constructor
        · intro h
          by_cases hc' : ((tg T m i : ℝ≥0) : ℝ) < p.1
          · exact Or.inr (h hc')
          · exact Or.inl (not_lt.1 hc')
        · rintro (h | h) hc'
          · exact absurd hc' (not_lt.2 h)
          · exact h
      rw [e]
      exact (measurableSet_le measurable_fst measurable_const).union
        (measurableSet_lt measurable_const ((hℓm _).comp measurable_snd))
    · simp [hi]
  have hall : MeasurableSet {p : ℝ × Ω | ∀ i, i ≤ 2 ^ m →
      ((tg T m i : ℝ≥0) : ℝ) < p.1 → M < ℓ (tg T m i) p.2} := by
    rw [setOf_forall]; exact MeasurableSet.iInter hQ
  exact (measurable_fst measurableSet_Ioc).inter
    ((measurableSet_lt hj measurable_const).inter hall)

theorem measurable_vol_Sm (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (m : ℕ)
    (hc : ∀ ω, Continuous fun s => ℓ s ω) (hℓm : ∀ s, Measurable (ℓ s)) :
    Measurable fun ω => volume (Sm ℓ M T m ω) :=
  measurable_measure_prodMk_right (measurableSet_Sprod ℓ M T m hc hℓm)

theorem vol_Sm_le (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    (volume (Sm ℓ M T m ω)).toReal ≤ T := by
  have h1 : volume (Sm ℓ M T m ω) ≤ volume (Ioc (0 : ℝ) T) := measure_mono fun s hs => hs.1
  have h2 : volume (Ioc (0 : ℝ) T) = ENNReal.ofReal T := by simp [Real.volume_Ioc]
  have := ENNReal.toReal_mono (by rw [h2]; exact ENNReal.ofReal_ne_top) h1
  rw [h2, ENNReal.toReal_ofReal (NNReal.coe_nonneg T)] at this
  exact this

theorem vol_Sm_tendsto (ℓ : ℝ → Ω → ℝ) (M : ℝ) (T : ℝ≥0) (hT : 0 < T) (ω : Ω)
    (hc : ∀ ω, Continuous fun s => ℓ s ω) (hℓm : ∀ s, Measurable (ℓ s)) :
    Tendsto (fun m => (volume (Sm ℓ M T m ω)).toReal) atTop (𝓝 0) := by
  have hanti : Antitone fun m => Sm ℓ M T m ω :=
    antitone_nat_of_succ_le fun m => Sm_succ_subset ℓ M T m ω
  have hmeas : ∀ m, NullMeasurableSet (Sm ℓ M T m ω) volume := fun m =>
    (measurable_prodMk_right (measurableSet_Sprod ℓ M T m hc hℓm)).nullMeasurableSet
  have hfin : ∃ m, volume (Sm ℓ M T m ω) ≠ ∞ :=
    ⟨0, ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono fun s hs => hs.1)⟩
  have h := tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [Sm_iInter ℓ M T hT ω (hc ω), measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

end Bad

section Glue
variable {Ω : Type*} [MeasurableSpace Ω]

/-- the clock at a stopped index is at least `-(a+L) D_m` -/
theorem clock_lower_stop (ℓ ρ : ℝ → Ω → ℝ) (ω : Ω) (hℓc : Continuous fun s => ℓ s ω)
    (hρc : Continuous fun s => ρ s ω) (M a L Te : ℝ) (T : ℝ≥0) (hT : 0 < T) (ha : 0 ≤ a)
    (hc0 : 0 ≤ a + L) (m : ℕ)
    (h1 : ∀ s, M ≤ ℓ s ω → a ≤ ρ s ω) (h2 : ∀ s, -L ≤ ρ s ω)
    (stop : ℕ → Set Ω)
    (hstop : ∀ k, ω ∈ stop k ↔ ((tg T m k : ℝ≥0) : ℝ) + Te ≤ T ∧ ℓ (tg T m k) ω ≤ M)
    (j : ℕ) (hj : j ≤ 2 ^ m) (hω : ω ∈ aliveS stop j ∩ stop j) :
    -((a + L) * (volume (Sm ℓ M T m ω)).toReal) ≤
      ∫ s in (0 : ℝ)..((tg T m j : ℝ≥0) : ℝ), ρ s ω := by
  have hlow := integral_lower (fun s => ρ s ω) (fun s => ℓ s ω) hρc hℓc a L M ((tg T m j : ℝ≥0) : ℝ)
    (NNReal.coe_nonneg _) h1 h2
  have hgood := ((hstop j).1 hω.2).1
  have hsub : {s | ℓ s ω < M} ∩ Ioc 0 ((tg T m j : ℝ≥0) : ℝ) ⊆ Sm ℓ M T m ω := by
    rintro s ⟨hs1, hs2⟩
    refine ⟨⟨hs2.1, le_trans hs2.2 (tg_le_T T m j hj)⟩, hs1, fun i hi hlt => ?_⟩
    have hij : i < j := lt_of_tg_lt T hT m i j (lt_of_lt_of_le hlt hs2.2)
    have hno : ω ∉ stop i := hω.1 i hij
    rw [hstop] at hno
    have hgi : ((tg T m i : ℝ≥0) : ℝ) + Te ≤ T := by
      linarith [tg_mono T m i j hij.le]
    by_contra hcon
    exact hno ⟨hgi, not_lt.1 hcon⟩
  have hfin : volume (Sm ℓ M T m ω) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono fun s hs => hs.1)
  have hv := ENNReal.toReal_mono hfin (measure_mono hsub)
  have hat : 0 ≤ a * ((tg T m j : ℝ≥0) : ℝ) := mul_nonneg ha (NNReal.coe_nonneg _)
  have := mul_le_mul_of_nonneg_left hv hc0
  linarith

/-- the clock at the final time on the alive event is at least `-(a+L) D_m` -/
theorem clock_lower_alive (ℓ ρ : ℝ → Ω → ℝ) (ω : Ω) (hℓc : Continuous fun s => ℓ s ω)
    (hρc : Continuous fun s => ρ s ω) (M a L Te : ℝ) (T : ℝ≥0) (hT : 0 < T) (ha : 0 ≤ a)
    (hc0 : 0 ≤ a + L) (hTe : 0 < Te) (hslack : (a + L) * Te ≤ a * T) (m : ℕ)
    (h1 : ∀ s, M ≤ ℓ s ω → a ≤ ρ s ω) (h2 : ∀ s, -L ≤ ρ s ω)
    (stop : ℕ → Set Ω)
    (hstop : ∀ k, ω ∈ stop k ↔ ((tg T m k : ℝ≥0) : ℝ) + Te ≤ T ∧ ℓ (tg T m k) ω ≤ M)
    (hω : ω ∈ aliveS stop (2 ^ m)) :
    -((a + L) * (volume (Sm ℓ M T m ω)).toReal) ≤
      ∫ s in (0 : ℝ)..((tg T m (2 ^ m) : ℝ≥0) : ℝ), ρ s ω := by
  have hlow := integral_lower (fun s => ρ s ω) (fun s => ℓ s ω) hρc hℓc a L M ((tg T m (2 ^ m) : ℝ≥0) : ℝ)
    (NNReal.coe_nonneg _) h1 h2
  rw [tg_top] at hlow ⊢
  have hfin : volume (Sm ℓ M T m ω) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono fun s hs => hs.1)
  set D := (volume (Sm ℓ M T m ω)).toReal with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  by_cases hnear : ∃ i, i ≤ 2 ^ m ∧ ℓ (tg T m i) ω ≤ M
  · classical
    obtain ⟨ξ, hξ, hmin⟩ : ∃ ξ, (ξ ≤ 2 ^ m ∧ ℓ (tg T m ξ) ω ≤ M) ∧
        ∀ i < ξ, ¬ (i ≤ 2 ^ m ∧ ℓ (tg T m i) ω ≤ M) :=
      ⟨Nat.find hnear, Nat.find_spec hnear, fun i hi => Nat.find_min hnear hi⟩
    have hbad : (T : ℝ) < ((tg T m ξ : ℝ≥0) : ℝ) + Te := by
      by_contra hcon
      have hg : ((tg T m ξ : ℝ≥0) : ℝ) + Te ≤ T := not_lt.1 hcon
      rcases lt_or_eq_of_le hξ.1 with hlt | heq
      · exact hω ξ hlt ((hstop ξ).2 ⟨hg, hξ.2⟩)
      · subst heq; rw [tg_top] at hg; linarith
    have htξ := tg_le_T T m ξ hξ.1
    have hsub : {s | ℓ s ω < M} ∩ Ioc 0 (T : ℝ) ⊆
        Sm ℓ M T m ω ∪ Ioc ((tg T m ξ : ℝ≥0) : ℝ) T := by
      rintro s ⟨hs1, hs2⟩
      by_cases hsξ : s ≤ ((tg T m ξ : ℝ≥0) : ℝ)
      · left
        refine ⟨hs2, hs1, fun i hi hlt => ?_⟩
        have hiξ : i < ξ := lt_of_tg_lt T hT m i ξ (lt_of_lt_of_le hlt hsξ)
        by_contra hcon
        exact hmin i hiξ ⟨hi, not_lt.1 hcon⟩
      · right; exact ⟨not_le.1 hsξ, hs2.2⟩
    have hv1 : volume ({s | ℓ s ω < M} ∩ Ioc 0 (T : ℝ)) ≤
        volume (Sm ℓ M T m ω) + ENNReal.ofReal ((T : ℝ) - tg T m ξ) := by
      calc _ ≤ volume (Sm ℓ M T m ω ∪ Ioc ((tg T m ξ : ℝ≥0) : ℝ) T) := measure_mono hsub
        _ ≤ volume (Sm ℓ M T m ω) + volume (Ioc ((tg T m ξ : ℝ≥0) : ℝ) T) := measure_union_le _ _
        _ = _ := by rw [Real.volume_Ioc]
    have hv2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hv1
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at hv2
    have h3 := mul_le_mul_of_nonneg_left hv2 hc0
    have h4 : (a + L) * ((T : ℝ) - tg T m ξ) ≤ (a + L) * Te :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    nlinarith
  · simp only [not_exists, not_and, not_le] at hnear
    have hsub : {s | ℓ s ω < M} ∩ Ioc 0 (T : ℝ) ⊆ Sm ℓ M T m ω := by
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs2, hs1, fun i hi _ => hnear i hi⟩
    have hv := ENNReal.toReal_mono hfin (measure_mono hsub)
    have h3 := mul_le_mul_of_nonneg_left hv hc0
    have : 0 ≤ a * (T : ℝ) := mul_nonneg ha (NNReal.coe_nonneg _)
    linarith

end Glue

section Main
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem far_glue_m (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : ℝ≥0 → MeasurableSpace Ω)
    (h𝓕 : ∀ t, 𝓕 t ≤ mΩ) (h𝓕mono : Monotone 𝓕)
    (ℓ ρ : ℝ → Ω → ℝ) (u : ℝ≥0 → Ω → ℝ)
    (hℓc : ∀ ω, Continuous fun s => ℓ s ω) (hρc : ∀ ω, Continuous fun s => ρ s ω)
    (hℓm : ∀ (t : ℝ≥0) (s : ℝ), s ≤ t → Measurable[𝓕 t] (ℓ s))
    (hρm : ∀ (t : ℝ≥0) (s : ℝ), s ≤ t → Measurable[𝓕 t] (ρ s))
    (hum : ∀ t, Measurable[𝓕 t] (u t))
    (M a L ς Te u0 : ℝ) (T : ℝ≥0) (hT : 0 < T) (ha : 0 ≤ a) (hL : 0 ≤ L) (hς : 0 ≤ ς)
    (hTe : 0 < Te) (hslack : (a + L) * Te ≤ a * T)
    (hρa : ∀ᵐ ω ∂P, ∀ s, M ≤ ℓ s ω → a ≤ ρ s ω) (hρL : ∀ᵐ ω ∂P, ∀ s, -L ≤ ρ s ω)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = u0)
    (H1 : ∀ (t h : ℝ≥0) (F : Ω → ℝ≥0∞), Measurable[𝓕 t] F →
      ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (∫ s in (t : ℝ)..((t + h : ℝ≥0) : ℝ), ρ s ω) *
        u (t + h) ω) ∂P ≤ ∫⁻ ω, F ω * ENNReal.ofReal (u t ω) ∂P)
    (H2 : ∀ t : ℝ≥0, (t : ℝ) + Te ≤ T → ∀ F : Ω → ℝ≥0∞, Measurable[𝓕 t] F →
      (∀ ω, F ω ≠ 0 → ℓ t ω ≤ M ∧ u t ω < ς) →
      ∫⁻ ω, F ω * ENNReal.ofReal (u T ω) ∂P ≤ ∫⁻ ω, F ω * ENNReal.ofReal (u t ω) ∂P)
    (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (min ς (u T ω)) ∂P ≤ ENNReal.ofReal u0 + ENNReal.ofReal ς *
      ∫⁻ ω, ENNReal.ofReal (Real.exp ((a + L) * (volume (Sm ℓ M T m ω)).toReal) - 1) ∂P := by
  have hc0 : 0 ≤ a + L := by linarith
  have hℓm' : ∀ s : ℝ, Measurable (ℓ s) := fun s =>
    (hℓm s.toNNReal s (Real.le_coe_toNNReal s)).mono (h𝓕 _) le_rfl
  have hum' : ∀ t, Measurable (u t) := fun t => (hum t).mono (h𝓕 t) le_rfl
  have hFmono : ∀ i j : ℕ, i ≤ j → 𝓕 (tg T m i) ≤ 𝓕 (tg T m j) := fun i j h =>
    h𝓕mono (NNReal.coe_le_coe.1 (tg_mono T m i j h))
  -- stopping events
  obtain ⟨stop, hstop⟩ : ∃ stop : ℕ → Set Ω, ∀ k ω, ω ∈ stop k ↔
      ((tg T m k : ℝ≥0) : ℝ) + Te ≤ T ∧ ℓ (tg T m k) ω ≤ M :=
    ⟨fun k => {ω | ((tg T m k : ℝ≥0) : ℝ) + Te ≤ T ∧ ℓ (tg T m k) ω ≤ M}, fun k ω => Iff.rfl⟩
  have hstopF : ∀ k, MeasurableSet[𝓕 (tg T m k)] (stop k) := by
    intro k
    have e : stop k = {_ω | ((tg T m k : ℝ≥0) : ℝ) + Te ≤ T} ∩ (ℓ (tg T m k)) ⁻¹' Iic M := by
      ext ω; rw [hstop]; rfl
    rw [e]
    exact (MeasurableSet.const _).inter ((hℓm _ _ le_rfl) measurableSet_Iic)
  have hstopM : ∀ k, MeasurableSet (stop k) := fun k => h𝓕 _ _ (hstopF k)
  have haliveF : ∀ k, MeasurableSet[𝓕 (tg T m k)] (aliveS stop (k + 1)) := fun k =>
    measurableSet_aliveS (m := 𝓕 (tg T m k)) stop (k + 1) fun j hj =>
      hFmono j k (by omega) _ (hstopF j)
  have haliveF' : ∀ k, MeasurableSet[𝓕 (tg T m k)] (aliveS stop k) := fun k =>
    measurableSet_aliveS (m := 𝓕 (tg T m k)) stop k fun j hj =>
      hFmono j k (by omega) _ (hstopF j)
  have haliveM : ∀ k, MeasurableSet (aliveS stop k) := fun k =>
    measurableSet_aliveS stop k fun j _ => hstopM j
  -- clock and weighted values
  set A : ℕ → Ω → ℝ := fun k ω => ∫ s in (0 : ℝ)..((tg T m k : ℝ≥0) : ℝ), ρ s ω with hAdef
  have hAF : ∀ k, Measurable[𝓕 (tg T m k)] (A k) := fun k =>
    meas_integral (m := 𝓕 (tg T m k)) ρ _ (NNReal.coe_nonneg _) hρc
      (fun s hs => hρm _ s hs)
  have hAM : ∀ k, Measurable (A k) := fun k => (hAF k).mono (h𝓕 _) le_rfl
  set W : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (Real.exp (A k ω) * u (tg T m k) ω)
    with hWdef
  have hWM : ∀ k, Measurable (W k) := fun k =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (hAM k)).mul (hum' _))
  -- one step
  have hstep : ∀ k < 2 ^ m, ∫⁻ ω, (aliveS stop (k + 1)).indicator (W (k + 1)) ω ∂P ≤
      ∫⁻ ω, (aliveS stop (k + 1)).indicator (W k) ω ∂P := by
    intro k _
    set F : Ω → ℝ≥0∞ := (aliveS stop (k + 1)).indicator
      (fun ω => ENNReal.ofReal (Real.exp (A k ω))) with hFdef
    have hF : Measurable[𝓕 (tg T m k)] F :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hAF k))).indicator
        (haliveF k)
    have h := H1 (tg T m k) (T / 2 ^ m) F hF
    rw [tg_succ] at h
    calc ∫⁻ ω, (aliveS stop (k + 1)).indicator (W (k + 1)) ω ∂P
        = ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (∫ s in ((tg T m k : ℝ≥0) : ℝ)..
            ((tg T m (k + 1) : ℝ≥0) : ℝ), ρ s ω) * u (tg T m (k + 1)) ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ aliveS stop (k + 1)
          · rw [hFdef, Set.indicator_of_mem hω, Set.indicator_of_mem hω, hWdef]
            simp only
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, hAdef]
            simp only
            rw [intervalIntegral.integral_add_adjacent_intervals
              ((hρc ω).intervalIntegrable _ _) ((hρc ω).intervalIntegrable _ _)]
          · rw [hFdef, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
      _ ≤ ∫⁻ ω, F ω * ENNReal.ofReal (u (tg T m k) ω) ∂P := h
      _ = ∫⁻ ω, (aliveS stop (k + 1)).indicator (W k) ω ∂P := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ aliveS stop (k + 1)
          · rw [hFdef, Set.indicator_of_mem hω, Set.indicator_of_mem hω, hWdef]
            simp only
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          · rw [hFdef, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hdyn := dynkin_grid P (2 ^ m) W stop hWM hstopM hstep
  have hW0 : ∫⁻ ω, W 0 ω ∂P = ENNReal.ofReal u0 := by
    have : W 0 =ᵐ[P] fun _ => ENNReal.ofReal u0 := by
      filter_upwards [hu0] with ω hω
      simp only [hWdef, hAdef, tg_zero, NNReal.coe_zero, intervalIntegral.integral_same,
        Real.exp_zero, one_mul, hω]
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  -- the capped values
  set D : Ω → ℝ := fun ω => (volume (Sm ℓ M T m ω)).toReal with hDdef
  set E : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ς * ENNReal.ofReal (Real.exp ((a + L) * D ω) - 1)
    with hEdef
  set Z : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (min ς (u (tg T m k) ω)) with hZdef
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (min ς (u T ω)) with hgdef
  have hgM : Measurable g := ENNReal.measurable_ofReal.comp (measurable_const.min (hum' T))
  have hZN : Z (2 ^ m) = g := by funext ω; simp only [hZdef, hgdef, tg_top]
  have hZM : ∀ k, Measurable (Z k) := fun k =>
    ENNReal.measurable_ofReal.comp (measurable_const.min (hum' _))
  -- (a) the target is at most the capped values at the stopping index
  have hsplit : ∀ (f : Ω → ℝ≥0∞), Measurable f → ∫⁻ ω, f ω ∂P =
      (∑ j ∈ Finset.range (2 ^ m), ∫⁻ ω, (aliveS stop j ∩ stop j).indicator f ω ∂P) +
        ∫⁻ ω, (aliveS stop (2 ^ m)).indicator f ω ∂P := by
    intro f hf
    rw [← lintegral_finset_sum _ fun j _ => hf.indicator ((haliveM j).inter (hstopM j)),
      ← lintegral_add_left (Finset.measurable_sum _ fun j _ =>
        hf.indicator ((haliveM j).inter (hstopM j)))]
    refine lintegral_congr fun ω => ?_
    exact (partition_sum stop f (2 ^ m) ω).symm
  have hterm : ∀ j < 2 ^ m, ∫⁻ ω, (aliveS stop j ∩ stop j).indicator g ω ∂P ≤
      ∫⁻ ω, (aliveS stop j ∩ stop j).indicator (Z j) ω ∂P := by
    intro j hj
    by_cases hgood : ((tg T m j : ℝ≥0) : ℝ) + Te ≤ T
    · set B1 := aliveS stop j ∩ stop j ∩ {ω | u (tg T m j) ω < ς} with hB1
      set B2 := aliveS stop j ∩ stop j ∩ {ω | ς ≤ u (tg T m j) ω} with hB2
      have hB1F : MeasurableSet[𝓕 (tg T m j)] B1 :=
        ((haliveF' j).inter (hstopF j)).inter ((hum _) measurableSet_Iio)
      have hB1M : MeasurableSet B1 := h𝓕 _ _ hB1F
      have hB2M : MeasurableSet B2 :=
        ((haliveM j).inter (hstopM j)).inter ((hum' _) measurableSet_Ici)
      have hH2 := H2 (tg T m j) hgood (B1.indicator 1)
        (measurable_const.indicator hB1F) (by
          intro ω hω
          have hm : ω ∈ B1 := by
            by_contra hn; exact hω (Set.indicator_of_notMem hn _)
          exact ⟨((hstop j ω).1 hm.1.2).2, hm.2⟩)
      have hind : ∀ (f : Ω → ℝ≥0∞) ω, B1.indicator 1 ω * f ω = B1.indicator f ω := by
        intro f ω
        by_cases hω : ω ∈ B1
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      rw [lintegral_congr fun ω => hind (fun ω => ENNReal.ofReal (u T ω)) ω,
        lintegral_congr fun ω => hind (fun ω => ENNReal.ofReal (u (tg T m j) ω)) ω] at hH2
      calc ∫⁻ ω, (aliveS stop j ∩ stop j).indicator g ω ∂P
          ≤ ∫⁻ ω, (B1.indicator (fun ω => ENNReal.ofReal (u T ω)) ω +
              B2.indicator (fun _ => ENNReal.ofReal ς) ω) ∂P := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : ω ∈ aliveS stop j ∩ stop j
            · rw [Set.indicator_of_mem hω]
              by_cases hu : u (tg T m j) ω < ς
              · rw [Set.indicator_of_mem (show ω ∈ B1 from ⟨hω, hu⟩)]
                exact le_add_right (ENNReal.ofReal_le_ofReal (min_le_right _ _))
              · rw [Set.indicator_of_mem (show ω ∈ B2 from ⟨hω, not_lt.1 hu⟩)]
                exact le_add_left (ENNReal.ofReal_le_ofReal (min_le_left _ _))
            · rw [Set.indicator_of_notMem hω]; exact bot_le
        _ = ∫⁻ ω, B1.indicator (fun ω => ENNReal.ofReal (u T ω)) ω ∂P +
              ∫⁻ ω, B2.indicator (fun _ => ENNReal.ofReal ς) ω ∂P :=
            lintegral_add_left ((ENNReal.measurable_ofReal.comp (hum' T)).indicator hB1M) _
        _ ≤ ∫⁻ ω, B1.indicator (fun ω => ENNReal.ofReal (u (tg T m j) ω)) ω ∂P +
              ∫⁻ ω, B2.indicator (fun _ => ENNReal.ofReal ς) ω ∂P := add_le_add hH2 le_rfl
        _ = ∫⁻ ω, (B1.indicator (fun ω => ENNReal.ofReal (u (tg T m j) ω)) ω +
              B2.indicator (fun _ => ENNReal.ofReal ς) ω) ∂P :=
            (lintegral_add_left ((ENNReal.measurable_ofReal.comp (hum' _)).indicator hB1M) _).symm
        _ = ∫⁻ ω, (aliveS stop j ∩ stop j).indicator (Z j) ω ∂P := by
            refine lintegral_congr fun ω => ?_
            by_cases hω : ω ∈ aliveS stop j ∩ stop j
            · rw [Set.indicator_of_mem hω]
              by_cases hu : u (tg T m j) ω < ς
              · rw [Set.indicator_of_mem (show ω ∈ B1 from ⟨hω, hu⟩),
                  Set.indicator_of_notMem (show ω ∉ B2 from fun h => absurd h.2 (not_le.2 hu)),
                  add_zero, hZdef]
                simp only [min_eq_right hu.le]
              · rw [Set.indicator_of_notMem (show ω ∉ B1 from fun h => hu h.2),
                  Set.indicator_of_mem (show ω ∈ B2 from ⟨hω, not_lt.1 hu⟩), zero_add, hZdef]
                simp only [min_eq_left (not_lt.1 hu)]
            · rw [Set.indicator_of_notMem hω,
                Set.indicator_of_notMem (show ω ∉ B1 from fun h => hω h.1),
                Set.indicator_of_notMem (show ω ∉ B2 from fun h => hω h.1), add_zero]
    · have hno : ∀ ω, ω ∉ aliveS stop j ∩ stop j := fun ω h => hgood ((hstop j ω).1 h.2).1
      simp [Set.indicator_of_notMem (hno _)]
  have hle1 : ∫⁻ ω, g ω ∂P ≤ ∫⁻ ω, ((∑ j ∈ Finset.range (2 ^ m),
      (aliveS stop j ∩ stop j).indicator (Z j) ω) + (aliveS stop (2 ^ m)).indicator (Z (2 ^ m)) ω) ∂P := by
    rw [hsplit g hgM, lintegral_add_left (Finset.measurable_sum _ fun j _ =>
        (hZM j).indicator ((haliveM j).inter (hstopM j))),
      lintegral_finset_sum _ fun j _ => (hZM j).indicator ((haliveM j).inter (hstopM j)), hZN]
    exact add_le_add (Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.1 hj)) le_rfl
  -- (b) pointwise comparison with the weighted values
  have hpt : ∀ᵐ ω ∂P, ((∑ j ∈ Finset.range (2 ^ m), (aliveS stop j ∩ stop j).indicator (Z j) ω) +
      (aliveS stop (2 ^ m)).indicator (Z (2 ^ m)) ω) ≤
      ((∑ j ∈ Finset.range (2 ^ m), (aliveS stop j ∩ stop j).indicator (W j) ω) +
      (aliveS stop (2 ^ m)).indicator (W (2 ^ m)) ω) + E ω := by
    filter_upwards [hρa, hρL] with ω h1 h2
    have hD0 : 0 ≤ D ω := ENNReal.toReal_nonneg
    have hZW : ∀ k, -((a + L) * D ω) ≤ A k ω → Z k ω ≤ W k ω + E ω := fun k hA =>
      min_le_weighted ς _ _ _ _ hς hD0 hc0 hA
    have hE := partition_sum stop E (2 ^ m) ω
    calc _ ≤ (∑ j ∈ Finset.range (2 ^ m), (aliveS stop j ∩ stop j).indicator
            (fun ω => W j ω + E ω) ω) +
          (aliveS stop (2 ^ m)).indicator (fun ω => W (2 ^ m) ω + E ω) ω := by
          refine add_le_add (Finset.sum_le_sum fun j hj => ?_) ?_
          · by_cases hω : ω ∈ aliveS stop j ∩ stop j
            · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
              exact hZW j (clock_lower_stop ℓ ρ ω (hℓc ω) (hρc ω) M a L Te T hT ha hc0 m
                h1 h2 stop (fun k => hstop k ω) j (Finset.mem_range.1 hj).le hω)
            · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
          · by_cases hω : ω ∈ aliveS stop (2 ^ m)
            · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
              exact hZW _ (clock_lower_alive ℓ ρ ω (hℓc ω) (hρc ω) M a L Te T hT ha hc0 hTe
                hslack m h1 h2 stop (fun k => hstop k ω) hω)
            · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      _ = _ := by
          have hia : ∀ (S : Set Ω) (f : Ω → ℝ≥0∞),
              S.indicator (fun ω => f ω + E ω) ω = S.indicator f ω + S.indicator E ω := by
            intro S f; by_cases h : ω ∈ S
            · simp [Set.indicator_of_mem h]
            · simp [Set.indicator_of_notMem h]
          simp only [hia, Finset.sum_add_distrib]
          rw [← hE]; ring
  -- (c) combine
  have hΨM : Measurable fun ω => (∑ j ∈ Finset.range (2 ^ m),
      (aliveS stop j ∩ stop j).indicator (W j) ω) + (aliveS stop (2 ^ m)).indicator (W (2 ^ m)) ω :=
    (Finset.measurable_sum _ fun j _ => (hWM j).indicator ((haliveM j).inter (hstopM j))).add
      ((hWM _).indicator (haliveM _))
  calc ∫⁻ ω, ENNReal.ofReal (min ς (u T ω)) ∂P = ∫⁻ ω, g ω ∂P := rfl
    _ ≤ _ := hle1
    _ ≤ ∫⁻ ω, (((∑ j ∈ Finset.range (2 ^ m), (aliveS stop j ∩ stop j).indicator (W j) ω) +
      (aliveS stop (2 ^ m)).indicator (W (2 ^ m)) ω) + E ω) ∂P := lintegral_mono_ae hpt
    _ = ∫⁻ ω, ((∑ j ∈ Finset.range (2 ^ m), (aliveS stop j ∩ stop j).indicator (W j) ω) +
      (aliveS stop (2 ^ m)).indicator (W (2 ^ m)) ω) ∂P + ∫⁻ ω, E ω ∂P := lintegral_add_left hΨM _
    _ ≤ ENNReal.ofReal u0 + ∫⁻ ω, E ω ∂P := by rw [← hW0]; exact add_le_add hdyn le_rfl
    _ = _ := by rw [hEdef, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Glue G: the far-case one-step bound `E min(ς, u_T) ≤ u0` from the grid Markov hypotheses. -/
theorem far_glue (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : ℝ≥0 → MeasurableSpace Ω)
    (h𝓕 : ∀ t, 𝓕 t ≤ mΩ) (h𝓕mono : Monotone 𝓕)
    (ℓ ρ : ℝ → Ω → ℝ) (u : ℝ≥0 → Ω → ℝ)
    (hℓc : ∀ ω, Continuous fun s => ℓ s ω) (hρc : ∀ ω, Continuous fun s => ρ s ω)
    (hℓm : ∀ (t : ℝ≥0) (s : ℝ), s ≤ t → Measurable[𝓕 t] (ℓ s))
    (hρm : ∀ (t : ℝ≥0) (s : ℝ), s ≤ t → Measurable[𝓕 t] (ρ s))
    (hum : ∀ t, Measurable[𝓕 t] (u t))
    (M a L ς Te u0 : ℝ) (T : ℝ≥0) (hT : 0 < T) (ha : 0 ≤ a) (hL : 0 ≤ L) (hς : 0 ≤ ς)
    (hTe : 0 < Te) (hslack : (a + L) * Te ≤ a * T)
    (hρa : ∀ᵐ ω ∂P, ∀ s, M ≤ ℓ s ω → a ≤ ρ s ω) (hρL : ∀ᵐ ω ∂P, ∀ s, -L ≤ ρ s ω)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = u0)
    (H1 : ∀ (t h : ℝ≥0) (F : Ω → ℝ≥0∞), Measurable[𝓕 t] F →
      ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (∫ s in (t : ℝ)..((t + h : ℝ≥0) : ℝ), ρ s ω) *
        u (t + h) ω) ∂P ≤ ∫⁻ ω, F ω * ENNReal.ofReal (u t ω) ∂P)
    (H2 : ∀ t : ℝ≥0, (t : ℝ) + Te ≤ T → ∀ F : Ω → ℝ≥0∞, Measurable[𝓕 t] F →
      (∀ ω, F ω ≠ 0 → ℓ t ω ≤ M ∧ u t ω < ς) →
      ∫⁻ ω, F ω * ENNReal.ofReal (u T ω) ∂P ≤ ∫⁻ ω, F ω * ENNReal.ofReal (u t ω) ∂P) :
    ∫⁻ ω, ENNReal.ofReal (min ς (u T ω)) ∂P ≤ ENNReal.ofReal u0 := by
  have hc0 : 0 ≤ a + L := by linarith
  have hℓm' : ∀ s : ℝ, Measurable (ℓ s) := fun s =>
    (hℓm s.toNNReal s (Real.le_coe_toNNReal s)).mono (h𝓕 _) le_rfl
  set F : ℕ → Ω → ℝ≥0∞ := fun m ω =>
    ENNReal.ofReal (Real.exp ((a + L) * (volume (Sm ℓ M T m ω)).toReal) - 1) with hFdef
  have hFM : ∀ m, Measurable (F m) := fun m =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (((measurable_vol_Sm ℓ M T m hℓc hℓm').ennreal_toReal).const_mul _)).sub_const _)
  have hbound : ∀ m, F m ≤ᵐ[P] fun _ => ENNReal.ofReal (Real.exp ((a + L) * T) - 1) := by
    intro m
    refine Filter.Eventually.of_forall fun ω => ENNReal.ofReal_le_ofReal ?_
    have := vol_Sm_le ℓ M T m ω
    have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this hc0)
    linarith
  have hlimω : ∀ ω, Tendsto (fun m => F m ω) atTop (𝓝 0) := by
    intro ω
    have h0 := vol_Sm_tendsto ℓ M T hT ω hℓc hℓm'
    have h1 : Tendsto (fun m => Real.exp ((a + L) * (volume (Sm ℓ M T m ω)).toReal) - 1)
        atTop (𝓝 (Real.exp ((a + L) * 0) - 1)) :=
      ((Real.continuous_exp.tendsto _).comp (h0.const_mul (a + L))).sub_const 1
    rw [mul_zero, Real.exp_zero, sub_self] at h1
    have := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_zero] at this
  have hlim : Tendsto (fun m => ∫⁻ ω, F m ω ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := P) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal (Real.exp ((a + L) * T) - 1)) (fun m => (hFM m).aemeasurable)
      hbound (by simp) (Filter.Eventually.of_forall hlimω)
    simpa using this
  have hlim2 : Tendsto (fun m => ENNReal.ofReal u0 + ENNReal.ofReal ς * ∫⁻ ω, F m ω ∂P) atTop
      (𝓝 (ENNReal.ofReal u0 + ENNReal.ofReal ς * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top))
  rw [mul_zero, add_zero] at hlim2
  exact ge_of_tendsto' hlim2 fun m => far_glue_m P 𝓕 h𝓕 h𝓕mono ℓ ρ u hℓc hρc hℓm hρm hum
    M a L ς Te u0 T hT ha hL hς hTe hslack hρa hρL hu0 H1 H2 m

end Main

section CondFun
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- set-level conditional Markov identity ⇒ functional identity `E[F(p)G(q)] = E[F(p) ∫G dν]`. -/
theorem condFun (P : Measure Ω) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (ν : Ω → Measure β)
    (hνm : ∀ Γ, MeasurableSet Γ → Measurable fun ω => ν ω Γ)
    (hM : ∀ A Γ, MeasurableSet A → MeasurableSet Γ →
      P (q ⁻¹' Γ ∩ p ⁻¹' A) = ∫⁻ ω in p ⁻¹' A, ν ω Γ ∂P)
    (F : α → ℝ≥0∞) (G : β → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, F (p ω) * G (q ω) ∂P = ∫⁻ ω, F (p ω) * ∫⁻ y, G y ∂(ν ω) ∂P := by
  have hνM : Measurable ν := Measure.measurable_of_measurable_coe _ hνm
  have step1 : ∀ A, MeasurableSet A → ∫⁻ ω in p ⁻¹' A, G (q ω) ∂P =
      ∫⁻ ω in p ⁻¹' A, ∫⁻ y, G y ∂(ν ω) ∂P := by
    intro A hA
    have hmeas : (P.restrict (p ⁻¹' A)).map q = (P.restrict (p ⁻¹' A)).bind ν := by
      ext Γ hΓ
      rw [Measure.map_apply hq hΓ, Measure.restrict_apply (hq hΓ),
        Measure.bind_apply hΓ hνM.aemeasurable, hM A Γ hA hΓ]
    rw [← lintegral_map hG hq, hmeas, Measure.lintegral_bind hνM.aemeasurable hG.aemeasurable]
  set φ : Ω → ℝ≥0∞ := fun ω => ∫⁻ y, G y ∂(ν ω) with hφdef
  have hφ : Measurable φ := (Measure.measurable_lintegral hG).comp hνM
  have hGq : Measurable fun ω => G (q ω) := hG.comp hq
  have hFp : Measurable fun ω => F (p ω) := hF.comp hp
  have hμ : (P.withDensity (fun ω => G (q ω))).map p = (P.withDensity φ).map p := by
    ext A hA
    rw [Measure.map_apply hp hA, Measure.map_apply hp hA, withDensity_apply _ (hp hA),
      withDensity_apply _ (hp hA)]
    exact step1 A hA
  have e1 := lintegral_map hF hp (μ := P.withDensity (fun ω => G (q ω)))
  have e2 := lintegral_map hF hp (μ := P.withDensity φ)
  rw [hμ] at e1
  rw [lintegral_withDensity_eq_lintegral_mul _ hGq hFp] at e1
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hFp] at e2
  calc ∫⁻ ω, F (p ω) * G (q ω) ∂P
      = ∫⁻ ω, ((fun ω => G (q ω)) * fun ω => F (p ω)) ω ∂P :=
        lintegral_congr fun ω => mul_comm _ _
    _ = ∫⁻ ω, (φ * fun ω => F (p ω)) ω ∂P := e1.symm.trans e2
    _ = _ := lintegral_congr fun ω => mul_comm _ _

end CondFun

/-- dyadic left Riemann sums with a real endpoint `h` (rational nodes `k 2^-n`) -/
theorem riemann_dyadic (φ : ℝ → ℝ) (hφ : Continuous φ) (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range ⌊h * 2 ^ n⌋₊,
      φ (k * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) atTop (𝓝 (∫ s in (0 : ℝ)..h, φ s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (Icc (0 : ℝ) (h + 1)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, by linarith⟩)
  have huc := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hφ.continuousOn)
  have hε' : 0 < ε / (2 * (h + 1)) := by positivity
  obtain ⟨η, hη, hηφ⟩ := huc _ hε'
  have hc : 0 < min η (ε / (2 * (B + 1))) := lt_min hη (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set δ : ℝ := (1 / 2 : ℝ) ^ n with hδ
  have hδ0 : 0 < δ := by positivity
  have hδN : δ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hδη : δ < η := lt_of_le_of_lt hδN (lt_of_lt_of_le hN (min_le_left _ _))
  have hδB : δ < ε / (2 * (B + 1)) := lt_of_le_of_lt hδN (lt_of_lt_of_le hN (min_le_right _ _))
  have h2δ : (2 : ℝ) ^ n * δ = 1 := by
    rw [hδ, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow]
  set K := ⌊h * 2 ^ n⌋₊ with hKdef
  have hKle : (K : ℝ) * δ ≤ h := by
    have := Nat.floor_le (mul_nonneg hh (by positivity : (0 : ℝ) ≤ 2 ^ n))
    calc (K : ℝ) * δ ≤ h * 2 ^ n * δ := mul_le_mul_of_nonneg_right this hδ0.le
      _ = h := by rw [mul_assoc, h2δ, mul_one]
  have hKgt : h < ((K : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (h * 2 ^ n)
    calc h = h * 2 ^ n * δ := by rw [mul_assoc, h2δ, mul_one]
      _ < _ := mul_lt_mul_of_pos_right this hδ0
  -- cell decomposition
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b => hφ.intervalIntegrable a b
  have hsumint : ∑ k ∈ Finset.range K, ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s =
      ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * δ)
      (f := φ) (μ := volume) (n := K) (fun k _ => hint _ _)
    simpa using this
  have hcell : ∀ k ∈ Finset.range K, ‖φ (k * δ) * δ -
      ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s‖ ≤ ε / (2 * (h + 1)) * δ := by
    intro k hk
    have hk' : k + 1 ≤ K := Finset.mem_range.1 hk
    have hconst : ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ (k * δ) = φ (k * δ) * δ := by
      rw [intervalIntegral.integral_const]; push_cast; simp only [smul_eq_mul]; ring
    rw [← hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    have hle : ((k : ℕ) * δ : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * δ := by
      push_cast; nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := ((k : ℕ) * δ : ℝ))
      (b := ((k + 1 : ℕ) : ℝ) * δ) (C := ε / (2 * (h + 1))) (f := fun s => φ (k * δ) - φ s) (by
        intro s hs
        rw [Set.uIoc_of_le hle] at hs
        have hk1 : ((k + 1 : ℕ) : ℝ) * δ ≤ h := by
          calc ((k + 1 : ℕ) : ℝ) * δ ≤ (K : ℝ) * δ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hδ0.le
            _ ≤ h := hKle
        have hkδ0 : (0 : ℝ) ≤ k * δ := by positivity
        have hsK : s ∈ Icc (0 : ℝ) (h + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hkK : (k : ℝ) * δ ∈ Icc (0 : ℝ) (h + 1) := ⟨hkδ0, by push_cast at hs hk1; linarith [hs.1]⟩
        have hd : dist ((k : ℝ) * δ) s < η := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.1])]
          push_cast at hs; linarith [hs.2]
        have := hηφ _ hkK _ hsK hd
        rw [Real.dist_eq] at this; rw [Real.norm_eq_abs]; exact this.le)
    calc _ ≤ ε / (2 * (h + 1)) * |((k + 1 : ℕ) : ℝ) * δ - (k : ℕ) * δ| := this
      _ = ε / (2 * (h + 1)) * δ := by
          rw [abs_of_nonneg (by linarith)]; push_cast; ring
  have hsum_le : ‖(∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s‖ ≤
      K * (ε / (2 * (h + 1)) * δ) := by
    rw [← hsumint, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k ∈ Finset.range K, ‖φ (k * δ) * δ -
          ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range K, ε / (2 * (h + 1)) * δ := Finset.sum_le_sum hcell
      _ = _ := by simp
  have htail : ‖∫ s in ((K : ℝ) * δ)..h, φ s‖ ≤ B * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (K : ℝ) * δ) (b := h)
      (C := B) (f := φ) (by
        intro s hs
        rw [Set.uIoc_of_le hKle] at hs
        have hKδ0 : (0 : ℝ) ≤ K * δ := by positivity
        exact hB s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    calc _ ≤ B * |h - (K : ℝ) * δ| := this
      _ ≤ B * δ := by
          apply mul_le_mul_of_nonneg_left _ hB0
          rw [abs_of_nonneg (by linarith)]; linarith
  have hsplit : ∫ s in (0 : ℝ)..h, φ s =
      (∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) + ∫ s in ((K : ℝ) * δ)..h, φ s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  rw [Real.dist_eq, hsplit]
  have e1 : (K : ℝ) * (ε / (2 * (h + 1)) * δ) ≤ ε / 2 * (h / (h + 1)) := by
    have : (K : ℝ) * δ ≤ h := hKle
    calc (K : ℝ) * (ε / (2 * (h + 1)) * δ) = (K * δ) * (ε / (2 * (h + 1))) := by ring
      _ ≤ h * (ε / (2 * (h + 1))) := mul_le_mul_of_nonneg_right this hε'.le
      _ = ε / 2 * (h / (h + 1)) := by field_simp
  have e2 : h / (h + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have e3 : B * δ < ε / 2 := by
    have : B * δ ≤ (B + 1) * δ := by nlinarith
    have h4 : (B + 1) * δ < (B + 1) * (ε / (2 * (B + 1))) :=
      mul_lt_mul_of_pos_left hδB (by linarith)
    have h5 : (B + 1) * (ε / (2 * (B + 1))) = ε / 2 := by field_simp
    linarith
  have hsum' := hsum_le
  rw [Real.norm_eq_abs] at hsum' htail
  have e4 : ε / 2 * (h / (h + 1)) < ε / 2 := by nlinarith
  calc |(∑ k ∈ Finset.range K, φ (k * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) -
        ((∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) + ∫ s in ((K : ℝ) * δ)..h, φ s)|
      ≤ |(∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s| +
        |∫ s in ((K : ℝ) * δ)..h, φ s| := by
        rw [← hδ]
        calc _ = |((∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) -
              ∫ s in ((K : ℝ) * δ)..h, φ s| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
    _ < ε := by linarith

end OSEG


/-! ef9e0740 StochKolmogorov.Extinct.one_step_5_11_5_12 (Hening-Nguyen 1704.06984 (5.11)-(5.12)).
Session 1: deterministic facts about the cap and the reduction of the target to the FAR case
(`Utheta x < ς` and `M < l1 x`), which is the paper's stopping argument at ξ (see progress file). -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace OSE
open StochKolmogorov.Extinct EthierKurtz

variable {n : ℕ}

theorem prod_le (c z : SDEState n) (hc : ∀ i, 0 < c i) (hz : ∀ i, 0 < z i) (S : Finset (Fin n))
    (p : Fin n → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i) (hs : ∑ i ∈ S, p i ≤ 1) :
    ∏ i ∈ S, z i ^ p i ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
  have hsum0 : 0 ≤ ∑ j, c j * z j :=
    Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  have hL1 : 1 ≤ 1 + ∑ j, c j * z j := by linarith
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  have hzi : ∀ i, z i ≤ (1 + ∑ j, c j * z j) * (c i)⁻¹ := by
    intro i
    have h1 : c i * z i ≤ ∑ j, c j * z j :=
      Finset.single_le_sum (f := fun j => c j * z j) (fun j _ => (mul_pos (hc j) (hz j)).le)
        (Finset.mem_univ i)
    rw [← div_eq_mul_inv, le_div_iff₀ (hc i)]
    linarith [mul_comm (z i) (c i)]
  calc ∏ i ∈ S, z i ^ p i ≤ ∏ i ∈ S, ((1 + ∑ j, c j * z j) * (c i)⁻¹) ^ p i :=
        Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hz i).le _)
          (fun i hi => Real.rpow_le_rpow (hz i).le (hzi i) (hp i hi))
    _ = (∏ i ∈ S, (1 + ∑ j, c j * z j) ^ p i) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => Real.mul_rpow hL0.le (inv_nonneg.2 (hc i).le)
    _ ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
        apply mul_le_mul_of_nonneg_right _
          (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (inv_nonneg.2 (hc i).le) _)
        rw [← Real.rpow_sum_of_pos hL0]
        calc (1 + ∑ j, c j * z j) ^ (∑ i ∈ S, p i) ≤ (1 + ∑ j, c j * z j) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 hs
          _ = 1 + ∑ j, c j * z j := Real.rpow_one _

theorem Ui_nonneg (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) (z : SDEState n) (hz : ∀ j, 0 < z j) :
    0 ≤ Ui c mu phat pcheck i z := by
  unfold Ui
  have : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hz i).le _))
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hz j).le _)

theorem Utheta_nonneg (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ : ℝ) (z : SDEState n) (hz : ∀ j, 0 < z j) :
    0 ≤ Utheta c mu phat pcheck θ z :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Ui_nonneg c hc mu phat pcheck i z hz) _

theorem CU_bdd (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ supp mu, 0 ≤ phat i) (hs : ∑ i ∈ supp mu, phat i ≤ 1) :
    BddAbove ((fun x : SDEState n => (∏ i ∈ supp mu, x i ^ phat i) /
      (1 + ∑ i, c i * x i)) '' openOrthant n) := by
  refine ⟨∏ i ∈ supp mu, (c i)⁻¹ ^ phat i, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∀ i, 0 < z i := hz
  have hsum0 : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz' j)).le
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  show (∏ i ∈ supp mu, z i ^ phat i) / (1 + ∑ i, c i * z i) ≤ _
  rw [div_le_iff₀ hL0]
  calc _ ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ supp mu, (c i)⁻¹ ^ phat i :=
        prod_le c z hc hz' _ phat hp hs
    _ = _ := mul_comm _ _

theorem CU_pos (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ supp mu, 0 ≤ phat i) (hs : ∑ i ∈ supp mu, phat i ≤ 1) :
    0 < CU c mu phat := by
  unfold CU
  have hsum0 : 0 ≤ ∑ j, c j * c j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hc j)).le
  have hv : 0 < (∏ i ∈ supp mu, c i ^ phat i) / (1 + ∑ i, c i * c i) :=
    div_pos (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hc j) _) (by linarith)
  exact lt_of_lt_of_le hv (le_csSup (CU_bdd c hc mu phat hp hs) ⟨c, hc, rfl⟩)

theorem measurable_Utheta (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck θ : ℝ) : Measurable (Utheta c mu phat pcheck θ) := by
  have hco : ∀ i, Measurable fun z : SDEState n => z i :=
    fun i => (PiLp.continuous_apply 2 _ i).measurable
  unfold Utheta Ui
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((measurable_const.add (Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (hco j))).mul ((hco i).pow_const _)).div
    (Finset.measurable_prod _ fun j _ => (hco j).pow_const _)

theorem measurable_Utilde (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck θ δe : ℝ) : Measurable (Utilde c mu phat pcheck θ δe) :=
  measurable_const.min (measurable_Utheta c mu phat pcheck θ)

/-- `U_θ(z) < ς` forces `zᵢ < δe` off `supp μ` (the cap only binds away from the face). -/
theorem coord_lt_of_lt_varsigma (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ supp mu, 0 ≤ phat i) (hs : ∑ i ∈ supp mu, phat i ≤ 1)
    (pcheck θ δe : ℝ) (hpc : 0 < pcheck) (hθ : 0 < θ) (hδe : 0 < δe)
    (z : SDEState n) (hz : ∀ j, 0 < z j)
    (hU : Utheta c mu phat pcheck θ z < varsigma c mu phat pcheck θ δe) :
    ∀ i, i ∉ supp mu → z i < δe := by
  intro i hi
  by_contra hge0
  have hge : δe ≤ z i := not_lt.mp hge0
  have hCU := CU_pos c hc mu phat hp hs
  have hsum0 : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  have hPr0 : 0 < ∏ j ∈ supp mu, z j ^ phat j :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hz j) _
  -- ∏/(1+cz) ≤ CU
  have hle : (∏ j ∈ supp mu, z j ^ phat j) / (1 + ∑ j, c j * z j) ≤ CU c mu phat :=
    le_csSup (CU_bdd c hc mu phat hp hs) ⟨z, hz, rfl⟩
  -- δe^p / CU ≤ Ui
  have hpow : δe ^ pcheck ≤ z i ^ pcheck := Real.rpow_le_rpow hδe.le hge hpc.le
  have hUi : δe ^ pcheck / CU c mu phat ≤ Ui c mu phat pcheck i z := by
    unfold Ui
    rw [div_le_div_iff₀ hCU hPr0]
    have h1 : ∏ j ∈ supp mu, z j ^ phat j ≤ (1 + ∑ j, c j * z j) * CU c mu phat := by
      rw [div_le_iff₀ hL0] at hle; linarith [mul_comm (CU c mu phat) (1 + ∑ j, c j * z j)]
    have h2 : δe ^ pcheck * ∏ j ∈ supp mu, z j ^ phat j ≤
        z i ^ pcheck * ((1 + ∑ j, c j * z j) * CU c mu phat) :=
      mul_le_mul hpow h1 hPr0.le (Real.rpow_nonneg (hz i).le _)
    calc δe ^ pcheck * ∏ j ∈ supp mu, z j ^ phat j
        ≤ z i ^ pcheck * ((1 + ∑ j, c j * z j) * CU c mu phat) := h2
      _ = (1 + ∑ j, c j * z j) * z i ^ pcheck * CU c mu phat := by ring
  have hUiθ : varsigma c mu phat pcheck θ δe ≤ Ui c mu phat pcheck i z ^ θ := by
    unfold varsigma
    have e1 : (δe ^ pcheck / CU c mu phat) ^ θ = δe ^ (pcheck * θ) / CU c mu phat ^ θ := by
      rw [Real.div_rpow (Real.rpow_nonneg hδe.le _) hCU.le, ← Real.rpow_mul hδe.le]
    rw [← e1]
    exact Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hδe.le _) hCU.le) hUi hθ.le
  have hsingle : Ui c mu phat pcheck i z ^ θ ≤ Utheta c mu phat pcheck θ z := by
    unfold Utheta
    exact Finset.single_le_sum (f := fun j => (Ui c mu phat pcheck j z) ^ θ)
      (fun j _ => Real.rpow_nonneg (Ui_nonneg c hc mu phat pcheck j z hz) _) (by simp [hi])
  linarith

/-- Reduction of (5.11)-(5.12) to the far case `M < ‖x‖₁`, `U_θ(x) < ς`
(given interior invariance of the solution, Extinct.lemma_3_1). -/
theorem one_step_of_far {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n)) (M : ℝ)
    (phat : Fin n → ℝ) (hp : ∀ i ∈ supp mu, 0 ≤ phat i) (hs : ∑ i ∈ supp mu, phat i ≤ 1)
    (pcheck : ℝ) (hpc : 0 < pcheck) (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (Te δe θ : ℝ) (hTe : 0 < Te) (hδe : 0 < δe) (hθ : 0 < θ)
    (hcontract : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ openOrthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
          Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x)
    (hinv : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hfar : ∀ x ∈ openOrthant n,
      Utheta c mu phat pcheck θ x < varsigma c mu phat pcheck θ δe → M < l1 x →
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x) :
    ∀ x ∈ openOrthant n,
      Integrable (fun ω => Utilde c mu phat pcheck θ δe
        (X x (((ne : ℝ) * Te).toNNReal) ω)) P ∧
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x := by
  have : IsProbabilityMeasure P := hX.1
  intro x hx
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  set T : ℝ≥0 := ((ne : ℝ) * Te).toNNReal with hT
  set ς := varsigma c mu phat pcheck θ δe with hς
  have hς0 : 0 < ς := by
    rw [hς]; unfold varsigma
    exact div_pos (Real.rpow_pos_of_pos hδe _)
      (Real.rpow_pos_of_pos (CU_pos c hc mu phat hp hs) _)
  have hmeas : Measurable (fun ω => Utilde c mu phat pcheck θ δe (X x T ω)) :=
    (measurable_Utilde c mu phat pcheck θ δe).comp (hsol.1 T)
  have hbd : ∀ᵐ ω ∂P, ‖Utilde c mu phat pcheck θ δe (X x T ω)‖ ≤ ς := by
    filter_upwards [hinv x hx T] with ω hω
    have h0 : 0 ≤ Utilde c mu phat pcheck θ δe (X x T ω) :=
      le_min hς0.le (Utheta_nonneg c hc mu phat pcheck θ _ hω)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _
  have hint : Integrable (fun ω => Utilde c mu phat pcheck θ δe (X x T ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable ς hbd
  refine ⟨hint, ?_⟩
  rcases le_or_gt ς (Utheta c mu phat pcheck θ x) with hbig | hsmall
  · -- the cap binds at x: Ũ(x) = ς ≥ Ũ everywhere
    have hx' : Utilde c mu phat pcheck θ δe x = ς := min_eq_left hbig
    rw [hx']
    have h1 : ∫ ω, Utilde c mu phat pcheck θ δe (X x T ω) ∂P ≤ ∫ _ω, ς ∂P :=
      integral_mono hint (integrable_const ς) fun ω => min_le_left _ _
    simpa using h1
  · have hxe : Utilde c mu phat pcheck θ δe x = Utheta c mu phat pcheck θ x :=
      min_eq_right hsmall.le
    rcases le_or_gt (l1 x) M with hnear | hfar'
    · rcases Nat.eq_zero_or_pos ne with h0 | hpos
      · -- T = 0: X x 0 = x a.s.
        have hT0 : T = 0 := by rw [hT, h0]; simp
        have hae : (fun ω => Utilde c mu phat pcheck θ δe (X x T ω)) =ᵐ[P]
            fun _ => Utilde c mu phat pcheck θ δe x := by
          filter_upwards [hsol.2.2.2.1] with ω hω
          rw [hT0, hω]
        rw [integral_congr_ae hae]
        simp
      · have hne1 : (1 : ℝ) ≤ ne := by exact_mod_cast hpos
        have hTmem : (ne : ℝ) * Te ∈ Set.Icc Te ((ne : ℝ) * Te) :=
          ⟨by nlinarith, le_rfl⟩
        have hcoord := coord_lt_of_lt_varsigma c hc mu phat hp hs pcheck θ δe hpc hθ hδe x hx
          hsmall
        obtain ⟨hUint, hUle⟩ := hcontract _ hTmem x hx hnear hcoord
        have hexp : Real.exp (-(1 / 2) * θ * ρe * ((ne : ℝ) * Te)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ θ * ρe * ((ne : ℝ) * Te) :=
            mul_nonneg (mul_nonneg hθ.le hρe.le) (mul_nonneg (by linarith) hTe.le)
          nlinarith
        have hU0 := Utheta_nonneg c hc mu phat pcheck θ x hx
        have h1 : ∫ ω, Utilde c mu phat pcheck θ δe (X x T ω) ∂P ≤
            ∫ ω, Utheta c mu phat pcheck θ (X x T ω) ∂P :=
          integral_mono hint hUint fun ω => min_le_right _ _
        rw [hxe]
        calc _ ≤ ∫ ω, Utheta c mu phat pcheck θ (X x T ω) ∂P := h1
          _ ≤ Real.exp (-(1 / 2) * θ * ρe * ((ne : ℝ) * Te)) * Utheta c mu phat pcheck θ x :=
            hUle
          _ ≤ 1 * Utheta c mu phat pcheck θ x := mul_le_mul_of_nonneg_right hexp hU0
          _ = _ := one_mul _
    · exact hfar x hx hsmall hfar'

end OSE


/-! ef9e0740 s3 (opus55): instantiation of the abstract far-case glue `OSEG.far_glue` for the SDE.
Markov identity (FDMC.condPath_of's conclusion) and child A enter as hypotheses. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace OSEH
open StochKolmogorov.Extinct EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- past rational times `q ∈ (0, t]` -/
def Past (t : ℝ≥0) : Type := {q : ℚ // 0 < q ∧ (q : ℝ) ≤ t}

/-- the past rational path up to time `t` -/
def past (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    Past t → SDEState n :=
  fun q => X x ((q.1 : ℚ) : ℝ).toNNReal ω

/-- the rational-time path after time `t` -/
def shiftPath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    ℚ → SDEState n :=
  fun q => X x (t + (q : ℝ).toNNReal) ω

def rpath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω) : ℚ → SDEState n :=
  fun q => X x (q : ℝ).toNNReal ω

open Classical in
noncomputable def Zf (X : SDEState n → ℝ≥0 → Ω → SDEState n) (y : SDEState n) (ω : Ω) :
    ℚ → SDEState n :=
  if y ∈ orthant n then rpath X y ω else fun _ => y

/-- the conditional path Markov identity (conclusion of `FDMC.condPath_of`) -/
def MarkovId [MeasurableSpace Ω] (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) :
    Prop :=
  ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (A : Set (Past t → SDEState n)), MeasurableSet A →
    ∀ (Γ : Set (ℚ → SDEState n)), MeasurableSet Γ →
    Measurable (fun y => P (Zf X y ⁻¹' Γ)) ∧
      P (shiftPath X x t ⁻¹' Γ ∩ past X x t ⁻¹' A) =
        ∫⁻ ω in past X x t ⁻¹' A, P (Zf X (X x t ω) ⁻¹' Γ) ∂P

open Classical in
/-- the solution started at `x`, reset to the constant `x` on the null set `X x 0 ≠ x` -/
noncomputable def Yp (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0)
    (ω : Ω) : SDEState n :=
  if X x 0 ω = x then X x t ω else x

noncomputable def Yf (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) :
    SDEState n → ℝ≥0 → Ω → SDEState n := fun _ => Yp X x

variable (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)

theorem Yp_zero (ω : Ω) : Yp X x 0 ω = x := by
  unfold Yp
  by_cases h : X x 0 ω = x
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem Yp_cont (hc : ∀ ω, Continuous fun t => X x t ω) (ω : Ω) :
    Continuous fun t => Yp X x t ω := by
  unfold Yp
  by_cases h : X x 0 ω = x
  · simp only [if_pos h]; exact hc ω
  · simp only [if_neg h]; exact continuous_const

theorem Yp_meas [MeasurableSpace Ω] (hm : ∀ t, Measurable (X x t)) (t : ℝ≥0) :
    Measurable (Yp X x t) := by
  unfold Yp
  exact Measurable.ite ((hm 0) (measurableSet_singleton x)) (hm t) measurable_const

theorem Yp_ae [MeasurableSpace Ω] (P : Measure Ω) (h0 : X x 0 =ᵐ[P] fun _ => x) :
    ∀ᵐ ω ∂P, ∀ t, Yp X x t ω = X x t ω := by
  filter_upwards [h0] with ω hω
  intro t
  unfold Yp
  rw [if_pos hω]

/-- the filtration generated by the rational past of `Y` -/
noncomputable def FF [MeasurableSpace Ω] (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (past (Yf X x) x t) (inferInstance : MeasurableSpace (Past t → SDEState n))

theorem FF_le [m : MeasurableSpace Ω] (hm : ∀ t, Measurable (X x t)) (t : ℝ≥0) :
    FF X x t ≤ m :=
  (measurable_pi_lambda _ fun q => Yp_meas X x hm _).comap_le

theorem meas_pi {m : MeasurableSpace Ω} {ι : Type*} {f : Ω → ι → SDEState n}
    (h : ∀ i, Measurable fun ω => f ω i) : Measurable f := measurable_pi_lambda _ h

theorem FF_mono [MeasurableSpace Ω] : Monotone (FF X x) := by
  intro s t hst
  have : Measurable[FF X x t] (past (Yf X x) x s) := by
    refine meas_pi (m := FF X x t) fun q => ?_
    exact (measurable_pi_apply (⟨q.1, q.2.1, q.2.2.trans (by exact_mod_cast hst)⟩ : Past t)).comp
      (comap_measurable (past (Yf X x) x t))
  exact this.comap_le

theorem meas_lim {m : MeasurableSpace Ω} {f : ℕ → Ω → SDEState n} {g : Ω → SDEState n}
    (hf : ∀ i, Measurable (f i)) (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable hf lim

theorem meas_lim_real {m : MeasurableSpace Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ i, Measurable (f i)) (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable hf lim

/-- dyadic floor `⌊s 2^k⌋ / 2^k` -/
noncomputable def dq (s : ℝ) (k : ℕ) : ℚ := (⌊s * 2 ^ k⌋₊ : ℚ) / 2 ^ k

theorem dq_cast (s : ℝ) (k : ℕ) : ((dq s k : ℚ) : ℝ) = (⌊s * 2 ^ k⌋₊ : ℝ) / 2 ^ k := by
  unfold dq; push_cast; rfl

theorem dq_nonneg (s : ℝ) (k : ℕ) : (0 : ℝ) ≤ dq s k := by
  rw [dq_cast]; positivity

theorem dq_le (s : ℝ) (hs : 0 ≤ s) (k : ℕ) : ((dq s k : ℚ) : ℝ) ≤ s := by
  rw [dq_cast, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem dq_gt (s : ℝ) (k : ℕ) : s - (1 / 2 : ℝ) ^ k < dq s k := by
  rw [dq_cast]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := Nat.lt_floor_add_one (s * 2 ^ k)
  have e : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
  rw [e, lt_div_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
  linarith

theorem dq_tendsto (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun k => ((dq s k : ℚ) : ℝ)) atTop (𝓝 s) := by
  have hlow : Tendsto (fun k : ℕ => s - (1 / 2 : ℝ) ^ k) atTop (𝓝 s) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_sub s
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => (dq_gt s k).le) (fun k => dq_le s hs k)

theorem Yp_coord_meas [MeasurableSpace Ω] (t : ℝ≥0) (q : ℚ) (hq0 : 0 ≤ q) (hqt : (q : ℝ) ≤ t) :
    Measurable[FF X x t] (Yp X x (q : ℝ).toNNReal) := by
  rcases hq0.lt_or_eq with hq | hq
  · exact (measurable_pi_apply (⟨q, hq, hqt⟩ : Past t)).comp
      (comap_measurable (past (Yf X x) x t))
  · subst hq
    have : Yp X x ((((0 : ℚ) : ℝ)).toNNReal) = fun _ => x := by
      funext ω; simp only [Rat.cast_zero, Real.toNNReal_zero]; exact Yp_zero X x ω
    rw [this]; exact measurable_const

/-- `Y s` is `𝓕 t`-measurable for every `s ≤ t` -/
theorem Yp_FF_meas [MeasurableSpace Ω] (hc : ∀ ω, Continuous fun t => X x t ω) (t s : ℝ≥0)
    (hst : s ≤ t) : Measurable[FF X x t] (Yp X x s) := by
  refine meas_lim (m := FF X x t) (f := fun k => Yp X x ((dq s k : ℚ) : ℝ).toNNReal)
    (fun k => Yp_coord_meas X x t _ (by exact_mod_cast dq_nonneg s k)
      ((dq_le s s.2 k).trans (by exact_mod_cast hst))) ?_
  rw [tendsto_pi_nhds]
  intro ω
  have h1 : Tendsto (fun k => (((dq s k : ℚ) : ℝ)).toNNReal) atTop (𝓝 s) := by
    have := (continuous_real_toNNReal.tendsto (s : ℝ)).comp (dq_tendsto s s.2)
    rwa [Real.toNNReal_coe] at this
  exact ((Yp_cont X x hc ω).tendsto s).comp h1

/-- the dyadic path functional: `exp(Riemann sum of r) * U(endpoint)`, limsup along `k` -/
noncomputable def Gh (r U : SDEState n → ℝ) (h : ℝ) (p : ℚ → SDEState n) : ℝ≥0∞ :=
  limsup (fun k : ℕ => ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range ⌊h * 2 ^ k⌋₊,
      r (p ((j : ℚ) * (1 / 2 : ℚ) ^ k)) * (1 / 2 : ℝ) ^ k) *
      U (p ((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k)))) atTop

theorem Gh_meas (r U : SDEState n → ℝ) (hr : Measurable r) (hU : Measurable U) (h : ℝ) :
    Measurable (Gh r U h) := by
  unfold Gh
  refine Measurable.limsup fun k => ENNReal.measurable_ofReal.comp ?_
  refine (Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => ?_)).mul
    (hU.comp (measurable_pi_apply ((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k)))
  exact (hr.comp (measurable_pi_apply ((j : ℚ) * (1 / 2 : ℚ) ^ k))).mul_const _


section CondFun
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- set-level conditional Markov identity ⇒ functional identity `E[F(p)G(q)] = E[F(p) ∫G dν]`. -/
theorem condFun (P : Measure Ω) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (ν : Ω → Measure β)
    (hνm : ∀ Γ, MeasurableSet Γ → Measurable fun ω => ν ω Γ)
    (hM : ∀ A Γ, MeasurableSet A → MeasurableSet Γ →
      P (q ⁻¹' Γ ∩ p ⁻¹' A) = ∫⁻ ω in p ⁻¹' A, ν ω Γ ∂P)
    (F : α → ℝ≥0∞) (G : β → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, F (p ω) * G (q ω) ∂P = ∫⁻ ω, F (p ω) * ∫⁻ y, G y ∂(ν ω) ∂P := by
  have hνM : Measurable ν := Measure.measurable_of_measurable_coe _ hνm
  have step1 : ∀ A, MeasurableSet A → ∫⁻ ω in p ⁻¹' A, G (q ω) ∂P =
      ∫⁻ ω in p ⁻¹' A, ∫⁻ y, G y ∂(ν ω) ∂P := by
    intro A hA
    have hmeas : (P.restrict (p ⁻¹' A)).map q = (P.restrict (p ⁻¹' A)).bind ν := by
      ext Γ hΓ
      rw [Measure.map_apply hq hΓ, Measure.restrict_apply (hq hΓ),
        Measure.bind_apply hΓ hνM.aemeasurable, hM A Γ hA hΓ]
    rw [← lintegral_map hG hq, hmeas, Measure.lintegral_bind hνM.aemeasurable hG.aemeasurable]
  set φ : Ω → ℝ≥0∞ := fun ω => ∫⁻ y, G y ∂(ν ω) with hφdef
  have hφ : Measurable φ := (Measure.measurable_lintegral hG).comp hνM
  have hGq : Measurable fun ω => G (q ω) := hG.comp hq
  have hFp : Measurable fun ω => F (p ω) := hF.comp hp
  have hμ : (P.withDensity (fun ω => G (q ω))).map p = (P.withDensity φ).map p := by
    ext A hA
    rw [Measure.map_apply hp hA, Measure.map_apply hp hA, withDensity_apply _ (hp hA),
      withDensity_apply _ (hp hA)]
    exact step1 A hA
  have e1 := lintegral_map hF hp (μ := P.withDensity (fun ω => G (q ω)))
  have e2 := lintegral_map hF hp (μ := P.withDensity φ)
  rw [hμ] at e1
  rw [lintegral_withDensity_eq_lintegral_mul _ hGq hFp] at e1
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hFp] at e2
  calc ∫⁻ ω, F (p ω) * G (q ω) ∂P
      = ∫⁻ ω, ((fun ω => G (q ω)) * fun ω => F (p ω)) ω ∂P :=
        lintegral_congr fun ω => mul_comm _ _
    _ = ∫⁻ ω, (φ * fun ω => F (p ω)) ω ∂P := e1.symm.trans e2
    _ = _ := lintegral_congr fun ω => mul_comm _ _

end CondFun



/-- dyadic left Riemann sums with a real endpoint `h` (rational nodes `k 2^-n`) -/
theorem riemann_dyadic (φ : ℝ → ℝ) (hφ : Continuous φ) (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range ⌊h * 2 ^ n⌋₊,
      φ (k * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) atTop (𝓝 (∫ s in (0 : ℝ)..h, φ s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (Icc (0 : ℝ) (h + 1)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, by linarith⟩)
  have huc := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hφ.continuousOn)
  have hε' : 0 < ε / (2 * (h + 1)) := by positivity
  obtain ⟨η, hη, hηφ⟩ := huc _ hε'
  have hc : 0 < min η (ε / (2 * (B + 1))) := lt_min hη (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set δ : ℝ := (1 / 2 : ℝ) ^ n with hδ
  have hδ0 : 0 < δ := by positivity
  have hδN : δ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hδη : δ < η := lt_of_le_of_lt hδN (lt_of_lt_of_le hN (min_le_left _ _))
  have hδB : δ < ε / (2 * (B + 1)) := lt_of_le_of_lt hδN (lt_of_lt_of_le hN (min_le_right _ _))
  have h2δ : (2 : ℝ) ^ n * δ = 1 := by
    rw [hδ, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow]
  set K := ⌊h * 2 ^ n⌋₊ with hKdef
  have hKle : (K : ℝ) * δ ≤ h := by
    have := Nat.floor_le (mul_nonneg hh (by positivity : (0 : ℝ) ≤ 2 ^ n))
    calc (K : ℝ) * δ ≤ h * 2 ^ n * δ := mul_le_mul_of_nonneg_right this hδ0.le
      _ = h := by rw [mul_assoc, h2δ, mul_one]
  have hKgt : h < ((K : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (h * 2 ^ n)
    calc h = h * 2 ^ n * δ := by rw [mul_assoc, h2δ, mul_one]
      _ < _ := mul_lt_mul_of_pos_right this hδ0
  -- cell decomposition
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b => hφ.intervalIntegrable a b
  have hsumint : ∑ k ∈ Finset.range K, ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s =
      ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * δ)
      (f := φ) (μ := volume) (n := K) (fun k _ => hint _ _)
    simpa using this
  have hcell : ∀ k ∈ Finset.range K, ‖φ (k * δ) * δ -
      ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s‖ ≤ ε / (2 * (h + 1)) * δ := by
    intro k hk
    have hk' : k + 1 ≤ K := Finset.mem_range.1 hk
    have hconst : ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ (k * δ) = φ (k * δ) * δ := by
      rw [intervalIntegral.integral_const]; push_cast; simp only [smul_eq_mul]; ring
    rw [← hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    have hle : ((k : ℕ) * δ : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * δ := by
      push_cast; nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := ((k : ℕ) * δ : ℝ))
      (b := ((k + 1 : ℕ) : ℝ) * δ) (C := ε / (2 * (h + 1))) (f := fun s => φ (k * δ) - φ s) (by
        intro s hs
        rw [Set.uIoc_of_le hle] at hs
        have hk1 : ((k + 1 : ℕ) : ℝ) * δ ≤ h := by
          calc ((k + 1 : ℕ) : ℝ) * δ ≤ (K : ℝ) * δ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hδ0.le
            _ ≤ h := hKle
        have hkδ0 : (0 : ℝ) ≤ k * δ := by positivity
        have hsK : s ∈ Icc (0 : ℝ) (h + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hkK : (k : ℝ) * δ ∈ Icc (0 : ℝ) (h + 1) := ⟨hkδ0, by push_cast at hs hk1; linarith [hs.1]⟩
        have hd : dist ((k : ℝ) * δ) s < η := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.1])]
          push_cast at hs; linarith [hs.2]
        have := hηφ _ hkK _ hsK hd
        rw [Real.dist_eq] at this; rw [Real.norm_eq_abs]; exact this.le)
    calc _ ≤ ε / (2 * (h + 1)) * |((k + 1 : ℕ) : ℝ) * δ - (k : ℕ) * δ| := this
      _ = ε / (2 * (h + 1)) * δ := by
          rw [abs_of_nonneg (by linarith)]; push_cast; ring
  have hsum_le : ‖(∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s‖ ≤
      K * (ε / (2 * (h + 1)) * δ) := by
    rw [← hsumint, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k ∈ Finset.range K, ‖φ (k * δ) * δ -
          ∫ s in ((k : ℕ) * δ : ℝ)..(((k + 1 : ℕ) : ℝ) * δ), φ s‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range K, ε / (2 * (h + 1)) * δ := Finset.sum_le_sum hcell
      _ = _ := by simp
  have htail : ‖∫ s in ((K : ℝ) * δ)..h, φ s‖ ≤ B * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (K : ℝ) * δ) (b := h)
      (C := B) (f := φ) (by
        intro s hs
        rw [Set.uIoc_of_le hKle] at hs
        have hKδ0 : (0 : ℝ) ≤ K * δ := by positivity
        exact hB s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    calc _ ≤ B * |h - (K : ℝ) * δ| := this
      _ ≤ B * δ := by
          apply mul_le_mul_of_nonneg_left _ hB0
          rw [abs_of_nonneg (by linarith)]; linarith
  have hsplit : ∫ s in (0 : ℝ)..h, φ s =
      (∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) + ∫ s in ((K : ℝ) * δ)..h, φ s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  rw [Real.dist_eq, hsplit]
  have e1 : (K : ℝ) * (ε / (2 * (h + 1)) * δ) ≤ ε / 2 * (h / (h + 1)) := by
    have : (K : ℝ) * δ ≤ h := hKle
    calc (K : ℝ) * (ε / (2 * (h + 1)) * δ) = (K * δ) * (ε / (2 * (h + 1))) := by ring
      _ ≤ h * (ε / (2 * (h + 1))) := mul_le_mul_of_nonneg_right this hε'.le
      _ = ε / 2 * (h / (h + 1)) := by field_simp
  have e2 : h / (h + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have e3 : B * δ < ε / 2 := by
    have : B * δ ≤ (B + 1) * δ := by nlinarith
    have h4 : (B + 1) * δ < (B + 1) * (ε / (2 * (B + 1))) :=
      mul_lt_mul_of_pos_left hδB (by linarith)
    have h5 : (B + 1) * (ε / (2 * (B + 1))) = ε / 2 := by field_simp
    linarith
  have hsum' := hsum_le
  rw [Real.norm_eq_abs] at hsum' htail
  have e4 : ε / 2 * (h / (h + 1)) < ε / 2 := by nlinarith
  calc |(∑ k ∈ Finset.range K, φ (k * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) -
        ((∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) + ∫ s in ((K : ℝ) * δ)..h, φ s)|
      ≤ |(∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s| +
        |∫ s in ((K : ℝ) * δ)..h, φ s| := by
        rw [← hδ]
        calc _ = |((∑ k ∈ Finset.range K, φ (k * δ) * δ) - ∫ s in (0 : ℝ)..((K : ℝ) * δ), φ s) -
              ∫ s in ((K : ℝ) * δ)..h, φ s| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
    _ < ε := by linarith



theorem Utheta_contAt (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck θ : ℝ) (hθ : 0 ≤ θ) (z : SDEState n) (hz : z ∈ openOrthant n) :
    ContinuousAt (Utheta c mu phat pcheck θ) z := by
  have hco : ∀ i, Tendsto (fun w : SDEState n => w i) (𝓝 z) (𝓝 (z i)) :=
    fun i => (PiLp.continuous_apply 2 _ i).tendsto z
  have hz' : ∀ i, 0 < z i := hz
  unfold ContinuousAt Utheta Ui
  refine tendsto_finset_sum _ fun i _ => ?_
  refine Tendsto.rpow_const ?_ (Or.inr hθ)
  refine Tendsto.div ((tendsto_const_nhds.add (tendsto_finset_sum _ fun j _ =>
    (hco j).const_mul _)).mul ((hco i).rpow_const (Or.inl (hz' i).ne')))
    (tendsto_finset_prod _ fun j _ => (hco j).rpow_const (Or.inl (hz' j).ne')) ?_
  exact (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hz' j) _).ne'

theorem ceil_tendsto (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun k : ℕ => ((((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k : ℚ)) : ℝ)) atTop (𝓝 h) := by
  have hup : Tendsto (fun k : ℕ => h + (1 / 2 : ℝ) ^ k) atTop (𝓝 h) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_add h
  have e : ∀ k : ℕ, ((((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k : ℚ)) : ℝ) =
      (⌈h * 2 ^ k⌉₊ : ℝ) / 2 ^ k := by
    intro k; push_cast; rw [div_pow, one_pow]; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
    (fun k => ?_)
  · have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [e, le_div_iff₀ h2]
    exact Nat.le_ceil _
  · have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ h * 2 ^ k)
    rw [e, div_le_iff₀ h2, add_mul, div_pow, one_pow, div_mul_cancel₀ _ h2.ne']
    linarith

theorem Gh_eq (r U : SDEState n → ℝ) (hr : Continuous r) (h : ℝ) (hh : 0 ≤ h)
    (γ : ℝ → SDEState n) (hγ : Continuous γ) (p : ℚ → SDEState n)
    (hp : ∀ q : ℚ, (0 : ℝ) ≤ q → p q = γ q) (hU : ContinuousAt U (γ h)) :
    Gh r U h p = ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..h, r (γ s)) * U (γ h)) := by
  unfold Gh
  apply Tendsto.limsup_eq
  apply ENNReal.tendsto_ofReal
  have hS : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range ⌊h * 2 ^ k⌋₊,
      r (p ((j : ℚ) * (1 / 2 : ℚ) ^ k)) * (1 / 2 : ℝ) ^ k) atTop
      (𝓝 (∫ s in (0 : ℝ)..h, r (γ s))) := by
    refine (riemann_dyadic (fun s => r (γ s)) (hr.comp hγ) h hh).congr fun k =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [hp _ (by push_cast; positivity)]
    push_cast; rfl
  have hpc : ∀ k : ℕ, p ((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k) =
      γ ((((⌈h * 2 ^ k⌉₊ : ℚ) * (1 / 2 : ℚ) ^ k : ℚ)) : ℝ) :=
    fun k => hp _ (by push_cast; positivity)
  simp_rw [hpc]
  exact ((Real.continuous_exp.tendsto _).comp hS).mul
    (hU.tendsto.comp ((hγ.tendsto h).comp (ceil_tendsto h hh)))

theorem measurable_Zf [MeasurableSpace Ω] (hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t))
    (y : SDEState n) : Measurable (Zf X y) := by
  unfold Zf
  split_ifs with h
  · exact measurable_pi_lambda _ fun q => hm y h _
  · exact measurable_const

/-- the Markov identity in functional form, for the reset path `Y` -/
theorem condY [MeasurableSpace Ω] (P : Measure Ω)
    (hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t)) (h0 : X x 0 =ᵐ[P] fun _ => x)
    (hM : MarkovId P X) (hx : x ∈ openOrthant n) (t : ℝ≥0)
    (F : (Past t → SDEState n) → ℝ≥0∞) (hF : Measurable F)
    (G : (ℚ → SDEState n) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ω, F (past (Yf X x) x t ω) * G (shiftPath (Yf X x) x t ω) ∂P =
      ∫⁻ ω, F (past (Yf X x) x t ω) * ∫⁻ ω', G (Zf X (Yp X x t ω) ω') ∂P ∂P := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hmx := hm x hxo
  have hae := Yp_ae X x P h0
  have e1 : ∫⁻ ω, F (past (Yf X x) x t ω) * G (shiftPath (Yf X x) x t ω) ∂P =
      ∫⁻ ω, F (past X x t ω) * G (shiftPath X x t ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have a1 : past (Yf X x) x t ω = past X x t ω := funext fun q => hω _
    have a2 : shiftPath (Yf X x) x t ω = shiftPath X x t ω := funext fun q => hω _
    rw [a1, a2]
  have e2 : ∫⁻ ω, F (past (Yf X x) x t ω) * ∫⁻ ω', G (Zf X (Yp X x t ω) ω') ∂P ∂P =
      ∫⁻ ω, F (past X x t ω) * ∫⁻ ω', G (Zf X (X x t ω) ω') ∂P ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have a1 : past (Yf X x) x t ω = past X x t ω := funext fun q => hω _
    rw [a1, hω t]
  rw [e1, e2]
  have hZ := measurable_Zf X hm
  have hp : Measurable (past X x t) := measurable_pi_lambda _ fun q => hmx _
  have hq : Measurable (shiftPath X x t) := measurable_pi_lambda _ fun q => hmx _
  have key := condFun P (past X x t) (shiftPath X x t) hp hq
    (fun ω => P.map (Zf X (X x t ω)))
    (fun Γ hΓ => by
      have hfun : (fun ω => P.map (Zf X (X x t ω)) Γ) = (fun y => P (Zf X y ⁻¹' Γ)) ∘ X x t :=
        funext fun ω => by simp only [Function.comp_apply]; rw [Measure.map_apply (hZ _) hΓ]
      rw [hfun]
      exact (hM x hx t univ MeasurableSet.univ Γ hΓ).1.comp (hmx t))
    (fun A Γ hA hΓ => by
      rw [(hM x hx t A hA Γ hΓ).2]
      refine setLIntegral_congr_fun (hp hA) (fun ω _ => ?_)
      rw [Measure.map_apply (hZ _) hΓ])
    F G hF hG
  rw [key]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_map hG (hZ _)]


theorem Hgen [MeasurableSpace Ω] (P : Measure Ω)
    (hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t)) (h0 : X x 0 =ᵐ[P] fun _ => x)
    (hM : MarkovId P X) (hx : x ∈ openOrthant n) (t : ℝ≥0)
    (U : SDEState n → ℝ) (I : Ω → ℝ≥0∞) (G : (ℚ → SDEState n) → ℝ≥0∞) (hG : Measurable G)
    (hIG : ∀ᵐ ω ∂P, I ω = G (shiftPath (Yf X x) x t ω))
    (F : Ω → ℝ≥0∞) (hF : Measurable[FF X x t] F)
    (hB : ∀ᵐ ω ∂P, F ω ≠ 0 →
      ∫⁻ ω', G (Zf X (Yp X x t ω) ω') ∂P ≤ ENNReal.ofReal (U (Yp X x t ω))) :
    ∫⁻ ω, F ω * I ω ∂P ≤ ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x t ω)) ∂P := by
  have hF' : Measurable[MeasurableSpace.comap (past (Yf X x) x t)
      (inferInstance : MeasurableSpace (Past t → SDEState n))] F := hF
  obtain ⟨F', hF'm, hFeq⟩ := hF'.exists_eq_measurable_comp
  have e1 : ∫⁻ ω, F ω * I ω ∂P =
      ∫⁻ ω, F' (past (Yf X x) x t ω) * G (shiftPath (Yf X x) x t ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hIG] with ω hω
    simp only [hω, hFeq, Function.comp_apply]
  rw [e1, condY X x P hm h0 hM hx t F' hF'm G hG]
  refine lintegral_mono_ae ?_
  filter_upwards [hB] with ω hω
  have hFω : F' (past (Yf X x) x t ω) = F ω := by simp only [hFeq, Function.comp_apply]
  rw [hFω]
  by_cases h : F ω = 0
  · simp [h]
  · gcongr
    exact hω h

/-- (H1) the one-step weighted supermartingale inequality at time `t`, from child A + Markov -/
theorem H1_inst [MeasurableSpace Ω] (P : Measure Ω)
    (hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t))
    (hc : ∀ y ∈ orthant n, ∀ ω, Continuous fun t => X y t ω)
    (h0 : X x 0 =ᵐ[P] fun _ => x) (hM : MarkovId P X) (hx : x ∈ openOrthant n)
    (hopen : ∀ y ∈ openOrthant n, ∀ t, ∀ᵐ ω ∂P, X y t ω ∈ openOrthant n)
    (r U : SDEState n → ℝ) (hr : Continuous r) (hUm : Measurable U)
    (hUc : ∀ z ∈ openOrthant n, ContinuousAt U z)
    (hA : ∀ y ∈ openOrthant n, ∀ h : ℝ≥0, ∫⁻ ω, ENNReal.ofReal (Real.exp
      (∫ s in (0 : ℝ)..(h : ℝ), r (X y s.toNNReal ω)) * U (X y h ω)) ∂P ≤ ENNReal.ofReal (U y))
    (t h : ℝ≥0) (F : Ω → ℝ≥0∞) (hF : Measurable[FF X x t] F) :
    ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (∫ s in (t : ℝ)..((t + h : ℝ≥0) : ℝ),
      r (Yp X x s.toNNReal ω)) * U (Yp X x (t + h) ω)) ∂P ≤
      ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x t ω)) ∂P := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hae := Yp_ae X x P h0
  refine Hgen X x P hm h0 hM hx t U _ (Gh r U h) (Gh_meas r U hr.measurable hUm h) ?_ F hF ?_
  · filter_upwards [hae, hopen x hx (t + h)] with ω hω hω'
    have hγ : Continuous fun s : ℝ => Yp X x (t + s.toNNReal) ω :=
      (Yp_cont X x (hc x hxo) ω).comp (continuous_const.add continuous_real_toNNReal)
    have hint : ∫ s in (0 : ℝ)..(h : ℝ), r (Yp X x (t + s.toNNReal) ω) =
        ∫ s in (t : ℝ)..((t + h : ℝ≥0) : ℝ), r (Yp X x s.toNNReal ω) := by
      rw [NNReal.coe_add]
      have := intervalIntegral.integral_comp_add_left (fun s => r (Yp X x s.toNNReal ω)) (t : ℝ)
        (a := 0) (b := (h : ℝ))
      rw [add_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs0 : 0 ≤ s := by rw [Set.uIcc_of_le (NNReal.coe_nonneg h)] at hs; exact hs.1
      show r (Yp X x (t + s.toNNReal) ω) = r (Yp X x ((↑t + s).toNNReal) ω)
      rw [Real.toNNReal_add (NNReal.coe_nonneg t) hs0, Real.toNNReal_coe]
    rw [Gh_eq r U hr h (NNReal.coe_nonneg h) _ hγ (shiftPath (Yf X x) x t ω) (fun q _ => rfl)
      (by simp only [Real.toNNReal_coe]; rw [hω]; exact hUc _ hω')]
    beta_reduce
    rw [hint, Real.toNNReal_coe]
  · filter_upwards [hae, hopen x hx t] with ω hω hω' _
    have hy : Yp X x t ω ∈ openOrthant n := by rw [hω t]; exact hω'
    have hyo : Yp X x t ω ∈ orthant n := fun i => (hy i).le
    have hZ : ∀ ω', Zf X (Yp X x t ω) ω' = rpath X (Yp X x t ω) ω' := fun ω' => by
      unfold Zf; rw [if_pos hyo]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hA _ hy h)
    filter_upwards [hopen _ hy h] with ω' hω''
    rw [hZ, Gh_eq r U hr h (NNReal.coe_nonneg h) (fun s => X (Yp X x t ω) s.toNNReal ω')
      ((hc _ hyo ω').comp continuous_real_toNNReal) (rpath X (Yp X x t ω) ω') (fun q _ => rfl)
      (by simp only [Real.toNNReal_coe]; exact hUc _ hω'')]
    simp only [Real.toNNReal_coe]

/-- (H2) the contraction step at time `t` (set `S` = where the contraction bound is known) -/
theorem H2_inst [MeasurableSpace Ω] (P : Measure Ω)
    (hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t))
    (hc : ∀ y ∈ orthant n, ∀ ω, Continuous fun t => X y t ω)
    (h0 : X x 0 =ᵐ[P] fun _ => x) (hM : MarkovId P X) (hx : x ∈ openOrthant n)
    (hopen : ∀ y ∈ openOrthant n, ∀ t, ∀ᵐ ω ∂P, X y t ω ∈ openOrthant n)
    (U : SDEState n → ℝ) (hUm : Measurable U) (hUc : ∀ z ∈ openOrthant n, ContinuousAt U z)
    (S : Set (SDEState n)) (T t : ℝ≥0) (htT : t ≤ T)
    (hB2 : ∀ y ∈ openOrthant n, y ∈ S →
      ∫⁻ ω, ENNReal.ofReal (U (X y (T - t) ω)) ∂P ≤ ENNReal.ofReal (U y))
    (F : Ω → ℝ≥0∞) (hF : Measurable[FF X x t] F) (hS : ∀ ω, F ω ≠ 0 → Yp X x t ω ∈ S) :
    ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x T ω)) ∂P ≤
      ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x t ω)) ∂P := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hae := Yp_ae X x P h0
  have hr0 : Continuous (fun _ : SDEState n => (0 : ℝ)) := continuous_const
  refine Hgen X x P hm h0 hM hx t U _ (Gh (fun _ => 0) U ((T - t : ℝ≥0) : ℝ))
    (Gh_meas _ U measurable_const hUm _) ?_ F hF ?_
  · filter_upwards [hae, hopen x hx T] with ω hω hω'
    have hγ : Continuous fun s : ℝ => Yp X x (t + s.toNNReal) ω :=
      (Yp_cont X x (hc x hxo) ω).comp (continuous_const.add continuous_real_toNNReal)
    have hT' : t + (((T - t : ℝ≥0) : ℝ)).toNNReal = T := by
      rw [Real.toNNReal_coe, add_tsub_cancel_of_le htT]
    rw [Gh_eq _ U hr0 _ (NNReal.coe_nonneg (T - t)) _ hγ (shiftPath (Yf X x) x t ω) (fun q _ => rfl)
      (by simp only [hT']; rw [hω]; exact hUc _ hω')]
    simp only [hT', intervalIntegral.integral_zero, Real.exp_zero, one_mul]
  · filter_upwards [hae, hopen x hx t] with ω hω hω' hF0
    have hy : Yp X x t ω ∈ openOrthant n := by rw [hω t]; exact hω'
    have hyo : Yp X x t ω ∈ orthant n := fun i => (hy i).le
    have hZ : ∀ ω', Zf X (Yp X x t ω) ω' = rpath X (Yp X x t ω) ω' := fun ω' => by
      unfold Zf; rw [if_pos hyo]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hB2 _ hy (hS ω hF0))
    filter_upwards [hopen _ hy (T - t)] with ω' hω''
    rw [hZ, Gh_eq _ U hr0 _ (NNReal.coe_nonneg (T - t)) (fun s => X (Yp X x t ω) s.toNNReal ω')
      ((hc _ hyo ω').comp continuous_real_toNNReal) (rpath X (Yp X x t ω) ω') (fun q _ => rfl)
      (by simp only [Real.toNNReal_coe]; exact hUc _ hω'')]
    simp only [Real.toNNReal_coe, intervalIntegral.integral_zero, Real.exp_zero, one_mul]

end OSEH

namespace OSEF
open StochKolmogorov.Extinct EthierKurtz OSEH

/-- the far case of (5.11)-(5.12), from the Markov identity, child A (weighted Dynkin for a rate
`r` with `r ≥ θ(γb - H)` and `r ≥ θγb` on `‖x‖₁ ≥ M`) and the contraction bound. -/
theorem far_case {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n)) (M : ℝ)
    (phat : Fin n → ℝ) (hp : ∀ i ∈ supp mu, 0 ≤ phat i) (hs : ∑ i ∈ supp mu, phat i ≤ 1)
    (pcheck : ℝ) (hpc : 0 < pcheck) (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (Te δe θ : ℝ) (hTe : 0 < Te) (hδe : 0 < δe) (hθ : 0 < θ)
    (γb Hc : ℝ) (hγb : 0 < γb) (hHγ : γb ≤ Hc) (hne : Hc < γb * ((ne : ℝ) - 1))
    (hcontract : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ openOrthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
          Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x)
    (hinv : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hM : MarkovId P X)
    (r : SDEState n → ℝ) (hr : Continuous r) (hr_lo : ∀ z, θ * (γb - Hc) ≤ r z)
    (hr_far : ∀ z ∈ orthant n, M ≤ l1 z → θ * γb ≤ r z)
    (hA : ∀ y ∈ openOrthant n, ∀ h : ℝ≥0, ∫⁻ ω, ENNReal.ofReal (Real.exp
      (∫ s in (0 : ℝ)..(h : ℝ), r (X y s.toNNReal ω)) * Utheta c mu phat pcheck θ (X y h ω)) ∂P ≤
        ENNReal.ofReal (Utheta c mu phat pcheck θ y)) :
    ∀ x ∈ openOrthant n,
      Utheta c mu phat pcheck θ x < varsigma c mu phat pcheck θ δe → M < l1 x →
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x := by
  intro x hx hU _
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t) := fun y hy => (hX.2.2 y hy).1
  have hcont : ∀ y ∈ orthant n, ∀ ω, Continuous fun t => X y t ω :=
    fun y hy => (hX.2.2 y hy).2.1
  have h0 : X x 0 =ᵐ[P] fun _ => x := (hX.2.2 x hxo).2.2.2.1
  set U := Utheta c mu phat pcheck θ with hUdef
  set ς := varsigma c mu phat pcheck θ δe with hςdef
  set T : ℝ≥0 := ((ne : ℝ) * Te).toNNReal with hTdef
  have hγlt : γb < γb * ((ne : ℝ) - 1) := lt_of_le_of_lt hHγ hne
  have hne2 : (2 : ℝ) < ne := by
    by_contra hh
    push_neg at hh
    nlinarith
  have hTreal : (T : ℝ) = ne * Te := Real.coe_toNNReal _ (by positivity)
  have hT0 : 0 < T := by
    rw [← NNReal.coe_pos, hTreal]; exact mul_pos (by linarith) hTe
  have hς0 : 0 < ς := by
    rw [hςdef]; unfold varsigma
    exact div_pos (Real.rpow_pos_of_pos hδe _)
      (Real.rpow_pos_of_pos (OSE.CU_pos c hc mu phat hp hs) _)
  have hUc : ∀ z ∈ openOrthant n, ContinuousAt U z :=
    fun z hz => Utheta_contAt c mu phat pcheck θ hθ.le z hz
  have hUm : Measurable U := OSE.measurable_Utheta c mu phat pcheck θ
  have hl1c : Continuous (fun z : SDEState n => l1 z) :=
    continuous_finset_sum _ fun i _ => (PiLp.continuous_apply 2 _ i).abs
  have hYorth : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Yp X x s ω ∈ orthant n := by
    have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, X x ((q : ℝ).toNNReal) ω ∈ openOrthant n :=
      ae_all_iff.2 fun q => hinv x hx _
    filter_upwards [hq, Yp_ae X x P h0] with ω hω hω' s
    have hcl : IsClosed (orthant n) := by
      have : orthant n = ⋂ i, {z : SDEState n | 0 ≤ z i} := by ext z; simp [orthant]
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)
    have h1 : Tendsto (fun k => (((dq s k : ℚ) : ℝ)).toNNReal) atTop (𝓝 s) := by
      have := (continuous_real_toNNReal.tendsto (s : ℝ)).comp (dq_tendsto s (NNReal.coe_nonneg s))
      rwa [Real.toNNReal_coe] at this
    have hlim := ((Yp_cont X x (hcont x hxo) ω).tendsto s).comp h1
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun k => by
      show Yp X x _ ω ∈ orthant n
      rw [hω']; exact fun i => (hω _ i).le)
  have hslack : (θ * γb + θ * (Hc - γb)) * Te ≤ θ * γb * (T : ℝ) := by
    rw [hTreal]
    have hH : Hc ≤ γb * ne := by nlinarith
    calc (θ * γb + θ * (Hc - γb)) * Te = θ * Te * Hc := by ring
      _ ≤ θ * Te * (γb * ne) := mul_le_mul_of_nonneg_left hH (by positivity)
      _ = θ * γb * (ne * Te) := by ring
  have hρa : ∀ᵐ ω ∂P, ∀ s : ℝ, M ≤ l1 (Yp X x s.toNNReal ω) →
      θ * γb ≤ r (Yp X x s.toNNReal ω) := by
    filter_upwards [hYorth] with ω hω s hs
    exact hr_far _ (hω _) hs
  have hρL : ∀ᵐ ω ∂P, ∀ s : ℝ, -(θ * (Hc - γb)) ≤ r (Yp X x s.toNNReal ω) :=
    Eventually.of_forall fun ω s => by have := hr_lo (Yp X x s.toNNReal ω); linarith
  have hu0 : ∀ᵐ ω ∂P, U (Yp X x 0 ω) = U x :=
    Eventually.of_forall fun ω => by rw [Yp_zero]
  have hH2 : ∀ t : ℝ≥0, (t : ℝ) + Te ≤ T → ∀ F : Ω → ℝ≥0∞, Measurable[FF X x t] F →
      (∀ ω, F ω ≠ 0 → l1 (Yp X x (t : ℝ).toNNReal ω) ≤ M ∧ U (Yp X x t ω) < ς) →
      ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x T ω)) ∂P ≤
        ∫⁻ ω, F ω * ENNReal.ofReal (U (Yp X x t ω)) ∂P := by
    intro t ht F hF hsupp
    have htT : t ≤ T := NNReal.coe_le_coe.1 (by linarith)
    refine H2_inst X x P hm hcont h0 hM hx hinv U hUm hUc {y | l1 y ≤ M ∧ U y < ς} T t htT
      ?_ F hF ?_
    · rintro y hy ⟨hyM, hyU⟩
      have hsub : ((T - t : ℝ≥0) : ℝ) = (T : ℝ) - t := NNReal.coe_sub htT
      have hmem : ((T - t : ℝ≥0) : ℝ) ∈ Set.Icc Te ((ne : ℝ) * Te) :=
        ⟨by rw [hsub]; linarith, by rw [hsub, ← hTreal]; linarith [NNReal.coe_nonneg t]⟩
      have hcoord := OSE.coord_lt_of_lt_varsigma c hc mu phat hp hs pcheck θ δe hpc hθ hδe y hy hyU
      obtain ⟨hint, hle⟩ := hcontract _ hmem y hy hyM hcoord
      rw [Real.toNNReal_coe] at hint hle
      rw [← ofReal_integral_eq_lintegral_ofReal hint]
      · refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
        have hU0 : 0 ≤ U y := OSE.Utheta_nonneg c hc mu phat pcheck θ y hy
        have hexp : Real.exp (-(1 / 2) * θ * ρe * ((T - t : ℝ≥0) : ℝ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ θ * ρe * ((T - t : ℝ≥0) : ℝ) :=
            mul_nonneg (mul_nonneg hθ.le hρe.le) (NNReal.coe_nonneg _)
          nlinarith
        exact mul_le_of_le_one_left hU0 hexp
      · filter_upwards [hinv y hy (T - t)] with ω hω
        exact OSE.Utheta_nonneg c hc mu phat pcheck θ _ hω
    · intro ω hω
      obtain ⟨h1, h2⟩ := hsupp ω hω
      rw [Real.toNNReal_coe] at h1
      exact ⟨h1, h2⟩
  have key := OSEG.far_glue P (FF X x) (FF_le X x (hm x hxo)) (FF_mono X x)
    (fun s ω => l1 (Yp X x s.toNNReal ω)) (fun s ω => r (Yp X x s.toNNReal ω))
    (fun t ω => U (Yp X x t ω))
    (fun ω => hl1c.comp ((Yp_cont X x (hcont x hxo) ω).comp continuous_real_toNNReal))
    (fun ω => hr.comp ((Yp_cont X x (hcont x hxo) ω).comp continuous_real_toNNReal))
    (fun t s hs => hl1c.measurable.comp
      (Yp_FF_meas X x (hcont x hxo) t _ (Real.toNNReal_le_iff_le_coe.2 hs)))
    (fun t s hs => hr.measurable.comp
      (Yp_FF_meas X x (hcont x hxo) t _ (Real.toNNReal_le_iff_le_coe.2 hs)))
    (fun t => hUm.comp (Yp_FF_meas X x (hcont x hxo) t t le_rfl))
    M (θ * γb) (θ * (Hc - γb)) ς Te (U x) T hT0 (mul_pos hθ hγb).le
    (mul_nonneg hθ.le (by linarith)) hς0.le hTe hslack hρa hρL hu0
    (fun t h F hF => H1_inst X x P hm hcont h0 hM hx hinv r U hr hUm hUc hA t h F hF)
    hH2
  have hUx : Utilde c mu phat pcheck θ δe x = U x := min_eq_right hU.le
  have hnn : 0 ≤ᵐ[P] fun ω => Utilde c mu phat pcheck θ δe (X x T ω) := by
    filter_upwards [hinv x hx T] with ω hω
    exact le_min hς0.le (OSE.Utheta_nonneg c hc mu phat pcheck θ _ hω)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    ((OSE.measurable_Utilde c mu phat pcheck θ δe).comp (hm x hxo T)).aestronglyMeasurable, hUx]
  have e : ∫⁻ ω, ENNReal.ofReal (Utilde c mu phat pcheck θ δe (X x T ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (min ς (U (Yp X x T ω))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [Yp_ae X x P h0] with ω hω
    rw [hω]; rfl
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal (OSE.Utheta_nonneg c hc mu phat pcheck θ x hx) key

end OSEF

namespace OSET
open StochKolmogorov.Extinct EthierKurtz

variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

theorem l1_continuous : Continuous (l1 (n := n)) :=
  continuous_finset_sum _ fun i _ => (PiLp.continuous_apply 2 _ i).abs

theorem bracket35_continuousOn (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ContinuousOn (bracket35 C c γb δ₀) (orthant n) := by
  have hf : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hg : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hx : ∀ i, Continuous fun x : SDEState n => x i := fun i => PiLp.continuous_apply 2 _ i
  have hden : ∀ x ∈ orthant n, 1 + ∑ i, c i * x i ≠ 0 := fun x hx' => by
    have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx' i)
    linarith
  have hD : Continuous fun x : SDEState n => 1 + ∑ i, c i * x i :=
    continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (hx i))
  unfold bracket35 cBracket
  refine ((((ContinuousOn.div ?_ hD.continuousOn hden).sub
    (ContinuousOn.div ?_ (hD.pow 2).continuousOn fun x hx' => pow_ne_zero 2 (hden x hx'))).add
      continuousOn_const).add (continuousOn_const.mul ?_)).add (continuousOn_const.mul ?_)
  · exact continuousOn_finset_sum _ fun i _ =>
      ((continuous_const.mul (hx i)).continuousOn).mul (hf i)
  · refine continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      continuousOn_finset_sum _ fun j _ => ?_)
    exact ((((continuous_const.mul continuous_const).mul (hx i)).mul (hx j)).continuousOn.mul
      (hg i)).mul (hg j)
  · exact continuousOn_finset_sum _ fun i _ =>
      (continuousOn_const.mul (hf i).abs).add ((hg i).pow 2)
  · exact continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
      (((hg i).mul (hg j)).mul continuousOn_const).abs

theorem B_continuousOn (C : Coeffs n) (c : SDEState n) (γb : ℝ)
    (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ContinuousOn (fun z => cBracket C c z + γb * ∑ i, (|C.f i z| + C.g i z ^ 2)) (orthant n) := by
  have hf : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hg : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hx : ∀ i, Continuous fun x : SDEState n => x i := fun i => PiLp.continuous_apply 2 _ i
  have hden : ∀ x ∈ orthant n, 1 + ∑ i, c i * x i ≠ 0 := fun x hx' => by
    have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx' i)
    linarith
  have hD : Continuous fun x : SDEState n => 1 + ∑ i, c i * x i :=
    continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (hx i))
  unfold cBracket
  refine ((ContinuousOn.div ?_ hD.continuousOn hden).sub
    (ContinuousOn.div ?_ (hD.pow 2).continuousOn fun x hx' => pow_ne_zero 2 (hden x hx'))).add
      (continuousOn_const.mul ?_)
  · exact continuousOn_finset_sum _ fun i _ =>
      ((continuous_const.mul (hx i)).continuousOn).mul (hf i)
  · refine continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      continuousOn_finset_sum _ fun j _ => ?_)
    exact ((((continuous_const.mul continuous_const).mul (hx i)).mul (hx j)).continuousOn.mul
      (hg i)).mul (hg j)
  · exact continuousOn_finset_sum _ fun i _ => (hf i).abs.add ((hg i).pow 2)

theorem bracket35_bddAbove (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) :
    BddAbove ((bracket35 C c γb δ₀) '' orthant n) := by
  obtain ⟨-, hC, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ0, hδγ, hδg⟩ := hδ
  set K : Set (SDEState n) := orthant n ∩ {x | l1 x ≤ R} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((orthant_isClosed).inter (isClosed_le l1_continuous continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : SDEState n)) (r := R)).subset fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    exact (euc_norm_le_sum' x).trans hx.2
  obtain ⟨M1, hM1⟩ := hKc.bddAbove_image
    ((bracket35_continuousOn C c γb δ₀ hc hC).mono Set.inter_subset_left)
  refine ⟨max M1 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hl : l1 x ≤ R
  · exact (hM1 ⟨x, ⟨hx, hl⟩, rfl⟩).trans (le_max_left _ _)
  · have h1 := hR x hx (not_le.1 hl).le
    have h2 := hδg x hx
    have hfa : 0 ≤ ∑ i, |C.f i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hs : ∑ i, (|C.f i x| + C.g i x ^ 2) = ∑ i, |C.f i x| + ∑ i, C.g i x ^ 2 :=
      Finset.sum_add_distrib
    have hs2 : ∑ i, (2 * |C.f i x| + C.g i x ^ 2) = 2 * ∑ i, |C.f i x| + ∑ i, C.g i x ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : 2 * δ₀ * ∑ i, |C.f i x| ≤ γb * ∑ i, |C.f i x| :=
      mul_le_mul_of_nonneg_right (by have := lt_of_lt_of_le hδγ (min_le_left _ _); linarith) hfa
    unfold bracket35
    rw [hs2]
    rw [hs] at h1
    refine le_trans ?_ (le_max_right _ _)
    linarith only [h1, h2, h3, hε]

theorem gamma_le_H (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) : γb ≤ Hconst C c γb δ₀ := by
  have h0 : (0 : SDEState n) ∈ orthant n := fun i => by simp
  refine le_trans ?_ (le_csSup (bracket35_bddAbove C c γb δ₀ hA hδ) ⟨0, h0, rfl⟩)
  have hcb : cBracket C c 0 = 0 := by unfold cBracket; simp
  have hδ0 := hδ.1
  have e1 : 0 ≤ δ₀ * ∑ i, (2 * |C.f i 0| + C.g i 0 ^ 2) :=
    mul_nonneg hδ0.le (Finset.sum_nonneg fun i _ => by positivity)
  have e2 : 0 ≤ 3 * δ₀ * ∑ i, ∑ j, |C.g i 0 * C.g j 0 * C.sig i j| :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
  unfold bracket35
  rw [hcb]
  linarith

theorem posPart_mem (z : SDEState n) : StochKolmogorov.Extinct.posPart z ∈ orthant n := fun i => by
  simp [StochKolmogorov.Extinct.posPart]

theorem posPart_of_mem (z : SDEState n) (hz : z ∈ orthant n) : StochKolmogorov.Extinct.posPart z = z := by
  ext i; simp [StochKolmogorov.Extinct.posPart, max_eq_left (hz i)]

theorem posPart_cont : Continuous (StochKolmogorov.Extinct.posPart (n := n)) := by
  unfold StochKolmogorov.Extinct.posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => (PiLp.continuous_apply 2 _ i).max continuous_const)

/-- the clock rate of the far-case argument -/
noncomputable def rate (C : Coeffs n) (c : SDEState n) (γb Hc θ : ℝ) (z : SDEState n) : ℝ :=
  θ * max (γb - Hc) (min γb (-(cBracket C c (StochKolmogorov.Extinct.posPart z) +
    γb * ∑ i, (|C.f i (StochKolmogorov.Extinct.posPart z)| + C.g i (StochKolmogorov.Extinct.posPart z) ^ 2))))

theorem rate_cont (C : Coeffs n) (c : SDEState n) (γb Hc θ : ℝ) (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (rate C c γb Hc θ) := by
  have hB := (B_continuousOn C c γb hc hC).comp_continuous posPart_cont posPart_mem
  unfold rate
  exact continuous_const.mul (continuous_const.max (continuous_const.min hB.neg))

theorem rate_lo (C : Coeffs n) (c : SDEState n) (γb Hc θ : ℝ) (hθ : 0 ≤ θ) (z : SDEState n) :
    θ * (γb - Hc) ≤ rate C c γb Hc θ z :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) hθ

theorem rate_far (C : Coeffs n) (c : SDEState n) (γb Hc θ M : ℝ) (hθ : 0 ≤ θ)
    (hM : IsRadiusM C c γb M) (z : SDEState n) (hz : z ∈ orthant n) (hl : M ≤ l1 z) :
    θ * γb ≤ rate C c γb Hc θ z := by
  unfold rate
  rw [posPart_of_mem z hz]
  have h1 := hM.2 z hz hl
  have h2 : γb ≤ -(cBracket C c z + γb * ∑ i, (|C.f i z| + C.g i z ^ 2)) := by
    rw [mul_add, mul_one] at h1; linarith
  exact mul_le_mul_of_nonneg_left ((min_eq_left h2).symm.le.trans (le_max_right _ _)) hθ

theorem rate_le (C : Coeffs n) (c : SDEState n) (γb Hc θ : ℝ) (hθ : 0 ≤ θ)
    (z : SDEState n) (hz : z ∈ orthant n) :
    rate C c γb Hc θ z ≤ θ * max (γb - Hc)
      (-(cBracket C c z + γb * ∑ i, (|C.f i z| + C.g i z ^ 2))) := by
  unfold rate
  rw [posPart_of_mem z hz]
  exact mul_le_mul_of_nonneg_left (max_le_max le_rfl (min_le_right _ _)) hθ

/-- the target from the three child conclusions: Markov identity, interior invariance
(Extinct.lemma_3_1 clause 2) and child A (weighted Dynkin). -/
theorem top {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1))
    (Te δe θ : ℝ) (hTe : 0 < Te) (hδe : 0 < δe) (hθ : 0 < θ ∧ θ < δ₀)
    (hcontract : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ openOrthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
          Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x)
    (hMk : OSEH.MarkovId P X)
    (hinv : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hAch : ∀ r : SDEState n → ℝ, Continuous r → (∃ K : ℝ, ∀ z, -K ≤ r z) →
      (∀ z ∈ orthant n, r z ≤ θ * max (γb - Hconst C c γb δ₀)
        (-(cBracket C c z + γb * ∑ i, (|C.f i z| + C.g i z ^ 2)))) →
      ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
        ∫⁻ ω, ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..(t : ℝ), r (X x s.toNNReal ω)) *
          Utheta c mu phat pcheck θ (X x t ω)) ∂P ≤
        ENNReal.ofReal (Utheta c mu phat pcheck θ x)) :
    ∀ x ∈ openOrthant n,
      Integrable (fun ω => Utilde c mu phat pcheck θ δe
        (X x (((ne : ℝ) * Te).toNNReal) ω)) P ∧
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x := by
  have hc : ∀ i, 0 < c i := hA.2.2.1
  have hC := hA.2.1
  have hγb : 0 < γb := hA.2.2.2.1
  have hp : ∀ i ∈ supp mu, 0 ≤ phat i := fun i hi => (hphat.1 i hi).1.le
  have hδ1 : δ₀ < 1 := lt_of_lt_of_le hδ₀.2.1 (min_le_right _ _)
  have hs : ∑ i ∈ supp mu, phat i ≤ 1 := by linarith [hphat.2]
  set Hc := Hconst C c γb δ₀ with hHc
  have hHγ : γb ≤ Hc := gamma_le_H C c γb δ₀ hA hδ₀
  set r := rate C c γb Hc θ with hrdef
  have hA' := hAch r (rate_cont C c γb Hc θ hA.2.2.1 hC)
    ⟨-(θ * (γb - Hc)), fun z => by linarith [rate_lo C c γb Hc θ hθ.1.le z]⟩
    (fun z hz => rate_le C c γb Hc θ hθ.1.le z hz)
  exact OSE.one_step_of_far P C B X hX c hc mu M phat hp hs pcheck hpcheck.1 ρe hρe ne Te δe θ
    hTe hδe hθ.1 hcontract hinv
    (OSEF.far_case P C B X hX c hc mu M phat hp hs pcheck hpcheck.1 ρe hρe ne Te δe θ hTe hδe
      hθ.1 γb Hc hγb hHγ hne hcontract hinv hMk r (rate_cont C c γb Hc θ hA.2.2.1 hC)
      (rate_lo C c γb Hc θ hθ.1.le) (fun z hz hl => rate_far C c γb Hc θ M hθ.1.le hM z hz hl) hA')

end OSET

-- ===== B (Markov identity from the fd conditional Markov child) =====

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false


namespace OSEB
open StochKolmogorov.Extinct EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- closed-orthant invariance from Lemma 3.1 clause 2 -/
theorem inv_closed [MeasurableSpace Ω] (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (h2 : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n →
      (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0)) :
    ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n := by
  classical
  intro x hx s
  have h := h2 (Finset.univ.filter fun i => 0 < x i) x hx (fun i => by simp)
  filter_upwards [h] with ω hω i
  by_cases hi : 0 < x i
  · exact ((hω s).1 i (by simp [hi])).le
  · exact ((hω s).2 i (by simp [hi])).ge

theorem markovId_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    OSEH.MarkovId P X := by
  intro x hx t A hA Γ hΓ
  exact StochKolmogorov.Classify.FDMC.condPath_of P
    (⟨C.f, C.g, C.Γ⟩ : StochKolmogorov.Classify.Coeffs n) B X hX hC hinv x hx t A hA Γ hΓ

end OSEB

-- ===== solution =====
open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1))
    (Te δe θ : ℝ) (hTe : 0 < Te) (hδe : 0 < δe) (hθ : 0 < θ ∧ θ < δ₀)
    (hcontract : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ openOrthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
          Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x) :
    ∀ x ∈ openOrthant n,
      Integrable (fun ω => Utilde c mu phat pcheck θ δe
        (X x (((ne : ℝ) * Te).toNNReal) ω)) P ∧
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x := by
  have h31 := StochKolmogorov.Extinct.lemma_3_1 hn P C B X hX c γb hA δ₀ hδ₀
  have hinvc := OSEB.inv_closed P X h31.2.1
  have hMk := OSEB.markovId_of P C B X hX hA.2.1 hinvc
  have hinv : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n := by
    intro x hx t
    have h := h31.2.1 Finset.univ x (fun i => (hx i).le) (fun i => by simp [hx i])
    filter_upwards [h] with ω hω i
    exact (hω t).1 i (Finset.mem_univ i)
  exact OSET.top hn P C B X hX c γb hA mu h13 M hM δ₀ hδ₀ phat hphat pcheck hpcheck ρe hρe ne hne
    Te δe θ hTe hδe hθ hcontract hMk hinv
    (fun r hr hK hrle x hx t =>
      StochKolmogorov.Extinct.weighted_lyapunov_dynkin hn P C B X hX c γb hA δ₀ hδ₀ mu phat hphat
        pcheck hpcheck θ hθ r hr hK.choose hK.choose_spec hrle x hx t)
