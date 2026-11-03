-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T01:02:35.999197+00:00
-- url     : https://prove2.me/submissions/ace5b9c6-c71b-47c5-aefe-9f4ad76b7466

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz_weighted
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_4

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace L57.FDM

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

end L57.FDM

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace L57.Dfam

variable {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

/-- countable family of balls: centre from a dense sequence, radius `1/(m+1)`. -/
noncomputable def ball' (j : ℕ) : Set E :=
  Metric.ball (TopologicalSpace.denseSeq E (Nat.unpair j).1) (1 / (((Nat.unpair j).2 : ℝ) + 1))

theorem exists_ball' {G : Set E} (hG : IsOpen G) {x : E} (hx : x ∈ G) :
    ∃ j, x ∈ ball' (E := E) j ∧ ball' (E := E) j ⊆ G := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hG x hx
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hr)
  have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨i, hi⟩ := (Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq E)) x _ hm0
  refine ⟨Nat.pair i m, ?_, ?_⟩
  · simp only [ball', Nat.unpair_pair, Metric.mem_ball]
    exact hi
  · intro z hz
    simp only [ball', Nat.unpair_pair, Metric.mem_ball] at hz
    apply hb
    rw [Metric.mem_ball]
    have := dist_triangle z (TopologicalSpace.denseSeq E i) x
    rw [dist_comm (TopologicalSpace.denseSeq E i) x] at this
    linarith

/-- finite unions of basic balls. -/
noncomputable def U (s : Finset ℕ) : Set E := ⋃ j ∈ s, ball' j

theorem isOpen_U (s : Finset ℕ) : IsOpen (U (E := E) s) :=
  isOpen_biUnion fun _ _ => Metric.isOpen_ball

/-- the tent function. -/
noncomputable def tent (s : Finset ℕ) (k : ℕ) (x : E) : ℝ :=
  min 1 (((k : ℝ) + 1) * Metric.infDist x (U s)ᶜ)

theorem continuous_tent (s : Finset ℕ) (k : ℕ) : Continuous (tent (E := E) s k) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem tent_nonneg (s : Finset ℕ) (k : ℕ) (x : E) : 0 ≤ tent s k x :=
  le_min zero_le_one (mul_nonneg (by positivity) Metric.infDist_nonneg)

theorem tent_le_one (s : Finset ℕ) (k : ℕ) (x : E) : tent s k x ≤ 1 := min_le_left _ _

theorem norm_tent_le (s : Finset ℕ) (k : ℕ) (x : E) : ‖tent s k x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg s k x)]; exact tent_le_one s k x

/-- the tent as a bounded continuous function. -/
noncomputable def hD (s : Finset ℕ) (k : ℕ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (tent s k) (continuous_tent s k) 1
    (norm_tent_le s k)

theorem hD_apply (s : Finset ℕ) (k : ℕ) (x : E) : hD s k x = tent s k x := rfl

theorem tent_eq_zero {s : Finset ℕ} (k : ℕ) {x : E} (hx : x ∉ U s) : tent s k x = 0 := by
  have : Metric.infDist x (U s)ᶜ = 0 := Metric.infDist_zero_of_mem hx
  simp [tent, this]

variable [MeasurableSpace E] [BorelSpace E]

/-- the approximating index sets for an open set `G`. -/
noncomputable def sG (G : Set E) (m : ℕ) : Finset ℕ := by
  classical exact (Finset.range m).filter fun j => ball' (E := E) j ⊆ G

theorem U_sG_subset (G : Set E) (m : ℕ) : U (sG G m) ⊆ G := by
  intro x hx
  simp only [U, Set.mem_iUnion] at hx
  obtain ⟨j, hj, hx⟩ := hx
  classical
  simp only [sG, Finset.mem_filter] at hj
  exact hj.2 hx

theorem tent_le_indicator (G : Set E) (m k : ℕ) (x : E) :
    tent (sG G m) k x ≤ G.indicator 1 x := by
  by_cases hx : x ∈ U (sG G m)
  · rw [Set.indicator_of_mem (U_sG_subset G m hx)]; exact tent_le_one _ _ _
  · rw [tent_eq_zero k hx]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem tent_tendsto_indicator {G : Set E} (hG : IsOpen G) (hGu : G ≠ Set.univ) (x : E) :
    Tendsto (fun m => tent (sG G m) m x) atTop (𝓝 (G.indicator 1 x)) := by
  by_cases hx : x ∈ G
  · rw [Set.indicator_of_mem hx]
    obtain ⟨j, hxj, hjG⟩ := exists_ball' hG hx
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem G).1 hGu
    -- for `m > j`, `x ∈ U (sG G m)` with a uniform distance to the complement
    have hsub : ∀ m, j < m → ball' (E := E) j ⊆ U (sG G m) := by
      intro m hm y hy
      simp only [U, Set.mem_iUnion]
      classical
      exact ⟨j, by simp [sG, Finset.mem_filter, Finset.mem_range, hm, hjG], hy⟩
    have hne : (ball' (E := E) j)ᶜ.Nonempty := ⟨z, fun h => hz (hjG h)⟩
    have hd : 0 < Metric.infDist x (ball' (E := E) j)ᶜ :=
      (IsClosed.notMem_iff_infDist_pos (Metric.isOpen_ball.isClosed_compl) hne).1
        (fun h => h hxj)
    set d := Metric.infDist x (ball' (E := E) j)ᶜ
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / d)
    refine tendsto_atTop_of_eventually_const (i₀ := max (j + 1) M) fun m hm => ?_
    have hmj : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) (le_trans (le_max_left _ _) hm)
    have hmM : (M : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
    have hcne : (U (E := E) (sG G m))ᶜ.Nonempty := ⟨z, fun h => hz (U_sG_subset G m h)⟩
    have hdd : d ≤ Metric.infDist x (U (sG G m))ᶜ :=
      Metric.infDist_le_infDist_of_subset (Set.compl_subset_compl.2 (hsub m hmj)) hcne
    have h1 : 1 ≤ ((m : ℝ) + 1) * Metric.infDist x (U (sG G m))ᶜ := by
      have h2 : 1 < ((m : ℝ) + 1) * d := by
        rw [div_lt_iff₀ hd] at hM
        nlinarith
      nlinarith
    simp only [tent]
    exact min_eq_left h1
  · rw [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds.congr fun m =>
      (tent_eq_zero m fun h => hx (U_sG_subset G m h)).symm

theorem integral_tent_tendsto (μ : Measure E) [IsFiniteMeasure μ] {G : Set E} (hG : IsOpen G)
    (hGu : G ≠ Set.univ) :
    Tendsto (fun m => ∫ x, tent (sG G m) m x ∂μ) atTop (𝓝 (μ.real G)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun m => (continuous_tent (sG G m) m).aestronglyMeasurable) (integrable_const 1)
    (fun m => Eventually.of_forall fun x => norm_tent_le _ _ x)
    (Eventually.of_forall fun x => tent_tendsto_indicator hG hGu x)
  rwa [integral_indicator_one hG.measurableSet] at h

theorem tent_lip (s : Finset ℕ) (k : ℕ) (x y : E) :
    |tent s k x - tent s k y| ≤ ((k : ℝ) + 1) * dist x y := by
  unfold tent
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (k:ℝ) + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_sub_le_iff]
  constructor
  · linarith [Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := (U s)ᶜ)]
  · linarith [Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := (U s)ᶜ), dist_comm x y]

theorem eq_of_tents (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ s k, ∫ x, tent s k x ∂μ = ∫ x, tent s k x ∂ν) : μ = ν := by
  have hopen : ∀ G : Set E, IsOpen G → μ G = ν G := by
    intro G hG
    by_cases hGu : G = Set.univ
    · subst hGu; simp
    have h1 := integral_tent_tendsto μ hG hGu
    have h2 := integral_tent_tendsto ν hG hGu
    simp_rw [h] at h1
    have h3 : μ.real G = ν.real G := tendsto_nhds_unique h1 h2
    rw [measureReal_def, measureReal_def] at h3
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3
  refine ext_of_generate_finite {G : Set E | IsOpen G} ?_ isPiSystem_isOpen
    (fun G hG => hopen G hG) (by simp)
  rw [BorelSpace.measurable_eq (α := E)]; rfl

end L57.Dfam

namespace L57
open Set

variable {Ω : Type*} [MeasurableSpace Ω]

theorem slice_meas {Z : ℝ → Ω → ℝ} (hZ : Measurable (fun p : Ω × ℝ => Z p.2 p.1)) (ω : Ω) :
    Measurable (fun s => Z s ω) :=
  hZ.comp (measurable_const.prodMk measurable_id)

theorem iInt {Z : ℝ → Ω → ℝ} (hZ : Measurable (fun p : Ω × ℝ => Z p.2 p.1)) {M : ℝ}
    (hM : ∀ s ω, |Z s ω| ≤ M) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s => Z s ω) volume a b :=
  (intervalIntegrable_const (c := M)).mono_fun' (slice_meas hZ ω).aestronglyMeasurable
    (ae_of_all _ fun s => by show ‖Z s ω‖ ≤ M; rw [Real.norm_eq_abs]; exact hM s ω)

theorem meas_S {Z : ℝ → Ω → ℝ} (hZ : Measurable (fun p : Ω × ℝ => Z p.2 p.1)) (T : ℝ) :
    Measurable (fun ω => ∫ s in Ioc 0 T, Z s ω) :=
  (hZ.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))).measurable

theorem sq_bound (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → ℝ)
    (hZ : Measurable (fun p : Ω × ℝ => Z p.2 p.1)) {M t : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ω, |Z s ω| ≤ M)
    (ht : 0 ≤ t) (hdec : ∀ s r, 0 ≤ s → s + t ≤ r → ∫ ω, Z s ω * Z r ω ∂P = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, (∫ s in Ioc 0 T, Z s ω) ^ 2 ∂P ≤ 2 * t * M ^ 2 * T := by
  set μT : Measure ℝ := volume.restrict (Ioc 0 T) with hμT
  haveI : IsFiniteMeasure μT := by
    rw [hμT]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  let F : Ω × (ℝ × ℝ) → ℝ := fun q => Z q.2.1 q.1 * Z q.2.2 q.1
  have hF : Measurable F :=
    (hZ.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hZ.comp (measurable_fst.prodMk measurable_snd.snd))
  have hFb : ∀ q, ‖F q‖ ≤ M ^ 2 := by
    intro q
    simp only [F, Real.norm_eq_abs, abs_mul, sq]
    exact mul_le_mul (hM _ _) (hM _ _) (abs_nonneg _) hM0
  have hFi : Integrable F (P.prod (μT.prod μT)) :=
    (integrable_const (M ^ 2)).mono' hF.aestronglyMeasurable (ae_of_all _ hFb)
  let c : ℝ × ℝ → ℝ := fun p => ∫ ω, F (ω, p) ∂P
  have hci : Integrable c (μT.prod μT) := hFi.integral_prod_right
  let band : Set (ℝ × ℝ) := {p | |p.1 - p.2| < t}
  have hband : MeasurableSet band :=
    measurableSet_lt ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable)
      measurable_const
  have hpos : ∀ᵐ p ∂(μT.prod μT), p ∈ Ioc 0 T ×ˢ Ioc 0 T := by
    rw [hμT, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hcb : ∀ᵐ p ∂(μT.prod μT), c p ≤ band.indicator (fun _ => M ^ 2) p := by
    filter_upwards [hpos] with p hp
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hp
    by_cases hpb : p ∈ band
    · rw [Set.indicator_of_mem hpb]
      calc c p ≤ |c p| := le_abs_self _
        _ ≤ ∫ ω, |F (ω, p)| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ ω, M ^ 2 ∂P := by
            refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
              (integrable_const _) (ae_of_all _ fun ω => ?_)
            have := hFb (ω, p); rwa [Real.norm_eq_abs] at this
        _ = M ^ 2 := by simp
    · rw [Set.indicator_of_notMem hpb]
      have hge : t ≤ |p.1 - p.2| := not_lt.1 hpb
      rcases le_abs'.1 hge with h | h
      · -- p.1 - p.2 ≤ -t : p.1 + t ≤ p.2
        have := hdec p.1 p.2 h1.le (by linarith)
        exact le_of_eq this
      · have := hdec p.2 p.1 h2.le (by linarith)
        have e : c p = ∫ ω, Z p.2 ω * Z p.1 ω ∂P := by
          simp only [c, F]; congr 1; funext ω; ring
        rw [e, this]
  have hbandm : (μT.prod μT) band ≤ ENNReal.ofReal (2 * t * T) := by
    rw [Measure.prod_apply hband]
    have hsl : ∀ s, μT (Prod.mk s ⁻¹' band) ≤ ENNReal.ofReal (2 * t) := by
      intro s
      calc μT (Prod.mk s ⁻¹' band) ≤ volume (Prod.mk s ⁻¹' band) := Measure.restrict_le_self _
        _ ≤ volume (Ioo (s - t) (s + t)) := by
            refine measure_mono fun r hr => ?_
            simp only [band, Set.mem_preimage, Set.mem_setOf_eq] at hr
            rw [abs_lt] at hr
            exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
        _ = ENNReal.ofReal (2 * t) := by rw [Real.volume_Ioo]; ring_nf
    calc ∫⁻ s, μT (Prod.mk s ⁻¹' band) ∂μT ≤ ∫⁻ s, ENNReal.ofReal (2 * t) ∂μT :=
          lintegral_mono hsl
      _ = ENNReal.ofReal (2 * t) * μT univ := lintegral_const _
      _ = ENNReal.ofReal (2 * t * T) := by
          rw [hμT, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
            ← ENNReal.ofReal_mul (by linarith)]
  have hbr : (μT.prod μT).real band ≤ 2 * t * T := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbandm
  have hsq : ∀ ω, (∫ s, Z s ω ∂μT) ^ 2 = ∫ p, F (ω, p) ∂(μT.prod μT) := by
    intro ω
    rw [sq]
    exact (integral_prod_mul (fun s => Z s ω) (fun s => Z s ω)).symm
  calc ∫ ω, (∫ s in Ioc 0 T, Z s ω) ^ 2 ∂P
        = ∫ ω, ∫ p, F (ω, p) ∂(μT.prod μT) ∂P := integral_congr_ae (ae_of_all _ hsq)
    _ = ∫ p, c p ∂(μT.prod μT) := by
        have := integral_integral_swap (μ := P) (ν := μT.prod μT)
          (f := fun ω p => F (ω, p)) hFi
        exact this
    _ ≤ ∫ p, band.indicator (fun _ => M ^ 2) p ∂(μT.prod μT) :=
        integral_mono_ae hci ((integrable_const _).indicator hband) hcb
    _ = (μT.prod μT).real band * M ^ 2 := by
        rw [integral_indicator_const _ hband, smul_eq_mul]
    _ ≤ (2 * t * T) * M ^ 2 := mul_le_mul_of_nonneg_right hbr (sq_nonneg _)
    _ = 2 * t * M ^ 2 * T := by ring

/-- deterministic interpolation between squares -/
theorem interp {f : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ a b, IntervalIntegrable f volume a b) (hfb : ∀ s, |f s| ≤ M)
    (h : ∀ j : ℕ, ∀ᶠ m : ℕ in atTop,
      |∫ s in (0:ℝ)..(((m:ℝ) + 1) ^ 2), f s| < ((j:ℝ) + 1)⁻¹ * ((m:ℝ) + 1) ^ 2) :
    Tendsto (fun T => T⁻¹ * ∫ s in (0:ℝ)..T, f s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hη)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (h j)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (6 * M / η)
  set K : ℕ := max (m₀ + 1) (N₀ + 1) with hK
  refine ⟨(K : ℝ) ^ 2, fun T hT => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by
    have : 1 ≤ K := le_trans (Nat.le_add_left 1 m₀) (le_max_left _ _)
    exact_mod_cast this
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  set N : ℕ := ⌊Real.sqrt T⌋₊ with hN
  have hKN : K ≤ N := by
    rw [hN]; apply Nat.le_floor
    have := Real.sqrt_le_sqrt hT
    rwa [Real.sqrt_sq (by positivity)] at this
  have hN1 : (1 : ℝ) ≤ N := le_trans hK1 (by exact_mod_cast hKN)
  have hNT : (N : ℝ) ^ 2 ≤ T := by
    have h1 : (N : ℝ) ≤ Real.sqrt T := Nat.floor_le (Real.sqrt_nonneg _)
    calc (N : ℝ) ^ 2 ≤ (Real.sqrt T) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      _ = T := Real.sq_sqrt hT0
  have hTN : T < ((N : ℝ) + 1) ^ 2 := by
    have h1 : Real.sqrt T < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    calc T = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT0).symm
      _ < ((N : ℝ) + 1) ^ 2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
  -- m := N - 1
  have hNpos : 1 ≤ N := by exact_mod_cast hN1
  set m : ℕ := N - 1 with hm
  have hmN : ((m : ℝ) + 1) = N := by
    rw [hm]; rw [Nat.cast_sub hNpos]; ring
  have hmm₀ : m₀ ≤ m := by
    have : m₀ + 1 ≤ N := le_trans (le_max_left _ _) hKN
    omega
  have hS := hm₀ m hmm₀
  rw [hmN] at hS
  have hsplit : ∫ s in (0:ℝ)..T, f s =
      (∫ s in (0:ℝ)..((N:ℝ) ^ 2), f s) + ∫ s in ((N:ℝ) ^ 2)..T, f s :=
    (intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)).symm
  have hrest : |∫ s in ((N:ℝ) ^ 2)..T, f s| ≤ M * (T - (N:ℝ) ^ 2) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N:ℝ) ^ 2) (b := T)
      (C := M) (f := f) (fun x _ => by rw [Real.norm_eq_abs]; exact hfb x)
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ T - (N:ℝ) ^ 2 by linarith)] at this
    exact this
  have hN0 : (0 : ℝ) < N := by linarith
  have hNN₀ : (N₀ : ℝ) + 1 ≤ N := by
    have : N₀ + 1 ≤ N := le_trans (le_max_right _ _) hKN
    exact_mod_cast this
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hNT
  have hI : |∫ s in (0:ℝ)..T, f s| ≤ ((j:ℝ) + 1)⁻¹ * (N:ℝ) ^ 2 + M * (3 * N) := by
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h3 : M * (T - (N:ℝ) ^ 2) ≤ M * (3 * N) := by
      apply mul_le_mul_of_nonneg_left _ hM0; nlinarith
    linarith [hS.le]
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hTpos]
  have hη2 : M * (3 * N) / (N:ℝ) ^ 2 < η / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have h6 : 6 * M / η < (N : ℝ) := by linarith
    rw [div_lt_iff₀ hη] at h6
    nlinarith
  have hj' : ((j:ℝ) + 1)⁻¹ < η / 2 := by rw [← one_div]; exact hj
  calc T⁻¹ * |∫ s in (0:ℝ)..T, f s|
      ≤ T⁻¹ * (((j:ℝ) + 1)⁻¹ * (N:ℝ) ^ 2 + M * (3 * N)) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hTpos.le)
    _ ≤ ((N:ℝ) ^ 2)⁻¹ * (((j:ℝ) + 1)⁻¹ * (N:ℝ) ^ 2 + M * (3 * N)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact inv_anti₀ (by positivity) hNT
    _ = ((j:ℝ) + 1)⁻¹ + M * (3 * N) / (N:ℝ) ^ 2 := by
        field_simp
    _ < η / 2 + η / 2 := add_lt_add hj' hη2
    _ = η := by ring

theorem lln (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → ℝ)
    (hZ : Measurable (fun p : Ω × ℝ => Z p.2 p.1)) {M t : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ω, |Z s ω| ≤ M)
    (ht : 0 ≤ t) (hdec : ∀ s r, 0 ≤ s → s + t ≤ r → ∫ ω, Z s ω * Z r ω ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0:ℝ)..T, Z s ω) atTop (𝓝 0) := by
  let S : ℕ → Ω → ℝ := fun m ω => ∫ s in (0:ℝ)..(((m:ℝ) + 1) ^ 2), Z s ω
  have hSeq : ∀ m ω, S m ω = ∫ s in Ioc 0 (((m:ℝ) + 1) ^ 2), Z s ω := fun m ω =>
    intervalIntegral.integral_of_le (by positivity)
  have hSm : ∀ m, Measurable (S m) := fun m => by
    have : S m = fun ω => ∫ s in Ioc 0 (((m:ℝ) + 1) ^ 2), Z s ω := funext (hSeq m)
    rw [this]; exact meas_S hZ _
  have hSb : ∀ m ω, |S m ω| ≤ M * ((m:ℝ) + 1) ^ 2 := by
    intro m ω
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ((m:ℝ) + 1) ^ 2)
      (C := M) (f := fun s => Z s ω) (fun x _ => by rw [Real.norm_eq_abs]; exact hM x ω)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (show (0:ℝ) ≤ ((m:ℝ) + 1) ^ 2 by positivity)] at this
    exact this
  have hS2 : ∀ m, ∫ ω, (S m ω) ^ 2 ∂P ≤ 2 * t * M ^ 2 * ((m:ℝ) + 1) ^ 2 := by
    intro m
    have h := sq_bound P Z hZ hM0 hM ht hdec (T := ((m:ℝ) + 1) ^ 2) (by positivity)
    simp_rw [← hSeq] at h
    exact h
  have key : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      |S m ω| < ((j:ℝ) + 1)⁻¹ * ((m:ℝ) + 1) ^ 2 := by
    intro j
    set ε : ℝ := ((j:ℝ) + 1)⁻¹ with hε
    have hεp : 0 < ε := by positivity
    set Kc : ℝ := 2 * t * M ^ 2 / ε ^ 2 with hKc
    have hKc0 : 0 ≤ Kc := by positivity
    let A : ℕ → Set Ω := fun m => {ω | ε * ((m:ℝ) + 1) ^ 2 ≤ |S m ω|}
    have hA : ∀ m, P (A m) ≤ ENNReal.ofReal (Kc * (1 / ((m:ℝ) + 1) ^ 2)) := by
      intro m
      set c0 : ℝ := (ε * ((m:ℝ) + 1) ^ 2) ^ 2 with hc0
      have hc0p : 0 < c0 := by positivity
      have hsub : A m ⊆ {ω | ENNReal.ofReal c0 ≤ ENNReal.ofReal ((S m ω) ^ 2)} := by
        intro ω hω
        simp only [A, Set.mem_setOf_eq] at hω ⊢
        apply ENNReal.ofReal_le_ofReal
        rw [hc0, ← sq_abs (S m ω)]
        exact pow_le_pow_left₀ (by positivity) hω 2
      have hint : Integrable (fun ω => (S m ω) ^ 2) P :=
        (integrable_const ((M * ((m:ℝ) + 1) ^ 2) ^ 2)).mono' ((hSm m).pow_const 2).aestronglyMeasurable
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hSb m ω) 2)
      have hl : ∫⁻ ω, ENNReal.ofReal ((S m ω) ^ 2) ∂P = ENNReal.ofReal (∫ ω, (S m ω) ^ 2 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)).symm
      calc P (A m) ≤ P {ω | ENNReal.ofReal c0 ≤ ENNReal.ofReal ((S m ω) ^ 2)} := measure_mono hsub
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((S m ω) ^ 2) ∂P) / ENNReal.ofReal c0 :=
            meas_ge_le_lintegral_div
              (ENNReal.measurable_ofReal.comp ((hSm m).pow_const 2)).aemeasurable
              (by simpa using hc0p) ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (2 * t * M ^ 2 * ((m:ℝ) + 1) ^ 2) / ENNReal.ofReal c0 := by
            rw [hl]; exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (hS2 m)) _
        _ = ENNReal.ofReal (2 * t * M ^ 2 * ((m:ℝ) + 1) ^ 2 / c0) :=
            (ENNReal.ofReal_div_of_pos hc0p).symm
        _ = ENNReal.ofReal (Kc * (1 / ((m:ℝ) + 1) ^ 2)) := by
            congr 1
            rw [hc0, hKc]
            field_simp
    have hsum0 : Summable (fun m : ℕ => Kc * (1 / ((m:ℝ) + 1) ^ 2)) := by
      have h1 := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      refine (h1.mul_left Kc).congr fun m => ?_
      push_cast; ring
    have hsum : ∑' m, P (A m) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum0]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    exact hω.mono fun m hm => by
      simp only [A, Set.mem_setOf_eq, not_le] at hm
      exact hm
  filter_upwards [ae_all_iff.2 key] with ω hω
  exact interp hM0 (iInt hZ hM ω) (fun s => hM s ω) hω

end L57

namespace L57.Mod
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

def toP (C : Coeffs n) : StochKolmogorov.Persist.Coeffs n := ⟨C.f, C.g, C.Γ⟩

theorem past_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (W : ℝ≥0 → Ω → SDEState d) (ξ : Ω → SDEState d) {s u : ℝ≥0} (h : s ≤ u) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ u := by
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  exact iSup_le fun v => le_iSup_of_le (⟨v.1, le_trans v.2 h⟩ : Set.Iic u) le_rfl

theorem path_orthant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x : SDEState n} (hx : x ∈ orthant n) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, X x s ω ∈ orthant n := by
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, X x ((q:ℝ).toNNReal) ω ∈ orthant n := fun q =>
    StochKolmogorov.Persist.orthant_invariance_closed P (toP C) B hB hC hx (hXs x hx) _
  filter_upwards [ae_all_iff.2 hq] with ω hω
  have hcl : IsClosed {r : ℝ | X x r.toNNReal ω ∈ orthant n} :=
    FDM.orthant_isClosed.preimage (((hXs x hx).2.1 ω).comp continuous_real_toNNReal)
  have hd := (Rat.denseRange_cast (𝕜 := ℝ)).closure_range
  have huniv : Set.univ ⊆ {r : ℝ | X x r.toNNReal ω ∈ orthant n} := by
    rw [← hd]
    exact hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hω q)
  intro s
  have := huniv (Set.mem_univ (s : ℝ))
  simpa [Real.toNNReal_coe] using this

theorem jmeas {Ω : Type*} [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (hm : ∀ t, Measurable (X x t)) (hc : ∀ ω, Continuous fun t => X x t ω) :
    Measurable (fun p : Ω × ℝ => X x p.2.toNNReal p.1) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (ω : Ω) => X x r.toNNReal ω)
    (fun ω => (hc ω).comp continuous_real_toNNReal) (fun r => hm _)
  exact h.comp measurable_swap

theorem lln_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {f : SDEState n → ℝ} (hf : Measurable f) (hf1 : ∀ y, |f y| ≤ 1) {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hfL : ∀ y y', |f y - f y'| ≤ Lf * ‖y - y'‖) {t : ℝ} (ht : 0 < t) :
    ∃ g : SDEState n → ℝ, Measurable g ∧ (∀ y, |g y| ≤ 1) ∧
      (∀ y ∈ orthant n, g y = ∫ ω, f (X y t.toNNReal ω) ∂P) ∧
      ∀ x ∈ orthant n, ∀ᵐ ω ∂P, Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0:ℝ)..T,
        (f (X x (s + t).toNNReal ω) - g (X x s.toNNReal ω))) atTop (𝓝 0) := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := FDM.kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  obtain ⟨g, hgm, hgK, hgD, hgM⟩ := EthierKurtz.sde_markov_property_lipschitz_weighted hB hσc hbc
    s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX' t.toNNReal hf hf1 hLf hfL
  refine ⟨g, hgm, hgK, hgD, fun x hx => ?_⟩
  have hinv := path_orthant P C B X ⟨hP, hB, hXs⟩ hC hx
  have hjm := jmeas X x (hXs x hx).1 (hXs x hx).2.1
  let Z : ℝ → Ω → ℝ := fun s ω => f (X x (s + t).toNNReal ω) - g (X x s.toNNReal ω)
  have hZm : Measurable (fun p : Ω × ℝ => Z p.2 p.1) := by
    have h1 : Measurable (fun p : Ω × ℝ => X x (p.2 + t).toNNReal p.1) :=
      hjm.comp (measurable_fst.prodMk (measurable_snd.add_const t))
    exact (hf.comp h1).sub (hgm.comp hjm)
  have hZb : ∀ s ω, |Z s ω| ≤ 2 := fun s ω => by
    simp only [Z]
    calc |f (X x (s + t).toNNReal ω) - g (X x s.toNNReal ω)|
        ≤ |f (X x (s + t).toNNReal ω)| + |g (X x s.toNNReal ω)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf1 _) (hgK _)
      _ = 2 := by norm_num
  have hdec : ∀ s r, 0 ≤ s → s + t ≤ r → ∫ ω, Z s ω * Z r ω ∂P = 0 := by
    intro s r hs hsr
    have hr : 0 < r := by linarith
    have hu0 : 0 < r.toNNReal := Real.toNNReal_pos.2 hr
    have hrt : (r + t).toNNReal = r.toNNReal + t.toNNReal := Real.toNNReal_add hr.le ht.le
    let Zw : Ω → ℝ := fun ω => Z s ω / 2
    have hpast : ∀ v : ℝ≥0, v ≤ r.toNNReal →
        Measurable[completedBrownianPast P B (fun _ => x) r.toNNReal] (X x v) :=
      fun v hv => ((hXs x hx).2.2.1 v).mono (past_mono P B _ hv) le_rfl
    have hv1 : (s + t).toNNReal ≤ r.toNNReal := Real.toNNReal_le_toNNReal hsr
    have hv2 : s.toNNReal ≤ r.toNNReal := Real.toNNReal_le_toNNReal (by linarith)
    have hZwp : Measurable[completedBrownianPast P B (fun _ => x) r.toNNReal] Zw :=
      ((hf.comp (hpast _ hv1)).sub (hgm.comp (hpast _ hv2))).div_const 2
    have hZwm : Measurable Zw :=
      ((hf.comp ((hXs x hx).1 _)).sub (hgm.comp ((hXs x hx).1 _))).div_const 2
    have hZw1 : ∀ ω, |Zw ω| ≤ 1 := fun ω => by
      have := hZb s ω
      simp only [Zw, abs_div, abs_two]
      linarith
    have hM := hgM x hx r.toNNReal hu0 (hinv.mono fun ω h => h _) Zw hZwp hZwm hZw1
    rw [← hrt] at hM
    have hI1 : Integrable (fun ω => Zw ω * f (X x (r + t).toNNReal ω)) P :=
      (integrable_const (1:ℝ)).mono' (hZwm.mul (hf.comp ((hXs x hx).1 _))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_one₀ (hZw1 ω) (abs_nonneg _) (hf1 _))
    have hI2 : Integrable (fun ω => Zw ω * g (X x r.toNNReal ω)) P :=
      (integrable_const (1:ℝ)).mono' (hZwm.mul (hgm.comp ((hXs x hx).1 _))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_one₀ (hZw1 ω) (abs_nonneg _) (hgK _))
    have key : ∀ ω, Z s ω * Z r ω =
        2 * (Zw ω * f (X x (r + t).toNNReal ω) - Zw ω * g (X x r.toNNReal ω)) := by
      intro ω; simp only [Zw, Z]; ring
    calc ∫ ω, Z s ω * Z r ω ∂P
        = ∫ ω, 2 * (Zw ω * f (X x (r + t).toNNReal ω) - Zw ω * g (X x r.toNNReal ω)) ∂P :=
          integral_congr_ae (ae_of_all _ key)
      _ = 2 * ((∫ ω, Zw ω * f (X x (r + t).toNNReal ω) ∂P) -
            ∫ ω, Zw ω * g (X x r.toNNReal ω) ∂P) := by
          rw [integral_const_mul, integral_sub hI1 hI2]
      _ = 0 := by rw [hM, sub_self, mul_zero]
  exact L57.lln P Z hZm (by norm_num) hZb ht.le hdec

end L57.Mod

namespace L57.Main
open StochKolmogorov.Classify EthierKurtz L57.Dfam

theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

/-- Assumption 1.4 is monotone in `δ₁` (only large `‖x‖ ≥ 1` matters). -/
theorem a14_mono {n : ℕ} (C : Coeffs n) {δ₁ δ' : ℝ} (h14 : Assumption14 C δ₁)
    (hδ' : 0 < δ') (hle : δ' ≤ δ₁) : Assumption14 C δ' := by
  refine ⟨hδ', ?_⟩
  have hev : ∀ᶠ x in comap l1 atTop ⊓ 𝓟 (orthant n), 1 ≤ l1 x :=
    Filter.Eventually.filter_mono inf_le_left
      (Filter.tendsto_comap.eventually (eventually_ge_atTop 1))
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => ?_) (hev.mono fun x hx => ?_) h14.2
  · have hl : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hl _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD
  · have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD


variable {n : ℕ}

theorem occ_integral {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) (h : SDEState n →ᵇ ℝ) :
    ∫ y, h y ∂(occ X x T ω) = T⁻¹ * ∫ s in (0 : ℝ)..T, h (X x s.toNNReal ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  unfold occ
  rw [integral_smul_measure, integral_map hm.aemeasurable h.continuous.aestronglyMeasurable,
    intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le, smul_eq_mul]

theorem posPart_eq {y : SDEState n} (hy : y ∈ orthant n) : posPart y = y := by
  ext i
  rw [L57.FDM.posPart_apply']
  exact max_eq_left (hy i)

theorem gw_lower (C : Coeffs n) (c : SDEState n) {m δ : ℝ} (hm : 0 < m) (hδ : 0 ≤ δ)
    (hmc : ∀ i, m ≤ c i) {y : SDEState n} (hy : y ∈ orthant n) :
    (1 + m * ‖y‖) ^ δ ≤ growthWeight C c δ y := by
  have hnorm : ‖y‖ ≤ ∑ i, y i := by
    have := L57.FDM.euc_norm_le_sum' y
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => abs_of_nonneg (hy i)))
  have hcy : m * ‖y‖ ≤ ∑ i, c i * y i := by
    calc m * ‖y‖ ≤ m * ∑ i, y i := mul_le_mul_of_nonneg_left hnorm hm.le
      _ = ∑ i, m * y i := Finset.mul_sum _ _ _
      _ ≤ ∑ i, c i * y i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hmc i) (hy i)
  have h0 : 0 ≤ 1 + m * ‖y‖ := by positivity
  have h1 : (1 + m * ‖y‖) ^ δ ≤ (1 + ∑ i, c i * y i) ^ δ :=
    Real.rpow_le_rpow h0 (by linarith) hδ
  have h2 : (1 : ℝ) ≤ 1 + ∑ i, (|C.f i y| + C.g i y ^ 2) := by
    have : 0 ≤ ∑ i, (|C.f i y| + C.g i y ^ 2) :=
      Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (sq_nonneg _)
    linarith
  unfold growthWeight
  calc (1 + m * ‖y‖) ^ δ ≤ (1 + ∑ i, c i * y i) ^ δ := h1
    _ = (1 + ∑ i, c i * y i) ^ δ * 1 := (mul_one _).symm
    _ ≤ (1 + ∑ i, c i * y i) ^ δ * (1 + ∑ i, (|C.f i y| + C.g i y ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)

theorem exists_min_pos (c : SDEState n) (hc : c ∈ openOrthant n) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ c i := by
  refine ⟨(1 + ∑ i, (c i)⁻¹)⁻¹, ?_, fun i => ?_⟩
  · have : 0 ≤ ∑ i, (c i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hc i)).le
    positivity
  · have hle : (c i)⁻¹ ≤ 1 + ∑ j, (c j)⁻¹ := by
      have := Finset.single_le_sum (f := fun j => (c j)⁻¹)
        (fun j _ => (inv_pos.2 (hc j)).le) (Finset.mem_univ i)
      linarith
    calc (1 + ∑ j, (c j)⁻¹)⁻¹ ≤ ((c i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (hc i)) hle
      _ = c i := inv_inv _

theorem tight_of {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (C : Coeffs n) (c : SDEState n) (hc : c ∈ openOrthant n) {δ Kh : ℝ} (hδ : 0 < δ) (hKh : 0 < Kh)
    (hcont : Continuous fun s => X x s ω) (horth : ∀ s, X x s ω ∈ orthant n)
    (hbd : ∀ᶠ t : ℝ in atTop, ∫⁻ s in Set.Icc (0:ℝ) t,
      ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω)) ≤ ENNReal.ofReal ((Kh + 1) * t)) :
    IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hbd
  set φ : ℝ → SDEState n := fun s => X x s.toNNReal ω with hφ
  have hφc : Continuous φ := hcont.comp continuous_real_toNNReal
  set T1 : ℝ := max T₀ 1 with hT1
  obtain ⟨ρ₀, hρ₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T1)).exists_bound_of_continuousOn
    hφc.continuousOn
  obtain ⟨m, hm, hmc⟩ := exists_min_pos c hc
  set e : ℝ := (min ε 1).toReal with he
  have hmin_ne : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have he0 : 0 < e := ENNReal.toReal_pos (ne_of_gt (lt_min hε one_pos)) hmin_ne
  have heε : ENNReal.ofReal e ≤ ε := by
    rw [he, ENNReal.ofReal_toReal hmin_ne]; exact min_le_left _ _
  set Wb : ℝ := (|Kh| + 1) / e + 1 with hWb
  have hWb0 : 0 < Wb := by positivity
  set ρ : ℝ := max ρ₀ ((Wb ^ δ⁻¹ - 1) / m) with hρ
  set W : ℝ := (1 + m * ρ) ^ δ with hW
  have hWge : Wb ≤ W := by
    have h1 : Wb ^ δ⁻¹ ≤ 1 + m * ρ := by
      have : (Wb ^ δ⁻¹ - 1) / m ≤ ρ := le_max_right _ _
      rw [div_le_iff₀ hm] at this
      linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hWb0.le _) h1 hδ.le
    rwa [Real.rpow_inv_rpow hWb0.le hδ.ne'] at h2
  have hW0 : 0 < W := lt_of_lt_of_le hWb0 hWge
  set K : Set (SDEState n) := orthant n ∩ Metric.closedBall 0 ρ with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 ρ).inter_left L57.FDM.orthant_isClosed
  refine ⟨K, hKc, ?_⟩
  rintro μ ⟨t, ht1, rfl⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have hA : MeasurableSet (φ ⁻¹' Kᶜ) := hφc.measurable hKc.isClosed.isOpen_compl.measurableSet
  have hocc : occ X x t ω Kᶜ =
      (ENNReal.ofReal t)⁻¹ * volume (φ ⁻¹' Kᶜ ∩ Set.Icc 0 t) := by
    unfold occ
    rw [Measure.smul_apply, Measure.map_apply hφc.measurable hKc.isClosed.isOpen_compl.measurableSet,
      Measure.restrict_apply hA, smul_eq_mul]
  rw [hocc]
  by_cases htT : t ≤ T1
  · have hempty : φ ⁻¹' Kᶜ ∩ Set.Icc 0 t = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hs hsI
      apply hs
      refine ⟨horth _, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hρ₀ s ⟨hsI.1, hsI.2.trans htT⟩).trans (le_max_left _ _)
    rw [hempty, measure_empty, mul_zero]; simp
  · push_neg at htT
    have htT0 : T₀ ≤ t := le_trans (le_max_left _ _) htT.le
    have hbt := hT₀ t htT0
    set v := volume (φ ⁻¹' Kᶜ ∩ Set.Icc 0 t) with hv
    have hvfin : v ≠ ⊤ := ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0:ℝ)) (b := t)).ne
      (measure_mono Set.inter_subset_right)
    have hind : ∀ s, (φ ⁻¹' Kᶜ).indicator (fun _ => ENNReal.ofReal W) s ≤
        ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω)) := by
      intro s
      by_cases hs : s ∈ φ ⁻¹' Kᶜ
      · rw [Set.indicator_of_mem hs]
        apply ENNReal.ofReal_le_ofReal
        have hsK : φ s ∉ K := hs
        have hnorm : ρ < ‖φ s‖ := by
          by_contra hcon
          push_neg at hcon
          exact hsK ⟨horth _, by rw [Metric.mem_closedBall, dist_zero_right]; exact hcon⟩
        calc W = (1 + m * ρ) ^ δ := rfl
          _ ≤ (1 + m * ‖φ s‖) ^ δ := by
              refine Real.rpow_le_rpow (by
                have : 0 ≤ ρ := le_trans (le_trans (norm_nonneg _) (hρ₀ 0 ⟨le_rfl, by
                  rw [hT1]; exact le_trans zero_le_one (le_max_right _ _)⟩)) (le_max_left _ _)
                positivity) ?_ hδ.le
              nlinarith
          _ ≤ growthWeight C c δ (φ s) := gw_lower C c hm hδ.le hmc (horth _)
      · rw [Set.indicator_of_notMem hs]; simp
    have hmk : ENNReal.ofReal W * v ≤ ENNReal.ofReal ((Kh + 1) * t) := by
      calc ENNReal.ofReal W * v
          = ∫⁻ s in Set.Icc (0:ℝ) t, (φ ⁻¹' Kᶜ).indicator (fun _ => ENNReal.ofReal W) s := by
            rw [lintegral_indicator_const hA, Measure.restrict_apply hA]
        _ ≤ ∫⁻ s in Set.Icc (0:ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω)) :=
            lintegral_mono hind
        _ ≤ ENNReal.ofReal ((Kh + 1) * t) := hbt
    have hvr : v = ENNReal.ofReal v.toReal := (ENNReal.ofReal_toReal hvfin).symm
    have hv0 : 0 ≤ v.toReal := ENNReal.toReal_nonneg
    have hreal : W * v.toReal ≤ (Kh + 1) * t := by
      rw [hvr, ← ENNReal.ofReal_mul hW0.le] at hmk
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmk
    rw [hvr, ← ENNReal.ofReal_inv_of_pos ht0, ← ENNReal.ofReal_mul (inv_nonneg.2 ht0.le)]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) heε
    have hK1 : Kh + 1 ≤ |Kh| + 1 := by linarith [le_abs_self Kh]
    have h3 : t⁻¹ * v.toReal ≤ (Kh + 1) / W := by
      rw [le_div_iff₀ hW0]
      have := mul_le_mul_of_nonneg_left hreal (inv_nonneg.2 ht0.le)
      calc t⁻¹ * v.toReal * W = t⁻¹ * (W * v.toReal) := by ring
        _ ≤ t⁻¹ * ((Kh + 1) * t) := this
        _ = Kh + 1 := by field_simp
    calc t⁻¹ * v.toReal ≤ (Kh + 1) / W := h3
      _ ≤ (|Kh| + 1) / W := div_le_div_of_nonneg_right hK1 hW0.le
      _ ≤ (|Kh| + 1) / Wb := div_le_div_of_nonneg_left (by positivity) hWb0 hWge
      _ ≤ e := by
          rw [div_le_iff₀ hWb0, hWb]
          have : (|Kh| + 1) / e * e = |Kh| + 1 := div_mul_cancel₀ _ he0.ne'
          nlinarith

/-- the deterministic identity behind invariance: along the limit sequence the LLN forces
`∫ f dπ = ∫ G' dπ`. -/
theorem ident_of_lln {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hcont : Continuous fun s => X x s ω) (horth : ∀ s, X x s ω ∈ orthant n)
    (f G' : SDEState n →ᵇ ℝ) (hf1 : ∀ y, |f y| ≤ 1) (G : SDEState n → ℝ)
    (hGG : ∀ y ∈ orthant n, G' y = G y) {t : ℝ} (ht : 0 < t)
    (hlln : Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0:ℝ)..T,
      (f (X x (s + t).toNNReal ω) - G (X x s.toNNReal ω))) atTop (𝓝 0))
    (π : Measure (SDEState n)) (ts : ℕ → ℝ) (h1 : ∀ k, 1 ≤ ts k) (hts : Tendsto ts atTop atTop)
    (hconv : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) :
    ∫ y, f y ∂π = ∫ y, G' y ∂π := by
  set φ : ℝ → SDEState n := fun s => X x s.toNNReal ω with hφ
  have hφc : Continuous φ := hcont.comp continuous_real_toNNReal
  have hfc : Continuous fun s => f (φ s) := f.continuous.comp hφc
  have hGc : Continuous fun s => G' (φ s) := G'.continuous.comp hφc
  have hfsc : Continuous fun s => f (φ (s + t)) := hfc.comp (continuous_add_right t)
  have hlln' : Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0:ℝ)..T,
      (f (φ (s + t)) - G' (φ s))) atTop (𝓝 0) := by
    refine hlln.congr fun T => ?_
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hφ, hGG _ (horth _)]
  have hA := ((hconv f).sub (hconv G'))
  have hB : Tendsto (fun k => ∫ y, f y ∂(occ X x (ts k) ω) - ∫ y, G' y ∂(occ X x (ts k) ω))
      atTop (𝓝 0) := by
    have hC := hlln'.comp hts
    have hE : Tendsto (fun k => 2 * t * (ts k)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp hts).const_mul (2 * t)
      simpa using this
    refine Metric.tendsto_atTop.2 fun η hη => ?_
    obtain ⟨k₁, hk₁⟩ := Metric.tendsto_atTop.1 hC (η / 2) (half_pos hη)
    obtain ⟨k₂, hk₂⟩ := Metric.tendsto_atTop.1 hE (η / 2) (half_pos hη)
    refine ⟨max k₁ k₂, fun k hk => ?_⟩
    have hT : 0 < ts k := lt_of_lt_of_le one_pos (h1 k)
    set T := ts k with hTdef
    have e1 := hk₁ k (le_trans (le_max_left _ _) hk)
    have e2 := hk₂ k (le_trans (le_max_right _ _) hk)
    simp only [Function.comp, dist_zero_right, Real.norm_eq_abs] at e1 e2
    rw [abs_of_nonneg (by positivity)] at e2
    rw [← hTdef] at e1 e2
    rw [occ_integral X x ω hcont hT, occ_integral X x ω hcont hT, dist_zero_right,
      Real.norm_eq_abs, ← mul_sub]
    rw [intervalIntegral.integral_sub (hfsc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)] at e1
    -- shift identity
    have hsh : ∫ s in (0:ℝ)..T, f (φ (s + t)) = ∫ s in t..(T + t), f (φ s) := by
      have := intervalIntegral.integral_comp_add_right (fun s => f (φ s)) (a := 0) (b := T) t
      simpa using this
    have hsplit1 : ∫ s in (0:ℝ)..(T + t), f (φ s) =
        (∫ s in (0:ℝ)..t, f (φ s)) + ∫ s in t..(T + t), f (φ s) :=
      (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)).symm
    have hsplit2 : ∫ s in (0:ℝ)..(T + t), f (φ s) =
        (∫ s in (0:ℝ)..T, f (φ s)) + ∫ s in T..(T + t), f (φ s) :=
      (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)).symm
    have hb1 : |∫ s in (0:ℝ)..t, f (φ s)| ≤ t := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
        (f := fun s => f (φ s)) (fun s _ => by rw [Real.norm_eq_abs]; exact hf1 _)
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos ht, one_mul] at this
      exact this
    have hb2 : |∫ s in T..(T + t), f (φ s)| ≤ t := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T + t) (C := 1)
        (f := fun s => f (φ s)) (fun s _ => by rw [Real.norm_eq_abs]; exact hf1 _)
      rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos ht, one_mul] at this
      exact this
    set I0 := ∫ s in (0:ℝ)..T, f (φ s)
    set Is := ∫ s in (0:ℝ)..T, f (φ (s + t))
    set Ig := ∫ s in (0:ℝ)..T, G' (φ s)
    have hdiff : |Is - I0| ≤ 2 * t := by
      have : Is - I0 = (∫ s in T..(T + t), f (φ s)) - ∫ s in (0:ℝ)..t, f (φ s) := by
        rw [hsh]; linarith [hsplit1, hsplit2]
      rw [this]
      calc |(∫ s in T..(T + t), f (φ s)) - ∫ s in (0:ℝ)..t, f (φ s)|
          ≤ |∫ s in T..(T + t), f (φ s)| + |∫ s in (0:ℝ)..t, f (φ s)| := abs_sub _ _
        _ ≤ t + t := add_le_add hb2 hb1
        _ = 2 * t := by ring
    have hTi : 0 < T⁻¹ := inv_pos.2 hT
    calc |T⁻¹ * (I0 - Ig)| = |T⁻¹ * (Is - Ig) - T⁻¹ * (Is - I0)| := by ring_nf
      _ ≤ |T⁻¹ * (Is - Ig)| + |T⁻¹ * (Is - I0)| := abs_sub _ _
      _ ≤ |T⁻¹ * (Is - Ig)| + 2 * t * T⁻¹ := by
          have h5 : |T⁻¹ * (Is - I0)| ≤ 2 * t * T⁻¹ := by
            rw [abs_mul, abs_of_pos hTi]; nlinarith
          linarith
      _ < η / 2 + η / 2 := add_lt_add e1 e2
      _ = η := by ring
  have := tendsto_nhds_unique hA hB
  linarith

/-- limit points live on the orthant. -/
theorem compl_zero {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hcont : Continuous fun s => X x s ω) (horth : ∀ s, X x s ω ∈ orthant n)
    (π : Measure (SDEState n)) [IsProbabilityMeasure π] (ts : ℕ → ℝ) (h1 : ∀ k, 1 ≤ ts k)
    (hconv : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) :
    π (orthant n)ᶜ = 0 := by
  set G := (orthant n)ᶜ with hG
  have hGo : IsOpen G := L57.FDM.orthant_isClosed.isOpen_compl
  have hGu : G ≠ Set.univ := by
    intro h
    have h0 : (0 : SDEState n) ∈ orthant n := fun i => by simp
    have : (0 : SDEState n) ∈ G := h ▸ Set.mem_univ _
    exact this h0
  have hz : ∀ m, ∫ y, tent (sG G m) m y ∂π = 0 := by
    intro m
    have hc := hconv (hD (sG G m) m)
    have h0 : ∀ k, ∫ y, hD (sG G m) m y ∂(occ X x (ts k) ω) = 0 := by
      intro k
      rw [occ_integral X x ω hcont (lt_of_lt_of_le one_pos (h1 k))]
      have : ∀ s : ℝ, hD (sG G m) m (X x s.toNNReal ω) = 0 := by
        intro s
        rw [hD_apply]
        refine le_antisymm ?_ (tent_nonneg _ _ _)
        have := tent_le_indicator G m m (X x s.toNNReal ω)
        rwa [Set.indicator_of_notMem (show X x s.toNNReal ω ∉ G from fun h => h (horth _))] at this
      simp [this]
    simp_rw [h0] at hc
    have h3 : ∫ y, hD (sG G m) m y ∂π = 0 := (tendsto_nhds_unique hc tendsto_const_nhds)
    simpa only [hD_apply] using h3
  have ht := integral_tent_tendsto π hGo hGu
  simp_rw [hz] at ht
  have h2 : π.real G = 0 := tendsto_nhds_unique ht tendsto_const_nhds
  rwa [measureReal_eq_zero_iff] at h2

end L57.Main

namespace L57.Fin
open StochKolmogorov.Classify EthierKurtz L57.Dfam L57.Main L57.Mod

noncomputable def tq (q : ℚ) : ℝ := if 0 < q then (q : ℝ) else 1

theorem tq_pos (q : ℚ) : 0 < tq q := by
  unfold tq; split_ifs with h
  · exact_mod_cast h
  · exact one_pos

theorem tq_eq {q : ℚ} (h : 0 < q) : tq q = q := by unfold tq; rw [if_pos h]

theorem tent_meas {n : ℕ} (s : Finset ℕ) (k : ℕ) : Measurable (tent (E := SDEState n) s k) :=
  (continuous_tent s k).measurable

theorem tent_abs {n : ℕ} (s : Finset ℕ) (k : ℕ) (y : SDEState n) : |tent s k y| ≤ 1 := by
  rw [abs_of_nonneg (tent_nonneg s k y)]; exact tent_le_one s k y

theorem main {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ x ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω} ∧
        ∀ π ∈ limitSet X x ω, IsInvariant P X π := by
  classical
  intro x hx
  have hX0 := hX
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  have hC := hA.2.1
  obtain ⟨δ₀, hδ₀⟩ := exists_isDelta0 C γb hA.2.2.2.1
  have hδ'0 : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' : Assumption14 C (min δ₁ δ₀) := a14_mono C h14 hδ'0 (min_le_left _ _)
  obtain ⟨⟨Kh, hKh, h54⟩, -⟩ := StochKolmogorov.Classify.lemma_5_4 hn P C B X hX0 c γb hA δ₀ hδ₀
    (min δ₁ δ₀) h14' (min_le_right _ _)
  obtain ⟨-, -, -, -, -, -, hfel⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P (toP C) B X hX0 c γb hA δ₀ hδ₀
  obtain ⟨hκ, -, -, -⟩ := StochKolmogorov.Persist.markov_property P (toP C) B X hX0 c γb hA
  choose κ hκM hκeq using hκ
  have hex : ∀ (s : Finset ℕ) (k : ℕ) (q : ℚ), ∃ g : SDEState n → ℝ, Measurable g ∧
      (∀ y, |g y| ≤ 1) ∧
      (∀ y ∈ orthant n, g y = ∫ ω, tent s k (X y (tq q).toNNReal ω) ∂P) ∧
      ∀ x ∈ orthant n, ∀ᵐ ω ∂P, Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0:ℝ)..T,
        (tent s k (X x (u + tq q).toNNReal ω) - g (X x u.toNNReal ω))) atTop (𝓝 0) := by
    intro s k q
    exact lln_markov P C B X hX0 hC (tent_meas s k) (tent_abs s k) (Lf := (k:ℝ) + 1)
      (by positivity) (fun y y' => by rw [← dist_eq_norm]; exact tent_lip s k y y') (tq_pos q)
  choose G hGm hG1 hGeq hGlln using hex
  have hGcont : ∀ s k q, ContinuousOn (G s k q) (orthant n) := by
    intro s k q
    refine (hfel (tq q).toNNReal (hD s k)).congr fun y hy => ?_
    rw [hGeq s k q y hy]; rfl
  let G' : Finset ℕ → ℕ → ℚ → (SDEState n →ᵇ ℝ) := fun s k q =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun y => G s k q (posPart y))
      ((hGcont s k q).comp_continuous L57.FDM.continuous_posPart
        (fun y => L57.FDM.posPart_mem_orthant y)) 1
      (fun y => by rw [Real.norm_eq_abs]; exact hG1 s k q _)
  have hG'eq : ∀ s k q, ∀ y ∈ orthant n, G' s k q y = G s k q y := by
    intro s k q y hy
    show G s k q (posPart y) = G s k q y
    rw [posPart_eq hy]
  -- inner integrals against the kernels
  have hΨy : ∀ (s : Finset ℕ) (k : ℕ) (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ t y) =
        ∫⁻ ω', ENNReal.ofReal (tent s k (X y t ω')) ∂P := by
    intro s k t y hy
    rw [hκeq t y hy]
    simp only [StochKolmogorov.Persist.trans]
    exact lintegral_map (ENNReal.measurable_ofReal.comp (tent_meas s k)) ((hXs y hy).1 t)
  have hinner : ∀ (s : Finset ℕ) (k : ℕ) (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      ∫⁻ ω', ENNReal.ofReal (tent s k (X y t ω')) ∂P =
        ENNReal.ofReal (∫ ω', tent s k (X y t ω') ∂P) := by
    intro s k t y hy
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (ae_of_all _ fun ω' => tent_nonneg s k _)).symm
    exact (integrable_const (1:ℝ)).mono'
      ((tent_meas s k).comp ((hXs y hy).1 t)).aestronglyMeasurable
      (ae_of_all _ fun ω' => by rw [Real.norm_eq_abs]; exact tent_abs s k _)
  have hκle : ∀ (s : Finset ℕ) (k : ℕ) (t : ℝ≥0) (y : SDEState n),
      ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ t y) ≤ 1 := by
    intro s k t y
    haveI := hκM t
    calc ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ t y) ≤ ∫⁻ z, 1 ∂(κ t y) :=
          lintegral_mono fun z => ENNReal.ofReal_le_one.2 (tent_le_one s k z)
      _ = 1 := by simp
  filter_upwards [path_orthant P C B X hX0 hC hx, h54 x hx,
    ae_all_iff.2 (fun i : Finset ℕ × ℕ × ℚ => hGlln i.1 i.2.1 i.2.2 x hx)] with ω hω1 hω2 hω3
  have hcont : Continuous fun s => X x s ω := (hXs x hx).2.1 ω
  refine ⟨tight_of X x ω C c hA.2.2.1 (δ := min δ₁ δ₀) hδ'0 hKh hcont hω1 (hω2 1 one_pos), ?_⟩
  intro π hπ
  obtain ⟨hπP, ts, h1, hts, hconv⟩ := hπ
  haveI := hπP
  have hπc : π (orthant n)ᶜ = 0 := compl_zero X x ω hcont hω1 π ts h1 hconv
  have hπa : ∀ᵐ y ∂π, y ∈ orthant n := by
    rw [ae_iff]; exact hπc
  have hid : ∀ s k q, ∫ y, hD s k y ∂π = ∫ y, G' s k q y ∂π := fun s k q =>
    ident_of_lln X x ω hcont hω1 (hD s k) (G' s k q) (fun y => tent_abs s k y) (G s k q)
      (hG'eq s k q) (tq_pos q) (hω3 (s, k, q)) π ts h1 hts hconv
  -- rational times
  have hR : ∀ (s : Finset ℕ) (k : ℕ) (q : ℚ), 0 < q →
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ (q : ℝ).toNNReal y) ∂π =
        ENNReal.ofReal (∫ y, tent s k y ∂π) := by
    intro s k q hq
    have htq : (tq q).toNNReal = (q : ℝ).toNNReal := by rw [tq_eq hq]
    have hGi : Integrable (G s k q) π :=
      (integrable_const (1:ℝ)).mono' (hGm s k q).aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hG1 s k q y)
    have hG0 : 0 ≤ᵐ[π] G s k q := by
      filter_upwards [hπa] with y hy
      rw [Pi.zero_apply, hGeq s k q y hy]
      exact integral_nonneg fun ω' => tent_nonneg s k _
    calc ∫⁻ y, ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ (q : ℝ).toNNReal y) ∂π
        = ∫⁻ y, ENNReal.ofReal (G s k q y) ∂π := by
          refine lintegral_congr_ae ?_
          filter_upwards [hπa] with y hy
          rw [hΨy s k _ y hy, hinner s k _ y hy, hGeq s k q y hy, htq]
      _ = ENNReal.ofReal (∫ y, G s k q y ∂π) := (ofReal_integral_eq_lintegral_ofReal hGi hG0).symm
      _ = ENNReal.ofReal (∫ y, G' s k q y ∂π) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hπa] with y hy
          exact (hG'eq s k q y hy).symm
      _ = ENNReal.ofReal (∫ y, tent s k y ∂π) := by rw [← hid s k q]; rfl
  -- all times, by dominated convergence along rationals from the right
  have hAll : ∀ (s : Finset ℕ) (k : ℕ) (t : ℝ≥0),
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ t y) ∂π =
        ENNReal.ofReal (∫ y, tent s k y ∂π) := by
    intro s k t
    have hq : ∀ m : ℕ, ∃ q : ℚ, (t : ℝ) < q ∧ (q : ℝ) < t + 1 / ((m : ℝ) + 1) := fun m =>
      exists_rat_btwn (by have : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
                          linarith)
    choose q hq1 hq2 using hq
    have hqpos : ∀ m, 0 < q m := fun m => by
      have : (0:ℝ) < q m := lt_of_le_of_lt t.2 (hq1 m)
      exact_mod_cast this
    have hqt : Tendsto (fun m => ((q m : ℚ) : ℝ)) atTop (𝓝 (t : ℝ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun m => (hq1 m).le) (fun m => (hq2 m).le)
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (t : ℝ)
      simpa using this
    have hqt' : Tendsto (fun m => ((q m : ℚ) : ℝ).toNNReal) atTop (𝓝 t) := by
      have := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hqt
      rw [Real.toNNReal_coe] at this
      exact this
    have hdct : Tendsto (fun m => ∫⁻ y, ∫⁻ z, ENNReal.ofReal (tent s k z)
        ∂(κ ((q m : ℚ) : ℝ).toNNReal y) ∂π) atTop
        (𝓝 (∫⁻ y, ∫⁻ z, ENNReal.ofReal (tent s k z) ∂(κ t y) ∂π)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
        (fun m => (ENNReal.measurable_ofReal.comp (tent_meas s k)).lintegral_kernel)
        (fun m => ae_of_all _ fun y => hκle s k _ y) (by simp) ?_
      filter_upwards [hπa] with y hy
      have hin : Tendsto (fun m => ∫⁻ ω', ENNReal.ofReal (tent s k (X y ((q m : ℚ) : ℝ).toNNReal ω')) ∂P)
          atTop (𝓝 (∫⁻ ω', ENNReal.ofReal (tent s k (X y t ω')) ∂P)) := by
        refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
          (fun m => (ENNReal.measurable_ofReal.comp (tent_meas s k)).comp ((hXs y hy).1 _))
          (fun m => ae_of_all _ fun ω' => ENNReal.ofReal_le_one.2 (tent_le_one s k _))
          (by simp) (ae_of_all _ fun ω' => ?_)
        exact ((ENNReal.continuous_ofReal.comp (continuous_tent s k)).tendsto _).comp
          ((((hXs y hy).2.1 ω').tendsto t).comp hqt')
      rw [hΨy s k t y hy]
      exact hin.congr fun m => (hΨy s k _ y hy).symm
    refine tendsto_nhds_unique hdct ?_
    exact tendsto_const_nhds.congr fun m => (hR s k (q m) (hqpos m)).symm
  refine ⟨hπP, hπc, fun t A hAm => ?_⟩
  haveI := hκM t
  have hbind_univ : π.bind (κ t) Set.univ = 1 := by
    rw [Measure.bind_apply MeasurableSet.univ (κ t).measurable.aemeasurable]
    simp
  haveI : IsProbabilityMeasure (π.bind (κ t)) := ⟨hbind_univ⟩
  have hν : π.bind (κ t) = π := by
    refine eq_of_tents _ _ fun s k => ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (tent_nonneg s k))
      (continuous_tent s k).aestronglyMeasurable,
      Measure.lintegral_bind (f := fun z => ENNReal.ofReal (tent s k z)) (κ t).measurable.aemeasurable
        (ENNReal.measurable_ofReal.comp (tent_meas s k)).aemeasurable,
      hAll s k t, ENNReal.toReal_ofReal (integral_nonneg (tent_nonneg s k))]
  calc ∫⁻ y, trans P X t y A ∂π = ∫⁻ y, κ t y A ∂π := by
        refine lintegral_congr_ae ?_
        filter_upwards [hπa] with y hy
        rw [hκeq t y hy]; rfl
    _ = π.bind (κ t) A := (Measure.bind_apply hAm (κ t).measurable.aemeasurable).symm
    _ = π A := by rw [hν]

end L57.Fin

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
open StochKolmogorov.Classify in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ x ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω} ∧
        ∀ π ∈ limitSet X x ω, IsInvariant P X π := by
  exact L57.Fin.main hn P C B X hX c γb hA δ₁ h14
