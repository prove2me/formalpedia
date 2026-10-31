-- Prove2me | solution 1 for Viterbo.exists_isConvexDomain_one_lt_systolicRatio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:54:47.133975+00:00
-- url     : https://prove2.me/submissions/57a0587a-3e5f-40c2-a7d5-889ca30f1269
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_cEHZ_pentagonK_prod_pentagonT
import Theorems.Thm_Viterbo_volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT
import Theorems.Thm_Viterbo_systolicRatio_symplecticPProduct_two
import Theorems.Thm_Viterbo_cEHZ_capacityBall
import Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ

open MeasureTheory
open scoped ENNReal Pointwise

namespace Viterbo.OneLtSys

open OAI.SymmetricPolar Viterbo Set

/-! ## Pentagons are convex domains containing `0` (from `Solutions/Viterbo/PentConv.lean`) -/

/-- Generic: a finite family in the plane summing to zero with two independent members spans a convex domain. -/
theorem convDomain_of_sum_zero (v : ℕ → Position 2) (hsum : ∑ k ∈ Finset.range 5, v k = 0)
    (hdet : v 0 0 * v 1 1 - v 0 1 * v 1 0 ≠ 0) :
    IsConvexDomain (convexHull ℝ (v '' (Finset.range 5 : Set ℕ))) ∧
      (0 : Position 2) ∈ convexHull ℝ (v '' (Finset.range 5 : Set ℕ)) := by
  have hfin : (v '' (Finset.range 5 : Set ℕ)).Finite := (Finset.finite_toSet _).image _
  have h0 : (0 : Position 2) ∈ convexHull ℝ (v '' (Finset.range 5 : Set ℕ)) := by
    have : (0 : Position 2) = ∑ k ∈ Finset.range 5, (1 / 5 : ℝ) • v k := by
      rw [← Finset.smul_sum, hsum, smul_zero]
    rw [this]
    refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by norm_num) (by simp) ?_
    intro k hk
    exact subset_convexHull ℝ _ ⟨k, by simpa using hk, rfl⟩
  refine ⟨⟨(isBounded_convexHull).mpr hfin.isBounded, convex_convexHull ℝ _, ?_⟩, h0⟩
  have hspan : affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) = ⊤ := by
    have h0s : (0 : Position 2) ∈ affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) :=
      convexHull_subset_affineSpan _ h0
    have hv : ∀ k ∈ Finset.range 5, v k ∈ affineSpan ℝ (v '' (Finset.range 5 : Set ℕ)) :=
      fun k hk => subset_affineSpan ℝ _ ⟨k, by simpa using hk, rfl⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, h0s⟩]
    have hd : ∀ k ∈ Finset.range 5, v k ∈ (affineSpan ℝ (v '' (Finset.range 5 : Set ℕ))).direction := by
      intro k hk
      simpa using AffineSubspace.vsub_mem_direction (hv k hk) h0s
    have hli : LinearIndependent ℝ ![v 0, v 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrArg (fun w : Position 2 => w 0) hst
      have e1 := congrArg (fun w : Position 2 => w 1) hst
      simp at e0 e1
      have hs : s * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by linear_combination v 1 1 * e0 - v 1 0 * e1
      have ht : t * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by linear_combination v 0 0 * e1 - v 0 1 * e0
      exact ⟨(mul_eq_zero.mp hs).resolve_right hdet, (mul_eq_zero.mp ht).resolve_right hdet⟩
    have htop : Submodule.span ℝ (Set.range ![v 0, v 1]) = ⊤ := by
      apply hli.span_eq_top_of_card_eq_finrank'
      simp
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hd 0 (by simp)
    · exact hd 1 (by simp)
  have := (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := v '' (Finset.range 5 : Set ℕ))).mpr hspan
  exact this


open Real in
theorem trig_vals :
    Real.cos (2 * π / 5) = (√5 - 1) / 4 ∧ Real.cos (4 * π / 5) = -(1 + √5) / 4 ∧
    Real.cos (6 * π / 5) = -(1 + √5) / 4 ∧ Real.cos (8 * π / 5) = (√5 - 1) / 4 ∧
    Real.sin (6 * π / 5) = - Real.sin (4 * π / 5) ∧ Real.sin (8 * π / 5) = - Real.sin (2 * π / 5) := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have c1 : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
    have : 2 * π / 5 = 2 * (π / 5) := by ring
    rw [this, Real.cos_two_mul, Real.cos_pi_div_five]; nlinarith
  have c2 : Real.cos (4 * π / 5) = -(1 + √5) / 4 := by
    have : 4 * π / 5 = 2 * (2 * π / 5) := by ring
    rw [this, Real.cos_two_mul, c1]; nlinarith
  refine ⟨c1, c2, ?_, ?_, ?_, ?_⟩
  · have : 6 * π / 5 = 2 * π - 4 * π / 5 := by ring
    rw [this, Real.cos_two_pi_sub, c2]
  · have : 8 * π / 5 = 2 * π - 2 * π / 5 := by ring
    rw [this, Real.cos_two_pi_sub, c1]
  · have : 6 * π / 5 = 2 * π - 4 * π / 5 := by ring
    rw [this, Real.sin_two_pi_sub]
  · have : 8 * π / 5 = 2 * π - 2 * π / 5 := by ring
    rw [this, Real.sin_two_pi_sub]

theorem sin_pos1 : 0 < Real.sin (2 * Real.pi / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem cos_rot (x : ℝ) : Real.cos (-(Real.pi / 2) + x) = Real.sin x := by
  rw [Real.cos_add]; simp
theorem sin_rot (x : ℝ) : Real.sin (-(Real.pi / 2) + x) = - Real.cos x := by
  rw [Real.sin_add]; simp

theorem pentagonK_conv : IsConvexDomain pentagonK ∧ (0 : Position 2) ∈ pentagonK := by
  obtain ⟨c1, c2, c3, c4, s3, s4⟩ := trig_vals
  have hs := sin_pos1
  have a2 : 2 * Real.pi * 2 / 5 = 4 * Real.pi / 5 := by ring
  have a3 : 2 * Real.pi * 3 / 5 = 6 * Real.pi / 5 := by ring
  have a4 : 2 * Real.pi * 4 / 5 = 8 * Real.pi / 5 := by ring
  unfold pentagonK
  refine convDomain_of_sum_zero pentagonVertex ?_ ?_
  · ext i
    fin_cases i
    · simp [Finset.sum_range_succ, pentagonVertex]
      rw [a2, a3, a4, c1, c2, c3, c4]; ring
    · simp [Finset.sum_range_succ, pentagonVertex]
      rw [a2, a3, a4, s3, s4]; ring
  · simp [pentagonVertex]
    exact hs.ne'

theorem pentagonT_conv : IsConvexDomain pentagonT ∧ (0 : Position 2) ∈ pentagonT := by
  obtain ⟨c1, c2, c3, c4, s3, s4⟩ := trig_vals
  have hs := sin_pos1
  have a2 : 2 * Real.pi * 2 / 5 = 4 * Real.pi / 5 := by ring
  have a3 : 2 * Real.pi * 3 / 5 = 6 * Real.pi / 5 := by ring
  have a4 : 2 * Real.pi * 4 / 5 = 8 * Real.pi / 5 := by ring
  unfold pentagonT
  refine convDomain_of_sum_zero rotatedVertex ?_ ?_
  · ext i
    fin_cases i
    · simp [Finset.sum_range_succ, rotatedVertex, cos_rot]
      rw [a2, a3, a4, s3, s4]; ring
    · simp [Finset.sum_range_succ, rotatedVertex, sin_rot]
      rw [a2, a3, a4, c1, c2, c3, c4]; ring
  · simp [rotatedVertex, cos_rot, sin_rot]
    exact hs.ne'


/-! ## Volume of the ball (from `Solutions/Viterbo/GromovVol.lean`) -/

/-- The phase-space ball of capacity `c` is the `ofLp`-preimage of a Euclidean ball. -/
theorem ofLp_preimage_capacityBall (n : ℕ) (c : ℝ) :
    (WithLp.ofLp : WithLp 2 (Position n × Position n) → Phase n) ⁻¹' capacityBall n c =
      Metric.ball (0 : WithLp 2 (Position n × Position n)) (Real.sqrt (c / Real.pi)) := by
  ext x
  simp only [Set.mem_preimage, capacityBall, Set.mem_ofPred_eq, mem_ball_zero_iff]
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  rw [← Real.sqrt_sq (norm_nonneg x)]
  rw [Real.sqrt_lt_sqrt_iff (sq_nonneg _), hx, lt_div_iff₀ Real.pi_pos, mul_comm]
  rfl

theorem volume_capacityBall (n : ℕ) {c : ℝ} (hc : 0 < c) :
    volume (capacityBall n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : capacityBall 0 c = Set.univ := by
      ext z
      simp only [capacityBall, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have h1 : z.1 = 0 := Subsingleton.elim _ _
      have h2 : z.2 = 0 := Subsingleton.elim _ _
      simp [h1, h2, hc]
    rw [huniv, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_euclideanSpace_eq_dirac]
  · have hopen : IsOpen (capacityBall n c) := by
      apply isOpen_lt (by fun_prop) continuous_const
    rw [← (WithLp.volume_preserving_ofLp (Position n) (Position n)).measure_preimage
      hopen.measurableSet.nullMeasurableSet, ofLp_preimage_capacityBall n c]
    have hfr : Module.finrank ℝ (WithLp 2 (Position n × Position n)) = 2 * n := by
      rw [(WithLp.linearEquiv 2 ℝ (Position n × Position n)).finrank_eq, Module.finrank_prod,
        finrank_euclideanSpace, Fintype.card_fin]
      ring
    have : Nontrivial (WithLp 2 (Position n × Position n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
    rw [InnerProductSpace.volume_ball, hfr]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : Real.sqrt (c / Real.pi) ^ (2 * n) = (c / Real.pi) ^ n := by
      rw [pow_mul, Real.sq_sqrt (by positivity)]
    have h2 : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
      rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
    have h3 : ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 := by push_cast; ring
    rw [h1, h2, h3, Real.Gamma_nat_eq_factorial, div_pow]
    have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-! ## Products, balls -/

theorem prod_conv {K T : Set (Position 2)} (hK : IsConvexDomain K) (hT : IsConvexDomain T) :
    IsConvexDomain (K ×ˢ T) :=
  ⟨hK.1.prod hT.1, hK.2.1.prod hT.2.1, by rw [interior_prod_eq]; exact hK.2.2.prod hT.2.2⟩

theorem ball_conv (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IsConvexDomain (capacityBall k c) ∧ (0 : Phase k) ∈ capacityBall k c := by
  have h0 : (0 : Phase k) ∈ capacityBall k c := by
    simp only [capacityBall, mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, norm_zero]; simpa using hc
  refine ⟨⟨?_, ?_, ?_⟩, h0⟩
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (c / Real.pi), fun z hz => ?_⟩
    simp only [capacityBall, mem_ofPred_eq] at hz
    have h1 : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ c / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; linarith
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    constructor <;> apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  · intro z hz w hw l μ hl hμ hlμ
    simp only [capacityBall, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd] at *
    have e1 : ‖l • z.1 + μ • w.1‖ ≤ l * ‖z.1‖ + μ * ‖w.1‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg hl, norm_smul_of_nonneg hμ]
    have e2 : ‖l • z.2 + μ • w.2‖ ≤ l * ‖z.2‖ + μ * ‖w.2‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg hl, norm_smul_of_nonneg hμ]
    have n1 := norm_nonneg (l • z.1 + μ • w.1)
    have n2 := norm_nonneg (l • z.2 + μ • w.2)
    have f1 : ‖l • z.1 + μ • w.1‖ ^ 2 ≤ (l * ‖z.1‖ + μ * ‖w.1‖) ^ 2 := pow_le_pow_left₀ n1 e1 2
    have f2 : ‖l • z.2 + μ • w.2‖ ^ 2 ≤ (l * ‖z.2‖ + μ * ‖w.2‖) ^ 2 := pow_le_pow_left₀ n2 e2 2
    have g : (l * ‖z.1‖ + μ * ‖w.1‖) ^ 2 + (l * ‖z.2‖ + μ * ‖w.2‖) ^ 2 ≤
        l * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) + μ * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) := by
      have : μ = 1 - l := by linarith
      subst this
      nlinarith [mul_nonneg hl hμ, mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (‖z.1‖ - ‖w.1‖)),
        mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (‖z.2‖ - ‖w.2‖))]
    have hlt : l * (Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) + μ * (Real.pi * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2)) < c := by
      rcases hl.eq_or_lt with rfl | hl'
      · have : μ = 1 := by linarith
        subst this; linarith
      · nlinarith
    nlinarith [Real.pi_pos]
  · have hopen : IsOpen (capacityBall k c) := isOpen_lt (by fun_prop) continuous_const
    rw [hopen.interior_eq]; exact ⟨0, h0⟩

theorem sys_ball (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    cEHZ (capacityBall k c) = ENNReal.ofReal c ∧ systolicRatio (capacityBall k c) = 1 := by
  have hr : Real.pi * Real.sqrt (c / Real.pi) ^ 2 = c := by
    rw [Real.sq_sqrt (div_nonneg hc.le Real.pi_pos.le)]; field_simp
  have h := cEHZ_capacityBall k hk (Real.sqrt (c / Real.pi))
    (Real.sqrt_pos.2 (div_pos hc Real.pi_pos))
  rw [hr] at h
  refine ⟨h, ?_⟩
  unfold systolicRatio
  rw [h, volume_capacityBall k hc, ← ENNReal.ofReal_pow hc.le]
  have : (k.factorial : ℝ≥0∞) * ENNReal.ofReal (c ^ k / k.factorial) = ENNReal.ofReal (c ^ k) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [this]
  exact ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.2 (by positivity))) ENNReal.ofReal_ne_top

/-! ## The symplectic 2-product of convex domains containing `0` -/

/-- `appendPos` as a linear equivalence. -/
noncomputable def appendL (m k : ℕ) : (Position m × Position k) ≃ₗ[ℝ] Position (m + k) where
  toFun p := appendPos p.1 p.2
  invFun z := (WithLp.toLp 2 (fun i => z (Fin.castAdd k i)), WithLp.toLp 2 (fun j => z (Fin.natAdd m j)))
  map_add' p q := by
    ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [appendPos]
  map_smul' c p := by
    ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [appendPos]
  left_inv p := by
    ext i <;> simp [appendPos]
  right_inv z := by
    ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [appendPos]

/-- The arrangement `((q, p), (q', p')) ↦ ((q, q'), (p, p'))` as a continuous linear equivalence. -/
noncomputable def arrL (m k : ℕ) : (Phase m × Phase k) ≃L[ℝ] Phase (m + k) :=
  ((LinearEquiv.prodProdProdComm ℝ (Position m) (Position m) (Position k) (Position k)).trans
    ((appendL m k).prodCongr (appendL m k))).toContinuousLinearEquiv

/-- The 2-product before the arrangement. -/
def Q {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k)) : Set (Phase m × Phase k) :=
  {zw | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 + b ^ 2 ≤ 1 ∧ zw.1 ∈ a • X ∧ zw.2 ∈ b • Y}

theorem star {E : Type*} [AddCommGroup E] [Module ℝ E] {X : Set E} (hX : Convex ℝ X) (h0 : (0 : E) ∈ X)
    {a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s) : a • X ⊆ s • X := by
  rintro _ ⟨x, hx, rfl⟩
  rcases (ha.trans has).eq_or_lt with hs | hs
  · have : a = 0 := le_antisymm (hs ▸ has) ha
    subst this; rw [← hs]; exact ⟨x, hx, rfl⟩
  · refine ⟨(a / s) • x, hX.smul_mem_of_zero_mem h0 hx ⟨div_nonneg ha hs.le, (div_le_one hs).2 has⟩, ?_⟩
    simp only [smul_smul]; rw [mul_div_cancel₀ _ hs.ne']

theorem comb {E : Type*} [AddCommGroup E] [Module ℝ E] {X : Set E} (hX : Convex ℝ X)
    {a a' l μ : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hl : 0 ≤ l) (hμ : 0 ≤ μ) {z z' : E}
    (hz : z ∈ a • X) (hz' : z' ∈ a' • X) : l • z + μ • z' ∈ (l * a + μ * a') • X := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨x', hx', rfl⟩ := hz'
  by_cases hs : l * a + μ * a' = 0
  · have h1 : l * a = 0 := by nlinarith [mul_nonneg hl ha, mul_nonneg hμ ha']
    have h2 : μ * a' = 0 := by nlinarith [mul_nonneg hl ha, mul_nonneg hμ ha']
    refine ⟨x, hx, ?_⟩
    simp only [smul_smul, h1, h2, zero_smul, add_zero]
  · have hpos : 0 < l * a + μ * a' := lt_of_le_of_ne (by positivity) (Ne.symm hs)
    refine ⟨(l * a / (l * a + μ * a')) • x + (μ * a' / (l * a + μ * a')) • x',
      hX hx hx' (by positivity) (by positivity) (by field_simp), ?_⟩
    simp only [smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hs]

theorem Q_convex {m k : ℕ} {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X)
    (hY : Convex ℝ Y) : Convex ℝ (Q X Y) := by
  rintro zw ⟨a, b, ha, hb, hab, h1, h2⟩ zw' ⟨a', b', ha', hb', hab', h1', h2'⟩ l μ hl hμ hlμ
  refine ⟨l * a + μ * a', l * b + μ * b', by positivity, by positivity, ?_,
    comb hX ha ha' hl hμ h1 h1', comb hY hb hb' hl hμ h2 h2'⟩
  have : μ = 1 - l := by linarith
  subst this
  nlinarith [mul_nonneg hl hμ, mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (a - a')),
    mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (b - b')),
    mul_nonneg (mul_nonneg hl hμ) (sub_nonneg.2 hab), mul_nonneg (mul_nonneg hl hμ) (sub_nonneg.2 hab'),
    mul_nonneg (sq_nonneg l) (sub_nonneg.2 hab), mul_nonneg (sq_nonneg (1 - l)) (sub_nonneg.2 hab')]

theorem rpow_two_inv (t : ℝ) : t ^ ((2 : ℝ≥0∞)⁻¹.toReal) = Real.sqrt t := by
  rw [Real.sqrt_eq_rpow]; congr 1; simp

theorem pprod_eq {m k : ℕ} {X : Set (Phase m)} {Y : Set (Phase k)}
    (hY : Convex ℝ Y) (hY0 : (0 : Phase k) ∈ Y) :
    symplecticPProduct 2 X Y = arrL m k '' Q X Y := by
  ext z
  simp only [symplecticPProduct, mem_iUnion, mem_image, rpow_two_inv, exists_prop]
  constructor
  · rintro ⟨t, ht, zw, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨zw, ⟨Real.sqrt (1 - t), Real.sqrt t, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, hz1, hz2⟩, rfl⟩
    rw [Real.sq_sqrt (by linarith [ht.2]), Real.sq_sqrt ht.1]; linarith
  · rintro ⟨zw, ⟨a, b, ha, hb, hab, h1, h2⟩, rfl⟩
    refine ⟨1 - a ^ 2, ⟨by nlinarith, by nlinarith⟩, zw, ⟨?_, ?_⟩, rfl⟩
    · rw [sub_sub_cancel, Real.sqrt_sq ha]; exact h1
    · refine star hY hY0 hb ?_ h2
      rw [← Real.sqrt_sq hb]; exact Real.sqrt_le_sqrt (by linarith)

theorem pprod_conv {m k : ℕ} {X : Set (Phase m)} {Y : Set (Phase k)} (hX : IsConvexDomain X)
    (hY : IsConvexDomain Y) (hX0 : (0 : Phase m) ∈ X) (hY0 : (0 : Phase k) ∈ Y) :
    IsConvexDomain (symplecticPProduct 2 X Y) := by
  rw [pprod_eq hY.2.1 hY0]
  refine ⟨?_, ?_, ?_⟩
  · have hsub : Q X Y ⊆ X ×ˢ Y := by
      rintro zw ⟨a, b, ha, hb, hab, h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := star hX.2.1 hX0 ha (show a ≤ 1 by nlinarith) h1
        rwa [one_smul] at this
      · have := star hY.2.1 hY0 hb (show b ≤ 1 by nlinarith) h2
        rwa [one_smul] at this
    exact (arrL m k : (Phase m × Phase k) →L[ℝ] Phase (m + k)).lipschitz.isBounded_image
      ((hX.1.prod hY.1).subset hsub)
  · exact (Q_convex hX.2.1 hY.2.1).linear_image
      ((arrL m k : (Phase m × Phase k) →L[ℝ] Phase (m + k)) : (Phase m × Phase k) →ₗ[ℝ] Phase (m + k))
  · have hsub : ((1 / 2 : ℝ) • X) ×ˢ ((1 / 2 : ℝ) • Y) ⊆ Q X Y := by
      rintro zw ⟨h1, h2⟩
      exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, h1, h2⟩
    obtain ⟨x, hx⟩ := hX.2.2
    obtain ⟨y, hy⟩ := hY.2.2
    have hin : ((1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y) ∈ interior (Q X Y) := by
      refine interior_mono hsub ?_
      rw [interior_prod_eq, interior_smul₀ (by norm_num), interior_smul₀ (by norm_num)]
      exact ⟨smul_mem_smul_set hx, smul_mem_smul_set hy⟩
    refine ⟨arrL m k ((1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y), ?_⟩
    have := (arrL m k).toHomeomorph.image_interior (Q X Y)
    change _ ∈ interior ((arrL m k).toHomeomorph '' Q X Y)
    rw [← this]
    exact ⟨_, hin, rfl⟩

/-! ## The main theorem -/

theorem c0_pos : 0 < 2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
  have h1 : 0 < Real.cos (Real.pi / 10) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h2 : 0 < Real.cos (Real.pi / 5) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  positivity

theorem main (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Set (Phase n), IsConvexDomain A ∧ cEHZ A < ⊤ ∧ 1 < systolicRatio A := by
  obtain ⟨hK, hK0⟩ := pentagonK_conv
  obtain ⟨hT, hT0⟩ := pentagonT_conv
  have hKT : IsConvexDomain (pentagonK ×ˢ pentagonT) := prod_conv hK hT
  have hKT0 : (0 : Phase 2) ∈ pentagonK ×ˢ pentagonT := ⟨hK0, hT0⟩
  have hsysKT := (volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT).2.2.2
  rcases hn.eq_or_lt with rfl | hlt
  · refine ⟨_, hKT, ?_, hsysKT⟩
    rw [cEHZ_pentagonK_prod_pentagonT]; exact ENNReal.ofReal_lt_top
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hk : 1 ≤ k := by omega
    obtain ⟨hB, hB0⟩ := ball_conv k c0_pos
    obtain ⟨hcB, hsB⟩ := sys_ball k hk c0_pos
    have hA := pprod_conv hKT hB hKT0 hB0
    refine ⟨_, hA, ?_, ?_⟩
    · obtain ⟨γ, -, -, hγ⟩ :=
        (exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ (2 + k) (by omega)).2 _ hA
      rw [hγ]; exact ENNReal.ofReal_lt_top
    · rw [systolicRatio_symplecticPProduct_two 2 k (by norm_num) hk _ _ hKT hB hKT0 hB0
        (by rw [cEHZ_pentagonK_prod_pentagonT, hcB]), hsB, mul_one]
      exact hsysKT

end Viterbo.OneLtSys

open scoped ENNReal in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Set (OAI.SymmetricPolar.Phase n), Viterbo.IsConvexDomain A ∧ Viterbo.cEHZ A < ⊤ ∧
      1 < Viterbo.systolicRatio A :=
  Viterbo.OneLtSys.main n hn
