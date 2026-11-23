-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:59:36.294638+00:00
-- url     : https://prove2.me/submissions/febbb643-5df4-4244-85d0-399682afe4b2

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_LocalGaussian
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_feasibility
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_3
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_4
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_update_identities

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace Prop21Aux

-- ============================================================================
-- Section 1: Basic Linear Algebra, Support, and Clipping Helpers
-- ============================================================================

lemma support_eq_sum_abs {d n : ℕ} (v : Fin n → E d) (b : E d) :
    support v b = ∑ i, |inner ℝ b (v i)| := by
  unfold support
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ⟨0, ⟨0, fun _ => by simp, by simp⟩, by simp⟩⟩
    · rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by gcongr with i; exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
  · have hbdd : BddAbove ((fun y => inner ℝ b y) '' zonotope v) := by
      refine ⟨∑ i, |inner ℝ b (v i)|, ?_⟩
      rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by gcongr with i; exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
    let t : Fin n → ℝ := fun i => if 0 ≤ inner ℝ b (v i) then 1 else -1
    have ht : ∀ i, |t i| ≤ 1 := by intro i; dsimp [t]; split_ifs <;> simp
    have hx_mem : (∑ i, t i • v i) ∈ zonotope v := ⟨t, ht, rfl⟩
    have hx_val : inner ℝ b (∑ i, t i • v i) = ∑ i, |inner ℝ b (v i)| := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]
      dsimp [t]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · simp [abs_of_neg (not_le.mp h)]
    rw [← hx_val]
    exact le_csSup hbdd ⟨∑ i, t i • v i, hx_mem, rfl⟩

lemma inner_le_support {d n : ℕ} {w : Fin n → E d} {x : E d}
    (hx : x ∈ zonotope w) (a : E d) :
    inner ℝ a x ≤ support w a := by
  rw [support_eq_sum_abs]
  rcases hx with ⟨t, ht, rfl⟩
  calc
    inner ℝ a (∑ i, t i • w i)
      = ∑ i, t i * inner ℝ a (w i) := by simp [inner_sum, real_inner_smul_right]
    _ ≤ ∑ i, |t i * inner ℝ a (w i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ = ∑ i, |t i| * |inner ℝ a (w i)| := by simp [abs_mul]
    _ ≤ ∑ i, 1 * |inner ℝ a (w i)| := by gcongr with i; exact ht i
    _ = ∑ i, |inner ℝ a (w i)| := by simp

lemma act_mul {d : ℕ} (M N : Mat d) (x : E d) :
    act (M * N) x = act M (act N x) := by
  ext k
  simp [act, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma act_one {d : ℕ} (x : E d) : act (1 : Mat d) x = x := by
  ext k
  simp [act]

lemma inner_act_transpose {d : ℕ} (M : Mat d) (x y : E d) :
    inner ℝ x (act M y) = inner ℝ (act M.transpose x) y := by
  calc
    inner ℝ x (act M y)
      = dotProduct (M.mulVec y.ofLp) x.ofLp := by
          simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    _ = dotProduct x.ofLp (M.mulVec y.ofLp) := dotProduct_comm _ _
    _ = dotProduct (M.vecMul x.ofLp) y.ofLp := Matrix.dotProduct_mulVec x.ofLp M y.ofLp
    _ = dotProduct (M.transpose.mulVec x.ofLp) y.ofLp := by rw [Matrix.mulVec_transpose]
    _ = dotProduct y.ofLp (M.transpose.mulVec x.ofLp) := dotProduct_comm _ _
    _ = inner ℝ (act M.transpose x) y := by
          simp [act, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]

lemma act_rankOne {d : ℕ} (u x : E d) :
    act (rankOne u) x = (inner ℝ u x) • u := by
  ext k
  simp [act, rankOne, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, mul_assoc, Finset.mul_sum, mul_comm]

lemma inner_weightedMatrix {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) (x : E d) :
    inner ℝ x (act (weightedMatrix v r) x) =
      ∑ i, (r i / ‖v i‖) * (inner ℝ x (v i)) ^ 2 := by
  have hlin : act (weightedMatrix v r) x =
      ∑ i, (r i / ‖v i‖) • act (rankOne (v i)) x := by
    unfold weightedMatrix
    simp [act, map_sum, map_smul]
  rw [hlin, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [act_rankOne, real_inner_smul_right, real_inner_smul_right, real_inner_comm (v i) x]
  ring

lemma q_pos (t : ℝ) : 0 < q t := by
  unfold q
  exact div_pos one_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|))

lemma q_le_one (t : ℝ) : q t ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact (div_le_one hpos).mpr (le_max_left 1 |t|)

lemma q_continuous : Continuous q := by
  unfold q
  exact continuous_const.div (continuous_const.max continuous_abs)
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |x|)))

-- ============================================================================
-- Section 2: Continuity of Matrix Square Root and Recorded Samples
-- ============================================================================

lemma continuous_mat_entry {d : ℕ} (a b : Fin d) :
    Continuous (fun M : Mat d => M a b) := by
  have h1 : Continuous (fun M : Mat d => (M : Fin d → Fin d → ℝ)) := continuous_id
  exact (continuous_apply b).comp ((continuous_apply a).comp h1)

lemma continuous_mat_mul {X : Type*} [TopologicalSpace X] {d : ℕ}
    {A B : X → Mat d} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  refine continuous_pi (fun a => continuous_pi (fun b => ?_))
  simp only [Matrix.mul_apply]
  refine continuous_finsetSum Finset.univ (fun c _ => ?_)
  exact ((continuous_mat_entry a c).comp hA).mul ((continuous_mat_entry c b).comp hB)

lemma exists_subseq_tendsto_sqrt {X : Type*} [TopologicalSpace X] {d : ℕ}
    {S : X → Mat d} (hS : Continuous S) (hpsd : ∀ x, (0 : Mat d) ≤ S x)
    {x₀ : X} {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x₀)) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun m => CFC.sqrt (S (u (ms m)))) atTop (𝓝 (CFC.sqrt (S x₀))) := by
  let R : ℕ → Mat d := fun m => CFC.sqrt (S (u m))
  have hR_psd : ∀ m, (0 : Mat d) ≤ R m := fun m => CFC.sqrt_nonneg (S (u m))
  have hR_herm : ∀ m, (R m).IsHermitian := fun m => by simpa using (hR_psd m).isHermitian
  have hRR : ∀ m, R m * R m = S (u m) := fun m => CFC.sqrt_mul_sqrt_self (S (u m))
  let g : ℕ → ℝ := fun m => ∑ i : Fin d, |S (u m) i i|
  let L₀ : ℝ := ∑ i : Fin d, |S x₀ i i|
  have hSu : Tendsto (fun m => S (u m)) atTop (𝓝 (S x₀)) := (hS.tendsto x₀).comp hu
  have hg_tend : Tendsto g atTop (𝓝 L₀) := by
    refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
    exact ((continuous_mat_entry i i).abs.tendsto (S x₀)).comp hSu
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hg_tend 1 zero_lt_one
  let B₀ : ℝ := max (L₀ + 1) (∑ m ∈ Finset.range N₀, g m)
  have hL₀_nn : 0 ≤ L₀ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB₀_nn : 0 ≤ B₀ := le_trans (by linarith) (le_max_left _ _)
  have hg_le : ∀ m, g m ≤ B₀ := by
    intro m
    by_cases hm : N₀ ≤ m
    · have hd := hN₀ m hm
      rw [Real.dist_eq] at hd
      have : g m ≤ L₀ + 1 := by linarith [(abs_lt.mp hd).2]
      exact le_trans this (le_max_left _ _)
    · have hm_lt : m ∈ Finset.range N₀ := Finset.mem_range.mpr (not_le.mp hm)
      have hg_nn : ∀ r ∈ Finset.range N₀, 0 ≤ g r :=
        fun r _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      exact le_trans (Finset.single_le_sum hg_nn hm_lt) (le_max_right _ _)
  let B : ℝ := Real.sqrt B₀
  let K : Set (Mat d) := Set.pi univ (fun _ : Fin d => Set.pi univ (fun _ : Fin d => Icc (-B) B))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hR_mem : ∀ m, R m ∈ K := by
    intro m k _ l _
    have hsq_entry : (R m k l) ^ 2 ≤ B₀ := by
      have h1 : (R m k l) ^ 2 ≤ ∑ j : Fin d, (R m k j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (R m k j)) (Finset.mem_univ l)
      have h2 : ∑ j : Fin d, (R m k j) ^ 2 = (R m * R m) k k := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hsym : R m j k = R m k j := by
          have := congrArg (fun M : Mat d => M k j) (hR_herm m)
          simpa [Matrix.conjTranspose_apply] using this
        rw [hsym, sq]
      have h3 : (R m * R m) k k ≤ g m := by
        rw [hRR m]
        exact le_trans (le_abs_self _)
          (Finset.single_le_sum (f := fun i : Fin d => |S (u m) i i|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ k))
      exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 (hg_le m)))
    have habs : |R m k l| ≤ B := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq_entry
    exact abs_le.mp habs
  have : FirstCountableTopology (Mat d) :=
    inferInstanceAs (FirstCountableTopology (Fin d → Fin d → ℝ))
  obtain ⟨Rstar, _, ms, hms_mono, hms_tend⟩ := hK.tendsto_subseq hR_mem
  have hRstar_sq : Rstar * Rstar = S x₀ := by
    have ht1 : Tendsto (fun m => R (ms m) * R (ms m)) atTop (𝓝 (Rstar * Rstar)) :=
      hms_tend.mul hms_tend
    have ht2 : Tendsto (fun m => R (ms m) * R (ms m)) atTop (𝓝 (S x₀)) := by
      simp only [hRR]
      exact hSu.comp hms_mono.tendsto_atTop
    exact tendsto_nhds_unique ht1 ht2
  have hRstar_psd : (0 : Mat d) ≤ Rstar := by
    change (Rstar - 0).PosSemidef
    rw [sub_zero, Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext k l
      simp only [Matrix.conjTranspose_apply, star_trivial]
      have ht1 : Tendsto (fun m => R (ms m) l k) atTop (𝓝 (Rstar l k)) :=
        ((continuous_mat_entry l k).tendsto Rstar).comp hms_tend
      have ht2 : Tendsto (fun m => R (ms m) l k) atTop (𝓝 (Rstar k l)) := by
        have hsym : (fun m => R (ms m) l k) = (fun m => R (ms m) k l) := by
          ext m
          have := congrArg (fun M : Mat d => M k l) (hR_herm (ms m))
          simpa [Matrix.conjTranspose_apply] using this
        rw [hsym]
        exact ((continuous_mat_entry k l).tendsto Rstar).comp hms_tend
      exact tendsto_nhds_unique ht1 ht2
    · intro v
      have hv_cont : Continuous (fun M : Mat d => dotProduct (star v) (M.mulVec v)) := by
        simp only [dotProduct, Matrix.mulVec]
        refine continuous_finsetSum Finset.univ (fun k _ => continuous_const.mul ?_)
        exact continuous_finsetSum Finset.univ (fun l _ =>
          (continuous_mat_entry k l).mul continuous_const)
      have hv_nn : ∀ m, 0 ≤ dotProduct (star v) ((R (ms m)).mulVec v) := by
        intro m
        have hm := hR_psd (ms m)
        change (R (ms m) - 0).PosSemidef at hm
        rw [sub_zero, Matrix.posSemidef_iff_dotProduct_mulVec] at hm
        exact hm.2 v
      exact ge_of_tendsto ((hv_cont.tendsto Rstar).comp hms_tend) (Eventually.of_forall hv_nn)
  have h_eq : CFC.sqrt (S x₀) = Rstar := by
    have hpsd0 : (0 : Mat d) ≤ S x₀ := hpsd x₀
    exact (CFC.sqrt_eq_iff (S x₀) Rstar).mpr hRstar_sq
  exact ⟨ms, hms_mono, h_eq ▸ hms_tend⟩

lemma continuous_sqrt_on_psd {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {d : ℕ} {S : X → Mat d} (hS : Continuous S) (hpsd : ∀ x, (0 : Mat d) ≤ S x) :
    Continuous (fun x => CFC.sqrt (S x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_seq_tendsto]
  intro u hu
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨ms, _, hms⟩ := exists_subseq_tendsto_sqrt hS hpsd (hu.comp hns)
  exact ⟨ms, hms⟩

lemma continuous_act {X : Type*} [TopologicalSpace X] {d : ℕ}
    {M : X → Mat d} {v : X → E d} (hM : Continuous M) (hv : Continuous v) :
    Continuous (fun x => act (M x) (v x)) := by
  have hvec : Continuous (fun x : X => (M x).mulVec (v x).ofLp) := by
    refine continuous_pi (fun k => ?_)
    simp only [Matrix.mulVec, dotProduct]
    refine continuous_finsetSum Finset.univ (fun l _ => ?_)
    have hm : Continuous (fun x : X => M x k l) := (continuous_mat_entry k l).comp hM
    have hvl : Continuous (fun x : X => (v x).ofLp l) :=
      (continuous_apply l).comp ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp hv)
    exact hm.mul hvl
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp hvec

lemma continuous_runState {d n : ℕ} (hd : 3 ≤ d) {C : ℝ} (hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) :
    ∀ k ≤ rounds d,
      Continuous (fun z : Tape d => (runState C w T z k).v) ∧
      Continuous (fun z : Tape d => (runState C w T z k).A) ∧
      (∀ z : Tape d, IsUnit ((runState C w T z k).A).det) := by
  have hT_det : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT.1
  intro k hk
  induction k with
  | zero =>
      refine ⟨continuous_const, continuous_const, fun _ => ?_⟩
      simp only [runState]
      have hmul : (T⁻¹ * T).det = 1 := by rw [Matrix.nonsing_inv_mul T hT_det, Matrix.det_one]
      rw [Matrix.det_mul] at hmul
      exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, zero_mul] at hmul; norm_num at hmul)
  | succ k ih =>
      have hk_lt : k < rounds d := Nat.lt_of_succ_le hk
      obtain ⟨hv_cont, hA_cont, hA_unit⟩ := ih (Nat.le_of_lt hk_lt)
      have hlam_ge1 : 1 ≤ scale d k := not_lt.mp (Nat.find_min _ hk_lt)
      have hC_pos : 0 < C := by linarith
      have hlam_pos : 0 < scale d k := lt_of_lt_of_le zero_lt_one hlam_ge1
      have hv_zero_iff : ∀ (z : Tape d) (i : Fin n),
          (runState C w T z k).v i = 0 ↔ w i = 0 := by
        intro z i
        have hfeas := feasibility d n hd C hC w T hT z
        rcases (hfeas.2.1 k (Nat.le_of_lt hk_lt)).2.1 i with ⟨θ, hθ_pos, _, hθ_eq⟩
        constructor
        · intro hv0
          rw [hv0] at hθ_eq
          have h0 : act (runState C w T z k).A 0 = 0 := by simp [act]
          rw [h0] at hθ_eq
          exact (smul_eq_zero.mp hθ_eq.symm).resolve_left (ne_of_gt hθ_pos)
        · intro hw0
          rw [hw0, smul_zero] at hθ_eq
          have hinvA := Matrix.nonsing_inv_mul (runState C w T z k).A (hA_unit z)
          calc
            (runState C w T z k).v i
              = act ((runState C w T z k).A⁻¹ * (runState C w T z k).A)
                  ((runState C w T z k).v i) := by rw [hinvA, act_one]
            _ = act (runState C w T z k).A⁻¹ (act (runState C w T z k).A
                  ((runState C w T z k).v i)) := act_mul _ _ _
            _ = 0 := by rw [hθ_eq]; simp [act]
      have hproj_cont : ∀ i : Fin n,
          Continuous (fun z : Tape d =>
            projections C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i) := by
        intro i
        by_cases hwi : w i = 0
        · have hzero : (fun z : Tape d =>
              projections C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i) = fun _ => 0 := by
            ext z
            have hvz : (runState C w T z k).v i = 0 := (hv_zero_iff z i).mpr hwi
            simp [projections, hvz]
          rw [hzero]; exact continuous_const
        · unfold projections
          have hvi_cont : Continuous (fun z : Tape d => (runState C w T z k).v i) :=
            (continuous_apply i).comp hv_cont
          have hnum : Continuous (fun z : Tape d =>
              inner ℝ (z ⟨k, hk_lt⟩) ((runState C w T z k).v i)) :=
            (continuous_apply (⟨k, hk_lt⟩ : Fin (rounds d))).inner hvi_cont
          have hden : Continuous (fun z : Tape d =>
              C * scale d k * ‖(runState C w T z k).v i‖) :=
            continuous_const.mul hvi_cont.norm
          refine hnum.div hden (fun z => ?_)
          have hvz : (runState C w T z k).v i ≠ 0 :=
            fun h0 => hwi ((hv_zero_iff z i).mp h0)
          exact mul_ne_zero (ne_of_gt (mul_pos hC_pos hlam_pos)) (norm_ne_zero_iff.mpr hvz)
      have hr_cont : ∀ i : Fin n,
          Continuous (fun z : Tape d =>
            weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i) :=
        fun i => q_continuous.comp (hproj_cont i)
      let S_fn : Tape d → Mat d := fun z =>
        weightedMatrix (runState C w T z k).v
          (weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩))
      have hS_cont : Continuous S_fn := by
        refine continuous_pi (fun a => continuous_pi (fun b => ?_))
        dsimp only [S_fn, weightedMatrix]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, rankOne]
        refine continuous_finsetSum Finset.univ (fun i _ => ?_)
        by_cases hwi : w i = 0
        · have hzero : (fun z : Tape d =>
              (weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i /
                ‖(runState C w T z k).v i‖) *
              (((runState C w T z k).v i).ofLp a * ((runState C w T z k).v i).ofLp b)) =
              fun _ => 0 := by
            ext z
            have hvz : (runState C w T z k).v i = 0 := (hv_zero_iff z i).mpr hwi
            simp [hvz]
          rw [hzero]; exact continuous_const
        · have hvi_cont : Continuous (fun z : Tape d => (runState C w T z k).v i) :=
            (continuous_apply i).comp hv_cont
          have hcoeff : Continuous (fun z : Tape d =>
              weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i /
                ‖(runState C w T z k).v i‖) :=
            (hr_cont i).div hvi_cont.norm (fun z =>
              norm_ne_zero_iff.mpr (fun h0 => hwi ((hv_zero_iff z i).mp h0)))
          have hva : Continuous (fun z : Tape d => ((runState C w T z k).v i).ofLp a) :=
            (continuous_apply a).comp ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp hvi_cont)
          have hvb : Continuous (fun z : Tape d => ((runState C w T z k).v i).ofLp b) :=
            (continuous_apply b).comp ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp hvi_cont)
          exact hcoeff.mul (hva.mul hvb)
      have hS_posDef : ∀ z : Tape d, (S_fn z).PosDef := by
        intro z
        exact ((feasibility d n hd C hC w T hT z).2.2 ⟨k, hk_lt⟩).1
      have hS_psd : ∀ z : Tape d, (0 : Mat d) ≤ S_fn z := by
        intro z
        change (S_fn z - 0).PosSemidef
        simpa using (hS_posDef z).posSemidef
      set R_fn : Tape d → Mat d := fun z => CFC.sqrt (S_fn z)
      have hR_cont : Continuous R_fn := continuous_sqrt_on_psd hS_cont hS_psd
      have hR_det_ne : ∀ z : Tape d, (R_fn z).det ≠ 0 := by
        intro z h0
        have hRR : R_fn z * R_fn z = S_fn z := CFC.sqrt_mul_sqrt_self (S_fn z)
        have : (S_fn z).det = 0 := by rw [← hRR, Matrix.det_mul, h0, zero_mul]
        linarith [(hS_posDef z).det_pos]
      have hRinv_cont : Continuous (fun z : Tape d => (R_fn z)⁻¹) := by
        have hrew : (fun z : Tape d => (R_fn z)⁻¹) =
            fun z : Tape d => ((R_fn z).det)⁻¹ • (R_fn z).adjugate := by
          ext z a b
          rw [Matrix.inv_def, Ring.inverse_eq_inv']
        rw [hrew]
        exact (hR_cont.matrix_det.inv₀ hR_det_ne).smul hR_cont.matrix_adjugate
      have hstep_eq : ∀ z : Tape d, runState C w T z (k + 1) =
          step C (scale d k) (runState C w T z k) (z ⟨k, hk_lt⟩) := by
        intro z; simp [runState, hk_lt]
      refine ⟨?_, ?_, ?_⟩
      · refine continuous_pi (fun i => ?_)
        have hfn : (fun z : Tape d => (runState C w T z (k + 1)).v i) =
            fun z : Tape d =>
              weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩) i •
                act (R_fn z)⁻¹ ((runState C w T z k).v i) := by
          funext z
          rw [hstep_eq z]
          dsimp only [step, updatedGenerators, R_fn, S_fn]
        rw [hfn]
        exact (hr_cont i).smul (continuous_act hRinv_cont ((continuous_apply i).comp hv_cont))
      · have hfn : (fun z : Tape d => (runState C w T z (k + 1)).A) =
            fun z : Tape d => (runState C w T z k).A * R_fn z := by
          funext z
          rw [hstep_eq z]
          dsimp only [step, R_fn, S_fn]
        rw [hfn]
        exact continuous_mat_mul hA_cont hR_cont
      · intro z
        rw [hstep_eq z]
        dsimp only [step]
        rw [Matrix.det_mul]
        exact IsUnit.mul (hA_unit z) (isUnit_iff_ne_zero.mpr (hR_det_ne z))

lemma continuous_recorded {d n : ℕ} (hd : 3 ≤ d) {C : ℝ} (hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) (j : Fin (rounds d)) :
    Continuous (fun z : Tape d => recorded C w T z j) := by
  obtain ⟨hv_cont, hA_cont, hA_unit⟩ :=
    continuous_runState hd hC w T hT j.1 (Nat.le_of_lt j.2)
  have hlam_ge1 : 1 ≤ scale d j.1 := not_lt.mp (Nat.find_min _ j.2)
  have hC_pos : 0 < C := by linarith
  have hlam_pos : 0 < scale d j.1 := lt_of_lt_of_le zero_lt_one hlam_ge1
  have hv_zero_iff : ∀ (z : Tape d) (i : Fin n),
      (runState C w T z j).v i = 0 ↔ w i = 0 := by
    intro z i
    have hfeas := feasibility d n hd C hC w T hT z
    rcases (hfeas.2.1 j.1 (Nat.le_of_lt j.2)).2.1 i with ⟨θ, hθ_pos, _, hθ_eq⟩
    constructor
    · intro hv0
      rw [hv0] at hθ_eq
      have h0 : act (runState C w T z j).A 0 = 0 := by simp [act]
      rw [h0] at hθ_eq
      exact (smul_eq_zero.mp hθ_eq.symm).resolve_left (ne_of_gt hθ_pos)
    · intro hw0
      rw [hw0, smul_zero] at hθ_eq
      have hinvA := Matrix.nonsing_inv_mul (runState C w T z j).A (hA_unit z)
      calc
        (runState C w T z j).v i
          = act ((runState C w T z j).A⁻¹ * (runState C w T z j).A)
              ((runState C w T z j).v i) := by rw [hinvA, act_one]
        _ = act (runState C w T z j).A⁻¹ (act (runState C w T z j).A
              ((runState C w T z j).v i)) := act_mul _ _ _
        _ = 0 := by rw [hθ_eq]; simp [act]
  have hloc_cont : Continuous (fun z : Tape d =>
      localPoint C (scale d j) (runState C w T z j).v (z j)) := by
    unfold localPoint
    refine continuous_finsetSum Finset.univ (fun i _ => ?_)
    by_cases hwi : w i = 0
    · have hzero : (fun z : Tape d =>
          (projections C (scale d j) (runState C w T z j).v (z j) i *
            weights C (scale d j) (runState C w T z j).v (z j) i) •
            (runState C w T z j).v i) = fun _ => 0 := by
        ext z
        have hvz : (runState C w T z j).v i = 0 := (hv_zero_iff z i).mpr hwi
        simp [hvz]
      rw [hzero]; exact continuous_const
    · have hvi_cont : Continuous (fun z : Tape d => (runState C w T z j).v i) :=
        (continuous_apply i).comp hv_cont
      have hproj : Continuous (fun z : Tape d =>
          projections C (scale d j) (runState C w T z j).v (z j) i) := by
        unfold projections
        exact ((continuous_apply j).inner hvi_cont).div
          (continuous_const.mul hvi_cont.norm) (fun z =>
            mul_ne_zero (ne_of_gt (mul_pos hC_pos hlam_pos))
              (norm_ne_zero_iff.mpr (fun h0 => hwi ((hv_zero_iff z i).mp h0))))
      exact (hproj.mul (q_continuous.comp hproj)).smul hvi_cont
  unfold recorded
  exact continuous_act hA_cont hloc_cont

-- ============================================================================
-- Section 3: Scale and Round-Count Estimates
-- ============================================================================

lemma log_d_gt_one {d : ℕ} (hd : 3 ≤ d) : 1 < Real.log d := by
  have hexp1 : Real.exp 1 < (d : ℝ) := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.exp_one_lt_d9]
  have h1 := Real.log_lt_log (Real.exp_pos 1) hexp1
  rwa [Real.log_exp] at h1

lemma scale_rounds_lt_one (d : ℕ) : scale d (rounds d) < 1 := by
  rw [rounds]
  exact @Nat.find_spec (fun j => scale d j < 1) _ _

lemma rounds_pos {d : ℕ} (hd : 3 ≤ d) : 1 ≤ rounds d := by
  by_contra h0
  have hR0 : rounds d = 0 := by omega
  have hspec : scale d (rounds d) < 1 := scale_rounds_lt_one d
  rw [hR0] at hspec
  unfold scale at hspec
  simp only [pow_zero, div_one] at hspec
  linarith [log_d_gt_one hd]

lemma rounds_le_logb {d : ℕ} (hd : 3 ≤ d) :
    (rounds d : ℝ) ≤ 1 + Real.logb 2 (Real.log d) := by
  set R := rounds d
  have hR1 : 1 ≤ R := rounds_pos hd
  have hmin : ¬ (scale d (R - 1) < 1) := Nat.find_min _ (by omega : R - 1 < R)
  have hge1 : 1 ≤ scale d (R - 1) := not_lt.mp hmin
  unfold scale at hge1
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (R - 1) := by positivity
  have hpow_le : (2 : ℝ) ^ (R - 1) ≤ Real.log d := (one_le_div hpow_pos).mp hge1
  have hlogb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpow_pos hpow_le
  have hpow_eq : Real.logb 2 ((2 : ℝ) ^ (R - 1)) = ((R - 1 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [hpow_eq, Nat.cast_sub hR1, Nat.cast_one] at hlogb
  linarith

lemma rounds_mul_sqrt_le {d : ℕ} (hd : 3 ≤ d) :
    (rounds d : ℝ) * Real.sqrt (Real.log d / d) ≤ 12 := by
  set R := rounds d
  have hR1 : 1 ≤ R := rounds_pos hd
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog1 : 1 < Real.log d := log_d_gt_one hd
  have hmin : 1 ≤ scale d (R - 1) := not_lt.mp (Nat.find_min _ (by omega : R - 1 < R))
  unfold scale at hmin
  have hpow_le : (2 : ℝ) ^ (R - 1) ≤ Real.log d :=
    (one_le_div (by positivity)).mp hmin
  have hnat_pow : R - 1 ≤ 2 ^ (R - 1) := Nat.le_of_lt (R - 1).lt_two_pow_self
  have hR_sub_le : ((R - 1 : ℕ) : ℝ) ≤ Real.log d := by
    calc
      ((R - 1 : ℕ) : ℝ) ≤ ((2 ^ (R - 1) : ℕ) : ℝ) := by exact_mod_cast hnat_pow
      _ = (2 : ℝ) ^ (R - 1) := by push_cast; rfl
      _ ≤ Real.log d := hpow_le
  rw [Nat.cast_sub hR1, Nat.cast_one] at hR_sub_le
  have hR_le : (R : ℝ) ≤ 2 * Real.log d := by linarith
  -- Bound Real.log d ≤ 3 * d ^ (1/3)
  let y : ℝ := (d : ℝ) ^ ((1 : ℝ) / 3)
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hd_pos _
  have hlog_y : Real.log y = (1 / 3 : ℝ) * Real.log d :=
    Real.log_rpow hd_pos _
  have hy_bound : Real.log y ≤ y := by
    linarith [Real.log_le_sub_one_of_pos hy_pos]
  have hlog_le : Real.log d ≤ 3 * y := by linarith
  have hlog_cube : (Real.log d) ^ 3 ≤ 27 * (d : ℝ) := by
    have hcube : (Real.log d) ^ 3 ≤ (3 * y) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hlog_le 3
    have hy3 : y ^ 3 = (d : ℝ) := by
      dsimp [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hd_pos)]
      norm_num
    calc
      (Real.log d) ^ 3 ≤ 27 * y ^ 3 := by linarith [show (3 * y) ^ 3 = 27 * y ^ 3 by ring]
      _ = 27 * (d : ℝ) := by rw [hy3]
  have hsq : ((R : ℝ) * Real.sqrt (Real.log d / d)) ^ 2 ≤ 12 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg (by linarith) (le_of_lt hd_pos))]
    have hR2 : (R : ℝ) ^ 2 ≤ (2 * Real.log d) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg R) hR_le 2
    calc
      (R : ℝ) ^ 2 * (Real.log d / d)
        ≤ (2 * Real.log d) ^ 2 * (Real.log d / d) :=
          mul_le_mul_of_nonneg_right hR2 (div_nonneg (by linarith) (le_of_lt hd_pos))
      _ = 4 * (Real.log d) ^ 3 / d := by ring
      _ ≤ 4 * (27 * d) / d := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
          linarith
      _ = 108 := by field_simp [ne_of_gt hd_pos]; ring
      _ ≤ 12 ^ 2 := by norm_num
  nlinarith [show 0 ≤ (R : ℝ) * Real.sqrt (Real.log d / d) by positivity]

lemma sum_inv_scale_le_two {d : ℕ} (hd : 3 ≤ d) :
    ∑ j ∈ Finset.range (rounds d), (1 / scale d j) ≤ 2 := by
  set R := rounds d
  have hR1 : 1 ≤ R := rounds_pos hd
  have hge1 : 1 ≤ scale d (R - 1) :=
    not_lt.mp (Nat.find_min _ (by omega : R - 1 < R))
  have hterm : ∀ j ∈ Finset.range R, 1 / scale d j ≤ (1 / 2 : ℝ) ^ (R - 1 - j) := by
    intro j hj
    have hj_lt : j < R := Finset.mem_range.mp hj
    have hsc_eq : scale d j = scale d (R - 1) * (2 : ℝ) ^ (R - 1 - j) := by
      unfold scale
      have hpow : (2 : ℝ) ^ (R - 1) = (2 : ℝ) ^ j * (2 : ℝ) ^ (R - 1 - j) := by
        rw [← pow_add]
        congr 1; omega
      rw [div_mul_eq_mul_div, hpow]
      field_simp
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (R - 1 - j) := by positivity
    have hsc_ge : (2 : ℝ) ^ (R - 1 - j) ≤ scale d j := by
      rw [hsc_eq]
      calc
        (2 : ℝ) ^ (R - 1 - j) = 1 * (2 : ℝ) ^ (R - 1 - j) := (one_mul _).symm
        _ ≤ scale d (R - 1) * (2 : ℝ) ^ (R - 1 - j) :=
          mul_le_mul_of_nonneg_right hge1 (le_of_lt hpow_pos)
    calc
      1 / scale d j ≤ 1 / (2 : ℝ) ^ (R - 1 - j) :=
        one_div_le_one_div_of_le hpow_pos hsc_ge
      _ = (1 / 2 : ℝ) ^ (R - 1 - j) := by rw [one_div_pow]
  calc
    ∑ j ∈ Finset.range R, (1 / scale d j)
      ≤ ∑ j ∈ Finset.range R, (1 / 2 : ℝ) ^ (R - 1 - j) := Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.range R, (1 / 2 : ℝ) ^ k := Finset.sum_range_reflect _ R
    _ = ((1 / 2 : ℝ) ^ R - 1) / (1 / 2 - 1) := geom_sum_eq (by norm_num) R
    _ = 2 - 2 * (1 / 2 : ℝ) ^ R := by ring
    _ ≤ 2 := by linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ R by positivity]

lemma sum_inv_scale_sq_le_two {d : ℕ} (hd : 3 ≤ d) :
    ∑ j ∈ Finset.range (rounds d), (1 / (scale d j) ^ 2) ≤ 2 := by
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (sum_inv_scale_le_two hd)
  have hj_lt : j < rounds d := Finset.mem_range.mp hj
  have hge1 : 1 ≤ scale d j := not_lt.mp (Nat.find_min _ hj_lt)
  have hsc_pos : 0 < scale d j := lt_of_lt_of_le zero_lt_one hge1
  have hinv_le1 : 1 / scale d j ≤ 1 := (div_le_one hsc_pos).mpr hge1
  have hinv_nn : 0 ≤ 1 / scale d j := le_of_lt (one_div_pos.mpr hsc_pos)
  calc
    1 / (scale d j) ^ 2 = (1 / scale d j) * (1 / scale d j) := by ring
    _ ≤ 1 * (1 / scale d j) := mul_le_mul_of_nonneg_right hinv_le1 hinv_nn
    _ = 1 / scale d j := one_mul _

-- ============================================================================
-- Section 4: Outer-Measure Product Lower Bound Lemma
-- ============================================================================

lemma prod_measure_ge {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {S : Set α} (hS : MeasurableSet S) {U : Set (α × β)} {c : ENNReal}
    (hfib : ∀ x ∈ S, c ≤ ν (Prod.mk x ⁻¹' U)) :
    μ S * c ≤ (μ.prod ν) U := by
  let W := toMeasurable (μ.prod ν) U
  have hUW : U ⊆ W := subset_toMeasurable (μ.prod ν) U
  have hW : MeasurableSet W := measurableSet_toMeasurable (μ.prod ν) U
  rw [← measure_toMeasurable U]
  change μ S * c ≤ (μ.prod ν) W
  rw [Measure.prod_apply hW]
  have hle1 : (∫⁻ _x in S, c ∂μ) ≤ ∫⁻ x in S, ν (Prod.mk x ⁻¹' W) ∂μ := by
    refine setLIntegral_mono' hS (fun x hx => le_trans (hfib x hx) (measure_mono ?_))
    intro y hy
    exact hUW hy
  have hle2 : (∫⁻ x in S, ν (Prod.mk x ⁻¹' W) ∂μ) ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' W) ∂μ :=
    setLIntegral_le_lintegral S _
  rw [setLIntegral_const S c, mul_comm] at hle1
  exact le_trans hle1 hle2

-- ============================================================================
-- Section 5: Tape Gluing & Prefix Independence
-- ============================================================================

def glue {d k m : ℕ} (_hk : k + m = rounds d) (pref : Fin k → E d) (tail : Fin m → E d) :
    Tape d :=
  fun j => if h : j.1 < k then pref ⟨j.1, h⟩ else tail ⟨j.1 - k, by omega⟩

lemma runState_congr_prefix {d n : ℕ} {C : ℝ} {w : Fin n → E d} {T : Mat d}
    {z z' : Tape d} {k : ℕ}
    (h : ∀ m, m < k → ∀ (hmR : m < rounds d), z ⟨m, hmR⟩ = z' ⟨m, hmR⟩) :
    ∀ j ≤ k, runState C w T z j = runState C w T z' j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj_lt : j < k := Nat.lt_of_succ_le hj
      by_cases hjR : j < rounds d
      · simp only [runState, hjR, ↓reduceDIte]
        rw [ih (Nat.le_of_lt hj_lt), h j hj_lt hjR]
      · simp only [runState, hjR, ↓reduceDIte]
        exact ih (Nat.le_of_lt hj_lt)

lemma recorded_congr_prefix {d n : ℕ} {C : ℝ} {w : Fin n → E d} {T : Mat d}
    {z z' : Tape d} {k : ℕ}
    (h : ∀ m, m < k → ∀ (hmR : m < rounds d), z ⟨m, hmR⟩ = z' ⟨m, hmR⟩)
    {j : Fin (rounds d)} (hj : j.1 < k) :
    recorded C w T z j = recorded C w T z' j := by
  unfold recorded
  rw [runState_congr_prefix h j.1 (Nat.le_of_lt hj), h j.1 hj j.2]

-- ============================================================================
-- Section 6: Deterministic Contradiction for Small-Mean Good Trajectories
-- ============================================================================

lemma no_all_small_good {d n : ℕ} (hd : 3 ≤ d) {C η : ℝ} (hC : 64 ≤ C)
    (hη_pos : 0 < η) (hη1 : η ≤ 1 / 384) (hη2 : 128 * C ^ 2 * η ≤ 1 / 256)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T)
    (a : E d) (ha_supp : support w a = 1) (z : Tape d)
    (hsmall : ∀ j : Fin (rounds d),
      conditionalMean C (scale d j) (runState C w T z j).v
        (act (runState C w T z j).A.transpose a) <
        η * Real.sqrt (Real.log d / d))
    (hgood : ∀ j : Fin (rounds d),
      GoodUpdate C (scale d j) (runState C w T z j).v
        (act (runState C w T z j).A.transpose a) (z j)) : False := by
  set R := rounds d
  have hR1 : 1 ≤ R := rounds_pos hd
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog1 : 1 < Real.log d := log_d_gt_one hd
  have hlog_pos : 0 < Real.log d := lt_trans zero_lt_one hlog1
  obtain ⟨h0_feas, hinv_feas, hstep_feas⟩ := feasibility d n hd C hC w T hT z
  obtain ⟨hlewis_23, hlow_23⟩ := lemma_2_3 d n hd C hC w T hT z
  let b : ℕ → E d := fun k => act (runState C w T z k).A.transpose a
  let H : ℕ → ℝ := fun k => support (runState C w T z k).v (b k)
  -- Initial support H 0 = 1 and norm ‖b 0‖ ≤ 4
  have hH0 : H 0 = 1 := by
    dsimp [H, b]
    rw [support_eq_sum_abs]
    have hcongr : ∑ i, |inner ℝ (act (runState C w T z 0).A.transpose a)
        ((runState C w T z 0).v i)| = ∑ i, |inner ℝ a (w i)| := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← inner_act_transpose, h0_feas i]
    rw [hcongr, ← support_eq_sum_abs, ha_supp]
  have hb0_le4 : ‖b 0‖ ≤ 4 := by
    have := hlow_23 (b 0)
    change ‖b 0‖ / 4 ≤ H 0 at this
    linarith
  -- H k ≤ 1 for all k ≤ R
  have hHk_le1 : ∀ k ≤ R, H k ≤ 1 := by
    intro k hk
    dsimp [H, b]
    rw [support_eq_sum_abs]
    have hle : ∑ i, |inner ℝ (act (runState C w T z k).A.transpose a)
        ((runState C w T z k).v i)| ≤ ∑ i, |inner ℝ a (w i)| := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← inner_act_transpose]
      obtain ⟨θ, hθ_pos, hθ_le, hθ_eq⟩ := (hinv_feas k hk).2.1 i
      rw [hθ_eq, real_inner_smul_right, abs_mul, abs_of_pos hθ_pos]
      calc
        θ * |inner ℝ a (w i)| ≤ 1 * |inner ℝ a (w i)| :=
          mul_le_mul_of_nonneg_right hθ_le (abs_nonneg _)
        _ = |inner ℝ a (w i)| := one_mul _
    exact le_trans hle (by rw [← support_eq_sum_abs, ha_supp])
  -- Relate b (j + 1) to act R_j (b j) for j < R
  have hb_step : ∀ (j : ℕ) (hj : j < R),
      b (j + 1) = act (CFC.sqrt (weightedMatrix (runState C w T z j).v
        (weights C (scale d j) (runState C w T z j).v (z ⟨j, hj⟩)))) (b j) ∧
      (runState C w T z (j + 1)).v = updatedGenerators (runState C w T z j).v
        (weights C (scale d j) (runState C w T z j).v (z ⟨j, hj⟩)) := by
    intro j hj
    have hst : runState C w T z (j + 1) =
        step C (scale d j) (runState C w T z j) (z ⟨j, hj⟩) := by
      have hjR : j < rounds d := hj
      simp [runState, hjR]
    refine ⟨?_, ?_⟩
    · dsimp [b]
      rw [hst]
      dsimp [step]
      set Sj := weightedMatrix (runState C w T z j).v
        (weights C (scale d j) (runState C w T z j).v (z ⟨j, hj⟩))
      set Rj := CFC.sqrt Sj
      have hRj_psd : (0 : Mat d) ≤ Rj := CFC.sqrt_nonneg Sj
      have hRj_herm : Rj.IsHermitian := by simpa using hRj_psd.isHermitian
      have hRj_symm : Rj.transpose = Rj := hRj_herm
      rw [Matrix.transpose_mul, hRj_symm, act_mul]
    · rw [hst]; rfl
  -- Part A: Lower bound H R ≥ 3 / 4
  have hHR_ge : 3 / 4 ≤ H R := by
    have hstep_loss : ∀ j ∈ Finset.range R,
        H j - H (j + 1) ≤ 4 / (C * scale d j) + 4 * η * Real.sqrt (Real.log d / d) := by
      intro j hj
      have hj_lt : j < R := Finset.mem_range.mp hj
      have hgd := (hgood ⟨j, hj_lt⟩).2
      obtain ⟨hb_eq, hv_eq⟩ := hb_step j hj_lt
      have hloss : H j - H (j + 1) ≤
          4 * H j / (C * scale d j) +
          4 * conditionalMean C (scale d j) (runState C w T z j).v (b j) := by
        dsimp [H]
        rw [hb_eq, hv_eq]
        exact hgd
      have hlam_ge1 : 1 ≤ scale d j := not_lt.mp (Nat.find_min _ hj_lt)
      have hC_lam_pos : 0 < C * scale d j := mul_pos (by linarith) (by linarith)
      have hHj_le1 : H j ≤ 1 := hHk_le1 j (Nat.le_of_lt hj_lt)
      have h1 : 4 * H j / (C * scale d j) ≤ 4 / (C * scale d j) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hC_lam_pos)
      have h2 := hsmall ⟨j, hj_lt⟩
      linarith
    have htele : ∑ j ∈ Finset.range R, (H j - H (j + 1)) = H 0 - H R := by
      have := Finset.sum_range_sub' H R
      exact this
    have hsum_le := Finset.sum_le_sum hstep_loss
    rw [htele, hH0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum_le
    have hsum_sc : ∑ j ∈ Finset.range R, (4 / (C * scale d j)) ≤ 8 / C := by
      have hrew : ∑ j ∈ Finset.range R, (4 / (C * scale d j)) =
          (4 / C) * ∑ j ∈ Finset.range R, (1 / scale d j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => by ring)
      rw [hrew]
      have h1 := sum_inv_scale_le_two hd
      calc
        (4 / C) * ∑ j ∈ Finset.range R, (1 / scale d j) ≤ (4 / C) * 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 8 / C := by ring
    have h8C : 8 / C ≤ 1 / 8 := by
      calc
        8 / C ≤ 8 / 64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hC
        _ = 1 / 8 := by norm_num
    have hRsqrt := rounds_mul_sqrt_le hd
    have hterm2 : (R : ℝ) * (4 * η * Real.sqrt (Real.log d / d)) ≤ 1 / 8 := by
      calc
        (R : ℝ) * (4 * η * Real.sqrt (Real.log d / d))
          = 4 * η * ((R : ℝ) * Real.sqrt (Real.log d / d)) := by ring
        _ ≤ 4 * (1 / 384) * 12 := by
            nlinarith [show 0 ≤ (R : ℝ) * Real.sqrt (Real.log d / d) by positivity]
        _ = 1 / 8 := by norm_num
    linarith
  -- Part B: Upper bound H R ≤ 3 / 8 via norm contraction
  set M : ℝ := 128 * C ^ 2 * η
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hM_le : M ≤ 1 / 256 := hη2
  let α : ℕ → ℝ := fun k => Real.sqrt d * ‖b k‖ / (scale d k) ^ 2
  have hα_nn : ∀ k, 0 ≤ α k := fun k => by dsimp [α]; positivity
  have hα_ind : ∀ k ≤ R,
      α k ≤ M ^ (1 - (2 : ℝ)⁻¹ ^ k) * (4 * Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ k) := by
    intro k hk
    induction k with
    | zero =>
        simp only [pow_zero, sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
        dsimp [α, scale]
        simp only [pow_zero, div_one]
        have h1 : 1 ≤ (Real.log d) ^ 2 := by nlinarith
        calc
          Real.sqrt d * ‖b 0‖ / (Real.log d) ^ 2
            ≤ Real.sqrt d * ‖b 0‖ / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one h1
          _ = Real.sqrt d * ‖b 0‖ := div_one _
          _ ≤ Real.sqrt d * 4 := mul_le_mul_of_nonneg_left hb0_le4 (Real.sqrt_nonneg d)
          _ = 4 * Real.sqrt d := by ring
    | succ k ih =>
        have hk_lt : k < R := Nat.lt_of_succ_le hk
        have hih := ih (Nat.le_of_lt hk_lt)
        have hgd1 := (hgood ⟨k, hk_lt⟩).1
        obtain ⟨hb_eq, _⟩ := hb_step k hk_lt
        have hb_norm_sq : ‖b (k + 1)‖ ^ 2 ≤
            (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖b k‖ *
              (η * Real.sqrt (Real.log d / d)) := by
          rw [hb_eq]
          have hsm := le_of_lt (hsmall ⟨k, hk_lt⟩)
          calc
            ‖act (CFC.sqrt (weightedMatrix (runState C w T z k).v
                (weights C (scale d k) (runState C w T z k).v (z ⟨k, hk_lt⟩)))) (b k)‖ ^ 2
              ≤ (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖b k‖ *
                  conditionalMean C (scale d k) (runState C w T z k).v (b k) := hgd1
            _ ≤ (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖b k‖ *
                  (η * Real.sqrt (Real.log d / d)) := by
                apply mul_le_mul_of_nonneg_left hsm
                positivity
        have hsc_succ : scale d (k + 1) = scale d k / 2 := by
          unfold scale; rw [pow_succ]; ring
        have hsc_pos : 0 < scale d k := by unfold scale; positivity
        have hα_succ_sq : (α (k + 1)) ^ 2 ≤ M * α k := by
          dsimp [α]
          rw [hsc_succ, div_pow, mul_pow, Real.sq_sqrt (le_of_lt hd_pos)]
          have hsqrt_div : Real.sqrt (Real.log d / d) =
              Real.sqrt (Real.log d) / Real.sqrt d := Real.sqrt_div (le_of_lt hlog_pos) d
          have hsqrt_log_ne : Real.sqrt (Real.log d) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.mpr hlog_pos)
          have hsqrt_d_ne : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
          have hsc_ne : scale d k ≠ 0 := ne_of_gt hsc_pos
          have hrhs_simp :
              (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖b k‖ *
                (η * Real.sqrt (Real.log d / d)) =
              (8 * C ^ 2 * η / Real.sqrt d) * (scale d k) ^ 2 * ‖b k‖ := by
            rw [hsqrt_div]
            field_simp [hsqrt_log_ne, hsqrt_d_ne]
          rw [hrhs_simp] at hb_norm_sq
          have hmul_d := mul_le_mul_of_nonneg_left hb_norm_sq (le_of_lt hd_pos)
          have hdiv_sc := div_le_div_of_nonneg_right hmul_d (by positivity : 0 ≤ (scale d k) ^ 4 / 16)
          calc
            d * ‖b (k + 1)‖ ^ 2 / ((scale d k / 2) ^ 2) ^ 2
              = d * ‖b (k + 1)‖ ^ 2 / ((scale d k) ^ 4 / 16) := by ring
            _ ≤ d * ((8 * C ^ 2 * η / Real.sqrt d) * (scale d k) ^ 2 * ‖b k‖) /
                  ((scale d k) ^ 4 / 16) := hdiv_sc
            _ = M * (Real.sqrt d * ‖b k‖ / (scale d k) ^ 2) := by
                dsimp [M]
                set sd := Real.sqrt d
                have hsd_ne : sd ≠ 0 := hsqrt_d_ne
                have hd_eq : (d : ℝ) = sd ^ 2 := (Real.sq_sqrt (le_of_lt hd_pos)).symm
                rw [hd_eq]
                field_simp [hsd_ne, hsc_ne]
                ring
        have hα_le_sqrt : α (k + 1) ≤ (M * α k) ^ ((1 : ℝ) / 2) := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.le_sqrt_of_sq_le hα_succ_sq
        have hbase4_pos : 0 < 4 * Real.sqrt d := by positivity
        calc
          α (k + 1) ≤ (M * α k) ^ ((1 : ℝ) / 2) := hα_le_sqrt
          _ ≤ (M * (M ^ (1 - (2 : ℝ)⁻¹ ^ k) * (4 * Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ k))) ^
                ((1 : ℝ) / 2) := by
              refine Real.rpow_le_rpow (mul_nonneg (le_of_lt hM_pos) (hα_nn k)) ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_left hih (le_of_lt hM_pos)
          _ = M ^ (1 - (2 : ℝ)⁻¹ ^ (k + 1)) *
                (4 * Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ (k + 1)) := by
              rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity),
                ← Real.rpow_one_add' (le_of_lt hM_pos) (by
                  have : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                  linarith),
                ← Real.rpow_mul (le_of_lt hM_pos),
                ← Real.rpow_mul (le_of_lt hbase4_pos)]
              congr 2 <;> (rw [pow_succ]; ring)
  have hαR := hα_ind R le_rfl
  have hexp_R : (2 : ℝ)⁻¹ ^ R ≤ 1 / 2 := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0) with ⟨m, hmR⟩
    rw [hmR, pow_succ']
    have hm1 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hexp_R_pos : 0 < (2 : ℝ)⁻¹ ^ R := by positivity
  have hM_term : M ^ (1 - (2 : ℝ)⁻¹ ^ R) ≤ 1 / 16 := by
    have hM_le1 : M ≤ 1 := by linarith
    have hexp_ge : (1 : ℝ) / 2 ≤ 1 - (2 : ℝ)⁻¹ ^ R := by linarith
    calc
      M ^ (1 - (2 : ℝ)⁻¹ ^ R) ≤ M ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hM_pos hM_le1 hexp_ge
      _ ≤ (1 / 256 : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (le_of_lt hM_pos) hM_le (by norm_num)
      _ = 1 / 16 := by
        rw [← Real.sqrt_eq_rpow]
        norm_num
  have h4d_term : (4 * Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ R) ≤ 6 := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg d)]
    have h4_le : (4 : ℝ) ^ ((2 : ℝ)⁻¹ ^ R) ≤ 2 := by
      calc
        (4 : ℝ) ^ ((2 : ℝ)⁻¹ ^ R) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_R
        _ = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
    have hd_le : (Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ R) ≤ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hd_pos),
        Real.rpow_def_of_pos hd_pos]
      have hscR : scale d R < 1 := scale_rounds_lt_one d
      unfold scale at hscR
      have hprod : Real.log d * (1 / 2 * (2 : ℝ)⁻¹ ^ R) < 1 := by
        have hrew : Real.log d * (1 / 2 * (2 : ℝ)⁻¹ ^ R) =
            (Real.log d / (2 : ℝ) ^ R) / 2 := by
          rw [inv_pow]; ring
        rw [hrew]; linarith
      calc
        Real.exp (Real.log d * (1 / 2 * (2 : ℝ)⁻¹ ^ R)) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr (le_of_lt hprod)
        _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
    calc
      (4 : ℝ) ^ ((2 : ℝ)⁻¹ ^ R) * (Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ R) ≤ 2 * 3 :=
        mul_le_mul h4_le hd_le (by positivity) (by norm_num)
      _ = 6 := by norm_num
  have hαR_le : α R ≤ 3 / 8 := by
    calc
      α R ≤ M ^ (1 - (2 : ℝ)⁻¹ ^ R) * (4 * Real.sqrt d) ^ ((2 : ℝ)⁻¹ ^ R) := hαR
      _ ≤ (1 / 16) * 6 := mul_le_mul hM_term h4d_term (by positivity) (by norm_num)
      _ = 3 / 8 := by norm_num
  have hscR_lt1 : scale d R < 1 := scale_rounds_lt_one d
  have hscR_pos : 0 < scale d R := by unfold scale; positivity
  have hscR_sq_le1 : (scale d R) ^ 2 ≤ 1 := by nlinarith
  have hHR_le : H R ≤ 3 / 8 := by
    have h23 := (hlewis_23 R le_rfl).2 (b R)
    change H R ≤ Real.sqrt d * ‖b R‖ at h23
    have hrew : Real.sqrt d * ‖b R‖ = (scale d R) ^ 2 * α R := by
      dsimp [α]; field_simp [ne_of_gt hscR_pos]
    calc
      H R ≤ (scale d R) ^ 2 * α R := hrew ▸ h23
      _ ≤ 1 * (3 / 8) := mul_le_mul hscR_sq_le1 hαR_le (hα_nn R) zero_le_one
      _ = 3 / 8 := one_mul _
  linarith

-- ============================================================================
-- Section 7: Sequential Product-Measure Induction over Remaining Rounds
-- ============================================================================

lemma tail_prob_lb {d n : ℕ} (hd : 3 ≤ d) {C c₀ η : ℝ} (hC : 64 ≤ C)
    (hc₀_pos : 0 < c₀)
    (h24 : ∀ (C' lam : ℝ), 64 ≤ C' → 1 ≤ lam →
      ∀ (v : Fin n → E d), Submodule.span ℝ (Set.range v) = ⊤ →
      ∀ b : E d, b ≠ 0 →
      ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C' ^ 2 * lam ^ 2))) ≤
        stdGaussian (E d) (alignmentEvent C' lam b) ∧
      0 < conditionalMean C' lam v b ∧
      stdGaussian (E d) {z | z ∈ alignmentEvent C' lam b ∧ ¬ GoodUpdate C' lam v b z} ≤
        stdGaussian (E d) (alignmentEvent C' lam b) / 2)
    (hη_pos : 0 < η) (hη1 : η ≤ 1 / 384) (hη2 : 128 * C ^ 2 * η ≤ 1 / 256)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T)
    (a : E d) (ha_supp : support w a = 1) :
    let qstar := (η / 2) * Real.sqrt (Real.log d / d)
    let p_step : ℕ → ℝ := fun j =>
      min 1 ((c₀ / 2) * Real.exp (-Real.log d / (C ^ 2 * (scale d j) ^ 2)))
    let HitTape : Set (Tape d) :=
      {z | ∃ j : Fin (rounds d), qstar ≤ inner ℝ a (recorded C w T z j)}
    ∀ (m k : ℕ) (hkm : k + m = rounds d) (pref : Fin k → E d),
      let z₀ := glue hkm pref (fun _ => 0)
      ((∃ j : Fin (rounds d), j.1 < k ∧ qstar ≤ inner ℝ a (recorded C w T z₀ j)) →
        (1 : ENNReal) ≤
          (Measure.pi fun _ : Fin m => stdGaussian (E d))
            {tail | glue hkm pref tail ∈ HitTape}) ∧
      ((∀ (j : ℕ) (hj : j < k),
          conditionalMean C (scale d j) (runState C w T z₀ j).v
            (act (runState C w T z₀ j).A.transpose a) <
            η * Real.sqrt (Real.log d / d) ∧
          GoodUpdate C (scale d j) (runState C w T z₀ j).v
            (act (runState C w T z₀ j).A.transpose a) (z₀ ⟨j, by omega⟩)) →
        ENNReal.ofReal (qstar * ∏ i ∈ Finset.Ico k (rounds d), p_step i) ≤
          (Measure.pi fun _ : Fin m => stdGaussian (E d))
            {tail | glue hkm pref tail ∈ HitTape}) := by
  intro qstar p_step HitTape
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog1 : 1 < Real.log d := log_d_gt_one hd
  have hlog_pos : 0 < Real.log d := lt_trans zero_lt_one hlog1
  -- Show qstar ≤ 1
  have hqstar_pos : 0 < qstar := by dsimp [qstar]; positivity
  have hqstar_le1 : qstar ≤ 1 := by
    have hlog_le_d : Real.log d ≤ d := by
      linarith [Real.log_le_sub_one_of_pos hd_pos]
    have hsqrt_le1 : Real.sqrt (Real.log d / d) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ((div_le_one hd_pos).mpr hlog_le_d)
    dsimp [qstar]
    nlinarith
  have hp_pos : ∀ j, 0 < p_step j := fun j => by
    dsimp [p_step]; exact lt_min zero_lt_one (by positivity)
  have hp_le1 : ∀ j, p_step j ≤ 1 := fun j => min_le_left 1 _
  have ha_ne : a ≠ 0 := by
    intro h0; subst h0
    simp [support_eq_sum_abs] at ha_supp
  intro m
  induction m with
  | zero =>
      intro k hkm pref
      have hkR : k = rounds d := by omega
      let z₀ := glue hkm pref (fun _ => 0)
      have hglue_eq : ∀ tail : Fin 0 → E d, glue hkm pref tail = z₀ := by
        intro tail; ext j
        dsimp [z₀, glue]
        have hj_lt : j.1 < k := by omega
        simp [hj_lt]
      refine ⟨?_, ?_⟩
      · intro hhit
        have huniv : {tail : Fin 0 → E d | glue hkm pref tail ∈ HitTape} = univ := by
          ext tail
          simp only [mem_univ, iff_true]
          change glue hkm pref tail ∈ HitTape
          rw [hglue_eq tail]
          obtain ⟨j, _, hj_hit⟩ := hhit
          exact ⟨j, hj_hit⟩
        rw [huniv, measure_univ]
      · intro hall
        exfalso
        subst hkR
        exact no_all_small_good hd hC hη_pos hη1 hη2 w T hT a ha_supp z₀
          (fun j => (hall j.1 j.2).1) (fun j => (hall j.1 j.2).2)
  | succ m ih =>
      intro k hkm pref
      have hkR : k < rounds d := by omega
      let z₀ := glue hkm pref (fun _ => 0)
      -- First branch: already hit before k
      have hbranch1 :
          (∃ j : Fin (rounds d), j.1 < k ∧ qstar ≤ inner ℝ a (recorded C w T z₀ j)) →
          (1 : ENNReal) ≤
            (Measure.pi fun _ : Fin (m + 1) => stdGaussian (E d))
              {tail | glue hkm pref tail ∈ HitTape} := by
        intro ⟨j, hj_lt, hj_hit⟩
        have huniv : {tail : Fin (m + 1) → E d | glue hkm pref tail ∈ HitTape} = univ := by
          ext tail
          simp only [mem_univ, iff_true]
          change glue hkm pref tail ∈ HitTape
          refine ⟨j, ?_⟩
          have hrec_eq : recorded C w T (glue hkm pref tail) j = recorded C w T z₀ j := by
            apply recorded_congr_prefix _ hj_lt
            intro r hr hrR
            simp [z₀, glue, hr]
          rwa [hrec_eq]
        rw [huniv, measure_univ]
      refine ⟨hbranch1, ?_⟩
      intro hall
      by_cases hhit_before :
          ∃ j : Fin (rounds d), j.1 < k ∧ qstar ≤ inner ℝ a (recorded C w T z₀ j)
      · have hprod_le1 : qstar * ∏ i ∈ Finset.Ico k (rounds d), p_step i ≤ 1 := by
          have h1 : ∏ i ∈ Finset.Ico k (rounds d), p_step i ≤ 1 :=
            Finset.prod_le_one (fun i _ => le_of_lt (hp_pos i)) (fun i _ => hp_le1 i)
          calc
            qstar * ∏ i ∈ Finset.Ico k (rounds d), p_step i ≤ 1 * 1 :=
              mul_le_mul hqstar_le1 h1
                (Finset.prod_nonneg fun i _ => le_of_lt (hp_pos i)) zero_le_one
            _ = 1 := mul_one 1
        exact le_trans (ENNReal.ofReal_le_one.mpr hprod_le1) (hbranch1 hhit_before)
      -- Otherwise, prepare state at round k (depends only on pref!)
      set sk := runState C w T z₀ k
      set bk : E d := act sk.A.transpose a
      have hspan_k : Submodule.span ℝ (Set.range sk.v) = ⊤ :=
        ((feasibility d n hd C hC w T hT z₀).2.1 k (Nat.le_of_lt hkR)).1
      have hAk_unit : IsUnit sk.A.det :=
        (continuous_runState hd hC w T hT k (Nat.le_of_lt hkR)).2.2 z₀
      have hbk_ne : bk ≠ 0 := by
        intro hb0
        have hAT_unit : IsUnit sk.A.transpose.det := by
          rw [Matrix.det_transpose]; exact hAk_unit
        have hinv := Matrix.nonsing_inv_mul sk.A.transpose hAT_unit
        have ha0 : a = 0 := by
          calc
            a = act (sk.A.transpose⁻¹ * sk.A.transpose) a := by rw [hinv, act_one]
            _ = act sk.A.transpose⁻¹ bk := act_mul _ _ _
            _ = 0 := by rw [hb0]; simp [act]
        exact ha_ne ha0
      have hlam_ge1 : 1 ≤ scale d k := not_lt.mp (Nat.find_min _ hkR)
      obtain ⟨hPE_lb, hμk_pos, hgood_fail⟩ :=
        h24 C (scale d k) hC hlam_ge1 sk.v hspan_k bk hbk_ne
      set Ev_k := alignmentEvent C (scale d k) bk
      have hEv_meas : MeasurableSet Ev_k := by
        have hEv_eq : Ev_k =
            {z : E d | Real.sqrt (Real.log d) / (C * scale d k) ≤ inner ℝ z (‖bk‖⁻¹ • bk)} ∩
            {z : E d | inner ℝ z (‖bk‖⁻¹ • bk) ≤ Real.sqrt (Real.log d) / (C * scale d k) + 1} :=
          rfl
        rw [hEv_eq]
        exact (measurableSet_le measurable_const
          (continuous_id.inner continuous_const).measurable).inter
          (measurableSet_le (continuous_id.inner continuous_const).measurable measurable_const)
      have hPE_lt_top : stdGaussian (E d) Ev_k < ⊤ := measure_lt_top _ _
      -- Split Fin (m + 1) → E d via piFinSuccAbove at 0
      have hkm' : (k + 1) + m = rounds d := by omega
      let snocPref : E d → Fin (k + 1) → E d := fun head r =>
        if hr : r.1 < k then pref ⟨r.1, hr⟩ else head
      let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E d) 0
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => stdGaussian (E d)) 0
      -- Relate glue hkm pref t to glue hkm' (snocPref (t 0)) (fun j => t j.succ)
      have hglue_split : ∀ t : Fin (m + 1) → E d,
          glue hkm pref t =
            glue hkm' (snocPref (eqv t).1) (eqv t).2 := by
        intro t
        funext j
        dsimp [glue, snocPref, eqv, MeasurableEquiv.piFinSuccAbove,
          Fin.insertNthEquiv, Fin.removeNth]
        by_cases hjk : j.1 < k
        · have hjk1 : j.1 < k + 1 := by omega
          simp [hjk, hjk1]
        · by_cases hjeq : j.1 = k
          · have hjk1 : j.1 < k + 1 := by omega
            simp only [hjk, ↓reduceDIte, hjk1]
            congr 1
            apply Fin.ext
            dsimp
            omega
          · have hjk1 : ¬ (j.1 < k + 1) := by omega
            simp only [hjk, ↓reduceDIte, hjk1]
            congr 1
            apply Fin.ext
            simp only [Fin.succAbove_zero, Fin.val_succ]
            omega
      let U_prod : Set (E d × (Fin m → E d)) :=
        {p | glue hkm' (snocPref p.1) p.2 ∈ HitTape}
      have hmeas_eq : (Measure.pi fun _ : Fin (m + 1) => stdGaussian (E d))
          {t | glue hkm pref t ∈ HitTape} =
          ((stdGaussian (E d)).prod (Measure.pi fun _ : Fin m => stdGaussian (E d))) U_prod := by
        have hpre : {t : Fin (m + 1) → E d | glue hkm pref t ∈ HitTape} = eqv ⁻¹' U_prod := by
          ext t
          change (glue hkm pref t ∈ HitTape) ↔ (glue hkm' (snocPref (eqv t).1) (eqv t).2 ∈ HitTape)
          rw [hglue_split t]
        rw [hpre, ← hmp.map_eq]
        exact (eqv.measurableEmbedding.map_apply _ U_prod).symm
      rw [hmeas_eq]
      have hIco_split : ∏ i ∈ Finset.Ico k (rounds d), p_step i =
          p_step k * ∏ i ∈ Finset.Ico (k + 1) (rounds d), p_step i := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_Ico.mpr ⟨le_rfl, hkR⟩)]
        congr 2
        ext r
        simp only [Finset.mem_erase, Finset.mem_Ico]
        omega
      -- Case split on SmallMean vs LargeMean at round k
      set μk := conditionalMean C (scale d k) sk.v bk
      by_cases hsm_k : μk < η * Real.sqrt (Real.log d / d)
      · -- Small-mean at round k: condition on Ev_k ∩ GoodUpdate
        let S_good : Set (E d) :=
          {head | head ∈ Ev_k ∧ GoodUpdate C (scale d k) sk.v bk head}
        have hS_good_meas : MeasurableSet S_good := by
          -- Express GoodUpdate via update_identities as continuous functions of head
          have hhr : ∀ (head : E d) (i : Fin n),
              0 < weights C (scale d k) sk.v head i ∧ weights C (scale d k) sk.v head i ≤ 1 :=
            fun _ _ => ⟨q_pos _, q_le_one _⟩
          let X₁ : E d → ℝ := fun head =>
            inner ℝ bk (act (weightedMatrix sk.v (weights C (scale d k) sk.v head)) bk)
          let X₂ : E d → ℝ := fun head =>
            ∑ i, (1 - weights C (scale d k) sk.v head i) * |inner ℝ bk (sk.v i)|
          have hgood_iff : ∀ head : E d, GoodUpdate C (scale d k) sk.v bk head ↔
              X₁ head ≤ (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖bk‖ * μk ∧
              X₂ head ≤ 4 * support sk.v bk / (C * scale d k) + 4 * μk := by
            intro head
            obtain ⟨hid1, hid2⟩ :=
              update_identities d n sk.v hspan_k (weights C (scale d k) sk.v head) (hhr head) bk
            unfold GoodUpdate
            dsimp only [X₁, X₂, μk]
            rw [← hid1, ← hid2]
          have hr_head_cont : ∀ i : Fin n,
              Continuous (fun head : E d => weights C (scale d k) sk.v head i) := by
            intro i
            by_cases hvi : sk.v i = 0
            · have : (fun head : E d => weights C (scale d k) sk.v head i) = fun _ => q 0 := by
                ext head; simp [weights, projections, hvi]
              rw [this]; exact continuous_const
            · unfold weights projections
              refine q_continuous.comp ((continuous_id.inner continuous_const).div_const _)
          have hX₁_cont : Continuous X₁ := by
            have : X₁ = fun head =>
                ∑ i, (weights C (scale d k) sk.v head i / ‖sk.v i‖) * (inner ℝ bk (sk.v i)) ^ 2 :=
              funext (fun head => inner_weightedMatrix sk.v _ bk)
            rw [this]
            exact continuous_finsetSum Finset.univ (fun i _ =>
              ((hr_head_cont i).div_const _).mul continuous_const)
          have hX₂_cont : Continuous X₂ :=
            continuous_finsetSum Finset.univ (fun i _ =>
              (continuous_const.sub (hr_head_cont i)).mul continuous_const)
          have hS_eq : S_good = Ev_k ∩
              ({head | X₁ head ≤
                  (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖bk‖ * μk} ∩
               {head | X₂ head ≤ 4 * support sk.v bk / (C * scale d k) + 4 * μk}) := by
            ext head
            change (head ∈ Ev_k ∧ GoodUpdate C (scale d k) sk.v bk head) ↔
              (head ∈ Ev_k ∧
                (X₁ head ≤ (8 * C ^ 2 * (scale d k) ^ 2 / Real.sqrt (Real.log d)) * ‖bk‖ * μk ∧
                 X₂ head ≤ 4 * support sk.v bk / (C * scale d k) + 4 * μk))
            rw [hgood_iff head]
          rw [hS_eq]
          exact hEv_meas.inter
            ((measurableSet_le hX₁_cont.measurable measurable_const).inter
             (measurableSet_le hX₂_cont.measurable measurable_const))
        -- Bound stdGaussian S_good ≥ ENNReal.ofReal (p_step k)
        have hS_good_lb : ENNReal.ofReal (p_step k) ≤ stdGaussian (E d) S_good := by
          have hunion : Ev_k ⊆ S_good ∪ {z | z ∈ Ev_k ∧ ¬ GoodUpdate C (scale d k) sk.v bk z} := by
            intro head hhead
            by_cases hg : GoodUpdate C (scale d k) sk.v bk head
            · exact Or.inl ⟨hhead, hg⟩
            · exact Or.inr ⟨hhead, hg⟩
          have hle_add := le_trans (measure_mono (μ := stdGaussian (E d)) hunion)
            (measure_union_le _ _)
          have hle_half : stdGaussian (E d) Ev_k ≤
              stdGaussian (E d) S_good + stdGaussian (E d) Ev_k / 2 := by
            calc
              stdGaussian (E d) Ev_k
                ≤ stdGaussian (E d) S_good +
                    stdGaussian (E d) {z | z ∈ Ev_k ∧ ¬ GoodUpdate C (scale d k) sk.v bk z} :=
                  hle_add
              _ ≤ stdGaussian (E d) S_good + stdGaussian (E d) Ev_k / 2 := by gcongr
          have hS_lt_top : stdGaussian (E d) S_good < ⊤ := measure_lt_top _ _
          set r_Ev := (stdGaussian (E d) Ev_k).toReal
          have hr_Ev_eq : stdGaussian (E d) Ev_k = ENNReal.ofReal r_Ev :=
            (ENNReal.ofReal_toReal (ne_of_lt hPE_lt_top)).symm
          have hdiv2_eq : stdGaussian (E d) Ev_k / 2 = ENNReal.ofReal (r_Ev / 2) := by
            rw [hr_Ev_eq]
            have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
            rw [htwo, ← ENNReal.ofReal_div_of_pos (by norm_num)]
          have hreal : r_Ev / 2 ≤ (stdGaussian (E d) S_good).toReal := by
            have h1 : ENNReal.ofReal r_Ev ≤
                ENNReal.ofReal ((stdGaussian (E d) S_good).toReal + r_Ev / 2) := by
              rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
                (div_nonneg ENNReal.toReal_nonneg (by norm_num)),
                ← hr_Ev_eq, ENNReal.ofReal_toReal (ne_of_lt hS_lt_top), ← hdiv2_eq]
              exact hle_half
            have h2 := (ENNReal.ofReal_le_ofReal_iff
              (add_nonneg ENNReal.toReal_nonneg
                (div_nonneg ENNReal.toReal_nonneg (by norm_num)))).mp h1
            linarith
          have hhalf_enn : stdGaussian (E d) Ev_k / 2 ≤ stdGaussian (E d) S_good := by
            rw [hdiv2_eq, ← ENNReal.ofReal_toReal (ne_of_lt hS_lt_top)]
            exact ENNReal.ofReal_le_ofReal hreal
          have hp_le_half : ENNReal.ofReal (p_step k) ≤ stdGaussian (E d) Ev_k / 2 := by
            have hexp_pos : 0 < c₀ * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2)) := by
              positivity
            by_cases hc1 : 1 ≤ (c₀ / 2) * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2))
            · -- Notice stdGaussian Ev_k ≤ 1, so c₀ * exp(...) ≤ 1, impossible since c₀/2 * exp ≥ 1!
              have hPE_le1 : stdGaussian (E d) Ev_k ≤ 1 := prob_le_one
              have hle1 := le_trans hPE_lb hPE_le1
              rw [ENNReal.ofReal_le_one] at hle1
              linarith
            · have hp_eq : p_step k =
                  (c₀ * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2))) / 2 := by
                dsimp [p_step]
                rw [min_eq_right (le_of_lt (not_le.mp hc1))]; ring
              rw [hp_eq, ENNReal.ofReal_div_of_pos (by norm_num)]
              have htwo : ENNReal.ofReal 2 = (2 : ENNReal) := by norm_num
              rw [htwo]
              exact ENNReal.div_le_div_right hPE_lb 2
          exact le_trans hp_le_half hhalf_enn
        -- For every head ∈ S_good, apply IH(m) to snocPref head
        let c_tail : ℝ := qstar * ∏ i ∈ Finset.Ico (k + 1) (rounds d), p_step i
        have hc_tail_nn : 0 ≤ c_tail :=
          mul_nonneg (le_of_lt hqstar_pos) (Finset.prod_nonneg fun i _ => le_of_lt (hp_pos i))
        have hfib : ∀ head ∈ S_good,
            ENNReal.ofReal c_tail ≤
              (Measure.pi fun _ : Fin m => stdGaussian (E d)) (Prod.mk head ⁻¹' U_prod) := by
          intro head ⟨_, hgood_head⟩
          apply (ih (k + 1) hkm' (snocPref head)).2
          intro j hj
          set z₁ := glue hkm' (snocPref head) (fun _ => 0)
          have hz₁_pref : ∀ r (hr : r < k) (hrR : r < rounds d),
              z₁ ⟨r, hrR⟩ = z₀ ⟨r, hrR⟩ := by
            intro r hr hrR
            have hr1 : r < k + 1 := by omega
            simp [z₁, z₀, glue, snocPref, hr, hr1]
          have hz₁_k : z₁ ⟨k, hkR⟩ = head := by
            have hk1 : k < k + 1 := by omega
            simp [z₁, glue, snocPref, hk1]
          by_cases hjk : j < k
          · have hst : runState C w T z₁ j = runState C w T z₀ j :=
              runState_congr_prefix hz₁_pref j (Nat.le_of_lt hjk)
            have hzj := hz₁_pref j hjk (by omega)
            rw [hst, hzj]
            exact hall j hjk
          · have hjeq : j = k := by omega
            subst j
            have hst : runState C w T z₁ k = runState C w T z₀ k :=
              runState_congr_prefix hz₁_pref k le_rfl
            rw [hst, hz₁_k]
            exact ⟨hsm_k, hgood_head⟩
        have hprod := prod_measure_ge (stdGaussian (E d))
          (Measure.pi fun _ : Fin m => stdGaussian (E d)) hS_good_meas hfib
        calc
          ENNReal.ofReal (qstar * ∏ i ∈ Finset.Ico k (rounds d), p_step i)
            = ENNReal.ofReal (p_step k * c_tail) := by
                dsimp [c_tail]; rw [hIco_split]; ring_nf
          _ = ENNReal.ofReal (p_step k) * ENNReal.ofReal c_tail :=
                ENNReal.ofReal_mul (le_of_lt (hp_pos k))
          _ ≤ stdGaussian (E d) S_good * ENNReal.ofReal c_tail := by gcongr
          _ ≤ ((stdGaussian (E d)).prod (Measure.pi fun _ : Fin m => stdGaussian (E d))) U_prod :=
                hprod
      · -- Large-mean at round k: reverse Markov on Ev_k gives Hit at round k!
        have hlg_k : η * Real.sqrt (Real.log d / d) ≤ μk := not_lt.mp hsm_k
        have hqstar_le_half : qstar ≤ μk / 2 := by
          dsimp [qstar]; linarith
        let S_hit : Set (E d) :=
          {head | head ∈ Ev_k ∧ qstar ≤ inner ℝ bk (localPoint C (scale d k) sk.v head)}
        have hloc_head_cont : Continuous (fun head : E d =>
            inner ℝ bk (localPoint C (scale d k) sk.v head)) := by
          unfold localPoint
          refine continuous_const.inner (continuous_finsetSum Finset.univ fun i _ => ?_)
          by_cases hvi : sk.v i = 0
          · have : (fun head : E d =>
                (projections C (scale d k) sk.v head i *
                  weights C (scale d k) sk.v head i) • sk.v i) = fun _ => 0 := by
              ext head; simp [hvi]
            rw [this]; exact continuous_const
          · have hproj : Continuous (fun head : E d => projections C (scale d k) sk.v head i) := by
              unfold projections
              exact (continuous_id.inner continuous_const).div_const _
            exact (hproj.mul (q_continuous.comp hproj)).smul continuous_const
        have hS_hit_meas : MeasurableSet S_hit :=
          hEv_meas.inter (measurableSet_le measurable_const hloc_head_cont.measurable)
        -- Reverse Markov: inner ℝ bk (localPoint ... head) ≤ 1 everywhere!
        have hloc_le1 : ∀ head : E d,
            inner ℝ bk (localPoint C (scale d k) sk.v head) ≤ 1 := by
          intro head
          -- Build a tape agreeing with z₀ before k and equal to head at k
          let z_head := glue hkm' (snocPref head) (fun _ => 0)
          have hz_pref : ∀ r (hr : r < k) (hrR : r < rounds d),
              z_head ⟨r, hrR⟩ = z₀ ⟨r, hrR⟩ := by
            intro r hr hrR
            have hr1 : r < k + 1 := by omega
            simp [z_head, z₀, glue, snocPref, hr, hr1]
          have hz_k : z_head ⟨k, hkR⟩ = head := by
            have hk1 : k < k + 1 := by omega
            simp [z_head, glue, snocPref, hk1]
          have hst : runState C w T z_head k = runState C w T z₀ k :=
            runState_congr_prefix hz_pref k le_rfl
          have hrec_mem : recorded C w T z_head ⟨k, hkR⟩ ∈ zonotope w :=
            ((feasibility d n hd C hC w T hT z_head).2.2 ⟨k, hkR⟩).2.2.2
          have hrec_eq : inner ℝ a (recorded C w T z_head ⟨k, hkR⟩) =
              inner ℝ bk (localPoint C (scale d k) sk.v head) := by
            unfold recorded
            dsimp only
            rw [hst, hz_k, inner_act_transpose]
          rw [← hrec_eq]
          exact ha_supp ▸ inner_le_support hrec_mem a
        have hloc_abs_le1 : ∀ head : E d,
            |inner ℝ bk (localPoint C (scale d k) sk.v head)| ≤ 1 := by
          intro head
          rw [abs_le]
          refine ⟨?_, hloc_le1 head⟩
          -- By symmetry localPoint ... (-head) = - localPoint ... head
          have hneg_eq : inner ℝ bk (localPoint C (scale d k) sk.v (-head)) =
              - inner ℝ bk (localPoint C (scale d k) sk.v head) := by
            unfold localPoint
            rw [inner_sum, inner_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_smul_right, real_inner_smul_right]
            have hp_neg : projections C (scale d k) sk.v (-head) i =
                - projections C (scale d k) sk.v head i := by
              unfold projections; rw [inner_neg_left, neg_div]
            have hw_neg : weights C (scale d k) sk.v (-head) i =
                weights C (scale d k) sk.v head i := by
              unfold weights; rw [hp_neg]; unfold q; rw [abs_neg]
            rw [hp_neg, hw_neg]; ring
          linarith [hloc_le1 (-head)]
        have hloc_int : IntegrableOn
            (fun head : E d => inner ℝ bk (localPoint C (scale d k) sk.v head))
            Ev_k (stdGaussian (E d)) := by
          refine (Integrable.of_bound hloc_head_cont.aestronglyMeasurable 1
            (ae_of_all _ fun head => ?_)).integrableOn
          rw [Real.norm_eq_abs]
          exact hloc_abs_le1 head
        have hpwise_rm : ∀ head ∈ Ev_k,
            inner ℝ bk (localPoint C (scale d k) sk.v head) ≤
              μk / 2 + S_hit.indicator (fun _ => (1 : ℝ)) head := by
          intro head hhead
          by_cases hmem : head ∈ S_hit
          · rw [indicator_of_mem hmem]
            linarith [hloc_le1 head]
          · rw [indicator_of_notMem hmem]
            have hlt : inner ℝ bk (localPoint C (scale d k) sk.v head) < qstar := by
              by_contra hge
              exact hmem ⟨hhead, not_lt.mp hge⟩
            linarith
        have hind_int : IntegrableOn (S_hit.indicator (fun _ : E d => (1 : ℝ)))
            Ev_k (stdGaussian (E d)) :=
          ((integrable_indicator_iff hS_hit_meas).mpr (integrable_const (1 : ℝ))).integrableOn
        have hconst_int : IntegrableOn (fun _ : E d => μk / 2) Ev_k (stdGaussian (E d)) :=
          integrable_const _
        have hrhs_int : IntegrableOn
            (fun head : E d => μk / 2 + S_hit.indicator (fun _ : E d => (1 : ℝ)) head)
            Ev_k (stdGaussian (E d)) := hconst_int.add hind_int
        have hrm_mono := setIntegral_mono_on hloc_int hrhs_int hEv_meas hpwise_rm
        rw [integral_add hconst_int hind_int, setIntegral_const, smul_eq_mul, Measure.real] at hrm_mono
        have hind_eval : (∫ head in Ev_k, S_hit.indicator (fun _ => (1 : ℝ)) head
            ∂stdGaussian (E d)) = (stdGaussian (E d) S_hit).toReal := by
          have hsub : S_hit ⊆ Ev_k := fun _ h => h.1
          rw [setIntegral_indicator hS_hit_meas, inter_eq_right.mpr hsub,
            setIntegral_const, smul_eq_mul, mul_one, Measure.real]
        rw [hind_eval] at hrm_mono
        have hPE_pos_enn : 0 < stdGaussian (E d) Ev_k :=
          lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hPE_lb
        have hPE_pos : 0 < (stdGaussian (E d) Ev_k).toReal :=
          ENNReal.toReal_pos (ne_of_gt hPE_pos_enn) (ne_of_lt hPE_lt_top)
        have hμ_int : (∫ head in Ev_k, inner ℝ bk (localPoint C (scale d k) sk.v head)
            ∂stdGaussian (E d)) = (stdGaussian (E d) Ev_k).toReal * μk := by
          have : μk = (stdGaussian (E d) Ev_k).toReal⁻¹ *
              ∫ head in Ev_k, inner ℝ bk (localPoint C (scale d k) sk.v head)
              ∂stdGaussian (E d) := rfl
          rw [this, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hPE_pos), one_mul]
        rw [hμ_int] at hrm_mono
        have hShit_real : qstar * (stdGaussian (E d) Ev_k).toReal ≤
            (stdGaussian (E d) S_hit).toReal := by
          have h1 : (μk / 2) * (stdGaussian (E d) Ev_k).toReal ≤
              (stdGaussian (E d) S_hit).toReal := by linarith
          have h2 : qstar * (stdGaussian (E d) Ev_k).toReal ≤
              (μk / 2) * (stdGaussian (E d) Ev_k).toReal :=
            mul_le_mul_of_nonneg_right hqstar_le_half (le_of_lt hPE_pos)
          exact le_trans h2 h1
        have hShit_lb : ENNReal.ofReal (qstar * p_step k) ≤ stdGaussian (E d) S_hit := by
          have hp_le_PE : p_step k ≤ (stdGaussian (E d) Ev_k).toReal := by
            have hPE_le1 : stdGaussian (E d) Ev_k ≤ 1 := prob_le_one
            have hle1 := le_trans hPE_lb hPE_le1
            rw [ENNReal.ofReal_le_one] at hle1
            have hc_lt1 : (c₀ / 2) * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2)) < 1 := by
              have : 0 < c₀ * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2)) := by positivity
              linarith
            have hp_eq : p_step k =
                (c₀ / 2) * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2)) :=
              min_eq_right (le_of_lt hc_lt1)
            have hPE_real : c₀ * Real.exp (-Real.log d / (C ^ 2 * (scale d k) ^ 2)) ≤
                (stdGaussian (E d) Ev_k).toReal := by
              have := ENNReal.toReal_mono (ne_of_lt hPE_lt_top) hPE_lb
              rwa [ENNReal.toReal_ofReal (by positivity)] at this
            rw [hp_eq]
            linarith
          have hShit_lt_top : stdGaussian (E d) S_hit < ⊤ := measure_lt_top _ _
          rw [← ENNReal.ofReal_toReal (ne_of_lt hShit_lt_top)]
          exact ENNReal.ofReal_le_ofReal
            (le_trans (mul_le_mul_of_nonneg_left hp_le_PE (le_of_lt hqstar_pos)) hShit_real)
        -- For every head ∈ S_hit, snocPref head already hits at round k!
        have hfib_hit : ∀ head ∈ S_hit,
            (1 : ENNReal) ≤
              (Measure.pi fun _ : Fin m => stdGaussian (E d)) (Prod.mk head ⁻¹' U_prod) := by
          intro head ⟨_, hhit_head⟩
          let z₁ := glue hkm' (snocPref head) (fun _ => 0)
          have hz₁_pref : ∀ r (hr : r < k) (hrR : r < rounds d),
              z₁ ⟨r, hrR⟩ = z₀ ⟨r, hrR⟩ := by
            intro r hr hrR
            have hr1 : r < k + 1 := by omega
            simp [z₁, z₀, glue, snocPref, hr, hr1]
          have hz₁_k : z₁ ⟨k, hkR⟩ = head := by
            have hk1 : k < k + 1 := by omega
            simp [z₁, glue, snocPref, hk1]
          apply (ih (k + 1) hkm' (snocPref head)).1
          refine ⟨⟨k, hkR⟩, Nat.lt_succ_self k, ?_⟩
          change qstar ≤ inner ℝ a (recorded C w T z₁ ⟨k, hkR⟩)
          unfold recorded
          dsimp only
          rw [runState_congr_prefix hz₁_pref k le_rfl, hz₁_k, inner_act_transpose]
          exact hhit_head
        have hprod := prod_measure_ge (stdGaussian (E d))
          (Measure.pi fun _ : Fin m => stdGaussian (E d)) hS_hit_meas hfib_hit
        rw [mul_one] at hprod
        have htail_le1 : ∏ i ∈ Finset.Ico (k + 1) (rounds d), p_step i ≤ 1 :=
          Finset.prod_le_one (fun i _ => le_of_lt (hp_pos i)) (fun i _ => hp_le1 i)
        have hfull_le : qstar * ∏ i ∈ Finset.Ico k (rounds d), p_step i ≤ qstar * p_step k := by
          rw [hIco_split]
          calc
            qstar * (p_step k * ∏ i ∈ Finset.Ico (k + 1) (rounds d), p_step i)
              = (qstar * p_step k) * ∏ i ∈ Finset.Ico (k + 1) (rounds d), p_step i := by ring
            _ ≤ (qstar * p_step k) * 1 :=
              mul_le_mul_of_nonneg_left htail_le1 (mul_nonneg (le_of_lt hqstar_pos) (le_of_lt (hp_pos k)))
            _ = qstar * p_step k := mul_one _
        exact le_trans (ENNReal.ofReal_le_ofReal hfull_le) (le_trans hShit_lb hprod)

end Prop21Aux

-- ============================================================================
-- Top-Level Solution: Proposition 2.1
-- ============================================================================

theorem solution (C : ℝ) (hC : 64 ≤ C) : ∃ c : ℝ, 0 < c ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ (w : Fin n → E d) (T : Mat d), ApproxLewis w T →
    (rounds d : ℝ) ≤ 1 + Real.logb 2 (Real.log d) ∧
    (∀ (z : Tape d) (j : Fin (rounds d)), recorded C w T z j ∈ zonotope w) ∧
    ∀ a : E d,
    (runLaw d {z | ∀ j : Fin (rounds d),
      inner ℝ a (recorded C w T z j) < c * Real.sqrt (Real.log d / d) * support w a}) ≤
      1 - ENNReal.ofReal (c / (d * (Real.log d) ^ 4)) := by
  obtain ⟨c₀, hc₀, h24⟩ := lemma_2_4
  let η : ℝ := min (1 / 384) (1 / (128 * 256 * C ^ 2))
  have hη_pos : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 384 := min_le_left _ _
  have hη2 : 128 * C ^ 2 * η ≤ 1 / 256 := by
    have hle : η ≤ 1 / (128 * 256 * C ^ 2) := min_le_right _ _
    have hC_ne : C ≠ 0 := by linarith
    calc
      128 * C ^ 2 * η ≤ 128 * C ^ 2 * (1 / (128 * 256 * C ^ 2)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 / 256 := by field_simp [hC_ne]
  let c₁ : ℝ := min (c₀ / 2) (1 / 2)
  have hc₁_pos : 0 < c₁ := lt_min (by positivity) (by norm_num)
  have hc₁_le_half : c₁ ≤ 1 / 2 := min_le_right _ _
  have hc₁_lt1 : c₁ < 1 := by linarith
  let D : ℝ := Real.log (1 / c₁) / Real.log 2
  have hD_pos : 0 < D := by
    dsimp [D]
    apply div_pos
    · apply Real.log_pos
      rw [one_div]
      exact (one_lt_inv₀ hc₁_pos).mpr hc₁_lt1
    · exact Real.log_pos (by norm_num)
  let M_deg : ℝ := 4 * (D + 4)
  have hM_deg_pos : 0 < M_deg := by dsimp [M_deg]; positivity
  let c : ℝ := min (η / 2) ((η / 2) * c₁ * (M_deg ^ (D + 4))⁻¹)
  have hc_pos : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc_pos, ?_⟩
  intro d n hd w T hT
  refine ⟨Prop21Aux.rounds_le_logb hd,
    fun z j => ((feasibility d n hd C hC w T hT z).2.2 j).2.2.2, ?_⟩
  intro a
  by_cases ha0 : a = 0
  · subst ha0
    have hR1 : 1 ≤ rounds d := Prop21Aux.rounds_pos hd
    let j₀ : Fin (rounds d) := ⟨0, hR1⟩
    have hempty : {z : Tape d | ∀ j : Fin (rounds d),
        inner ℝ (0 : E d) (recorded C w T z j) <
          c * Real.sqrt (Real.log d / d) * support w (0 : E d)} = ∅ := by
      ext z
      simp only [mem_empty_iff_false, iff_false]
      intro hall
      have h0 := hall j₀
      simp [Prop21Aux.support_eq_sum_abs] at h0
    rw [hempty, measure_empty]
    exact zero_le
  -- Nonzero direction a ≠ 0: show support w a > 0 and normalize a' = (support w a)⁻¹ • a
  have hT_det : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT.1
  have hsupp_pos : 0 < support w a := by
    let z_dummy : Tape d := fun _ => 0
    obtain ⟨h0_feas, _, _⟩ := feasibility d n hd C hC w T hT z_dummy
    obtain ⟨_, hlow_23⟩ := lemma_2_3 d n hd C hC w T hT z_dummy
    set b₀ : E d := act (runState C w T z_dummy 0).A.transpose a
    have hb₀_ne : b₀ ≠ 0 := by
      intro hb0
      have hA0_unit : IsUnit (runState C w T z_dummy 0).A.transpose.det := by
        rw [Matrix.det_transpose]
        exact (Prop21Aux.continuous_runState hd hC w T hT 0 (Nat.zero_le _)).2.2 z_dummy
      have hinv := Matrix.nonsing_inv_mul (runState C w T z_dummy 0).A.transpose hA0_unit
      apply ha0
      calc
        a = act ((runState C w T z_dummy 0).A.transpose⁻¹ *
              (runState C w T z_dummy 0).A.transpose) a := by rw [hinv, Prop21Aux.act_one]
        _ = act (runState C w T z_dummy 0).A.transpose⁻¹ b₀ := Prop21Aux.act_mul _ _ _
        _ = 0 := by rw [hb0]; simp [act]
    have hH0_eq : support (runState C w T z_dummy 0).v b₀ = support w a := by
      rw [Prop21Aux.support_eq_sum_abs, Prop21Aux.support_eq_sum_abs]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Prop21Aux.inner_act_transpose, h0_feas i]
    have hlow := hlow_23 b₀
    rw [hH0_eq] at hlow
    exact lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hb₀_ne) (by norm_num)) hlow
  let a' : E d := (support w a)⁻¹ • a
  have ha'_supp : support w a' = 1 := by
    rw [Prop21Aux.support_eq_sum_abs]
    have h1 : ∑ i, |inner ℝ a' (w i)| = (support w a)⁻¹ * ∑ i, |inner ℝ a (w i)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp [a']
      rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hsupp_pos)]
    rw [h1, ← Prop21Aux.support_eq_sum_abs, inv_mul_cancel₀ (ne_of_gt hsupp_pos)]
  -- Apply tail_prob_lb at m = rounds d, k = 0
  set R := rounds d
  set qstar := (η / 2) * Real.sqrt (Real.log d / d)
  let p_step : ℕ → ℝ := fun j =>
    min 1 ((c₀ / 2) * Real.exp (-Real.log d / (C ^ 2 * (scale d j) ^ 2)))
  let HitTape : Set (Tape d) :=
    {z | ∃ j : Fin R, qstar ≤ inner ℝ a' (recorded C w T z j)}
  have h0m : 0 + R = R := Nat.zero_add R
  have hlb_tail := (Prop21Aux.tail_prob_lb hd hC hc₀ (fun C' lam hC' hlam v hv b hb =>
    h24 d n hd C' lam hC' hlam v hv b hb) hη_pos hη1 hη2 w T hT a' ha'_supp R 0 h0m Fin.elim0).2
    (fun j hj => by omega)
  have hglue_id : ∀ z : Tape d, Prop21Aux.glue h0m Fin.elim0 z = z := by
    intro z; ext j
    simp [Prop21Aux.glue]
  have hHit_eq : {tail : Tape d | Prop21Aux.glue h0m Fin.elim0 tail ∈ HitTape} = HitTape := by
    ext z; simp [hglue_id]
  rw [hHit_eq] at hlb_tail
  -- Bound qstar * ∏ p_step i ≥ c / (d * (Real.log d) ^ 4)
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog1 : 1 < Real.log d := Prop21Aux.log_d_gt_one hd
  have hlog_pos : 0 < Real.log d := lt_trans zero_lt_one hlog1
  have hp_ge_c1 : ∀ i ∈ Finset.Ico 0 R,
      c₁ * Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2)) ≤ p_step i := by
    intro i _
    dsimp [p_step]
    have hexp_le1 : Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hden_nn : 0 ≤ C ^ 2 * (scale d i) ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden_nn
    have hexp_pos : 0 < Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2)) := Real.exp_pos _
    apply le_min
    · calc
        c₁ * Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2)) ≤ (1 / 2) * 1 :=
          mul_le_mul hc₁_le_half hexp_le1 (le_of_lt hexp_pos) (by norm_num)
        _ ≤ 1 := by norm_num
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hexp_pos)
  have hprod_lb : c₁ ^ R * Real.exp (- (Real.log d / C ^ 2) *
      ∑ i ∈ Finset.range R, (1 / (scale d i) ^ 2)) ≤
      ∏ i ∈ Finset.Ico 0 R, p_step i := by
    have hIco : Finset.Ico 0 R = Finset.range R := Nat.Ico_zero_eq_range R
    rw [hIco]
    calc
      c₁ ^ R * Real.exp (- (Real.log d / C ^ 2) *
          ∑ i ∈ Finset.range R, (1 / (scale d i) ^ 2))
        = (∏ _i ∈ Finset.range R, c₁) *
            ∏ i ∈ Finset.range R, Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2)) := by
          rw [Finset.prod_const, Finset.card_range, ← Real.exp_sum, Finset.mul_sum]
          congr 2
          refine Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∏ i ∈ Finset.range R,
            (c₁ * Real.exp (-Real.log d / (C ^ 2 * (scale d i) ^ 2))) :=
          Finset.prod_mul_distrib.symm
      _ ≤ ∏ i ∈ Finset.range R, p_step i :=
          Finset.prod_le_prod
            (fun i _ => by positivity)
            (fun i hi => hp_ge_c1 i (hIco.symm ▸ hi))
  -- Lower bound c₁ ^ R ≥ c₁ * (Real.log d) ^ (-D)
  have hc1R_lb : c₁ * (Real.log d) ^ (-D) ≤ c₁ ^ R := by
    have hR_le := Prop21Aux.rounds_le_logb hd
    rw [← Real.rpow_natCast c₁ R]
    have hrpow_le : c₁ ^ (1 + Real.logb 2 (Real.log d)) ≤ c₁ ^ (R : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hc₁_pos (le_of_lt hc₁_lt1) hR_le
    have hc1_eq : c₁ = (2 : ℝ) ^ (-D) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlog_eq : Real.log 2 * (-D) = Real.log c₁ := by
        dsimp [D]
        have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
        rw [one_div, Real.log_inv]
        field_simp [hlog2_ne]
      rw [hlog_eq, Real.exp_log hc₁_pos]
    have hlogb_pow : c₁ ^ (Real.logb 2 (Real.log d)) = (Real.log d) ^ (-D) := by
      conv_lhs => rw [hc1_eq]
      rw [← Real.rpow_mul (by norm_num), mul_comm (-D), Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hlog_pos]
    have hsplit : c₁ ^ (1 + Real.logb 2 (Real.log d)) = c₁ * (Real.log d) ^ (-D) := by
      rw [Real.rpow_add hc₁_pos, Real.rpow_one, hlogb_pow]
    linarith
  -- Lower bound exp factor ≥ d ^ (-1/4)
  have hexp_lb : (d : ℝ) ^ (- (1 / 4 : ℝ)) ≤
      Real.exp (- (Real.log d / C ^ 2) * ∑ i ∈ Finset.range R, (1 / (scale d i) ^ 2)) := by
    rw [Real.rpow_def_of_pos hd_pos]
    apply Real.exp_le_exp.mpr
    have hsum2 := Prop21Aux.sum_inv_scale_sq_le_two hd
    have hC2 : (4096 : ℝ) ≤ C ^ 2 := by nlinarith
    have h1 : (Real.log d / C ^ 2) * ∑ i ∈ Finset.range R, (1 / (scale d i) ^ 2) ≤
        (Real.log d / 4096) * 2 := by
      have ha : Real.log d / C ^ 2 ≤ Real.log d / 4096 :=
        div_le_div_of_nonneg_left (le_of_lt hlog_pos) (by norm_num) hC2
      exact mul_le_mul ha hsum2
        (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    linarith
  -- Lower bound sqrt(log d / d) ≥ d ^ (-1/2)
  have hsqrt_lb : (d : ℝ) ^ (- (1 / 2 : ℝ)) ≤ Real.sqrt (Real.log d / d) := by
    have h1 : 1 / (d : ℝ) ≤ Real.log d / d :=
      div_le_div_of_nonneg_right (le_of_lt hlog1) (le_of_lt hd_pos)
    calc
      (d : ℝ) ^ (- (1 / 2 : ℝ))
        = ((d : ℝ) ^ ((1 / 2 : ℝ)))⁻¹ := Real.rpow_neg (le_of_lt hd_pos) (1 / 2)
      _ = (Real.sqrt d)⁻¹ := by rw [← Real.sqrt_eq_rpow]
      _ = Real.sqrt (1 / d) := by rw [one_div, Real.sqrt_inv]
      _ ≤ Real.sqrt (Real.log d / d) := Real.sqrt_le_sqrt h1
  -- Polynomial vs polylogarithmic domination: (log d) ^ (D + 4) ≤ M_deg ^ (D + 4) * d ^ (1/4)
  have hpoly_dom : (M_deg ^ (D + 4))⁻¹ / ((d : ℝ) * (Real.log d) ^ 4) ≤
      (Real.log d) ^ (-D) * (d : ℝ) ^ (- (1 / 2 : ℝ)) * (d : ℝ) ^ (- (1 / 4 : ℝ)) := by
    let y : ℝ := (d : ℝ) ^ (1 / M_deg)
    have hy_pos : 0 < y := Real.rpow_pos_of_pos hd_pos _
    have hlog_y : Real.log y = (1 / M_deg) * Real.log d := Real.log_rpow hd_pos _
    have hy_le : Real.log y ≤ y := by linarith [Real.log_le_sub_one_of_pos hy_pos]
    have hlog_le_My : Real.log d ≤ M_deg * y := by
      have hmul := mul_le_mul_of_nonneg_left hy_le (le_of_lt hM_deg_pos)
      rw [hlog_y] at hmul
      have hrew : M_deg * ((1 / M_deg) * Real.log d) = Real.log d := by
        field_simp [ne_of_gt hM_deg_pos]
      linarith
    have hpow_D4 : (Real.log d) ^ (D + 4) ≤ M_deg ^ (D + 4) * (d : ℝ) ^ ((1 / 4 : ℝ)) := by
      have h1 := Real.rpow_le_rpow (le_of_lt hlog_pos) hlog_le_My (by linarith : 0 ≤ D + 4)
      rw [Real.mul_rpow (le_of_lt hM_deg_pos) (le_of_lt hy_pos)] at h1
      have hy_pow : y ^ (D + 4) = (d : ℝ) ^ ((1 / 4 : ℝ)) := by
        dsimp [y]
        rw [← Real.rpow_mul (le_of_lt hd_pos)]
        congr 1
        dsimp [M_deg]
        have hD4_ne : D + 4 ≠ 0 := by linarith
        field_simp [hD4_ne]
      rwa [hy_pow] at h1
    have hd_comb : (d : ℝ) ^ (- (1 / 2 : ℝ)) * (d : ℝ) ^ (- (1 / 4 : ℝ)) =
        (d : ℝ) ^ ((1 / 4 : ℝ)) / d := by
      rw [← Real.rpow_add hd_pos]
      have hsub : (- (1 / 2 : ℝ) + - (1 / 4 : ℝ)) = (1 / 4 : ℝ) - 1 := by ring
      rw [hsub, Real.rpow_sub hd_pos, Real.rpow_one]
    have hlog_comb : (Real.log d) ^ (D + 4) = (Real.log d) ^ D * (Real.log d) ^ 4 := by
      rw [Real.rpow_add hlog_pos, Real.rpow_ofNat]
    rw [mul_assoc, hd_comb, Real.rpow_neg (le_of_lt hlog_pos) D]
    have hpow_D : (Real.log d) ^ D * (Real.log d) ^ 4 ≤
        M_deg ^ (D + 4) * (d : ℝ) ^ ((1 / 4 : ℝ)) := hlog_comb ▸ hpow_D4
    have hlogD_pos : 0 < (Real.log d) ^ D := Real.rpow_pos_of_pos hlog_pos D
    have hMpow_pos : 0 < M_deg ^ (D + 4) := Real.rpow_pos_of_pos hM_deg_pos _
    have hlog4_ge1 : 1 ≤ (Real.log d) ^ 4 := one_le_pow₀ (le_of_lt hlog1)
    have hpow_D_only : (Real.log d) ^ D ≤ M_deg ^ (D + 4) * (d : ℝ) ^ ((1 / 4 : ℝ)) := by
      calc
        (Real.log d) ^ D = (Real.log d) ^ D * 1 := (mul_one _).symm
        _ ≤ (Real.log d) ^ D * (Real.log d) ^ 4 :=
            mul_le_mul_of_nonneg_left hlog4_ge1 (le_of_lt hlogD_pos)
        _ ≤ M_deg ^ (D + 4) * (d : ℝ) ^ ((1 / 4 : ℝ)) := hpow_D
    have h1 : (M_deg ^ (D + 4))⁻¹ ≤ ((Real.log d) ^ D)⁻¹ * (d : ℝ) ^ ((1 / 4 : ℝ)) := by
      have hlogD_ne : (Real.log d) ^ D ≠ 0 := ne_of_gt hlogD_pos
      have hM_ne : M_deg ^ (D + 4) ≠ 0 := ne_of_gt hMpow_pos
      rw [inv_le_iff_one_le_mul₀ hMpow_pos]
      have hdiv2 := (one_le_div hlogD_pos).mpr hpow_D_only
      calc
        (1 : ℝ) ≤ (M_deg ^ (D + 4) * (d : ℝ) ^ ((1 / 4 : ℝ))) / (Real.log d) ^ D := hdiv2
        _ = (((Real.log d) ^ D)⁻¹ * (d : ℝ) ^ ((1 / 4 : ℝ))) * M_deg ^ (D + 4) := by
            field_simp [hlogD_ne, hM_ne]
    have hd_le_dlog4 : (d : ℝ) ≤ (d : ℝ) * (Real.log d) ^ 4 := by
      calc
        (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
        _ ≤ (d : ℝ) * (Real.log d) ^ 4 :=
            mul_le_mul_of_nonneg_left hlog4_ge1 (le_of_lt hd_pos)
    calc
      (M_deg ^ (D + 4))⁻¹ / ((d : ℝ) * (Real.log d) ^ 4)
        ≤ (M_deg ^ (D + 4))⁻¹ / (d : ℝ) :=
          div_le_div_of_nonneg_left (inv_nonneg.mpr (le_of_lt hMpow_pos)) hd_pos hd_le_dlog4
      _ ≤ (((Real.log d) ^ D)⁻¹ * (d : ℝ) ^ ((1 / 4 : ℝ))) / (d : ℝ) :=
          div_le_div_of_nonneg_right h1 (le_of_lt hd_pos)
      _ = ((Real.log d) ^ D)⁻¹ * ((d : ℝ) ^ ((1 / 4 : ℝ)) / d) := by ring
  have hfull_prob_lb : c / ((d : ℝ) * (Real.log d) ^ 4) ≤
      qstar * ∏ i ∈ Finset.Ico 0 R, p_step i := by
    have hc_le2 : c ≤ (η / 2) * c₁ * (M_deg ^ (D + 4))⁻¹ := min_le_right _ _
    calc
      c / ((d : ℝ) * (Real.log d) ^ 4)
        ≤ ((η / 2) * c₁ * (M_deg ^ (D + 4))⁻¹) / ((d : ℝ) * (Real.log d) ^ 4) :=
          div_le_div_of_nonneg_right hc_le2 (by positivity)
      _ = (η / 2) * c₁ * ((M_deg ^ (D + 4))⁻¹ / ((d : ℝ) * (Real.log d) ^ 4)) := by ring
      _ ≤ (η / 2) * c₁ *
            ((Real.log d) ^ (-D) * (d : ℝ) ^ (- (1 / 2 : ℝ)) * (d : ℝ) ^ (- (1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hpoly_dom (by positivity)
      _ = (η / 2) * (d : ℝ) ^ (- (1 / 2 : ℝ)) *
            ((c₁ * (Real.log d) ^ (-D)) * (d : ℝ) ^ (- (1 / 4 : ℝ))) := by ring
      _ ≤ (η / 2) * Real.sqrt (Real.log d / d) *
            (c₁ ^ R * Real.exp (- (Real.log d / C ^ 2) *
              ∑ i ∈ Finset.range R, (1 / (scale d i) ^ 2))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hsqrt_lb (by positivity)
          · exact mul_le_mul hc1R_lb hexp_lb (by positivity) (by positivity)
          · positivity
          · positivity
      _ ≤ qstar * ∏ i ∈ Finset.Ico 0 R, p_step i :=
          mul_le_mul_of_nonneg_left hprod_lb (by positivity)
  have hHit_lb : ENNReal.ofReal (c / ((d : ℝ) * (Real.log d) ^ 4)) ≤
      runLaw d HitTape :=
    le_trans (ENNReal.ofReal_le_ofReal hfull_prob_lb) hlb_tail
  -- Relate Failure event to HitTapeᶜ via continuity/measurability of Bad
  let Bad : Set (Tape d) := {z | ∀ j : Fin R,
    inner ℝ a (recorded C w T z j) < c * Real.sqrt (Real.log d / d) * support w a}
  have hBad_meas : MeasurableSet Bad := by
    have : Bad = ⋂ j : Fin R, {z : Tape d |
        inner ℝ a (recorded C w T z j) < c * Real.sqrt (Real.log d / d) * support w a} := by
      ext z; simp [Bad]
    rw [this]
    refine MeasurableSet.iInter (fun j => ?_)
    exact measurableSet_lt
      (continuous_const.inner (Prop21Aux.continuous_recorded hd hC w T hT j)).measurable
      measurable_const
  have hHit_sub_compl : HitTape ⊆ Badᶜ := by
    rintro z ⟨j, hj⟩ hbad
    have hlt := hbad j
    have hc_le1 : c ≤ η / 2 := min_le_left _ _
    have h1 : (η / 2) * Real.sqrt (Real.log d / d) * support w a ≤
        inner ℝ a (recorded C w T z j) := by
      have hm := mul_le_mul_of_nonneg_left hj (le_of_lt hsupp_pos)
      have hrhs : support w a * inner ℝ a' (recorded C w T z j) =
          inner ℝ a (recorded C w T z j) := by
        dsimp [a']
        rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsupp_pos), one_mul]
      rw [hrhs] at hm
      dsimp [qstar] at hm
      linarith
    have h2 : c * Real.sqrt (Real.log d / d) * support w a ≤
        (η / 2) * Real.sqrt (Real.log d / d) * support w a := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hsupp_pos)
      exact mul_le_mul_of_nonneg_right hc_le1 (by positivity)
    linarith
  have hBad_compl_lb : ENNReal.ofReal (c / ((d : ℝ) * (Real.log d) ^ 4)) ≤
      runLaw d Badᶜ := le_trans hHit_lb (measure_mono hHit_sub_compl)
  rw [prob_compl_eq_one_sub hBad_meas] at hBad_compl_lb
  change runLaw d Bad ≤ 1 - ENNReal.ofReal (c / ((d : ℝ) * (Real.log d) ^ 4))
  have hab : runLaw d Bad + ENNReal.ofReal (c / ((d : ℝ) * (Real.log d) ^ 4)) ≤ 1 := by
    calc
      runLaw d Bad + ENNReal.ofReal (c / ((d : ℝ) * (Real.log d) ^ 4))
        ≤ runLaw d Bad + (1 - runLaw d Bad) := by gcongr
      _ = 1 := add_tsub_cancel_of_le prob_le_one
  exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hab
