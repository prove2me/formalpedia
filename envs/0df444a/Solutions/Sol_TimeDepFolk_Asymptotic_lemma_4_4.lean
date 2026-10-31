-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:22:02.885698+00:00
-- url     : https://prove2.me/submissions/56da32f4-abf0-418c-ad7b-efec0011988f

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model
import Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_2

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail

open TimeDepFolk.Asymptotic Finset

theorem solution {ι : Type*} [Fintype ι] (θ : ℕ → Evaluation) (hθ : IsPatient θ)
    {L : ℕ} (hL : L ≤ Fintype.card ι + 1) (x : Fin L → ι → ℝ) (hx : AffineIndependent ℝ x)
    (x0 : ι → ℝ) (hx0 : x0 ∈ convexHull ℝ (Set.range x))
    (η : ℝ) (hη : 0 < η) (hball : Metric.closedBall x0 η ⊆ convexHull ℝ (Set.range x)) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ xx : Fin L → ℕ → ι → ℝ,
      (∀ ℓ m, xx ℓ m ∈ Metric.closedBall (x ℓ) (η / 5)) →
        ∃ φ : ℕ → Fin L, HasSum (fun m => (θ k).θ m • xx (φ m) m) x0 := by
  classical
  -- the affine basis given by the vertices
  have htop : affineSpan ℝ (Set.range x) = ⊤ := by
    rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top]
    refine ⟨x0, ?_⟩
    have : Metric.ball x0 η ⊆ interior (convexHull ℝ (Set.range x)) :=
      interior_maximal (Metric.ball_subset_closedBall.trans hball) Metric.isOpen_ball
    exact this (Metric.mem_ball_self hη)
  let b : AffineBasis (Fin L) ℝ (ι → ℝ) := ⟨x, hx, htop⟩
  have hb : ∀ ℓ, b ℓ = x ℓ := fun ℓ => rfl
  have hL0 : 0 < L := by
    obtain ⟨y, hy⟩ := (convexHull_nonempty_iff.1 ⟨x0, hx0⟩)
    obtain ⟨ℓ, -⟩ := hy
    exact ℓ.pos
  have : Nonempty (Fin L) := ⟨⟨0, hL0⟩⟩
  set a : Fin L → ℝ := fun j => b.coord j x0 with ha
  have hhull : ∀ y, y ∈ Metric.closedBall x0 η → ∀ j, 0 ≤ b.coord j y := by
    intro y hy j
    have := hball hy
    have e : Set.range x = Set.range b := rfl
    rw [e, b.convexHull_eq_nonneg_coord] at this
    exact this j
  have ha0 : ∀ j, 0 ≤ a j := fun j => hhull x0 (Metric.mem_closedBall_self hη.le) j
  have hsuma : ∑ j, a j = 1 := b.sum_coord_apply_eq_one x0
  -- perturbation bound on the coordinates
  have hpert : ∀ (y e : ι → ℝ), ‖e‖ ≤ η / 5 → ∀ j, |b.coord j (y + e) - b.coord j y| ≤ a j / 5 := by
    intro y e he j
    have hlin : ∀ z w : ι → ℝ, b.coord j (z + w) = (b.coord j).linear w + b.coord j z := by
      intro z w
      have := (b.coord j).map_vadd z w
      rw [vadd_eq_add, add_comm w z] at this
      exact this
    rw [hlin, add_sub_cancel_right]
    have h1 := hhull (x0 + (5 : ℝ) • e) (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      norm_num; linarith) j
    have h2 := hhull (x0 + (-5 : ℝ) • e) (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      norm_num; linarith) j
    rw [hlin, map_smul, smul_eq_mul] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  -- the coordinates of the perturbed vertices
  have hcoordxx : ∀ (y : ι → ℝ) (l : Fin L), y ∈ Metric.closedBall (x l) (η / 5) → ∀ j,
      |b.coord j y - (if j = l then 1 else 0)| ≤ a j / 5 := by
    intro y l hy j
    have := hpert (x l) (y - x l) (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hy) j
    rw [add_sub_cancel, ← hb l, b.coord_apply] at this
    exact this
  -- patience: the first continuation weight is small
  have h42 := (lemma_4_2 θ hθ).1
  rw [Metric.tendstoUniformly_iff] at h42
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (h42 (4 / (5 * L)) (by positivity))
  refine ⟨K, fun k hk xx hxx => ?_⟩
  set w := (θ k).θ with hw
  set τ : ℕ → ℝ := fun m => ∑' r, w (m + r) with hτ
  have hτsucc : ∀ m, τ (m + 1) = τ m - w m := by
    intro m
    have := TDFTail.tail_split (θ k) m 1
    simp only [Finset.range_one, Finset.sum_singleton, add_zero] at this
    simp only [τ, w]; linarith
  have hτ0 : τ 0 = 1 := by simp [τ, w, (θ k).hasSum.tsum_eq]
  have hw0 : ∀ m, 0 ≤ w m := (θ k).nonneg
  have hwτ : ∀ m, w m ≤ 4 / (5 * L) * τ m := by
    intro m
    have hc := hK k hk m
    rw [dist_zero_left, Real.norm_eq_abs] at hc
    have hτm : 0 ≤ τ m := TDFTail.tail_nonneg (θ k) m
    rcases hτm.eq_or_lt with h0 | hpos
    · have : τ (m + 1) ≥ 0 := TDFTail.tail_nonneg (θ k) (m + 1)
      rw [hτsucc] at this
      rw [← h0] at this ⊢
      linarith [hw0 m]
    · have : cont (θ k).θ m 0 = w m / τ m := by simp [cont, τ, w]
      rw [this, abs_of_nonneg (div_nonneg (hw0 m) hpos.le), div_lt_iff₀ hpos] at hc
      linarith
  -- the greedy construction on unnormalised barycentric coordinates
  let amax : (Fin L → ℝ) → Fin L := fun f => (Finite.exists_max f).choose
  have hamax : ∀ (f : Fin L → ℝ) (j : Fin L), f j ≤ f (amax f) := fun f => (Finite.exists_max f).choose_spec
  let pick : ℕ → (Fin L → ℝ) → Fin L := fun m c => amax (fun l => c l - τ m * a l / 5)
  let C : ℕ → Fin L → ℝ := fun m =>
    Nat.rec a (fun m c j => c j - w m * b.coord j (xx (pick m c) m)) m
  have hC0 : C 0 = a := rfl
  have hCs : ∀ m j, C (m + 1) j = C m j - w m * b.coord j (xx (pick m (C m)) m) :=
    fun m j => rfl
  set φ : ℕ → Fin L := fun m => pick m (C m) with hφ
  -- invariant (i): the coordinates sum to the tail
  have hsumC : ∀ m, ∑ j, C m j = τ m := by
    intro m
    induction m with
    | zero => rw [hC0, hsuma, hτ0]
    | succ m ih =>
      simp only [hCs, Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_coord_apply_eq_one,
        mul_one, ih, hτsucc]
  -- invariant (ii): every coordinate keeps a safety margin
  have hmarg : ∀ m j, τ m * a j / 5 ≤ C m j := by
    intro m
    induction m with
    | zero => intro j; rw [hC0, hτ0]; linarith [ha0 j]
    | succ m ih =>
      intro j
      rw [hCs, hτsucc]
      have hj := hcoordxx _ _ (hxx (pick m (C m)) m) j
      rw [abs_le] at hj
      by_cases hjp : j = pick m (C m)
      · -- the chosen coordinate had the largest slack, at least `4τ/(5L)`
        rw [if_pos hjp] at hj
        have hslack : 4 / (5 * L) * τ m ≤ C m j - τ m * a j / 5 := by
          have hle : ∀ l, C m l - τ m * a l / 5 ≤ C m j - τ m * a j / 5 := by
            intro l; rw [hjp]; exact hamax (fun l => C m l - τ m * a l / 5) l
          have hs : ∑ l, (C m l - τ m * a l / 5) = 4 / 5 * τ m := by
            rw [Finset.sum_sub_distrib, hsumC, ← Finset.sum_div, ← Finset.mul_sum, hsuma]; ring
          have := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hle l
          rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
          rw [show 4 / (5 * (L : ℝ)) * τ m = (4 / 5 * τ m) / L by ring, div_le_iff₀ hLpos]
          linarith
        have := hwτ m
        have hp := mul_le_mul_of_nonneg_left (show b.coord j (xx (pick m (C m)) m) ≤ 1 + a j / 5 by
          linarith [hj.2]) (hw0 m)
        nlinarith [hw0 m]
      · rw [if_neg hjp] at hj
        have hp := mul_le_mul_of_nonneg_left (show b.coord j (xx (pick m (C m)) m) ≤ a j / 5 by
          linarith [hj.2]) (hw0 m)
        have := ih j
        nlinarith [hw0 m]
  -- invariant (iii): the remainder is the combination of the coordinates
  have hrem : ∀ m, x0 - ∑ i ∈ range m, w i • xx (φ i) i = ∑ j, C m j • x j := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, hC0, a]
      exact (b.linear_combination_coord_eq_self x0).symm
    | succ m ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih]
      have hxxm := b.linear_combination_coord_eq_self (xx (φ m) m)
      conv_lhs => rw [← hxxm]
      simp only [hCs, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
      rfl
  -- bounds and convergence
  obtain ⟨Bx, hBx⟩ : ∃ B, ∀ j, ‖x j‖ ≤ B :=
    ⟨∑ j, ‖x j‖, fun j => Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ j)⟩
  have hBx0 : 0 ≤ Bx := (norm_nonneg _).trans (hBx ⟨0, hL0⟩)
  refine ⟨φ, ?_⟩
  have hsumm : Summable (fun m => w m • xx (φ m) m) := by
    refine Summable.of_norm_bounded ((θ k).hasSum.summable.mul_right (Bx + η / 5)) fun m => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 m)]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 m)
    have := Metric.mem_closedBall.1 (hxx (φ m) m)
    rw [dist_eq_norm] at this
    calc ‖xx (φ m) m‖ = ‖(xx (φ m) m - x (φ m)) + x (φ m)‖ := by rw [sub_add_cancel]
      _ ≤ ‖xx (φ m) m - x (φ m)‖ + ‖x (φ m)‖ := norm_add_le _ _
      _ ≤ η / 5 + Bx := add_le_add this (hBx _)
      _ = Bx + η / 5 := add_comm _ _
  rw [hsumm.hasSum_iff_tendsto_nat]
  -- the tail tends to zero
  have hτlim : Filter.Tendsto τ Filter.atTop (nhds 0) := by
    have e : ∀ m, τ m = 1 - ∑ i ∈ range m, w i := by
      intro m
      have := TDFTail.tail_split (θ k) 0 m
      simp only [zero_add] at this
      rw [(θ k).hasSum.tsum_eq] at this
      simp only [τ, w]; linarith
    rw [show τ = fun m => 1 - ∑ i ∈ range m, w i from funext e]
    have := (θ k).hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hnorm : ∀ m, ‖x0 - ∑ i ∈ range m, w i • xx (φ i) i‖ ≤ τ m * Bx := by
    intro m
    rw [hrem]
    calc ‖∑ j, C m j • x j‖ ≤ ∑ j, ‖C m j • x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, C m j * Bx := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hC : 0 ≤ C m j := le_trans (by
            have := TDFTail.tail_nonneg (θ k) m
            have := ha0 j
            positivity) (hmarg m j)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_left (hBx j) hC
      _ = τ m * Bx := by rw [← Finset.sum_mul, hsumC]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) (by simpa using hτlim.mul_const Bx)
  rw [norm_sub_rev]
  exact hnorm m
