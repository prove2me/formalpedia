-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.cvx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:26.903152+00:00
-- url     : https://prove2.me/submissions/4f3866b7-a76c-4736-a38e-89b8d8e04d0b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_CvxOfConvex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CVXStatement H := by
  unfold CVXStatement
  intro K hanti hne hcl hmid hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hbdd : ∀ n, BddBelow ((fun w : H => ‖w‖) '' K n) :=
    fun n => ⟨0, by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w⟩
  have hSne : ∀ n, ((fun w : H => ‖w‖) '' K n).Nonempty := fun n => (hne n).image _
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, d = fun n => sInf ((fun w : H => ‖w‖) '' K n) := ⟨_, rfl⟩
  have hdle : ∀ n, ∀ w ∈ K n, d n ≤ ‖w‖ := by
    intro n w hw; rw [hd]; exact csInf_le (hbdd n) ⟨w, hw, rfl⟩
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n; rw [hd]
    exact le_csInf (hSne n) (by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w)
  have hdmono : Monotone d := by
    intro n m hnm; rw [hd]
    exact csInf_le_csInf (hbdd n) (hSne m) (Set.image_mono (hanti hnm))
  have hdR : ∀ n, d n ≤ R := by
    intro n
    obtain ⟨w, hw⟩ := hne n
    exact (hdle n w hw).trans (hR w (hanti (Nat.zero_le n) hw))
  have happrox : ∀ n, ∃ w ∈ K n, ‖w‖ < d n + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf ((fun w : H => ‖w‖) '' K n) < d n + 1 / ((n : ℝ) + 1) := by
      rw [hd]; exact lt_add_of_pos_right _ hpos
    obtain ⟨_, ⟨w, hw, rfl⟩, hw2⟩ := exists_lt_of_csInf_lt (hSne n) hlt
    exact ⟨w, hw, hw2⟩
  choose x hxK hxn using happrox
  have hbddA : BddAbove (Set.range d) := ⟨R, by rintro _ ⟨n, rfl⟩; exact hdR n⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ⨆ n, d n := ⟨_, rfl⟩
  have hdL : ∀ n, d n ≤ L := fun n => by rw [hL]; exact le_ciSup hbddA n
  have hL0 : 0 ≤ L := (hd0 0).trans (hdL 0)
  have hkey : ∀ n m, n ≤ m → ‖x m - x n‖ ^ 2 ≤ 2 * ‖x m‖ ^ 2 + 2 * ‖x n‖ ^ 2 - 4 * d n ^ 2 := by
    intro n m hnm
    have hmK : x m ∈ K n := hanti hnm (hxK m)
    have h1 := hdle n _ (hmid n (x m) hmK (x n) (hxK n))
    have h2 : ‖x m + x n‖ = 2 * ‖(2 : ℂ)⁻¹ • (x m + x n)‖ := by
      first
        | (rw [norm_smul, norm_inv, Complex.norm_two]; ring)
        | (rw [norm_smul]; norm_num)
        | (simp [norm_smul]; ring)
    have h3 : 4 * d n ^ 2 ≤ ‖x m + x n‖ ^ 2 := by
      rw [h2]; nlinarith [h1, hd0 n]
    have hpar := parallelogram_law_with_norm ℂ (x m) (x n)
    nlinarith [hpar, h3]
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨η, hηdef⟩ : ∃ η, η = min 1 (ε ^ 2 / (16 * (L + 1))) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hηdef]; exact lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
    have hηε : η ≤ ε ^ 2 / (16 * (L + 1)) := by rw [hηdef]; exact min_le_right _ _
    obtain ⟨N₁, hN₁⟩ := exists_lt_of_lt_ciSup (f := d) (by rw [← hL]; linarith : L - η < ⨆ n, d n)
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hη0
    refine ⟨max N₁ N₂, fun m hm => ?_⟩
    have hdN : L - η < d (max N₁ N₂) := hN₁.trans_le (hdmono (le_max_left _ _))
    have heN : 1 / (((max N₁ N₂ : ℕ) : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ ((max N₁ N₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right N₁ N₂
      linarith
    have hem : 1 / ((m : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N₁ N₂).trans hm
      linarith
    have hk := hkey (max N₁ N₂) m hm
    have hxm := hxn m
    have hxN := hxn (max N₁ N₂)
    have hdm := hdL m
    have hdNL := hdL (max N₁ N₂)
    have hd0N := hd0 (max N₁ N₂)
    have a1 : ‖x m‖ < L + η := by linarith
    have a2 : ‖x (max N₁ N₂)‖ < d (max N₁ N₂) + η := by linarith
    have b1 : ‖x m‖ ^ 2 ≤ (L + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1.le 2
    have b2 : ‖x (max N₁ N₂)‖ ^ 2 ≤ (d (max N₁ N₂) + η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) a2.le 2
    have c0 : 0 ≤ (d (max N₁ N₂) - L + η) * (d (max N₁ N₂) + L) :=
      mul_nonneg (by linarith) (by linarith)
    have c1 : d (max N₁ N₂) * η ≤ L * η := mul_le_mul_of_nonneg_right hdNL hη0.le
    have c2 : η * η ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
    have c3 : 0 ≤ L * η := mul_nonneg hL0 hη0.le
    have b3 : L ^ 2 - 2 * L * η ≤ d (max N₁ N₂) ^ 2 := by nlinarith
    have b4 : η * (16 * (L + 1)) ≤ ε ^ 2 := (le_div_iff₀ (by positivity)).1 hηε
    have hsq : ‖x m - x (max N₁ N₂)‖ ^ 2 < ε ^ 2 := by nlinarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x m - x (max N₁ N₂))]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, fun n => ?_⟩
  apply (hcl n).mem_of_tendsto hy
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact hanti hm (hxK m)
end ReciprocityTheory.L2DbarEstimates
