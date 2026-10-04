-- Prove2me | solution 1 for SennottDP.AvgFinite.cor_4_5_5_bounded_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:28:55.795013+00:00
-- url     : https://prove2.me/submissions/c9283b5b-a370-4096-a6c5-23879fe0f80e

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal

namespace SennottDP.AvgFinite.C455

open SennottDP.AvgFinite

variable {S : Type*} {Act : Type*} [Countable S]

theorem c455_list_tsum {α : Type*} (f : List α → ℝ≥0∞) (hf : f [] = 0) :
    ∑' h, f h = ∑' p : α × List α, f (p.1 :: p.2) := by
  have hinj : Function.Injective (fun p : α × List α => p.1 :: p.2) := by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  refine (hinj.tsum_eq ?_).symm
  intro h hh
  cases h with
  | nil => exact (hh hf).elim
  | cons x l => exact ⟨(x, l), rfl⟩

theorem c455_prev_sum (M : MDC S Act) (i : S) (rest : List (S × Act)) :
    ∑' j, prevWeight M i rest j = 1 := by
  cases rest with
  | nil =>
    classical
    show ∑' j, (if j = i then (1 : ℝ≥0∞) else 0) = 1
    simp
  | cons x l =>
    obtain ⟨k, b⟩ := x
    exact M.P_sum k b

theorem c455_mass {M : MDC S Act} (θ : Policy M) (i : S) :
    ∀ t, ∑' h : List (S × Act), (if h.length = t then histProb θ i h else 0) = 1 := by
  intro t
  induction t with
  | zero =>
    rw [tsum_eq_single []]
    · simp [histProb]
    · intro h hh
      rw [if_neg]
      intro hl; exact hh (List.length_eq_zero_iff.mp hl)
  | succ t ih =>
    rw [c455_list_tsum _ (by simp)]
    refine (ENNReal.tsum_prod (f := fun (x : S × Act) (rest : List (S × Act)) =>
      if (x :: rest).length = t + 1 then histProb θ i (x :: rest) else 0)).trans ?_
    rw [ENNReal.tsum_comm, ← ih]
    refine tsum_congr fun rest => ?_
    by_cases hr : rest.length = t
    · rw [if_pos hr]
      have : ∀ x : S × Act, (if (x :: rest).length = t + 1 then histProb θ i (x :: rest) else 0) =
          histProb θ i rest * (prevWeight M i rest x.1 * θ.prob rest x.1 x.2) := by
        intro x
        rw [if_pos (by simp [hr])]
        obtain ⟨j, a⟩ := x
        simp only [histProb, mul_assoc]
      rw [tsum_congr this, ENNReal.tsum_mul_left]
      conv_rhs => rw [← mul_one (histProb θ i rest)]
      congr 1
      refine (ENNReal.tsum_prod (f := fun (j : S) (a : Act) =>
        prevWeight M i rest j * θ.prob rest j a)).trans ?_
      have h2 : ∀ j, ∑' a, prevWeight M i rest j * θ.prob rest j a = prevWeight M i rest j := by
        intro j
        rw [ENNReal.tsum_mul_left, tsum_eq_sum (s := M.A j) (fun a ha => θ.prob_supp rest j a ha),
          θ.prob_sum, mul_one]
      rw [tsum_congr h2, c455_prev_sum]
    · rw [if_neg hr]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      rw [if_neg (by simp [hr])]

theorem c455_expCost_le {M : MDC S Act} (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (θ : Policy M) (i : S) (t : ℕ) : expCost θ i t ≤ B := by
  unfold expCost
  calc ∑' h : List (S × Act), (if h.length = t + 1 then histProb θ i h * lastCost M h else 0)
      ≤ ∑' h : List (S × Act), (B : ℝ≥0∞) * (if h.length = t + 1 then histProb θ i h else 0) := by
        refine ENNReal.tsum_le_tsum fun h => ?_
        split_ifs with hl
        · cases h with
          | nil => simp at hl
          | cons x rest =>
            obtain ⟨j, a⟩ := x
            by_cases ha : a ∈ M.A j
            · rw [mul_comm (B : ℝ≥0∞)]
              exact mul_le_mul_of_nonneg_left
                (show (M.C j a : ℝ≥0∞) ≤ B by exact_mod_cast hB j a ha) bot_le
            · have : histProb θ i ((j, a) :: rest) = 0 := by
                simp [histProb, θ.prob_supp rest j a ha]
              simp [this]
        · simp
    _ = B := by rw [ENNReal.tsum_mul_left, c455_mass θ i (t + 1), mul_one]

theorem c455_mono {M : MDC S Act} (θ : Policy M) (i : S) {α β : ℝ} (h : α ≤ β) :
    discCost θ α i ≤ discCost θ β i := by
  unfold discCost
  refine ENNReal.tsum_le_tsum fun t => ?_
  gcongr

theorem c455_incr {M : MDC S Act} (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (θ : Policy M) (i : S) {α β : ℝ} (h0 : 0 < α) (h : α ≤ β) (h1 : β < 1) :
    discCost θ β i ≤ discCost θ α i + B * ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hsum : ∑' t : ℕ, ENNReal.ofReal (β ^ t - α ^ t) = ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
    have sβ := summable_geometric_of_lt_one hβ0 h1
    have sα := summable_geometric_of_lt_one h0.le (by linarith)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => sub_nonneg.mpr (pow_le_pow_left₀ h0.le h t))
      (sβ.sub sα), sβ.tsum_sub sα, tsum_geometric_of_lt_one hβ0 h1,
      tsum_geometric_of_lt_one h0.le (by linarith), one_div, one_div]
  rw [← hsum, ← ENNReal.tsum_mul_left]
  unfold discCost
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun t => ?_
  have e : ENNReal.ofReal β ^ t = ENNReal.ofReal α ^ t + ENNReal.ofReal (β ^ t - α ^ t) := by
    rw [← ENNReal.ofReal_pow hβ0, ← ENNReal.ofReal_pow h0.le, ← ENNReal.ofReal_add
      (pow_nonneg h0.le t) (sub_nonneg.mpr (pow_le_pow_left₀ h0.le h t))]
    congr 1; ring
  rw [e, add_mul]
  refine add_le_add le_rfl ?_
  rw [mul_comm (B : ℝ≥0∞)]
  exact mul_le_mul_of_nonneg_left (c455_expCost_le B hB θ i t) bot_le

end SennottDP.AvgFinite.C455

open SennottDP.AvgFinite SennottDP.AvgFinite.C455 in
theorem solution {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (hB : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (i : S) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α i ≠ ⊤) ∧
    ContinuousOn (fun α : ℝ => (discValue M α i).toReal) (Set.Ioo 0 1) := by
  obtain ⟨B, hB⟩ := hB
  classical
  let θ0 : Policy M := StationaryPolicy.toPolicy
    ⟨fun j => (M.A_nonempty j).choose, fun j => (M.A_nonempty j).choose_spec⟩
  have hfin : ∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α i ≠ ⊤ := by
    intro α hα
    have h1 : discValue M α i ≤ discCost θ0 α i := iInf_le _ θ0
    refine ne_top_of_le_ne_top ?_ h1
    have hα1 : ENNReal.ofReal α < 1 := by rw [ENNReal.ofReal_lt_one]; exact hα.2
    refine ne_top_of_le_ne_top (b := ∑' t : ℕ, ENNReal.ofReal α ^ t * B) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hα1).ne') ENNReal.coe_ne_top
    · exact ENNReal.tsum_le_tsum fun t => mul_le_mul_of_nonneg_left (c455_expCost_le B hB θ0 i t) bot_le
  refine ⟨hfin, ?_⟩
  set f : ℝ → ℝ := fun α => (discValue M α i).toReal with hf
  set g : ℝ → ℝ := fun α => (B : ℝ) * (1 / (1 - α)) with hg
  -- sandwich: for α ≤ β in (0,1), f α ≤ f β ≤ f α + (g β - g α)
  have hsand : ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioo (0 : ℝ) 1, α ≤ β →
      f α ≤ f β ∧ f β ≤ f α + (g β - g α) := by
    intro α hα β hβ hab
    have hmono : discValue M α i ≤ discValue M β i :=
      iInf_mono fun θ => c455_mono θ i hab
    have hinc : discValue M β i ≤ discValue M α i + B * ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
      unfold discValue
      rw [ENNReal.iInf_add]
      exact iInf_mono fun θ => c455_incr B hB θ i hα.1 hab hβ.2
    have hg0 : 0 ≤ 1 / (1 - β) - 1 / (1 - α) := by
      have : 1 / (1 - α) ≤ 1 / (1 - β) :=
        one_div_le_one_div_of_le (by linarith [(Set.mem_Ioo.mp hβ).2]) (by linarith)
      linarith
    refine ⟨ENNReal.toReal_mono (hfin β hβ) hmono, ?_⟩
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin α hα,
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top⟩) hinc
    rw [ENNReal.toReal_add (hfin α hα) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hg0, ENNReal.coe_toReal] at this
    simp only [hf, hg]
    linarith
  have hgc : ContinuousOn g (Set.Ioo 0 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (continuousOn_const.sub continuousOn_id) ?_)
    intro x hx; have := (Set.mem_Ioo.mp hx).2; linarith
  intro x hx
  have hgx := hgc x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hgx ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := hgx ε hε
  refine ⟨δ, hδ, fun y hy hyd => ?_⟩
  have hgy := hδg hy hyd
  rw [Real.dist_eq] at hgy ⊢
  rcases le_total x y with hxy | hyx
  · obtain ⟨h1, h2⟩ := hsand x hx y hy hxy
    rw [abs_lt] at hgy ⊢; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hsand y hy x hx hyx
    rw [abs_lt] at hgy ⊢; constructor <;> linarith


