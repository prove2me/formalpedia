-- Prove2me | solution 1 for RevenueManagement.overbooking_limits_demand
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-26T09:12:32.44104+00:00
-- url     : https://prove2.me/submissions/1fdfa13f-c9ed-4bf4-8073-b2989ee3b2fe

import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

/-- The counterexample model: two periods, no denied-service cost, in period 2 every reservation
cancels (`q 2 = 0`), in period 1 none does (`q 1 = 1`); no demand at all. -/
noncomputable def rm2cexM : DynOverbooking where
  T := 2
  C := 0
  c := fun _ => 0
  p := fun t => if t = 2 then 2 else 0
  r := fun _ => 1
  q := fun t => if t = 2 then 0 else 1
  f := fun _ d => if d = 0 then 1 else 0

/-- A heavy-tailed demand pmf `P(D = d) = 1/((d+1)(d+2))`, with infinite mean. -/
noncomputable def rm2cexF : ℕ → ℕ → ℝ := fun _ d => 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2))

lemma rm2_binom0 (x w : ℕ) : binomPmf 0 x w = if w = 0 then 1 else 0 := by
  unfold binomPmf
  rcases Nat.eq_zero_or_pos w with h | h
  · subst h; simp
  · simp [Nat.pos_iff_ne_zero.1 h, zero_pow (Nat.pos_iff_ne_zero.1 h)]

lemma rm2_binom1 (x w : ℕ) (hw : w ≤ x) : binomPmf 1 x w = if w = x then 1 else 0 := by
  unfold binomPmf
  by_cases h : w = x
  · subst h; simp
  · have : 0 < x - w := by omega
    simp [h, zero_pow (Nat.pos_iff_ne_zero.1 this)]

lemma rm2_cexF_hasSum : HasSum (fun d : ℕ => 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun d => by positivity)]
  have hpart : ∀ n : ℕ, ∑ d ∈ Finset.range n, 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2))
      = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  simp only [hpart]
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
  simpa using this

lemma rm2_cexF_not_summable (z : ℕ) :
    ¬ Summable (fun d : ℕ => 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) * ((d : ℝ) - z)) := by
  intro hs
  have h2 : Summable (fun d : ℕ => ((z : ℝ) + 1) * (1 / (((d : ℝ) + 1) * ((d : ℝ) + 2)))) :=
    rm2_cexF_hasSum.summable.mul_left _
  have h3 := hs.add h2
  have e : (fun d : ℕ => 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) * ((d : ℝ) - z)
      + ((z : ℝ) + 1) * (1 / (((d : ℝ) + 1) * ((d : ℝ) + 2))))
      = fun d : ℕ => 1 / ((d : ℝ) + 2) := by
    funext d
    have h1 : (d : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (d : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at h3
  have h4 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 2]
    have : (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) = fun n : ℕ => 1 / ((n : ℝ) + 2) := by
      funext n; push_cast; ring
    rw [this]; exact h3
  exact Real.not_summable_one_div_natCast h4

end RevenueManagement

open RevenueManagement

theorem solution : ¬ (∀ (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (f' : ℕ → ℕ → ℝ) (hf' : ∀ t, (∀ d, 0 ≤ f' t d) ∧ HasSum (f' t) 1)
    (hst : ∀ t k, ∑' d, (if k ≤ d then M.f t d else 0) ≤ ∑' d, (if k ≤ d then f' t d else 0))
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T),
    ({ M with f := f' } : DynOverbooking).overbookingLimit t ≤ M.overbookingLimit t) := by
  intro H
  set M := rm2cexM with hMdef
  set M' : DynOverbooking := { M with f := rm2cexF } with hM'def
  -- the hypotheses
  have hM : M.IsModel := by
    refine ⟨fun t => ⟨fun d => ?_, ?_⟩, fun t => ?_, fun t => ?_, fun t => ?_, rfl, fun k => ?_⟩
    · simp only [hMdef, rm2cexM]; split_ifs <;> norm_num
    · simp only [hMdef, rm2cexM]; exact hasSum_ite_eq 0 1
    · simp only [hMdef, rm2cexM]; split_ifs <;> norm_num
    · simp only [hMdef, rm2cexM]; split_ifs <;> norm_num
    · simp only [hMdef, rm2cexM]; norm_num
    · simp only [hMdef, rm2cexM]; norm_num
  have hc : IsConvexSeq M.c := fun k => by simp [hMdef, rm2cexM]
  have hf' : ∀ t, (∀ d, 0 ≤ rm2cexF t d) ∧ HasSum (rm2cexF t) 1 :=
    fun t => ⟨fun d => by unfold rm2cexF; positivity, rm2_cexF_hasSum⟩
  have hst : ∀ t k, ∑' d, (if k ≤ d then M.f t d else 0)
      ≤ ∑' d, (if k ≤ d then rm2cexF t d else 0) := by
    intro t k
    have hR : 0 ≤ ∑' d, (if k ≤ d then rm2cexF t d else 0) :=
      tsum_nonneg (fun d => by split_ifs <;> [unfold rm2cexF; skip] <;> positivity)
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [zero_le, if_true, hMdef, rm2cexM]
      have e1 : (∑' d : ℕ, if d = 0 then (1 : ℝ) else 0) = 1 := by simp
      have e2 : (∑' d : ℕ, rm2cexF t d) = 1 := rm2_cexF_hasSum.tsum_eq
      rw [e1, e2]
    · have : (fun d => if k ≤ d then M.f t d else 0) = fun _ => (0 : ℝ) := by
        funext d
        simp only [hMdef, rm2cexM]
        split_ifs with h1 h2 <;> first | rfl | omega
      rw [this, tsum_zero]; exact hR
  have key := H M hM hc rm2cexF hf' hst 1 le_rfl (by simp [hMdef, rm2cexM])
  -- terminal values vanish
  have hterm : ∀ (N : DynOverbooking), N.c = (fun _ => 0) → ∀ z, N.valueGo 0 z = 0 := by
    intro N hN z
    simp [DynOverbooking.valueGo, hN]
  -- the period-2 objective inside the window
  have hinner : ∀ (N : DynOverbooking), N.T = 2 → N.c = (fun _ => 0) → N.q 2 = 0 → N.r 2 = 1 →
      N.p 2 = 2 → ∀ z d, (Finset.Icc z (z + d)).sup'
        ⟨z, Finset.mem_Icc.2 ⟨le_rfl, Nat.le_add_right _ _⟩⟩ (fun x =>
        (∑ w ∈ Finset.range (x + 1), binomPmf (N.q (N.T - 0)) x w *
          (N.valueGo 0 w - ((x : ℝ) - w) * N.r (N.T - 0))) + ((x : ℝ) - z) * N.p (N.T - 0))
        = (d : ℝ) - z := by
    intro N hT hc0 hq hr hp z d
    have hx : ∀ x : ℕ, (∑ w ∈ Finset.range (x + 1), binomPmf (N.q (N.T - 0)) x w *
          (N.valueGo 0 w - ((x : ℝ) - w) * N.r (N.T - 0))) + ((x : ℝ) - z) * N.p (N.T - 0)
          = (x : ℝ) - 2 * z := by
      intro x
      rw [hT, Nat.sub_zero, hq, hr, hp]
      rw [Finset.sum_eq_single 0]
      · rw [rm2_binom0, if_pos rfl, hterm N hc0]; push_cast; ring
      · intro w _ hw; rw [rm2_binom0, if_neg hw, zero_mul]
      · intro h; simp at h
    simp only [hx]
    apply le_antisymm
    · apply Finset.sup'_le
      intro x hx'
      have := (Finset.mem_Icc.1 hx').2
      have : (x : ℝ) ≤ z + d := by exact_mod_cast this
      linarith
    · have := Finset.le_sup' (fun x : ℕ => (x : ℝ) - 2 * z)
        (Finset.mem_Icc.2 ⟨Nat.le_add_right z d, le_rfl⟩ : z + d ∈ Finset.Icc z (z + d))
      push_cast at this
      linarith
  -- values at period 2
  have hV : ∀ z, M.value 2 z = -(z : ℝ) := by
    intro z
    show M.valueGo (0 + 1) z = _
    rw [DynOverbooking.valueGo.eq_2]
    simp only [hinner M rfl rfl rfl rfl rfl]
    have e : (fun d : ℕ => M.f (M.T - 0) d * ((d : ℝ) - z))
        = fun d : ℕ => if d = 0 then -(z : ℝ) else 0 := by
      funext d
      simp only [hMdef, rm2cexM]
      split_ifs with h <;> simp [h]
    rw [e]; simp
  have hV' : ∀ z, M'.value 2 z = 0 := by
    intro z
    show M'.valueGo (0 + 1) z = _
    rw [DynOverbooking.valueGo.eq_2]
    simp only [hinner M' rfl rfl rfl rfl rfl]
    exact tsum_eq_zero_of_not_summable (rm2_cexF_not_summable z)
  -- the period-1 objectives
  have hG : ∀ x, M.limitObjective 1 x = -(x : ℝ) := by
    intro x
    unfold DynOverbooking.limitObjective DynOverbooking.postValue
    have hq1 : M.q 1 = 1 := by simp [hMdef, rm2cexM]
    have hp1 : M.p 1 = 0 := by simp [hMdef, rm2cexM]
    rw [hq1, hp1, Finset.sum_eq_single x]
    · rw [rm2_binom1 x x le_rfl, if_pos rfl, show (1 : ℕ) + 1 = 2 from rfl, hV]; ring
    · intro w hw hne
      rw [rm2_binom1 x w (by simp at hw; omega), if_neg hne, zero_mul]
    · intro h; simp at h
  have hG' : ∀ x, M'.limitObjective 1 x = 0 := by
    intro x
    unfold DynOverbooking.limitObjective DynOverbooking.postValue
    have hq1 : M'.q 1 = 1 := by simp [hM'def, hMdef, rm2cexM]
    have hp1 : M'.p 1 = 0 := by simp [hM'def, hMdef, rm2cexM]
    rw [hq1, hp1, Finset.sum_eq_single x]
    · rw [rm2_binom1 x x le_rfl, if_pos rfl, show (1 : ℕ) + 1 = 2 from rfl, hV']; ring
    · intro w hw hne
      rw [rm2_binom1 x w (by simp at hw; omega), if_neg hne, zero_mul]
    · intro h; simp at h
  -- the booking limits
  have hL : M.overbookingLimit 1 ≤ 0 := by
    unfold DynOverbooking.overbookingLimit
    apply sSup_le
    rintro b ⟨x, hx, rfl⟩
    have := hx 0 (Nat.zero_le x)
    rw [hG, hG] at this
    have : (x : ℝ) ≤ 0 := by push_cast at this; linarith
    have : x = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg x)
    simp [this]
  have hL' : (1 : ℕ∞) ≤ M'.overbookingLimit 1 := by
    unfold DynOverbooking.overbookingLimit
    apply le_sSup
    refine ⟨1, fun x' _ => ?_, rfl⟩
    rw [hG', hG']
  have := le_trans hL' (le_trans key hL)
  exact absurd this (by norm_num)
