-- Prove2me | solution 1 for TwoStageMatch.proposition_ec1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T13:58:23.231807+00:00
-- url     : https://prove2.me/submissions/50a3d0c1-abe8-459c-b086-41c103a8ff28

import Mathlib
import Definitions.Def_TwoStageMatch_Lagrangian
import Theorems.Thm_TwoStageMatch_lp1_duality

open Finset

namespace TSMec1
open TwoStageMatch

open Classical

set_option linter.unusedSectionVars false

variable {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S]

/-! ### Convexity -/

lemma grad_ineq {g : ℝ → ℝ} (hgd : Differentiable ℝ g) (hc : ConvexOn ℝ Set.univ g) (a b : ℝ) :
    g a + deriv g a * (b - a) ≤ g b := by
  rcases lt_trichotomy a b with h | rfl | h
  · have := hc.deriv_le_slope (Set.mem_univ a) (Set.mem_univ b) h (hgd a)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.slope_le_deriv (Set.mem_univ b) (Set.mem_univ a) h (hgd a)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    have e : deriv g a * (b - a) = -(deriv g a * (a - b)) := by ring
    linarith

/-! ### Decomposition of the Lagrangian -/

noncomputable def gamSum (I : Instance D₁ D₂ S) (m : Multipliers D₁ S) (x : D₁ → S → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), m.gam i j * x i j

noncomputable def linPart (I : Instance D₁ D₂ S) (m : Multipliers D₁ S) (x : D₁ → S → ℝ) : ℝ :=
  ∑ i, m.lam i * (demandLoad I x i - 1) + ∑ j, m.theta j * (supplyLoad I x j - 1) - gamSum I m x

noncomputable def linD (I : Instance D₁ D₂ S) (m : Multipliers D₁ S) (d : D₁ → S → ℝ) : ℝ :=
  ∑ i, m.lam i * demandLoad I d i + ∑ j, m.theta j * supplyLoad I d j - gamSum I m d

noncomputable def F0 (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) : ℝ :=
  ∑ j, (1 / I.w j) * g (I.w j * (1 - supplyLoad I x j))

lemma lag_eq (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) (m : Multipliers D₁ S) :
    lagrangian I g x m = F0 I g x + linPart I m x := by
  unfold lagrangian F0 linPart gamSum
  ring

lemma sl_line (I : Instance D₁ D₂ S) (x d : D₁ → S → ℝ) (t : ℝ) (j : S) :
    supplyLoad I (fun i j => x i j + t * d i j) j = supplyLoad I x j + t * supplyLoad I d j := by
  unfold supplyLoad
  rw [sum_add_distrib, mul_sum]

lemma dl_line (I : Instance D₁ D₂ S) (x d : D₁ → S → ℝ) (t : ℝ) (i : D₁) :
    demandLoad I (fun i j => x i j + t * d i j) i = demandLoad I x i + t * demandLoad I d i := by
  unfold demandLoad
  rw [sum_add_distrib, mul_sum]

lemma gam_line (I : Instance D₁ D₂ S) (m : Multipliers D₁ S) (x d : D₁ → S → ℝ) (t : ℝ) :
    gamSum I m (fun i j => x i j + t * d i j) = gamSum I m x + t * gamSum I m d := by
  unfold gamSum
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma lin_line (I : Instance D₁ D₂ S) (m : Multipliers D₁ S) (x d : D₁ → S → ℝ) (t : ℝ) :
    linPart I m (fun i j => x i j + t * d i j) = linPart I m x + t * linD I m d := by
  unfold linPart linD
  simp only [sl_line, dl_line, gam_line]
  have h1 : ∑ i, m.lam i * (demandLoad I x i + t * demandLoad I d i - 1) =
      ∑ i, m.lam i * (demandLoad I x i - 1) + t * ∑ i, m.lam i * demandLoad I d i := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  have h2 : ∑ j, m.theta j * (supplyLoad I x j + t * supplyLoad I d j - 1) =
      ∑ j, m.theta j * (supplyLoad I x j - 1) + t * ∑ j, m.theta j * supplyLoad I d j := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [h1, h2]; ring

lemma F0_line (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x d : D₁ → S → ℝ) (t : ℝ) :
    F0 I g (fun i j => x i j + t * d i j) =
      ∑ j, (1 / I.w j) * g (I.w j * (1 - supplyLoad I x j) + t * (-(I.w j * supplyLoad I d j))) := by
  unfold F0
  refine sum_congr rfl fun j _ => ?_
  rw [sl_line]; ring_nf

lemma F0_hasDeriv (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g)
    (hw : ∀ j, 0 < I.w j) (x d : D₁ → S → ℝ) :
    HasDerivAt (fun t => F0 I g (fun i j => x i j + t * d i j))
      (∑ j, -(deriv g (I.w j * (1 - supplyLoad I x j)) * supplyLoad I d j)) 0 := by
  simp only [F0_line]
  apply HasDerivAt.fun_sum
  intro j _
  have h1 : HasDerivAt (fun t : ℝ => I.w j * (1 - supplyLoad I x j) + t * (-(I.w j * supplyLoad I d j)))
      (-(I.w j * supplyLoad I d j)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (-(I.w j * supplyLoad I d j))).const_add
      (I.w j * (1 - supplyLoad I x j))
  have h2 := ((hgd (I.w j * (1 - supplyLoad I x j))).hasDerivAt.comp_of_eq (0:ℝ) h1
    (by simp)).const_mul (1 / I.w j)
  refine h2.congr_deriv ?_
  have := (hw j).ne'
  field_simp

/-! ### Loads of feasible points -/

lemma sl_eq_sum (I : Instance D₁ D₂ S) (z : D₁ → S → ℝ)
    (hz : ∀ i j, ¬ I.E (Sum.inl i) j → z i j = 0) (j : S) :
    supplyLoad I z j = ∑ i, z i j := by
  unfold supplyLoad
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [hz i j h]

lemma dl_eq_sum (I : Instance D₁ D₂ S) (z : D₁ → S → ℝ)
    (hz : ∀ i j, ¬ I.E (Sum.inl i) j → z i j = 0) (i : D₁) :
    demandLoad I z i = ∑ j, z i j := by
  unfold demandLoad
  rw [sum_filter]
  refine sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · rw [hz i j h]

lemma objective_eq_F0 (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (z : D₁ → S → ℝ)
    (hz : ∀ i j, ¬ I.E (Sum.inl i) j → z i j = 0) : objective I g z = F0 I g z := by
  unfold objective F0
  simp only [sl_eq_sum I z hz]

/-- swapping the edge sum -/
lemma edge_swap (I : Instance D₁ D₂ S) (z : D₁ → S → ℝ) (f : S → ℝ) :
    ∑ i, ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), f j * z i j =
      ∑ j, f j * supplyLoad I z j := by
  unfold supplyLoad
  simp only [sum_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma fracWeight_eq (I : Instance D₁ D₂ S) (z : D₁ → S → ℝ)
    (hz : ∀ i j, ¬ I.E (Sum.inl i) j → z i j = 0) (c : S → ℝ) :
    fracWeight c z = ∑ j, c j * supplyLoad I z j := by
  unfold fracWeight
  simp only [sl_eq_sum I z hz, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

/-! ### One-sided derivative -/

lemma deriv_nonneg_of_right_min {φ : ℝ → ℝ} {φ' : ℝ} (h : HasDerivAt φ φ' 0)
    (hmin : ∀ t ∈ Set.Ioo (0:ℝ) 1, φ 0 ≤ φ t) : 0 ≤ φ' := by
  have ht := h.tendsto_slope_zero_right
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr (hmin t ht))

/-! ### Main argument -/

section main

variable (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ)

noncomputable def cc (j : S) : ℝ := deriv g (I.w j * (1 - supplyLoad I x j))

lemma off_edge (hx : IsOptimal I g x) : ∀ i j, ¬ I.E (Sum.inl i) j → x i j = 0 := hx.1.2.1

/-- First-order optimality: `x` maximises the linearised objective over feasible points. -/
lemma first_order (hgd : Differentiable ℝ g) (hw : ∀ j, 0 < I.w j) (hx : IsOptimal I g x)
    (y : D₁ → S → ℝ) (hy : IsFeasible I y) :
    ∑ j, cc I g x j * supplyLoad I y j ≤ ∑ j, cc I g x j * supplyLoad I x j := by
  set d : D₁ → S → ℝ := fun i j => y i j - x i j with hd
  have hder := F0_hasDeriv I g hgd hw x d
  have key := deriv_nonneg_of_right_min hder ?_
  · have hsd : ∀ j, supplyLoad I d j = supplyLoad I y j - supplyLoad I x j := by
      intro j; unfold supplyLoad; rw [← sum_sub_distrib]
    simp only [hsd] at key
    have : ∑ j, -(cc I g x j * (supplyLoad I y j - supplyLoad I x j)) =
        ∑ j, cc I g x j * supplyLoad I x j - ∑ j, cc I g x j * supplyLoad I y j := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    unfold cc at this ⊢
    linarith
  · intro t ht
    have hx0 : (fun i j => x i j + (0:ℝ) * d i j) = x := by funext i j; simp
    simp only [hx0]
    have hxe := off_edge I g x hx
    have hfz : ∀ i j, ¬ I.E (Sum.inl i) j → x i j + t * d i j = 0 := by
      intro i j h; simp [hd, hxe i j h, hy.2.1 i j h]
    have hfeas : IsFeasible I (fun i j => x i j + t * d i j) := by
      refine ⟨fun i j => ?_, hfz, fun i => ?_, fun j => ?_⟩
      · have := hx.1.1 i j; have := hy.1 i j
        have e : x i j + t * d i j = (1 - t) * x i j + t * y i j := by simp [hd]; ring
        show 0 ≤ x i j + t * d i j
        rw [e]; nlinarith [ht.1, ht.2]
      · have e : ∑ j, (x i j + t * d i j) = (1 - t) * ∑ j, x i j + t * ∑ j, y i j := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by simp [hd]; ring
        rw [e]; have := hx.1.2.2.1 i; have := hy.2.2.1 i; nlinarith [ht.1, ht.2]
      · have e : ∑ i, (x i j + t * d i j) = (1 - t) * ∑ i, x i j + t * ∑ i, y i j := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by simp [hd]; ring
        rw [e]; have := hx.1.2.2.2 j; have := hy.2.2.2 j; nlinarith [ht.1, ht.2]
    have := hx.2 hfeas
    rw [← objective_eq_F0 I g x hxe, ← objective_eq_F0 I g _ hfz]
    exact this

lemma linPart_nonpos (hx : IsOptimal I g x) (m : Multipliers D₁ S) (hm : m.Nonneg) :
    linPart I m x ≤ 0 := by
  have hxe := off_edge I g x hx
  unfold linPart
  have h1 : ∑ i, m.lam i * (demandLoad I x i - 1) ≤ 0 := by
    apply sum_nonpos; intro i _
    rw [dl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.1 i) (by linarith [hx.1.2.2.1 i])
  have h2 : ∑ j, m.theta j * (supplyLoad I x j - 1) ≤ 0 := by
    apply sum_nonpos; intro j _
    rw [sl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.2.1 j) (by linarith [hx.1.2.2.2 j])
  have h3 : 0 ≤ gamSum I m x := by
    unfold gamSum
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hm.2.2 i j) (hx.1.1 i j)
  linarith

def m0 : Multipliers D₁ S := ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩

lemma m0_nonneg : (m0 : Multipliers D₁ S).Nonneg :=
  ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ => le_rfl⟩

lemma linPart_m0 (z : D₁ → S → ℝ) : linPart I (m0 : Multipliers D₁ S) z = 0 := by
  simp [linPart, gamSum, m0]

/-- Existence of KKT multipliers via LP duality. -/
lemma exists_kkt (hgd : Differentiable ℝ g) (hgm : Monotone g) (hgc : ConvexOn ℝ Set.univ g)
    (hw : ∀ j, 0 < I.w j) (hx : IsOptimal I g x) :
    ∃ m : Multipliers D₁ S, m.Nonneg ∧ lagrangian I g x m = F0 I g x ∧
      ∀ z, F0 I g x ≤ lagrangian I g z m := by
  have hxe := off_edge I g x hx
  have hc0 : ∀ j, 0 ≤ cc I g x j := fun j => hgm.deriv_nonneg
  obtain ⟨⟨⟨y0, hy0, hy0w⟩, hub⟩, ⟨α, β, hdf, hobj⟩, -⟩ :=
    lp1_duality (fun i j => I.E (Sum.inl i) j) (cc I g x) hc0
      (Finset.univ : Finset D₁) (Finset.univ : Finset S)
  have hxfm : IsFracMatching (fun i j => I.E (Sum.inl i) j) Finset.univ Finset.univ x := by
    refine ⟨hx.1.1, fun i j h => ⟨?_, mem_univ _, mem_univ _⟩, hx.1.2.2.1, hx.1.2.2.2⟩
    by_contra hE; exact h (hxe i j hE)
  have hy0e : ∀ i j, ¬ I.E (Sum.inl i) j → y0 i j = 0 := by
    intro i j hE; by_contra h; exact hE (hy0.2.1 i j h).1
  have hy0f : IsFeasible I y0 := ⟨hy0.1, hy0e, hy0.2.2.1, hy0.2.2.2⟩
  have hfo := first_order I g x hgd hw hx y0 hy0f
  rw [← fracWeight_eq I y0 hy0e, ← fracWeight_eq I x hxe] at hfo
  have hxw := hub x hxfm
  -- `P x = Σ α + Σ β`
  have hPx : ∑ j, cc I g x j * supplyLoad I x j = ∑ i, α i + ∑ j, β j := by
    rw [← fracWeight_eq I x hxe]
    unfold dualObj at hobj
    linarith
  let ms : Multipliers D₁ S :=
    ⟨α, β, fun i j => if I.E (Sum.inl i) j then α i + β j - cc I g x j else 0⟩
  have hms : ms.Nonneg := by
    refine ⟨fun i => hdf.1 i (mem_univ _), fun j => hdf.2.1 j (mem_univ _), fun i j => ?_⟩
    show 0 ≤ (if I.E (Sum.inl i) j then α i + β j - cc I g x j else 0)
    split_ifs with h
    · linarith [hdf.2.2 i (mem_univ _) j (mem_univ _) h]
    · exact le_rfl
  have hlin : ∀ z, linPart I ms z = ∑ j, cc I g x j * supplyLoad I z j - (∑ i, α i + ∑ j, β j) := by
    intro z
    have hg : gamSum I ms z = ∑ i, α i * demandLoad I z i + ∑ j, β j * supplyLoad I z j -
        ∑ j, cc I g x j * supplyLoad I z j := by
      unfold gamSum
      have : ∀ i, ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j),
          ms.gam i j * z i j =
          α i * demandLoad I z i +
          ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), β j * z i j -
          ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), cc I g x j * z i j := by
        intro i
        unfold demandLoad
        rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hE : I.E (Sum.inl i) j := (mem_filter.mp hj).2
        show (if I.E (Sum.inl i) j then α i + β j - cc I g x j else 0) * z i j = _
        rw [if_pos hE]; ring
      rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, sum_add_distrib, edge_swap, edge_swap]
    unfold linPart
    rw [hg]
    show ∑ i, α i * (demandLoad I z i - 1) + ∑ j, β j * (supplyLoad I z j - 1) - _ = _
    simp only [mul_sub, mul_one, sum_sub_distrib]
    ring
  refine ⟨ms, hms, ?_, ?_⟩
  · rw [lag_eq, hlin, hPx]; ring
  · intro z
    rw [lag_eq, hlin]
    have hconv : ∀ j, (1 / I.w j) * g (I.w j * (1 - supplyLoad I x j)) -
        cc I g x j * (supplyLoad I z j - supplyLoad I x j) ≤
        (1 / I.w j) * g (I.w j * (1 - supplyLoad I z j)) := by
      intro j
      have hwj := hw j
      have := grad_ineq hgd hgc (I.w j * (1 - supplyLoad I x j)) (I.w j * (1 - supplyLoad I z j))
      have h2 := mul_le_mul_of_nonneg_left this (le_of_lt (one_div_pos.mpr hwj))
      have e : (1 / I.w j) * (g (I.w j * (1 - supplyLoad I x j)) +
          deriv g (I.w j * (1 - supplyLoad I x j)) *
            (I.w j * (1 - supplyLoad I z j) - I.w j * (1 - supplyLoad I x j))) =
          (1 / I.w j) * g (I.w j * (1 - supplyLoad I x j)) -
            cc I g x j * (supplyLoad I z j - supplyLoad I x j) := by
        unfold cc; field_simp; ring
      linarith
    have hs := sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset S)) => hconv j
    rw [sum_sub_distrib] at hs
    have e2 : ∑ j, cc I g x j * (supplyLoad I z j - supplyLoad I x j) =
        ∑ j, cc I g x j * supplyLoad I z j - ∑ j, cc I g x j * supplyLoad I x j := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    unfold F0
    linarith

/-- edge perturbation -/
lemma edge_pert (i0 : D₁) (j0 : S) (h0 : I.E (Sum.inl i0) j0) :
    let d : D₁ → S → ℝ := fun i j => if i = i0 ∧ j = j0 then 1 else 0
    (∀ j, supplyLoad I d j = if j = j0 then 1 else 0) ∧
    (∀ i, demandLoad I d i = if i = i0 then 1 else 0) ∧
    (∀ m : Multipliers D₁ S, gamSum I m d = m.gam i0 j0) := by
  intro d
  refine ⟨fun j => ?_, fun i => ?_, fun m => ?_⟩
  · unfold supplyLoad
    by_cases hj : j = j0
    · subst hj
      rw [if_pos rfl, sum_eq_single_of_mem i0 (by simp [h0])]
      · simp [d]
      · intro b _ hb; simp [d, hb]
    · rw [if_neg hj]; exact sum_eq_zero fun i _ => by simp [d, hj]
  · unfold demandLoad
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl, sum_eq_single_of_mem j0 (by simp [h0])]
      · simp [d]
      · intro b _ hb; simp [d, hb]
    · rw [if_neg hi]; exact sum_eq_zero fun j _ => by simp [d, hi]
  · unfold gamSum
    rw [sum_eq_single_of_mem i0 (mem_univ _)]
    · rw [sum_eq_single_of_mem j0 (by simp [h0])]
      · simp [d]
      · intro b _ hb; simp [d, hb]
    · intro b _ hb; exact sum_eq_zero fun j _ => by simp [d, hb]

end main

end TSMec1

open TwoStageMatch TSMec1 in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
    (x : D₁ → S → ℝ) (hx : IsOptimal I g x) :
    (minimax I g = maximin I g ∧
      maximin I g = ⨆ (m : Multipliers D₁ S) (_ : m.Nonneg), (lagrangian I g x m : EReal)) ∧
    (∃ m : Multipliers D₁ S, m.Nonneg ∧ dualFunction I g m = maximin I g) ∧
    (∃ m : Multipliers D₁ S, m.Nonneg ∧
      (lagrangian I g x m : EReal) =
        ⨆ (m' : Multipliers D₁ S) (_ : m'.Nonneg), (lagrangian I g x m' : EReal)) ∧
    ∀ m : Multipliers D₁ S, m.Nonneg → dualFunction I g m = maximin I g →
      ∀ i j, I.E (Sum.inl i) j →
        (-deriv g (I.w j * (1 - supplyLoad I x j)) + m.lam i + m.theta j - m.gam i j = 0) ∧
        (0 ≤ m.lam i ∧ 0 ≤ m.theta j ∧ 0 ≤ m.gam i j) ∧
        (m.gam i j = 0 ∨ (0 < m.gam i j ∧ x i j = 0)) ∧
        (m.lam i = 0 ∨ (0 < m.lam i ∧ demandLoad I x i = 1)) ∧
        (m.theta j = 0 ∨ (0 < m.theta j ∧ supplyLoad I x j = 1)) := by
  classical
  have hcv : ConvexOn ℝ Set.univ g := hgc.convexOn
  have hxe := off_edge I g x hx
  set F := F0 I g x with hF
  obtain ⟨ms, hms, hLms, hmin⟩ := exists_kkt I g x hgd hgm hcv hw hx
  have hLle : ∀ m : Multipliers D₁ S, m.Nonneg → lagrangian I g x m ≤ F := by
    intro m hm; rw [lag_eq]; linarith [linPart_nonpos I g x hx m hm]
  have hL0 : lagrangian I g x m0 = F := by rw [lag_eq, linPart_m0]; simp [hF]
  have hpv : (⨆ (m : Multipliers D₁ S) (_ : m.Nonneg), (lagrangian I g x m : EReal)) = F :=
    le_antisymm (iSup₂_le fun m hm => EReal.coe_le_coe_iff.mpr (hLle m hm))
      (le_iSup₂_of_le m0 m0_nonneg (by rw [hL0]))
  have hminimax : minimax I g = F := by
    unfold minimax
    refine le_antisymm (iInf_le_of_le x ?_) (le_iInf fun z => ?_)
    · unfold primalValue; rw [hpv]
    · unfold primalValue
      exact le_iSup₂_of_le ms hms (EReal.coe_le_coe_iff.mpr (hmin z))
  have hdual : dualFunction I g ms = F := by
    unfold dualFunction
    exact le_antisymm (iInf_le_of_le x (by rw [hLms]))
      (le_iInf fun z => EReal.coe_le_coe_iff.mpr (hmin z))
  have hmaximin : maximin I g = F := by
    unfold maximin
    refine le_antisymm (iSup₂_le fun m hm => ?_) (le_iSup₂_of_le ms hms hdual.ge)
    unfold dualFunction
    exact iInf_le_of_le x (EReal.coe_le_coe_iff.mpr (hLle m hm))
  refine ⟨⟨by rw [hminimax, hmaximin], by rw [hmaximin, hpv]⟩, ⟨ms, hms, by rw [hdual, hmaximin]⟩,
    ⟨m0, m0_nonneg, by rw [hpv, hL0]⟩, ?_⟩
  intro m hm hd i0 j0 hE
  rw [hmaximin] at hd
  have hge : ∀ z, F ≤ lagrangian I g z m := by
    intro z
    have : dualFunction I g m ≤ (lagrangian I g z m : EReal) := iInf_le _ z
    rw [hd] at this
    exact EReal.coe_le_coe_iff.mp this
  have hLx : lagrangian I g x m = F := le_antisymm (hLle m hm) (hge x)
  have hlin0 : linPart I m x = 0 := by rw [lag_eq] at hLx; linarith
  -- complementary slackness
  have h1 : ∑ i, m.lam i * (demandLoad I x i - 1) ≤ 0 := by
    apply sum_nonpos; intro i _
    rw [dl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.1 i) (by linarith [hx.1.2.2.1 i])
  have h2 : ∑ j, m.theta j * (supplyLoad I x j - 1) ≤ 0 := by
    apply sum_nonpos; intro j _
    rw [sl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.2.1 j) (by linarith [hx.1.2.2.2 j])
  have h3 : 0 ≤ gamSum I m x := by
    unfold gamSum
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hm.2.2 i j) (hx.1.1 i j)
  unfold linPart at hlin0
  have e1 : ∑ i, m.lam i * (demandLoad I x i - 1) = 0 := by linarith
  have e2 : ∑ j, m.theta j * (supplyLoad I x j - 1) = 0 := by linarith
  have e3 : gamSum I m x = 0 := by linarith
  have cs1 : m.lam i0 * (demandLoad I x i0 - 1) = 0 := by
    refine (sum_eq_zero_iff_of_nonpos (fun i _ => ?_)).mp e1 i0 (mem_univ _)
    rw [dl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.1 i) (by linarith [hx.1.2.2.1 i])
  have cs2 : m.theta j0 * (supplyLoad I x j0 - 1) = 0 := by
    refine (sum_eq_zero_iff_of_nonpos (fun j _ => ?_)).mp e2 j0 (mem_univ _)
    rw [sl_eq_sum I x hxe]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.2.1 j) (by linarith [hx.1.2.2.2 j])
  have cs3 : m.gam i0 j0 * x i0 j0 = 0 := by
    unfold gamSum at e3
    have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (hm.2.2 i j) (hx.1.1 i j))).mp e3 i0 (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hm.2.2 i0 j) (hx.1.1 i0 j))).mp hi j0
      (by simp [hE])
  -- stationarity
  obtain ⟨hsd, hdd, hgd'⟩ := edge_pert I i0 j0 hE
  set d : D₁ → S → ℝ := fun i j => if i = i0 ∧ j = j0 then 1 else 0 with hd'
  have hder : HasDerivAt (fun t => lagrangian I g (fun i j => x i j + t * d i j) m)
      (∑ j, -(deriv g (I.w j * (1 - supplyLoad I x j)) * supplyLoad I d j) + linD I m d) 0 := by
    have := (F0_hasDeriv I g hgd hw x d).add ((hasDerivAt_id (0:ℝ)).mul_const (linD I m d)
      |>.const_add (linPart I m x))
    have hfun : (fun t => lagrangian I g (fun i j => x i j + t * d i j) m) =
        fun t => F0 I g (fun i j => x i j + t * d i j) + (linPart I m x + id t * linD I m d) := by
      funext t; rw [lag_eq, lin_line]; rfl
    rw [hfun]
    exact this.congr_deriv (by simp)
  have hlocmin : IsLocalMin (fun t => lagrangian I g (fun i j => x i j + t * d i j) m) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    have hx0 : (fun i j => x i j + (0:ℝ) * d i j) = x := by funext i j; simp
    simp only [hx0, hLx]
    exact hge _
  have hz := hlocmin.hasDerivAt_eq_zero hder
  have hsum : ∑ j, -(deriv g (I.w j * (1 - supplyLoad I x j)) * supplyLoad I d j) =
      -deriv g (I.w j0 * (1 - supplyLoad I x j0)) := by
    simp only [hsd, mul_ite, mul_one, mul_zero, sum_neg_distrib, sum_ite_eq', mem_univ, if_true]
  have hlinD : linD I m d = m.lam i0 + m.theta j0 - m.gam i0 j0 := by
    unfold linD
    simp only [hsd, hdd, hgd', mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [hsum, hlinD] at hz
  refine ⟨by linarith, ⟨hm.1 i0, hm.2.1 j0, hm.2.2 i0 j0⟩, ?_, ?_, ?_⟩
  · rcases (hm.2.2 i0 j0).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h, (mul_eq_zero.mp cs3).resolve_left h.ne'⟩
  · rcases (hm.1 i0).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h, by linarith [(mul_eq_zero.mp cs1).resolve_left h.ne']⟩
  · rcases (hm.2.1 j0).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h, by linarith [(mul_eq_zero.mp cs2).resolve_left h.ne']⟩
