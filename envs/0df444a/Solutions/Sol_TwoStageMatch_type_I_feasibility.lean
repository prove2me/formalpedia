-- Prove2me | solution 1 for TwoStageMatch.type_I_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:41:31.846184+00:00
-- url     : https://prove2.me/submissions/184ffd06-f04d-40fe-aa9e-e09dad01f43b

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment

namespace Aux_TSM_L1

open TwoStageMatch

variable {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq S]

/-! ### The objective and first-order exchange arguments -/

noncomputable def H (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (k : S) (t : ℝ) : ℝ :=
  (1 / I.w k) * g (I.w k * (1 - t))

lemma objective_eq (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) :
    objective I g x = ∑ k, H I g k (load x k) := rfl

lemma strictMono_g (g : ℝ → ℝ) (hgm : Monotone g) (hgc : StrictConvexOn ℝ Set.univ g) :
    StrictMono g := by
  intro a b hab
  rcases lt_or_eq_of_le (hgm hab.le) with h | h
  · exact h
  · exfalso
    have hm := hgc.2 (Set.mem_univ a) (Set.mem_univ b) (ne_of_lt hab)
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at hm
    have h2 : g a ≤ g (1 / 2 * a + 1 / 2 * b) := hgm (by linarith)
    linarith

lemma load_le_one (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) (j : S) :
    load x j ≤ 1 := hx.2.2.2 j

lemma load_nonneg (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) (j : S) :
    0 ≤ load x j := by
  unfold load
  exact Finset.sum_nonneg (fun i _ => hx.1 i j)

lemma edge_of_pos (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) (i : D₁)
    (j : S) (h : 0 < x i j) : I.E (Sum.inl i) j := by
  by_contra hE
  rw [hx.2.1 i j hE] at h
  exact lt_irrefl _ h

lemma row_pert (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) (hx : IsOptimal I g x)
    (i : D₁) (v : S → ℝ) (h0 : ∀ b, 0 ≤ x i b + v b)
    (hE : ∀ b, ¬ I.E (Sum.inl i) b → v b = 0)
    (hrow : ∑ b, x i b + ∑ b, v b ≤ 1) (hcol : ∀ b, load x b + v b ≤ 1) :
    objective I g x ≤ ∑ k, H I g k (load x k + v k) := by
  obtain ⟨⟨hx0, hxE, hxr, _⟩, hmin⟩ := hx
  obtain ⟨x', hx'⟩ : ∃ x' : D₁ → S → ℝ, x' = fun a b => x a b + (if a = i then v b else 0) :=
    ⟨_, rfl⟩
  have hx'ab : ∀ a b, x' a b = x a b + (if a = i then v b else 0) := by
    intro a b
    rw [hx']
  have hcolsum : ∀ b, load x' b = load x b + v b := by
    intro b
    unfold load
    rw [Finset.sum_congr rfl (fun a _ => hx'ab a b), Finset.sum_add_distrib,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hfeas : IsFeasible I x' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b
      rw [hx'ab]
      by_cases ha : a = i
      · rw [if_pos ha, ha]
        exact h0 b
      · rw [if_neg ha, add_zero]
        exact hx0 a b
    · intro a b hab
      rw [hx'ab, hxE a b hab]
      by_cases ha : a = i
      · rw [if_pos ha]
        rw [ha] at hab
        rw [hE b hab, add_zero]
      · rw [if_neg ha, add_zero]
    · intro a
      rw [Finset.sum_congr rfl (fun b _ => hx'ab a b), Finset.sum_add_distrib]
      by_cases ha : a = i
      · rw [Finset.sum_congr rfl (fun b _ => (if_pos ha : (if a = i then v b else 0) = v b)), ha]
        exact hrow
      · rw [Finset.sum_congr rfl (fun b _ => (if_neg ha : (if a = i then v b else 0) = 0)),
          Finset.sum_const_zero, add_zero]
        exact hxr a
    · intro b
      have h1 := hcolsum b
      unfold load at h1
      rw [h1]
      exact hcol b
  have hle := (isMinOn_iff.mp hmin) x' hfeas
  rw [objective_eq I g x'] at hle
  simp only [hcolsum] at hle
  exact hle

/-- Exchange: moving mass of demand `i` from `j` to an unsaturated neighbour `j'` cannot help. -/
lemma exch (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgc : StrictConvexOn ℝ Set.univ g)
    (hw : ∀ j, 0 < I.w j) (x : D₁ → S → ℝ) (hx : IsOptimal I g x)
    (i : D₁) (j j' : S) (hij : 0 < x i j) (hE' : I.E (Sum.inl i) j') (hy' : load x j' < 1) :
    I.w j' * (1 - load x j') ≤ I.w j * (1 - load x j) := by
  by_cases hjj : j = j'
  · subst hjj
    exact le_refl _
  by_contra hlt
  push_neg at hlt
  have hfeas := hx.1
  have hjj' : j' ≠ j := fun h => hjj h.symm
  have hwj := hw j
  have hwj' := hw j'
  have hyj := load_le_one I x hfeas j
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = I.w j * (1 - load x j) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = I.w j' * (1 - load x j') := ⟨_, rfl⟩
  have hab : a < b := by rw [ha, hb]; exact hlt
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ,
      ε = min (x i j) (min (1 - load x j') ((b - a) / (2 * (I.w j + I.w j')))) := ⟨_, rfl⟩
  have hden : 0 < 2 * (I.w j + I.w j') := by linarith
  have hε1 : ε ≤ x i j := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ 1 - load x j' := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ (b - a) / (2 * (I.w j + I.w j')) := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hba : 0 < b - a := by linarith
  have hy1 : 0 < 1 - load x j' := by linarith
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_min hij (lt_min hy1 (div_pos hba hden))
  have hε3' : ε * (2 * (I.w j + I.w j')) ≤ b - a := (le_div_iff₀ hden).mp hε3
  obtain ⟨v, hv⟩ : ∃ v : S → ℝ,
      v = fun k => (if k = j' then ε else 0) - (if k = j then ε else 0) := ⟨_, rfl⟩
  have hvk : ∀ k, v k = (if k = j' then ε else 0) - (if k = j then ε else 0) := by
    intro k
    rw [hv]
  have hvj : v j = -ε := by rw [hvk, if_neg hjj, if_pos rfl, zero_sub]
  have hvj' : v j' = ε := by rw [hvk, if_pos rfl, if_neg hjj', sub_zero]
  have hEj : I.E (Sum.inl i) j := edge_of_pos I x hfeas i j hij
  have h0 : ∀ k, 0 ≤ x i k + v k := by
    intro k
    by_cases h1 : k = j'
    · rw [h1, hvj']
      linarith [hfeas.1 i j']
    · by_cases h2 : k = j
      · rw [h2, hvj]
        linarith
      · rw [hvk, if_neg h1, if_neg h2]
        linarith [hfeas.1 i k]
  have hE0 : ∀ k, ¬ I.E (Sum.inl i) k → v k = 0 := by
    intro k hk
    have h1 : k ≠ j' := fun h => hk (by rw [h]; exact hE')
    have h2 : k ≠ j := fun h => hk (by rw [h]; exact hEj)
    rw [hvk, if_neg h1, if_neg h2, sub_zero]
  have hvsum : ∑ k, v k = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => hvk k), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (Finset.mem_univ j'), if_pos (Finset.mem_univ j), sub_self]
  have hrow : ∑ k, x i k + ∑ k, v k ≤ 1 := by
    rw [hvsum, add_zero]
    exact hfeas.2.2.1 i
  have hcol : ∀ k, load x k + v k ≤ 1 := by
    intro k
    by_cases h1 : k = j'
    · rw [h1, hvj']
      linarith
    · by_cases h2 : k = j
      · rw [h2, hvj]
        linarith
      · rw [hvk, if_neg h1, if_neg h2]
        linarith [load_le_one I x hfeas k]
  have hle := row_pert I g x hx i v h0 hE0 hrow hcol
  rw [objective_eq] at hle
  have hsplit : ∑ k, (H I g k (load x k + v k) - H I g k (load x k)) =
      (H I g j (load x j + v j) - H I g j (load x j)) +
        (H I g j' (load x j' + v j') - H I g j' (load x j')) :=
    Fintype.sum_eq_add j j' hjj (fun k hk => by
      rw [hvk k, if_neg hk.2, if_neg hk.1, sub_zero, add_zero, sub_self])
  rw [Finset.sum_sub_distrib, hvj, hvj'] at hsplit
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = a + I.w j * ε := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = b - I.w j' * ε := ⟨_, rfl⟩
  have hap : a < p := by
    rw [hp]
    nlinarith [mul_pos hwj hε0]
  have hpq : p < q := by
    rw [hp, hq]
    nlinarith [mul_pos hwj hε0, mul_pos hwj' hε0, hε3']
  have hqb : q < b := by
    rw [hq]
    nlinarith [mul_pos hwj' hε0]
  have hs1 := hgc.slope_strict_mono_adjacent (Set.mem_univ a) (Set.mem_univ q) hap hpq
  have hs2 := hgc.slope_strict_mono_adjacent (Set.mem_univ p) (Set.mem_univ b) hpq hqb
  have e1 : g p - g a = (g p - g a) / (p - a) * (I.w j * ε) := by
    have h1 : p - a = I.w j * ε := by rw [hp]; ring
    rw [← h1, div_mul_cancel₀ _ (sub_pos.mpr hap).ne']
  have e3 : g b - g q = (g b - g q) / (b - q) * (I.w j' * ε) := by
    have h1 : b - q = I.w j' * ε := by rw [hq]; ring
    rw [← h1, div_mul_cancel₀ _ (sub_pos.mpr hqb).ne']
  have hHj : H I g j (load x j + -ε) - H I g j (load x j) = (g p - g a) / (p - a) * ε := by
    unfold H
    have harg : I.w j * (1 - (load x j + -ε)) = p := by rw [hp, ha]; ring
    rw [harg, ← ha]
    calc 1 / I.w j * g p - 1 / I.w j * g a = 1 / I.w j * (g p - g a) := by ring
      _ = 1 / I.w j * ((g p - g a) / (p - a) * (I.w j * ε)) := by rw [← e1]
      _ = (g p - g a) / (p - a) * ε * (I.w j * (1 / I.w j)) := by ring
      _ = (g p - g a) / (p - a) * ε := by rw [mul_one_div_cancel hwj.ne', mul_one]
  have hHj' : H I g j' (load x j' + ε) - H I g j' (load x j') =
      -((g b - g q) / (b - q) * ε) := by
    unfold H
    have harg : I.w j' * (1 - (load x j' + ε)) = q := by rw [hq, hb]; ring
    rw [harg, ← hb]
    calc 1 / I.w j' * g q - 1 / I.w j' * g b = -(1 / I.w j' * (g b - g q)) := by ring
      _ = -(1 / I.w j' * ((g b - g q) / (b - q) * (I.w j' * ε))) := by rw [← e3]
      _ = -((g b - g q) / (b - q) * ε * (I.w j' * (1 / I.w j'))) := by ring
      _ = -((g b - g q) / (b - q) * ε) := by rw [mul_one_div_cancel hwj'.ne', mul_one]
  have hfin : (g p - g a) / (p - a) * ε < (g b - g q) / (b - q) * ε :=
    mul_lt_mul_of_pos_right (hs1.trans hs2) hε0
  linarith

/-- An unsaturated demand cannot have an unsaturated neighbour. -/
lemma unsat (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (x : D₁ → S → ℝ)
    (hx : IsOptimal I g x) (i : D₁) (j' : S) (hrow : ∑ b, x i b < 1)
    (hE' : I.E (Sum.inl i) j') (hy' : load x j' < 1) : False := by
  have hsm := strictMono_g g hgm hgc
  have hfeas := hx.1
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1 - ∑ b, x i b) (1 - load x j') := ⟨_, rfl⟩
  have hr1 : 0 < 1 - ∑ b, x i b := by linarith
  have hy1 : 0 < 1 - load x j' := by linarith
  have hε0 : 0 < ε := by rw [hε]; exact lt_min hr1 hy1
  have hε1 : ε ≤ 1 - ∑ b, x i b := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ 1 - load x j' := by rw [hε]; exact min_le_right _ _
  obtain ⟨v, hv⟩ : ∃ v : S → ℝ, v = fun k => if k = j' then ε else 0 := ⟨_, rfl⟩
  have hvk : ∀ k, v k = if k = j' then ε else 0 := by
    intro k
    rw [hv]
  have hvj' : v j' = ε := by rw [hvk, if_pos rfl]
  have h0 : ∀ k, 0 ≤ x i k + v k := by
    intro k
    by_cases h1 : k = j'
    · rw [h1, hvj']
      linarith [hfeas.1 i j']
    · rw [hvk, if_neg h1]
      linarith [hfeas.1 i k]
  have hE0 : ∀ k, ¬ I.E (Sum.inl i) k → v k = 0 := by
    intro k hk
    have h1 : k ≠ j' := fun h => hk (by rw [h]; exact hE')
    rw [hvk, if_neg h1]
  have hvsum : ∑ k, v k = ε := by
    rw [Finset.sum_congr rfl (fun k _ => hvk k), Finset.sum_ite_eq',
      if_pos (Finset.mem_univ j')]
  have hrow' : ∑ k, x i k + ∑ k, v k ≤ 1 := by
    rw [hvsum]
    linarith
  have hcol : ∀ k, load x k + v k ≤ 1 := by
    intro k
    by_cases h1 : k = j'
    · rw [h1, hvj']
      linarith
    · rw [hvk, if_neg h1]
      linarith [load_le_one I x hfeas k]
  have hle := row_pert I g x hx i v h0 hE0 hrow' hcol
  rw [objective_eq] at hle
  have hsplit : ∑ k, (H I g k (load x k + v k) - H I g k (load x k)) =
      H I g j' (load x j' + v j') - H I g j' (load x j') :=
    Fintype.sum_eq_single j' (fun k hk => by rw [hvk k, if_neg hk, add_zero, sub_self])
  rw [Finset.sum_sub_distrib, hvj'] at hsplit
  have hlt : H I g j' (load x j' + ε) < H I g j' (load x j') := by
    unfold H
    refine mul_lt_mul_of_pos_left ?_ (one_div_pos.mpr (hw j'))
    apply hsm
    nlinarith [mul_pos (hw j') hε0]
  linarith

/-! ### Basic facts on `S0`, `D0`, and the support graph -/

lemma mem_S0 (x : D₁ → S → ℝ) (j : S) : j ∈ S0 x ↔ load x j = 1 := by
  unfold S0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_D0 (x : D₁ → S → ℝ) (i : D₁) : i ∈ D0 x ↔ ∃ j ∈ S0 x, 0 < x i j := by
  unfold D0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma load_lt (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) (j : S)
    (hj : j ∉ S0 x) : load x j < 1 :=
  lt_of_le_of_ne (load_le_one I x hx j) (fun h => hj ((mem_S0 x j).2 h))

lemma c_zero (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (j : S) (hj : j ∈ S0 x) :
    I.w j * (1 - load x j) = 0 := by
  rw [(mem_S0 x j).1 hj, sub_self, mul_zero]

lemma c_nonneg (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x) (j : S) :
    0 ≤ I.w j * (1 - load x j) := by
  have h1 := load_le_one I x hx j
  exact mul_nonneg (I.w_nonneg j) (by linarith)

lemma adj_of_pos (x : D₁ → S → ℝ) (i : D₁) (j : S) (h : 0 < x i j) :
    (supportGraph x).Adj (Sum.inl i) (Sum.inr j) := by
  unfold supportGraph
  rw [SimpleGraph.fromRel_adj]
  exact ⟨Sum.inl_ne_inr, Or.inl ⟨i, j, rfl, rfl, h⟩⟩

lemma adj_inl (x : D₁ → S → ℝ) (i : D₁) (v : D₁ ⊕ S)
    (h : (supportGraph x).Adj (Sum.inl i) v) : ∃ j, v = Sum.inr j ∧ 0 < x i j := by
  unfold supportGraph at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨i', j, h1, h2, h3⟩ := h
    have h4 : i = i' := Sum.inl_injective h1
    subst h4
    exact ⟨j, h2, h3⟩
  · obtain ⟨i', j, _, h2, _⟩ := h
    exact absurd h2 Sum.inl_ne_inr

lemma res_inl (x : D₁ → S → ℝ) (i : D₁)
    (h : (Sum.inl i : D₁ ⊕ S) ∈ residualVertices x) : i ∉ D0 x := by
  unfold residualVertices at h
  rw [Set.mem_setOf_eq] at h
  rcases h with ⟨i', h1, h2⟩ | ⟨j, h1, _⟩
  · rw [Sum.inl_injective h1]
    exact h2
  · exact absurd h1 Sum.inl_ne_inr

lemma levelD_of_mem (x : D₁ → S → ℝ) (i : D₁) (h : i ∈ D0 x) : levelD x i = none := by
  unfold levelD
  rw [dif_pos h]

lemma levelD_of_not (x : D₁ → S → ℝ) (i : D₁) (h : i ∉ D0 x) :
    levelD x i = some ((residualGraph x).connectedComponentMk ⟨Sum.inl i, Or.inl ⟨i, rfl, h⟩⟩) := by
  unfold levelD
  rw [dif_neg h]

lemma levelS_of_mem (x : D₁ → S → ℝ) (j : S) (h : j ∈ S0 x) : levelS x j = none := by
  unfold levelS
  rw [dif_pos h]

lemma levelS_of_not (x : D₁ → S → ℝ) (j : S) (h : j ∉ S0 x) :
    levelS x j = some ((residualGraph x).connectedComponentMk ⟨Sum.inr j, Or.inr ⟨j, rfl, h⟩⟩) := by
  unfold levelS
  rw [dif_neg h]

lemma levelSlack_none (w : S → ℝ) (x : D₁ → S → ℝ) : levelSlack w x none = 0 := rfl

lemma levelSlack_some_pos (w : S → ℝ) (x : D₁ → S → ℝ) (K : (residualGraph x).ConnectedComponent)
    (h : ∃ j, levelS x j = some K) :
    levelSlack w x (some K) = w h.choose * (1 - load x h.choose) := by
  first
  | exact dif_pos h
  | (simp only [levelSlack]; rw [dif_pos h])

lemma levelSlack_some_neg (w : S → ℝ) (x : D₁ → S → ℝ) (K : (residualGraph x).ConnectedComponent)
    (h : ¬ ∃ j, levelS x j = some K) : levelSlack w x (some K) = 0 := by
  first
  | exact dif_neg h
  | (simp only [levelSlack]; rw [dif_neg h])

lemma levelSlack_nonneg (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (hx : IsFeasible I x)
    (L : Level x) : 0 ≤ levelSlack I.w x L := by
  cases L with
  | none => exact le_refl _
  | some K =>
    by_cases hK : ∃ j, levelS x j = some K
    · rw [levelSlack_some_pos I.w x K hK]
      exact c_nonneg I x hx _
    · rw [levelSlack_some_neg I.w x K hK]

lemma walk_const {V : Type*} {G : SimpleGraph V} (F : V → ℝ)
    (hF : ∀ u v, G.Adj u v → F u = F v) {u v : V} (p : G.Walk u v) : F u = F v := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hF _ _ h).trans ih

lemma exists_adj_of_reach {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Reachable u v)
    (hne : u ≠ v) : ∃ w, G.Adj u w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ => exact ⟨_, h⟩

open Classical in
noncomputable def Fv (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) : D₁ ⊕ S → ℝ :=
  Sum.elim (fun i => if h : ∃ j, 0 < x i j then I.w h.choose * (1 - load x h.choose) else 0)
    (fun j => I.w j * (1 - load x j))

lemma Fv_inr (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (j : S) :
    Fv I x (Sum.inr j) = I.w j * (1 - load x j) := rfl

lemma Fv_inl (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (i : D₁) (h : ∃ j, 0 < x i j) :
    Fv I x (Sum.inl i) = I.w h.choose * (1 - load x h.choose) := by
  unfold Fv
  exact dif_pos h

section Opt

variable (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgm : Monotone g)
  (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
  (x : D₁ → S → ℝ) (hx : IsOptimal I g x)

include hgc hw hx in
lemma pair_eq (i : D₁) (hi : i ∉ D0 x) (j j' : S) (h1 : 0 < x i j) (h2 : 0 < x i j') :
    I.w j * (1 - load x j) = I.w j' * (1 - load x j') := by
  have hj : j ∉ S0 x := fun hm => hi ((mem_D0 x i).2 ⟨j, hm, h1⟩)
  have hj' : j' ∉ S0 x := fun hm => hi ((mem_D0 x i).2 ⟨j', hm, h2⟩)
  exact le_antisymm
    (exch I g hgc hw x hx i j' j h2 (edge_of_pos I x hx.1 i j h1) (load_lt I x hx.1 j hj))
    (exch I g hgc hw x hx i j j' h1 (edge_of_pos I x hx.1 i j' h2) (load_lt I x hx.1 j' hj'))

include hgc hw hx in
lemma Fv_adj (u v : residualVertices x) (h : (residualGraph x).Adj u v) :
    Fv I x u.1 = Fv I x v.1 := by
  have h' : (supportGraph x).Adj u.1 v.1 := h
  unfold supportGraph at h'
  rw [SimpleGraph.fromRel_adj] at h'
  obtain ⟨_, h' | h'⟩ := h'
  · obtain ⟨i, j, hu, hv, hp⟩ := h'
    have hmem : (Sum.inl i : D₁ ⊕ S) ∈ residualVertices x := by rw [← hu]; exact u.2
    have hi : i ∉ D0 x := res_inl x i hmem
    have hex : ∃ j', 0 < x i j' := ⟨j, hp⟩
    rw [hu, hv, Fv_inr, Fv_inl I x i hex]
    exact pair_eq I g hgc hw x hx i hi hex.choose j hex.choose_spec hp
  · obtain ⟨i, j, hv, hu, hp⟩ := h'
    have hmem : (Sum.inl i : D₁ ⊕ S) ∈ residualVertices x := by rw [← hv]; exact v.2
    have hi : i ∉ D0 x := res_inl x i hmem
    have hex : ∃ j', 0 < x i j' := ⟨j, hp⟩
    rw [hu, hv, Fv_inr, Fv_inl I x i hex]
    exact (pair_eq I g hgc hw x hx i hi hex.choose j hex.choose_spec hp).symm

include hgc hw hx in
lemma comp_c (j j' : S) (hj : j ∉ S0 x) (hj' : j' ∉ S0 x) (h : levelS x j = levelS x j') :
    I.w j * (1 - load x j) = I.w j' * (1 - load x j') := by
  rw [levelS_of_not x j hj, levelS_of_not x j' hj'] at h
  have h2 := Option.some.inj h
  have h3 := SimpleGraph.ConnectedComponent.eq.mp h2
  obtain ⟨p⟩ := h3
  exact walk_const (fun v : residualVertices x => Fv I x v.1) (Fv_adj I g hgc hw x hx) p

include hgc hw hx in
lemma LS1 (j : S) : I.w j * (1 - load x j) = levelSlack I.w x (levelS x j) := by
  by_cases hj : j ∈ S0 x
  · rw [levelS_of_mem x j hj, levelSlack_none, c_zero I x j hj]
  · obtain ⟨K, hK⟩ : ∃ K, levelS x j = some K := ⟨_, levelS_of_not x j hj⟩
    have hK' : ∃ j', levelS x j' = some K := ⟨j, hK⟩
    rw [hK, levelSlack_some_pos I.w x K hK']
    have hs := hK'.choose_spec
    have hnot : hK'.choose ∉ S0 x := by
      intro hm
      rw [levelS_of_mem x _ hm] at hs
      cases hs
    exact comp_c I g hgc hw x hx j hK'.choose hj hnot (by rw [hs, hK])

include hgc hw hx in
lemma DL (i : D₁) (hi : i ∉ D0 x) (j0 : S) (hp : 0 < x i j0) :
    j0 ∉ S0 x ∧ levelD x i = levelS x j0 := by
  have hj0 : j0 ∉ S0 x := fun hm => hi ((mem_D0 x i).2 ⟨j0, hm, hp⟩)
  refine ⟨hj0, ?_⟩
  rw [levelD_of_not x i hi, levelS_of_not x j0 hj0]
  have hadj : (residualGraph x).Adj ⟨Sum.inl i, Or.inl ⟨i, rfl, hi⟩⟩
      ⟨Sum.inr j0, Or.inr ⟨j0, rfl, hj0⟩⟩ := adj_of_pos x i j0 hp
  exact congrArg some (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hadj))

include hgm hgc hw hx in
lemma clause2 (i : D₁) (j : S) (hE : I.E (Sum.inl i) j) :
    levelSlack I.w x (levelS x j) ≤ levelSlack I.w x (levelD x i) := by
  rw [← LS1 I g hgc hw x hx j]
  by_cases hj : j ∈ S0 x
  · rw [c_zero I x j hj]
    exact levelSlack_nonneg I x hx.1 _
  · by_cases hi : i ∈ D0 x
    · obtain ⟨j0, hj0, hp⟩ := (mem_D0 x i).1 hi
      rw [levelD_of_mem x i hi, levelSlack_none]
      have h1 := exch I g hgc hw x hx i j0 j hp hE (load_lt I x hx.1 j hj)
      rw [c_zero I x j0 hj0] at h1
      exact h1
    · by_cases hex : ∃ j0, 0 < x i j0
      · obtain ⟨j0, hp⟩ := hex
        obtain ⟨_, hlev⟩ := DL I g hgc hw x hx i hi j0 hp
        rw [hlev, ← LS1 I g hgc hw x hx j0]
        exact exch I g hgc hw x hx i j0 j hp hE (load_lt I x hx.1 j hj)
      · push_neg at hex
        have hz : ∑ b, x i b = 0 :=
          Finset.sum_eq_zero (fun b _ => le_antisymm (hex b) (hx.1.1 i b))
        exfalso
        exact unsat I g hgm hgc hw x hx i j (by rw [hz]; norm_num) hE (load_lt I x hx.1 j hj)

lemma not_D0_of_ne_none (i : D₁) (h : levelD x i ≠ none) : i ∉ D0 x := by
  intro hm
  exact h (levelD_of_mem x i hm)

include hgm hgc hw hx in
lemma clause3 (i : D₁) (hne : levelD x i ≠ none) (hex : ∃ j, levelS x j = levelD x i) :
    ∑ j, x i j = 1 := by
  have hi : i ∉ D0 x := not_D0_of_ne_none x i hne
  obtain ⟨j, hj⟩ := hex
  have hjS : j ∉ S0 x := by
    intro hm
    rw [levelS_of_mem x j hm] at hj
    exact hne hj.symm
  rw [levelD_of_not x i hi, levelS_of_not x j hjS] at hj
  have h2 := Option.some.inj hj
  have h3 := (SimpleGraph.ConnectedComponent.eq.mp h2).symm
  have hne' : (⟨Sum.inl i, Or.inl ⟨i, rfl, hi⟩⟩ : residualVertices x) ≠
      ⟨Sum.inr j, Or.inr ⟨j, rfl, hjS⟩⟩ := fun h => Sum.inl_ne_inr (congrArg Subtype.val h)
  obtain ⟨w', hw'⟩ := exists_adj_of_reach h3 hne'
  have hw'' : (supportGraph x).Adj (Sum.inl i) w'.1 := hw'
  obtain ⟨j0, _, hp⟩ := adj_inl x i w'.1 hw''
  obtain ⟨hj0, _⟩ := DL I g hgc hw x hx i hi j0 hp
  by_contra hlt
  have hlt' : ∑ b, x i b < 1 := lt_of_le_of_ne (hx.1.2.2.1 i) hlt
  exact unsat I g hgm hgc hw x hx i j0 hlt' (edge_of_pos I x hx.1 i j0 hp)
    (load_lt I x hx.1 j0 hj0)

include hgm hgc hw hx in
lemma clause4 (i : D₁) (hne : levelD x i ≠ none) (hnex : ¬ ∃ j, levelS x j = levelD x i) :
    (∀ i', levelD x i' = levelD x i → i' = i) ∧
      ∀ j, I.E (Sum.inl i) j → levelS x j = none := by
  have hi : i ∉ D0 x := not_D0_of_ne_none x i hne
  have hno0 : ∀ j0, ¬ 0 < x i j0 := by
    intro j0 hp
    obtain ⟨_, hl⟩ := DL I g hgc hw x hx i hi j0 hp
    exact hnex ⟨j0, hl.symm⟩
  refine ⟨?_, ?_⟩
  · intro i' hi'
    by_contra hne'
    have hi'D : i' ∉ D0 x := by
      intro hm
      rw [levelD_of_mem x i' hm] at hi'
      exact hne hi'.symm
    rw [levelD_of_not x i' hi'D, levelD_of_not x i hi] at hi'
    have h2 := Option.some.inj hi'
    have h3 := (SimpleGraph.ConnectedComponent.eq.mp h2).symm
    have hne'' : (⟨Sum.inl i, Or.inl ⟨i, rfl, hi⟩⟩ : residualVertices x) ≠
        ⟨Sum.inl i', Or.inl ⟨i', rfl, hi'D⟩⟩ := by
      intro h
      have h4 : (Sum.inl i : D₁ ⊕ S) = Sum.inl i' := congrArg Subtype.val h
      exact hne' (Sum.inl_injective h4).symm
    obtain ⟨w', hw'⟩ := exists_adj_of_reach h3 hne''
    have hw'' : (supportGraph x).Adj (Sum.inl i) w'.1 := hw'
    obtain ⟨j0, _, hp⟩ := adj_inl x i w'.1 hw''
    exact hno0 j0 hp
  · intro j hE
    by_contra hjn
    have hjS : j ∉ S0 x := fun hm => hjn (levelS_of_mem x j hm)
    have hz : ∑ b, x i b = 0 :=
      Finset.sum_eq_zero (fun b _ => le_antisymm (not_lt.mp (hno0 b)) (hx.1.1 i b))
    exact unsat I g hgm hgc hw x hx i j (by rw [hz]; norm_num) hE (load_lt I x hx.1 j hjS)

end Opt

end Aux_TSM_L1

lemma Aux_TSM_L1.three_quarter (w y : ℝ) (hw : 0 ≤ w) :
    (3 / 4 : ℝ) * w ≤ w * (1 - y) + w * y ^ 2 := by
  have h := mul_nonneg hw (sq_nonneg (y - 1 / 2))
  nlinarith [h]

open TwoStageMatch in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (r : Run I g) (A : Finset D₂)
    (M : Finset ((D₁ ⊕ D₂) × S)) (hM : IsFirstStageMatching I M)
    (αh : D₁ ⊕ D₂ → ℝ) (βh : S → ℝ)
    (hopt : IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) αh βh ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) αh βh =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) :
    ∀ i j, I.E (Sum.inl i) j →
      levelSlack I.w r.x (levelD r.x i) + I.w j * (load r.x j) ^ 2 ≤
          dualAlpha I r.x αh (Sum.inl i) + dualBeta I r.x M βh j ∧
        levelSlack I.w r.x (levelS r.x j) + I.w j * (load r.x j) ^ 2 ≤
          levelSlack I.w r.x (levelD r.x i) + I.w j * (load r.x j) ^ 2 ∧
        levelSlack I.w r.x (levelS r.x j) + I.w j * (load r.x j) ^ 2 =
          I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 ∧
        (3 / 4 : ℝ) * I.w j ≤ I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 := by
  intro i j hij
  have hx := r.x_opt
  have hA : dualAlpha I r.x αh (Sum.inl i) = levelSlack I.w r.x (levelD r.x i) := rfl
  have hB : dualBeta I r.x M βh j = I.w j * (load r.x j) ^ 2 +
      (if j ∈ Finset.univ \ matchedSupply M then βh j else 0) := rfl
  have hite : 0 ≤ (if j ∈ Finset.univ \ matchedSupply M then βh j else 0) := by
    by_cases hj : j ∈ Finset.univ \ matchedSupply M
    · rw [if_pos hj]
      exact hopt.1.2.1 j hj
    · rw [if_neg hj]
  refine ⟨?_, ?_, ?_, Aux_TSM_L1.three_quarter (I.w j) (load r.x j) (hw j).le⟩
  · rw [hA, hB]
    linarith
  · have h2 := Aux_TSM_L1.clause2 I g hgm hgc hw r.x hx i j hij
    linarith
  · rw [← Aux_TSM_L1.LS1 I g hgc hw r.x hx j]

