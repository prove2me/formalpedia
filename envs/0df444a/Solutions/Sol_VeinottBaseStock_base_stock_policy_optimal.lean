-- Prove2me | solution 1 for VeinottBaseStock.base_stock_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-29T23:58:16.721275+00:00
-- url     : https://prove2.me/submissions/f5354342-b976-446b-8d51-35ceefaa5bc9

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Down-closure (in `EReal^n`) of a set of real vectors. -/
def down {n : ℕ} (C : Set (Fin n → ℝ)) : Set (Fin n → EReal) :=
  {v | ∃ y ∈ C, v ≤ coeVec y}

lemma coeVec_mono {n : ℕ} {y y' : Fin n → ℝ} (h : y ≤ y') : coeVec y ≤ coeVec y' :=
  fun j => EReal.coe_le_coe_iff.mpr (h j)

/-- A compact nonempty chain has a least element. -/
lemma chain_least {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : IsChain (· ≤ ·) K)
    (hne : K.Nonempty) : ∃ a ∈ K, ∀ y ∈ K, a ≤ y := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne
    (f := fun y : Fin n → ℝ => ∑ j, y j)
    (continuous_finsetSum Finset.univ (fun j _ => continuous_apply j)).continuousOn
  refine ⟨a, ha, fun y hy => ?_⟩
  rcases hc.total ha hy with h | h
  · exact h
  · have h1 : ∑ j, a j ≤ ∑ j, y j := hmin hy
    have h2 : ∑ j, y j ≤ ∑ j, a j := Finset.sum_le_sum fun j _ => h j
    have h3 : ∑ j, y j = ∑ j, a j := le_antisymm h2 h1
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => h j)).1 h3
    intro j
    exact le_of_eq (this j (Finset.mem_univ j)).symm

/-- A compact nonempty chain has a greatest element. -/
lemma chain_greatest {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : IsChain (· ≤ ·) K)
    (hne : K.Nonempty) : ∃ a ∈ K, ∀ y ∈ K, y ≤ a := by
  obtain ⟨a, ha, hmax⟩ := hK.exists_isMaxOn hne
    (f := fun y : Fin n → ℝ => ∑ j, y j)
    (continuous_finsetSum Finset.univ (fun j _ => continuous_apply j)).continuousOn
  refine ⟨a, ha, fun y hy => ?_⟩
  rcases hc.total ha hy with h | h
  · have h1 : ∑ j, y j ≤ ∑ j, a j := hmax hy
    have h2 : ∑ j, a j ≤ ∑ j, y j := Finset.sum_le_sum fun j _ => h j
    have h3 : ∑ j, a j = ∑ j, y j := le_antisymm h2 h1
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => h j)).1 h3
    intro j
    exact le_of_eq (this j (Finset.mem_univ j)).symm
  · exact h

lemma closedChain_least {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsClosed S)
    (hc : IsChain (· ≤ ·) S) (b : Fin n → ℝ) (hb : ∀ y ∈ S, b ≤ y) (hne : S.Nonempty) :
    ∃ a, IsLeast S a := by
  obtain ⟨y0, hy0⟩ := hne
  have hK : IsCompact (S ∩ Set.Icc b y0) := (isCompact_Icc).inter_left hS
  obtain ⟨a, ha, hmin⟩ := chain_least hK (hc.mono Set.inter_subset_left)
    ⟨y0, hy0, hb y0 hy0, le_rfl⟩
  refine ⟨a, ha.1, fun y hy => ?_⟩
  rcases hc.total ha.1 hy with h | h
  · exact h
  · exact hmin y ⟨hy, hb y hy, h.trans ha.2.2⟩

lemma closedChain_greatest {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsClosed S)
    (hc : IsChain (· ≤ ·) S) (u : Fin n → ℝ) (hu : ∀ y ∈ S, y ≤ u) (hne : S.Nonempty) :
    ∃ a, IsGreatest S a := by
  obtain ⟨y0, hy0⟩ := hne
  have hK : IsCompact (S ∩ Set.Icc y0 u) := (isCompact_Icc).inter_left hS
  obtain ⟨a, ha, hmax⟩ := chain_greatest hK (hc.mono Set.inter_subset_left)
    ⟨y0, hy0, le_rfl, hu y0 hy0⟩
  refine ⟨a, ha.1, fun y hy => ?_⟩
  rcases hc.total ha.1 hy with h | h
  · exact hmax y ⟨hy, ha.2.1.trans h, hu y hy⟩
  · exact h

lemma measurableSet_down {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsClosed C)
    (hc : IsChain (· ≤ ·) C) : MeasurableSet (down C) := by
  have hunion : down C = ⋃ N : ℕ, down (C ∩ Set.Icc (fun _ => -(N : ℝ)) (fun _ => (N : ℝ))) := by
    ext v
    simp only [down, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hv⟩
      obtain ⟨N, hN⟩ := exists_nat_ge (∑ j, |y j|)
      have hb : ∀ j, |y j| ≤ N := fun j =>
        (Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ j)).trans hN
      refine ⟨N, y, ⟨hy, fun j => ?_, fun j => ?_⟩, hv⟩
      · exact (abs_le.mp (hb j)).1
      · exact (abs_le.mp (hb j)).2
    · rintro ⟨N, y, ⟨hy, _⟩, hv⟩
      exact ⟨y, hy, hv⟩
  rw [hunion]
  refine MeasurableSet.iUnion fun N => ?_
  set K : Set (Fin n → ℝ) := C ∩ Set.Icc (fun _ => -(N : ℝ)) (fun _ => (N : ℝ)) with hK
  by_cases hne : K.Nonempty
  · obtain ⟨g, hg⟩ := closedChain_greatest (hC.inter isClosed_Icc)
      (hc.mono Set.inter_subset_left) (fun _ => (N : ℝ)) (fun y hy => hy.2.2) hne
    have : down K = {v | v ≤ coeVec g} := by
      ext v
      simp only [down, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy, hv⟩
        exact hv.trans (coeVec_mono (hg.2 hy))
      · intro hv
        exact ⟨g, hg.1, hv⟩
    rw [this]
    have h2 : {v : Fin n → EReal | v ≤ coeVec g} = ⋂ j, {v | v j ≤ coeVec g j} := by
      ext v
      simp [Pi.le_def]
    rw [h2]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j) measurable_const
  · have : down K = ∅ := by
      ext v
      simp only [down, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, hy, _⟩
      exact hne ⟨y, hy⟩
    rw [this]
    exact MeasurableSet.empty

section
variable {n m : ℕ}

lemma least_exists (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hY : IsClosed (M.Y k)) (hc : IsChain (· ≤ ·) (M.Y k))
    (hne : ∃ y ∈ M.Y k, M.q k x ≤ coeVec y ∧ ybar k ≤ y) :
    ∃ a, IsLeast (M.orderSet ybar k x) a := by
  have h1 : IsClosed {y : Fin n → ℝ | M.q k x ≤ coeVec y} := by
    have : {y : Fin n → ℝ | M.q k x ≤ coeVec y} = ⋂ j, {y | M.q k x j ≤ ((y j : ℝ) : EReal)} := by
      ext y
      simp [Pi.le_def, coeVec]
    rw [this]
    exact isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_coe_real_ereal.comp (continuous_apply j))
  have hcl : IsClosed (M.orderSet ybar k x) := by
    have : M.orderSet ybar k x = M.Y k ∩ ({y | M.q k x ≤ coeVec y} ∩ Set.Ici (ybar k)) := rfl
    rw [this]
    exact hY.inter (h1.inter isClosed_Ici)
  obtain ⟨y, hy, hqy, hby⟩ := hne
  exact closedChain_least hcl (hc.mono Set.inter_subset_left) (ybar k)
    (fun z hz => hz.2.2) ⟨y, hy, hqy, hby⟩

lemma measurable_w (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (hq : Measurable (M.q k))
    (hY : IsClosed (M.Y k)) (hc : IsChain (· ≤ ·) (M.Y k)) : Measurable (M.w ybar k) := by
  classical
  set T : Set (Fin n → ℝ) := M.Y k ∩ {y | ybar k ≤ y} with hT
  have hTc : IsClosed T := hY.inter isClosed_Ici
  have hTch : IsChain (· ≤ ·) T := hc.mono Set.inter_subset_left
  have key : ∀ x, (∃ a, IsLeast (M.orderSet ybar k x) a) ↔ M.q k x ∈ down T := by
    intro x
    constructor
    · rintro ⟨a, ha, _⟩
      exact ⟨a, ⟨ha.1, ha.2.2⟩, ha.2.1⟩
    · rintro ⟨y, hyT, hy⟩
      exact least_exists M ybar k x hY hc ⟨y, hyT.1, hy, hyT.2⟩
  refine measurable_pi_iff.mpr fun j => measurable_of_Iic fun c => ?_
  have hTj : IsClosed (T ∩ {y | y j ≤ c}) :=
    hTc.inter (isClosed_le (continuous_apply j) continuous_const)
  have hset : (fun x => M.w ybar k x j) ⁻¹' Set.Iic c =
      (M.q k) ⁻¹' down (T ∩ {y | y j ≤ c}) ∪
        (((M.q k) ⁻¹' down T)ᶜ ∩ {_x | ybar k j ≤ c}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases h : ∃ a, IsLeast (M.orderSet ybar k x) a
    · have hw : M.w ybar k x = h.choose := by
        unfold Model.w
        rw [dif_pos h]
      have hspec := h.choose_spec
      rw [hw]
      have hmem : M.q k x ∈ down T := (key x).1 h
      constructor
      · intro hle
        left
        exact ⟨h.choose, ⟨⟨hspec.1.1, hspec.1.2.2⟩, hle⟩, hspec.1.2.1⟩
      · rintro (⟨y, ⟨hyT, hyj⟩, hy⟩ | ⟨hn, _⟩)
        · have := hspec.2 (show y ∈ M.orderSet ybar k x from ⟨hyT.1, hy, hyT.2⟩)
          exact (this j).trans hyj
        · exact absurd hmem hn
    · have hw : M.w ybar k x = ybar k := by
        unfold Model.w
        rw [dif_neg h]
      rw [hw]
      have hn : M.q k x ∉ down T := fun hm => h ((key x).2 hm)
      constructor
      · intro hle
        right
        exact ⟨hn, hle⟩
      · rintro (⟨y, ⟨hyT, _⟩, hy⟩ | ⟨_, hle⟩)
        · exact absurd ⟨y, hyT, hy⟩ hn
        · exact hle
  rw [hset]
  exact (hq (measurableSet_down hTj (hTch.mono Set.inter_subset_left))).union
    ((hq (measurableSet_down hTc hTch)).compl.inter (MeasurableSet.const _))

lemma measurable_rule (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (hq : Measurable (M.q k))
    (hY : IsClosed (M.Y k)) (hc : IsChain (· ≤ ·) (M.Y k)) :
    Measurable (M.baseStockRule ybar k) := by
  classical
  unfold Model.baseStockRule
  have hset : MeasurableSet {x : Fin n → ℝ | M.q k x ≤ coeVec (ybar k)} := by
    have : {x : Fin n → ℝ | M.q k x ≤ coeVec (ybar k)} =
        ⋂ j, {x | M.q k x j ≤ coeVec (ybar k) j} := by
      ext x
      simp [Pi.le_def]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((measurable_pi_apply j).comp hq) measurable_const
  exact Measurable.ite hset measurable_const (measurable_w M ybar k hq hY hc)

lemma extendHist_apply_measurable (K j : ℕ) :
    Measurable (fun z : Fin K → Fin m → ℝ => extendHist z j) := by
  unfold extendHist
  by_cases h : j < K
  · simp only [h, dif_pos]
    exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]
    exact measurable_const

lemma measurable_state (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hs : ∀ k, Measurable (Function.uncurry (M.s k)))
    (hrule : ∀ k, Measurable (M.baseStockRule ybar k)) (K k : ℕ) :
    Measurable (fun z : Fin K → Fin m → ℝ => M.baseStockState ybar x₁ (extendHist z) k) := by
  induction k with
  | zero =>
    exact measurable_const
  | succ k ih =>
    exact (hs k).comp (((hrule k).comp ih).prodMk (extendHist_apply_measurable K k))

lemma state_congr (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d d' : ℕ → Fin m → ℝ) (k : ℕ) (h : ∀ j < k, d j = d' j) :
    M.baseStockState ybar x₁ d k = M.baseStockState ybar x₁ d' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h k (Nat.lt_succ_self k)
    show M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k) =
      M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d' k)) (d' k)
    rw [h1, h2]

lemma orderSeq_base (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.orderSeq (M.baseStock ybar x₁) d k =
      M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) := by
  show M.baseStockRule ybar k
      (M.baseStockState ybar x₁ (extendHist (fun j : Fin k => d j)) k) = _
  congr 1
  apply state_congr
  intro j hj
  simp [extendHist, hj]

lemma stateSeq_base (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.stateSeq (M.baseStock ybar x₁) x₁ d k = M.baseStockState ybar x₁ d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show M.s k (M.orderSeq (M.baseStock ybar x₁) d k) (d k) =
      M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k)
    rw [orderSeq_base]

lemma w_mem_ge (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hb : ybar k ∈ M.Y k) :
    M.w ybar k x ∈ M.Y k ∧ ybar k ≤ M.w ybar k x := by
  classical
  unfold Model.w
  by_cases h : ∃ a, IsLeast (M.orderSet ybar k x) a
  · rw [dif_pos h]
    have hs := h.choose_spec
    exact ⟨hs.1.1, hs.1.2.2⟩
  · rw [dif_neg h]
    exact ⟨hb, le_rfl⟩

lemma w_le (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hb : ybar k ∈ M.Y k) (y : Fin n → ℝ) (hy : y ∈ M.Y k) (hqy : M.q k x ≤ coeVec y)
    (hby : ybar k ≤ y) : M.w ybar k x ≤ y := by
  classical
  unfold Model.w
  by_cases h : ∃ a, IsLeast (M.orderSet ybar k x) a
  · rw [dif_pos h]
    exact h.choose_spec.2 (show y ∈ M.orderSet ybar k x from ⟨hy, hqy, hby⟩)
  · rw [dif_neg h]
    exact hby

lemma w_spec (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hY : IsClosed (M.Y k)) (hc : IsChain (· ≤ ·) (M.Y k))
    (hne : ∃ y ∈ M.Y k, M.q k x ≤ coeVec y ∧ ybar k ≤ y) :
    M.q k x ≤ coeVec (M.w ybar k x) := by
  classical
  have h := least_exists M ybar k x hY hc hne
  have hw : M.w ybar k x = h.choose := by
    unfold Model.w
    rw [dif_pos h]
  rw [hw]
  exact h.choose_spec.1.2.1

lemma rule_mem_ge (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hb : ybar k ∈ M.Y k) :
    M.baseStockRule ybar k x ∈ M.Y k ∧ ybar k ≤ M.baseStockRule ybar k x := by
  classical
  unfold Model.baseStockRule
  by_cases h : M.q k x ≤ coeVec (ybar k)
  · rw [if_pos h]
    exact ⟨hb, le_rfl⟩
  · rw [if_neg h]
    exact w_mem_ge M ybar k x hb

lemma base_state_mem (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hs : ∀ k, ∀ y ∈ M.Y k, ∀ t ∈ M.Dset k, M.s k y t ∈ M.X (k + 1))
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.baseStockState ybar x₁ d k ∈ M.X k := by
  intro k
  induction k with
  | zero => exact hx₁
  | succ k ih =>
    exact hs k _ (rule_mem_ge M ybar k _ (h3a k).1).1 _ (hd k)

lemma base_feasible (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ) (hM : M.Standing)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3c : M.H3c) (hfeas : M.OrderFeasible) :
    M.Feasible x₁ (M.baseStock ybar x₁) := by
  classical
  have hrule : ∀ k, Measurable (M.baseStockRule ybar k) := fun k =>
    measurable_rule M ybar k (hM.q_measurable k) (h3c k).1 (h3c k).2
  refine ⟨fun k => ?_, fun k z => ?_, fun d hd k => ?_⟩
  · exact (hrule k).comp (measurable_state M ybar x₁ hM.s_measurable hrule k k)
  · exact (rule_mem_ge M ybar k _ (h3a k).1).1
  · rw [stateSeq_base, orderSeq_base]
    have hX := base_state_mem M ybar x₁ hM.s_mem hx₁ h3a d hd k
    unfold Model.baseStockRule
    by_cases hA : M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k)
    · rw [if_pos hA]
      exact hA
    · rw [if_neg hA]
      obtain ⟨y, hy, hqy⟩ := hfeas k _ hX
      have hby : ybar k ≤ y := by
        rcases (h3c k).2.total (h3a k).1 hy with h | h
        · exact h
        · exact absurd (hqy.trans (coeVec_mono h)) hA
      exact w_spec M ybar k _ (h3c k).1 (h3c k).2 ⟨y, hy, hqy, hby⟩

lemma dominance (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ) (hM : M.Standing)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (Y' : Pol n m) (hF : M.Feasible x₁ Y') (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) = ybar k ∨
      M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) ≤ M.orderSeq Y' d k := by
  classical
  have hXs : ∀ k, M.baseStockState ybar x₁ d k ∈ M.X k :=
    base_state_mem M ybar x₁ hM.s_mem hx₁ h3a d hd
  have hXp : ∀ k, M.stateSeq Y' x₁ d k ∈ M.X k := by
    intro k
    induction k with
    | zero => exact hx₁
    | succ k ih => exact hM.s_mem k _ (hF.mem_Y k _) _ (hd k)
  have hInv : ∀ k, (M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k) ∨
      M.baseStockState ybar x₁ d k ≤ M.stateSeq Y' x₁ d k) →
      (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) = ybar k ∨
        M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) ≤ M.orderSeq Y' d k) := by
    intro k hP
    by_cases hA : M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k)
    · left
      unfold Model.baseStockRule
      rw [if_pos hA]
    · right
      rcases hP with h | h
      · exact absurd h hA
      · have hq' := h3d.2.2 k _ (hXs k) _ (hXp k) h hA
        have hq2 := hF.q_le d hd k
        have hy' : M.orderSeq Y' d k ∈ M.Y k := hF.mem_Y k _
        have hby : ybar k ≤ M.orderSeq Y' d k := by
          rcases (h3c k).2.total (h3a k).1 hy' with h1 | h1
          · exact h1
          · exact absurd ((hq'.trans hq2).trans (coeVec_mono h1)) hA
        unfold Model.baseStockRule
        rw [if_neg hA]
        exact w_le M ybar k _ (h3a k).1 _ hy' (hq'.trans hq2) hby
  have hP : ∀ k, (M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k) ∨
      M.baseStockState ybar x₁ d k ≤ M.stateSeq Y' x₁ d k) := by
    intro k
    induction k with
    | zero => exact Or.inr le_rfl
    | succ k ih =>
      rcases hInv k ih with h | h
      · left
        show M.q (k + 1) (M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k)) ≤ _
        rw [h]
        exact h3b k (d k) (hd k)
      · right
        show M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k) ≤
          M.s k (M.orderSeq Y' d k) (d k)
        have hr := rule_mem_ge M ybar k (M.baseStockState ybar x₁ d k) (h3a k).1
        exact h3d.2.1 k (d k) (hd k) ⟨hr.1, hr.2⟩
          ⟨hF.mem_Y k _, hr.2.trans h⟩ h
  exact fun k => hInv k (hP k)

lemma G_dominance (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ) (hM : M.Standing)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (Y' : Pol n m) (hF : M.Feasible x₁ Y') (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j)
    (k : ℕ) :
    M.G k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) ≤
      M.G k (M.orderSeq Y' d k) := by
  have hr := rule_mem_ge M ybar k (M.baseStockState ybar x₁ d k) (h3a k).1
  rcases dominance M ybar x₁ hM hx₁ h3a h3b h3c h3d Y' hF d hd k with h | h
  · rw [h]
    exact (h3a k).2 _ (hF.mem_Y k _)
  · exact h3d.1 k ⟨hr.1, hr.2⟩ ⟨hF.mem_Y k _, hr.2.trans h⟩ h

end

end VeinottBaseStock

open VeinottBaseStock MeasureTheory ProbabilityTheory in
theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (hfeas : M.OrderFeasible) :
    M.IsOptimal x₁ P D (M.baseStock ybar x₁) := by
  refine ⟨base_feasible M ybar x₁ hM hx₁ h3a h3c hfeas, fun Y' hF => ?_⟩
  unfold Model.cost
  refine add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_) _
  unfold Model.excess
  refine ENNReal.tsum_le_tsum fun k => lintegral_mono fun ω => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hβ : 0 ≤ M.β k := Finset.prod_nonneg fun j _ => hM.alpha_nonneg j
  have hG := G_dominance M ybar x₁ hM hx₁ h3a h3b h3c h3d Y' hF (fun j => D j ω)
    (fun j => hD.mem j ω) k
  rw [orderSeq_base]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hG _) hβ
