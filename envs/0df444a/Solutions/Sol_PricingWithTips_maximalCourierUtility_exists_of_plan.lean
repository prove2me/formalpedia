-- Prove2me | solution 1 for PricingWithTips.maximalCourierUtility_exists_of_plan
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:47:50.429977+00:00
-- url     : https://prove2.me/submissions/52c533e7-d142-4617-87d4-5453d94b5d02

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem courierPlan_max
    (M : Market B S D) (A : Allocation B S D)
    (w₁ w₂ : B → S → ℝ)
    (h₁ : IsCourierPlanFor M A w₁)
    (h₂ : IsCourierPlanFor M A w₂) :
    IsCourierPlanFor M A (fun b s => max (w₁ b s) (w₂ b s)) := by
  constructor
  · intro b s
    exact le_trans (h₁.1 b s) (le_max_left _ _)
  constructor
  · intro d b s ht
    constructor
    · linarith [le_max_left (w₁ b s) (w₂ b s), (h₁.2.1 d b s ht).1]
    · intro b' s'
      apply sub_le_iff_le_add.mpr
      apply max_le
      · have h := (h₁.2.1 d b s ht).2 b' s'
        have hm := le_max_left (w₁ b s) (w₂ b s)
        linarith
      · have h := (h₂.2.1 d b s ht).2 b' s'
        have hm := le_max_right (w₁ b s) (w₂ b s)
        linarith
  constructor
  · intro d hnot b s
    apply sub_le_iff_le_add.mpr
    apply max_le
    · linarith [(h₁.2.2.1 d hnot b s)]
    · linarith [(h₂.2.2.1 d hnot b s)]
  · intro b s hnot
    simp [h₁.2.2.2 b s hnot, h₂.2.2.2 b s hnot]

theorem courierRealizedUtility_max
    (M : Market B S D) (A : Allocation B S D)
    (w₁ w₂ : B → S → ℝ) (d : D) :
    courierRealizedUtility M A (fun b s => max (w₁ b s) (w₂ b s)) d =
      max (courierRealizedUtility M A w₁ d)
        (courierRealizedUtility M A w₂ d) := by
  classical
  unfold courierRealizedUtility
  split_ifs with h h₁ h₂
  · dsimp
    exact (max_sub_sub_right _ _ _).symm
  all_goals simp_all



private theorem realized_eq_of_trade'
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    {d : D} {b : B} {s : S} (ht : A.Trades b s d) :
    courierRealizedUtility M A w d = w b s - M.cost d b s := by
  classical
  have hwork : ∃ b' s', A.Trades b' s' d := ⟨b,s,ht⟩
  unfold courierRealizedUtility
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb,hss]

private theorem realized_eq_zero_of_idle
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    (d : D) (hd : ¬ A.CourierWorks d) :
    courierRealizedUtility M A w d = 0 := by
  classical
  change ¬ ∃ b s, A.Trades b s d at hd
  simp [courierRealizedUtility, hd]

theorem courierPlan_iff_bounds
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ) :
    IsCourierPlanFor M A w ↔
      (∀ b s, 0 ≤ w b s) ∧
      (∀ d, 0 ≤ courierRealizedUtility M A w d) ∧
      (∀ d b s, w b s - M.cost d b s ≤ courierRealizedUtility M A w d) ∧
      (∀ b s, ¬ A.Delivers b s → w b s = 0) := by
  classical
  constructor
  · intro hp
    refine ⟨hp.1, ?_, ?_, hp.2.2.2⟩
    · intro d
      by_cases hd : A.CourierWorks d
      · obtain ⟨b,s,ht⟩ := hd
        rw [realized_eq_of_trade' M A w ht]
        exact (hp.2.1 d b s ht).1
      · rw [realized_eq_zero_of_idle M A w d hd]
    · intro d b s
      by_cases hd : A.CourierWorks d
      · obtain ⟨b₀,s₀,ht⟩ := hd
        rw [realized_eq_of_trade' M A w ht]
        exact (hp.2.1 d b₀ s₀ ht).2 b s
      · rw [realized_eq_zero_of_idle M A w d hd]
        exact hp.2.2.1 d hd b s
  · rintro ⟨hw, hnonneg, hupper, hoff⟩
    refine ⟨hw, ?_, ?_, hoff⟩
    · intro d b s ht
      have hnd := hnonneg d
      rw [realized_eq_of_trade' M A w ht] at hnd
      refine ⟨hnd, ?_⟩
      intro b' s'
      have hup := hupper d b' s'
      rw [realized_eq_of_trade' M A w ht] at hup
      exact hup
    · intro d hd b s
      have hup := hupper d b s
      rw [realized_eq_zero_of_idle M A w d hd] at hup
      exact hup

theorem solution
    (M : Market B S D) (A : Allocation B S D)
    (hplan0 : ∃ w : B → S → ℝ, IsCourierPlanFor M A w)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    ∃ uBar : D → ℝ, IsMaximalCourierUtility M A uBar := by
  classical
  push_neg at hnotfull
  obtain ⟨d₀, hd₀⟩ := hnotfull
  let W : Set (B → S → ℝ) := {w | IsCourierPlanFor M A w}
  have heval (b : B) (s : S) :
      Continuous (fun w : B → S → ℝ => w b s) :=
    (continuous_apply s).comp (continuous_apply b)
  have hrealcont (d : D) : Continuous
      (fun w : B → S → ℝ => courierRealizedUtility M A w d) := by
    unfold courierRealizedUtility
    split_ifs
    · fun_prop
    · fun_prop
  have hC₁ : IsClosed {w : B → S → ℝ | ∀ b s, 0 ≤ w b s} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun b => isClosed_iInter (fun s =>
      isClosed_le continuous_const (heval b s)))
  have hC₂ : IsClosed {w : B → S → ℝ |
      ∀ d, 0 ≤ courierRealizedUtility M A w d} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun d => isClosed_le continuous_const (hrealcont d))
  have hC₃ : IsClosed {w : B → S → ℝ |
      ∀ d b s, w b s - M.cost d b s ≤ courierRealizedUtility M A w d} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun d => isClosed_iInter (fun b =>
      isClosed_iInter (fun s => isClosed_le
        ((heval b s).sub continuous_const) (hrealcont d))))
  have hC₄ : IsClosed {w : B → S → ℝ |
      ∀ b s, ¬ A.Delivers b s → w b s = 0} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun b => isClosed_iInter (fun s => ?_))
    by_cases hd : A.Delivers b s
    · simpa [hd] using (isClosed_univ : IsClosed (Set.univ : Set (B → S → ℝ)))
    · simpa [hd] using (isClosed_eq (heval b s) continuous_const)
  have hWclosed : IsClosed W := by
    have hW_eq : W =
        {w : B → S → ℝ | ∀ b s, 0 ≤ w b s} ∩
        {w : B → S → ℝ | ∀ d, 0 ≤ courierRealizedUtility M A w d} ∩
        {w : B → S → ℝ |
          ∀ d b s, w b s - M.cost d b s ≤ courierRealizedUtility M A w d} ∩
        {w : B → S → ℝ | ∀ b s, ¬ A.Delivers b s → w b s = 0} := by
      ext w
      simp only [W, Set.mem_inter_iff, Set.mem_setOf_eq,
        courierPlan_iff_bounds]
      tauto
    rw [hW_eq]
    exact ((hC₁.inter hC₂).inter hC₃).inter hC₄
  let K : Set (B → S → ℝ) :=
    Set.pi Set.univ (fun b => Set.pi Set.univ (fun s => Set.Icc 0 (M.cost d₀ b s)))
  have hK : IsCompact K := by
    have hK' : IsCompact {w : B → S → ℝ |
        ∀ b s, w b s ∈ Set.Icc 0 (M.cost d₀ b s)} :=
      isCompact_pi_infinite (fun b => isCompact_pi_infinite
        (fun s => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (M.cost d₀ b s)))))
    convert hK' using 1
    ext w
    simp [K, Pi.le_def]
    constructor
    · rintro ⟨hlo, hhi⟩ b s
      exact ⟨hlo b s, hhi b s⟩
    · intro h
      exact ⟨(fun b s => (h b s).1), (fun b s => (h b s).2)⟩
  have hWsubset : W ⊆ K := by
    intro w hw
    have hp : IsCourierPlanFor M A w := hw
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro b s
    exact ⟨hp.1 b s, by linarith [hp.2.2.1 d₀ hd₀ b s]⟩
  have hWcompact : IsCompact W := hK.of_isClosed_subset hWclosed hWsubset
  let F : (B → S → ℝ) → ℝ := fun w =>
    ∑ d, courierRealizedUtility M A w d
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro d _
    exact hrealcont d
  obtain ⟨w₀, hw₀⟩ := hplan0
  obtain ⟨wStar, hwStar, hmax⟩ :=
    hWcompact.exists_isMaxOn ⟨w₀, hw₀⟩ hF.continuousOn
  refine ⟨fun d => courierRealizedUtility M A wStar d, ⟨wStar, hwStar, fun _ => rfl⟩, ?_⟩
  intro w hw d
  let wJoin : B → S → ℝ := fun b s => max (wStar b s) (w b s)
  have hjoin : IsCourierPlanFor M A wJoin := courierPlan_max M A wStar w hwStar hw
  have hmaxsum : F wJoin ≤ F wStar := hmax hjoin
  by_contra hnot
  have hlt : courierRealizedUtility M A wStar d < courierRealizedUtility M A w d :=
    lt_of_not_ge hnot
  have hstrict : F wStar < F wJoin := by
    apply Finset.sum_lt_sum
    · intro i hi
      change courierRealizedUtility M A wStar i ≤ courierRealizedUtility M A wJoin i
      rw [courierRealizedUtility_max]
      exact le_max_left _ _
    · refine ⟨d, Finset.mem_univ _, ?_⟩
      change courierRealizedUtility M A wStar d < courierRealizedUtility M A wJoin d
      rw [courierRealizedUtility_max]
      exact lt_of_lt_of_le hlt (le_max_right _ _)
  exact (not_lt_of_ge hmaxsum) hstrict
