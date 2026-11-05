-- Prove2me | solution 1 for SupplierAudit.Joint.lemma_OA10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:40:59.549195+00:00
-- url     : https://prove2.me/submissions/42ec3bae-3a73-4445-9698-448ccde8884a

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

open SupplierAudit.Joint Set

namespace SAJHelp

variable (P : SupplierAudit.Competition.Params)

theorem gp_eq (l1 lc l2 : ℝ) : grossProfit₁ P l1 lc l2 =
    (1 - lc) * ((1 - l1) * (1 - l2) * stage2Profit₁ P 0 0 + l1 * (1 - l2) * stage2Profit₁ P 1 0
      + (1 - l1) * l2 * stage2Profit₁ P 0 1 + l1 * l2 * stage2Profit₁ P 1 1)
    + lc * ((1 - l1) * (1 - l2) * stage2Profit₁ P 1 1 + l1 * (1 - l2) * stage2Profit₁ P 2 1
      + (1 - l1) * l2 * stage2Profit₁ P 1 2 + l1 * l2 * stage2Profit₁ P 2 2) := by
  simp only [grossProfit₁, Fintype.sum_prod_type, Fintype.sum_bool, if_true,
    Bool.toNat_true, Bool.toNat_false]
  norm_num
  ring

theorem X_pos : 0 < P.r * (1 - P.e) := mul_pos P.hr0 (by linarith [P.he1])

theorem X_lt_one : P.r * (1 - P.e) < 1 := by
  have := P.hr1; have := P.he0; have := P.he1; have := P.hr0
  nlinarith

theorem ac_zero (K : ℝ) : SupplierAudit.Competition.auditCost P K 0 = 0 := by
  simp [SupplierAudit.Competition.auditCost]

theorem ac_pos (K y : ℝ) (hy : 0 < y) :
    SupplierAudit.Competition.auditCost P K y = K + P.a / 2 * y ^ 2 := by
  simp [SupplierAudit.Competition.auditCost, hy]

theorem ac_K0 (y : ℝ) : SupplierAudit.Competition.auditCost P 0 y = P.a / 2 * y ^ 2 := by
  simp [SupplierAudit.Competition.auditCost]

theorem agg_eq (K : ℝ) (x : ℝ × ℝ × ℝ) : aggProfit P K x =
    grossProfit₁ P (P.r * (1 - P.e) * (1 - x.1)) (P.r * (1 - P.e) * (1 - x.2.1))
        (P.r * (1 - P.e) * (1 - x.2.2))
      + grossProfit₁ P (P.r * (1 - P.e) * (1 - x.2.2)) (P.r * (1 - P.e) * (1 - x.2.1))
        (P.r * (1 - P.e) * (1 - x.1))
      - (SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1
        + SupplierAudit.Competition.auditCost P K x.2.2) := rfl

theorem agg_symm (K a b c : ℝ) : aggProfit P K (a, b, c) = aggProfit P K (c, b, a) := by
  simp only [agg_eq]; ring

/-- cost decomposition -/
theorem agg_K (K : ℝ) (x : ℝ × ℝ × ℝ) : aggProfit P K x = aggProfit P 0 x
    - ((if 0 < x.1 then K else 0) + (if 0 < x.2.1 then K else 0) + (if 0 < x.2.2 then K else 0)) := by
  simp only [agg_eq, SupplierAudit.Competition.auditCost]; simp only [ite_self]; ring

theorem agg_K_0b0 (K b : ℝ) (hb : 0 < b) : aggProfit P K (0, b, 0) = aggProfit P 0 (0, b, 0) - K := by
  rw [agg_K]; simp [hb]

theorem agg_K_ab0 (K a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    aggProfit P K (a, b, 0) = aggProfit P 0 (a, b, 0) - 2 * K := by
  rw [agg_K]; simp [ha, hb]; ring

theorem agg_K_000 (K : ℝ) : aggProfit P K (0, 0, 0) = aggProfit P 0 (0, 0, 0) := by
  rw [agg_K]; simp

theorem agg_cont : Continuous (aggProfit P 0) := by
  have : aggProfit P 0 = fun x => _ := funext fun x => by
    rw [agg_eq, gp_eq, gp_eq, ac_K0, ac_K0, ac_K0]
  rw [this]; fun_prop

theorem scen_facts (hscen : Scenario P) :
    2 * stage2Profit₁ P 1 1 ≤ stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 ∧
    stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2 ≤ 2 * stage2Profit₁ P 1 1 := by
  obtain ⟨_, h2, h3, _⟩ := hscen
  simp only [piAgg, stage2Profit₂] at h2 h3
  constructor <;> linarith

/-- Lemma OA9 core (same effort `y`). -/
theorem oa9_core (hscen : Scenario P) (K y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
    aggProfit P K (y, 0, 0) ≤ aggProfit P K (0, y, 0) ∧
    aggProfit P K (0, 0, y) ≤ aggProfit P K (0, y, 0) := by
  obtain ⟨S2, S3⟩ := scen_facts P hscen
  have hX0 := X_pos P; have hX1 := X_lt_one P
  set X := P.r * (1 - P.e) with hX
  have key : aggProfit P K (0, y, 0) - aggProfit P K (y, 0, 0) =
      X * y * ((1 - X) ^ 2 * (stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 - 2 * stage2Profit₁ P 1 1)
        + X * (1 - X) * (stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1
            - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2))
        + X ^ 2 * (2 * stage2Profit₁ P 1 1 - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2))) := by
    simp only [agg_eq, gp_eq]; ring
  have hnn : 0 ≤ X * y * ((1 - X) ^ 2 * (stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 - 2 * stage2Profit₁ P 1 1)
        + X * (1 - X) * (stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1
            - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2))
        + X ^ 2 * (2 * stage2Profit₁ P 1 1 - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2))) := by
    apply mul_nonneg (mul_nonneg hX0.le hy.1)
    have h1 : 0 ≤ 1 - X := by linarith
    have := mul_nonneg (pow_two_nonneg (1 - X)) (show 0 ≤ stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 - 2 * stage2Profit₁ P 1 1 by linarith)
    have := mul_nonneg (mul_nonneg hX0.le h1) (show 0 ≤ stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1
            - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2) by linarith)
    have := mul_nonneg (pow_two_nonneg X) (show 0 ≤ 2 * stage2Profit₁ P 1 1 - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2) by linarith)
    linarith
  refine ⟨by linarith, ?_⟩
  rw [agg_symm P K 0 0 y]; linarith

/-- Lemma OA10 core (same efforts). -/
theorem oa10_core (hscen : Scenario P) (K y z : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    aggProfit P K (y, 0, z) ≤ aggProfit P K (y, z, 0) := by
  obtain ⟨S2, S3⟩ := scen_facts P hscen
  have hX0 := X_pos P; have hX1 := X_lt_one P
  set X := P.r * (1 - P.e) with hX
  have key : aggProfit P K (y, z, 0) - aggProfit P K (y, 0, z) =
      X * z * ((1 - X * (1 - y)) * (stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 - 2 * stage2Profit₁ P 1 1)
        + X * (1 - y) * (2 * stage2Profit₁ P 1 1 - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2))) := by
    simp only [agg_eq, gp_eq]; ring
  have ha0 : 0 ≤ X * (1 - y) := mul_nonneg hX0.le (by linarith [hy.2])
  have ha1 : 0 ≤ 1 - X * (1 - y) := by nlinarith [hy.1]
  have := mul_nonneg ha1 (show 0 ≤ stage2Profit₁ P 1 0 + stage2Profit₁ P 0 1 - 2 * stage2Profit₁ P 1 1 by linarith)
  have := mul_nonneg ha0 (show 0 ≤ 2 * stage2Profit₁ P 1 1 - (stage2Profit₁ P 2 1 + stage2Profit₁ P 1 2) by linarith)
  have := mul_nonneg (mul_nonneg hX0.le hz.1) (add_nonneg ‹0 ≤ (1 - X * (1 - y)) * _› this)
  linarith

/-! Stage-2 profit comparisons. -/

theorem margin0 : margin P 0 = P.α - 2 * P.w := by simp [margin]
theorem margin1 : margin P 1 = P.α - P.dM - (P.w + P.wh) := by simp [margin]; ring
theorem margin2 : margin P 2 = P.α - P.dM - 2 * P.wh := by simp [margin]

theorem sp_eq (i j : ℕ) : stage2Profit₁ P i j = ((2 * margin P i - P.β * margin P j) / (4 - P.β ^ 2)) ^ 2 := rfl

theorem p_facts (hβ : 0 < P.β) :
    stage2Profit₁ P 1 0 < stage2Profit₁ P 0 0 ∧ stage2Profit₁ P 1 0 < stage2Profit₁ P 0 1 ∧
    stage2Profit₁ P 1 1 < stage2Profit₁ P 0 1 ∧ stage2Profit₁ P 1 0 < stage2Profit₁ P 1 1 ∧
    stage2Profit₁ P 1 0 < stage2Profit₁ P 1 2 ∧ stage2Profit₁ P 1 1 ≤ stage2Profit₁ P 1 2 ∧
    stage2Profit₁ P 2 1 ≤ stage2Profit₁ P 1 2 := by
  have hb1 := P.hβ1; have hw := P.hw; have hd := P.hdM
  have h1 := P.hpos1; have h2 := P.hpos2; have h3 := P.hpos3
  have hD : 0 < 4 - P.β ^ 2 := by nlinarith
  simp only [sp_eq, margin0, margin1, margin2]
  set D := 4 - P.β ^ 2
  -- numerators
  have n10 : 0 < 2 * (P.α - P.dM - (P.w + P.wh)) - P.β * (P.α - 2 * P.w) := by nlinarith
  have hm1 : 0 < P.α - P.dM - (P.w + P.wh) := by linarith
  have n11 : 0 < 2 * (P.α - P.dM - (P.w + P.wh)) - P.β * (P.α - P.dM - (P.w + P.wh)) := by nlinarith
  have n21 : 0 < 2 * (P.α - P.dM - 2 * P.wh) - P.β * (P.α - P.dM - (P.w + P.wh)) := by nlinarith
  have sq_lt : ∀ u v : ℝ, 0 < u → u < v → (u / D) ^ 2 < (v / D) ^ 2 := by
    intro u v hu huv
    have h1 : 0 < u / D := div_pos hu hD
    have h2 : u / D < v / D := div_lt_div_of_pos_right huv hD
    nlinarith
  have sq_le : ∀ u v : ℝ, 0 < u → u ≤ v → (u / D) ^ 2 ≤ (v / D) ^ 2 := by
    intro u v hu huv
    have h1 : 0 < u / D := div_pos hu hD
    have h2 : u / D ≤ v / D := div_le_div_of_nonneg_right huv hD.le
    nlinarith
  refine ⟨sq_lt _ _ n10 (by nlinarith), sq_lt _ _ n10 (by nlinarith), sq_lt _ _ n11 (by nlinarith),
    sq_lt _ _ n10 (by nlinarith), sq_lt _ _ n10 (by nlinarith), sq_le _ _ n11 (by nlinarith),
    sq_le _ _ n21 (by nlinarith)⟩

/-- `∆Π > 0` when `S₁` and `S_c` are audited with positive efforts. -/
theorem deltaPi_pos (hβ : 0 < P.β) (y z : ℝ) (hy : y ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 < deltaPi P (y, z, 0) := by
  obtain ⟨_, f2, _, _, _, _, f7⟩ := p_facts P hβ
  have hX0 := X_pos P; have hX1 := X_lt_one P
  set X := P.r * (1 - P.e) with hX
  have key : deltaPi P (y, z, 0) = X * y * ((1 - X * (1 - z)) * (stage2Profit₁ P 0 1 - stage2Profit₁ P 1 0)
      + X * (1 - z) * (stage2Profit₁ P 1 2 - stage2Profit₁ P 2 1)) := by
    simp only [deltaPi, jointG₁, jointG₂, grossProfit₂, SupplierAudit.Competition.lamI, gp_eq]; ring
  rw [key]
  have hc1 : 0 < 1 - X * (1 - z) := by nlinarith [hz.1, hz.2]
  have hc2 : 0 ≤ X * (1 - z) := mul_nonneg hX0.le (by linarith [hz.2])
  apply mul_pos (mul_pos hX0 hy.1)
  have := mul_pos hc1 (sub_pos.2 f2)
  have := mul_nonneg hc2 (sub_nonneg.2 f7)
  linarith

theorem deltaPi_zero (y : ℝ) : deltaPi P (0, y, 0) = 0 := by
  simp only [deltaPi, jointG₁, jointG₂, grossProfit₂]; ring

/-- Attainment of `optCommonOnly`. -/
theorem optC_att : ∃ y ∈ Icc (0 : ℝ) 1, optCommonOnly P = aggProfit P 0 (0, y, 0) ∧
    ∀ y' ∈ Icc (0 : ℝ) 1, aggProfit P 0 (0, y', 0) ≤ aggProfit P 0 (0, y, 0) := by
  have hc : Continuous fun y : ℝ => aggProfit P 0 (0, y, 0) :=
    (agg_cont P).comp (by fun_prop)
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hc.continuousOn
  rw [isMaxOn_iff] at hmax
  refine ⟨y, hy, ?_, hmax⟩
  unfold optCommonOnly
  exact IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact hmax y' hy'⟩

/-- Attainment of `optOneCommon`. -/
theorem optO_att : ∃ y ∈ Icc (0 : ℝ) 1, ∃ z ∈ Icc (0 : ℝ) 1, optOneCommon P = aggProfit P 0 (y, z, 0) ∧
    ∀ y' ∈ Icc (0 : ℝ) 1, ∀ z' ∈ Icc (0 : ℝ) 1, aggProfit P 0 (y', z', 0) ≤ aggProfit P 0 (y, z, 0) := by
  have hc : Continuous fun p : ℝ × ℝ => aggProfit P 0 (p.1, p.2, 0) :=
    (agg_cont P).comp (by fun_prop)
  obtain ⟨⟨y, z⟩, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ((nonempty_Icc.2 zero_le_one).prod (nonempty_Icc.2 zero_le_one)) hc.continuousOn
  rw [isMaxOn_iff] at hmax
  refine ⟨y, hp.1, z, hp.2, ?_, fun y' hy' z' hz' => hmax (y', z') ⟨hy', hz'⟩⟩
  unfold optOneCommon
  exact IsGreatest.csSup_eq ⟨⟨(y, z), hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hmax q hq⟩

end SAJHelp

open SupplierAudit.Joint

theorem solution (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (K : ℝ) (hK : 0 ≤ K) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ∃ y' ∈ Set.Icc (0 : ℝ) 1, ∃ z' ∈ Set.Icc (0 : ℝ) 1,
        aggProfit P K (y, 0, z) ≤ aggProfit P K (y', z', 0) :=
  fun y hy z hz => ⟨y, hy, z, hz, SAJHelp.oa10_core P hscen K y z hy hz⟩
