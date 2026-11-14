-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.useful_duals
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:53.170195+00:00
-- url     : https://prove2.me/submissions/4ee1e954-ef6e-49c3-90ba-686888b891f4

import Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

/-- Positivity of all atom probabilities makes the flow balance equivalent to
vanishing of all the payment coefficients, even when type supports differ. -/
private theorem secondBestTradeCoefficients (N : Market) (z : Dual N) :
    coefficientsVanish N z ↔ useful N z := by
  constructor
  · intro h a t
    let v : Profile N := overwrite N (fun b => ⟨0, N.nt_pos b⟩) a t
    have hv : v a = t := by simp [v, overwrite]
    have hvp : 0 < prior N v := Finset.prod_pos (fun b _ => N.mass_pos b (v b))
    have hzero := h a v
    unfold paymentCoeff at hzero
    have hflow := (mul_eq_zero.mp hzero).resolve_left (div_pos hvp (N.mass_pos a (v a))).ne'
    rw [hv] at hflow
    linarith only [hflow]
  · intro h a v
    simp only [paymentCoeff, h a (v a)]
    ring

/-- Global profile sums and one-coordinate conditional sums agree after dividing
by the positive probability of the reported type. -/
private theorem secondBestTradeWeightedOverwrite (N : Market) (a : Agent N) (r : Ty N a)
    (g : Profile N → ℝ) :
    N.mass a r * expect N (fun v => g (overwrite N v a r)) =
      expect N (fun v => if v a = r then g v else 0) := by
  classical
  let E := Equiv.piSplitAt a (Ty N)
  let W := (b : {b : Agent N // b ≠ a}) → Ty N b
  let other (w : W) := ∏ b, N.mass b.1 (w b)
  have factor (v : Profile N) : prior N v = N.mass a (v a) * other (E v).2 := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun b : Agent N => b = a) (fun b => N.mass b (v b))
    letI : Unique {b : Agent N // b = a} :=
      ⟨⟨⟨a,rfl⟩⟩, fun x => Subtype.ext x.2⟩
    change (∏ b, N.mass b (v b)) = N.mass a (v a) * ∏ b : {b : Agent N // b ≠ a}, N.mass b.1 (v b.1)
    rw [← h]
    congr 1
    exact @Fintype.prod_unique ℝ _ (Subtype.fintype _) _ _ (fun b : {b : Agent N // b = a} => N.mass b (v b))
  have ov (t : Ty N a) (w : W) :
      overwrite N (E.symm (t,w)) a r = E.symm (r,w) := by
    apply E.injective
    apply Prod.ext
    · simp [E,overwrite]
    · funext b
      simp [E,overwrite,Function.update_of_ne b.2,b.2]
  have key (f : Profile N → ℝ) :
      expect N f = ∑ t : Ty N a, N.mass a t * ∑ w : W, other w * f (E.symm (t,w)) := by
    unfold expect
    rw [← E.symm.sum_comp (fun v => prior N v * f v), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [factor]
    have ev : E (E.symm (t,w)) = (t,w) := E.apply_symm_apply _
    have et : (E.symm (t,w)) a = t := congrArg Prod.fst ev
    simp [ev, et, mul_assoc]
  rw [key, key]
  have atCoordinate (t : Ty N a) (w : W) : (E.symm (t,w)) a = t :=
    congrArg Prod.fst (E.apply_symm_apply (t,w))
  simp only [ov, atCoordinate]
  simp only [← Finset.sum_mul, N.mass_sum, one_mul]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

/-- Each report average can be replaced by a realized-report transfer, giving
an exact finite-sum rearrangement used in both payment and allocation terms. -/
private theorem secondBestTradeSumReports (N : Market) (a : Agent N) (c : Ty N a → ℝ)
    (g : Profile N → ℝ) :
    (∑ r, c r * expect N (fun v => g (overwrite N v a r))) =
      expect N (fun v => c (v a) / N.mass a (v a) * g v) := by
  classical
  have hterm (r : Ty N a) :
      c r * expect N (fun v => g (overwrite N v a r)) =
        expect N (fun v => if v a = r then c r / N.mass a r * g v else 0) := by
    calc
      _ = c r / N.mass a r * (N.mass a r * expect N (fun v => g (overwrite N v a r))) := by
        field_simp [(N.mass_pos a r).ne']
      _ = c r / N.mass a r * expect N (fun v => if v a = r then g v else 0) := by
        rw [secondBestTradeWeightedOverwrite]
      _ = _ := by
        simp only [expect, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v a = r <;> simp [h] <;> ring
  simp_rw [hterm]
  unfold expect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum]
  simp


/-- The same conditional reindexing is valid for score functions depending on
the reported type. This is used for the truthful-utility terms of the Lagrangian. -/
private theorem secondBestTradeDependentSumReports (N : Market) (a : Agent N) (c : Ty N a → ℝ)
    (g : Ty N a → Profile N → ℝ) :
    (∑ r, c r * expect N (fun v => g r (overwrite N v a r))) =
      expect N (fun v => c (v a) / N.mass a (v a) * g (v a) v) := by
  have heq (r : Ty N a) (v : Profile N) : (overwrite N v a r) a = r := by simp [overwrite]
  simpa only [heq] using secondBestTradeSumReports N a c (fun v => g (v a) v)

/-- Expand the incentive multiplier sum into an expected score on each profile.
The null report contributes no report utility. -/
private theorem secondBestTradeIncentiveSum (N : Market) (z : Dual N) (m : SignedMechanism N)
    (a : Agent N) :
    (∑ t, ∑ r : Option (Ty N a), (z.flow a t r : ℝ) *
      (U N m a t t - reportUtility N m a t r)) =
    expect N (fun v =>
      outflow N z a (v a) / N.mass a (v a) * (valueUtility N a (v a) (m.q v) - m.t a v) -
      ∑ t, (z.flow a t (some (v a)) : ℝ) / N.mass a (v a) *
        (valueUtility N a t (m.q v) - m.t a v)) := by
  classical
  let sc := fun (t : Ty N a) (v : Profile N) => valueUtility N a t (m.q v) - m.t a v
  have truth := secondBestTradeDependentSumReports N a (outflow N z a) sc
  have report (t : Ty N a) := secondBestTradeSumReports N a (fun r => (z.flow a t (some r) : ℝ)) (sc t)
  have hzero (t : Ty N a) : reportUtility N m a t none = 0 := by
    cases a <;> simp [reportUtility, valueUtility, nullAllocation, nullTransfer]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ t, outflow N z a t * expect N (fun v => sc t (overwrite N v a t))) - _ = _
  rw [truth]
  have split (t : Ty N a) :
      (∑ r : Option (Ty N a), (z.flow a t r : ℝ) * reportUtility N m a t r) =
        ∑ r : Ty N a, (z.flow a t (some r) : ℝ) * expect N (fun v => sc t (overwrite N v a r)) := by
    rw [Fintype.sum_option]
    simp [hzero, reportUtility, U, sc, valueUtility, nullAllocation, nullTransfer]
  simp_rw [split, report]
  unfold expect
  rw [Finset.sum_comm (f := fun t v => prior N v * ((z.flow a t (some (v a)) : ℝ) / N.mass a (v a) * sc t v))]
  simp [sc, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

private theorem secondBestTradeExpectSum (N : Market) {I : Type} [Fintype I]
    (f : I → Profile N → ℝ) : (∑ i, expect N (f i)) = expect N (fun v => ∑ i, f i v) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- The coefficient formula on one profile, before taking expectations. -/
private theorem secondBestTradeAgentContribution (N : Market) (z : Dual N) (m : SignedMechanism N)
    (a : Agent N) (v : Profile N) :
    outflow N z a (v a) / N.mass a (v a) * (valueUtility N a (v a) (m.q v) - m.t a v) -
      ∑ t, (z.flow a t (some (v a)) : ℝ) / N.mass a (v a) *
        (valueUtility N a t (m.q v) - m.t a v) =
    (∑ e, XiAgent N z a (v a) e * m.q v e) +
      (inflow N z a (v a) - outflow N z a (v a)) / N.mass a (v a) * m.t a v := by
  classical
  cases a with
  | inl i =>
    simp only [valueUtility, XiAgent, Sum.elim_inl, one_mul, inflow, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum, sub_div, sub_mul, Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm (f := fun t e => (z.flow (.inl i) t (some (v (.inl i))) : ℝ) /
      N.mass (.inl i) (v (.inl i)) * (coord N (.inl i) t e * m.q v e))]
    ring_nf
  | inr j =>
    simp only [valueUtility, XiAgent, Sum.elim_inr, neg_one_mul, inflow, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum, sub_div, sub_mul, Finset.sum_mul, Finset.sum_div, mul_neg, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_comm (f := fun t e => (z.flow (.inr j) t (some (v (.inr j))) : ℝ) /
      N.mass (.inr j) (v (.inr j)) * (coord N (.inr j) t e * m.q v e))]
    ring_nf


private theorem secondBestTradeSumXi (N : Market) (z : Dual N) (v : Profile N) (e : Trade N) :
    (∑ a, XiAgent N z a (v a) e) =
      XiAgent N z (.inl (N.buyer e)) (v (.inl (N.buyer e))) e +
      XiAgent N z (.inr (N.seller e)) (v (.inr (N.seller e))) e := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_eq_single (N.buyer e)
    · intro i _ hi
      simp [XiAgent, coord, incident, Ne.symm hi]
    · simp
  · apply Finset.sum_eq_single (N.seller e)
    · intro j _ hj
      simp [XiAgent, coord, incident, Ne.symm hj]
    · simp

private theorem secondBestTradeLagrangianExpansion (N : Market) (z : Dual N) (m : SignedMechanism N) :
    lagrangian N z m = expect N (fun v => (∑ e, Xi N z v e * m.q v e) +
      ∑ a, ((z.tau : ℝ) + (inflow N z a (v a) - outflow N z a (v a)) / N.mass a (v a)) * m.t a v) := by
  classical
  unfold lagrangian
  simp_rw [secondBestTradeIncentiveSum, secondBestTradeAgentContribution]
  rw [secondBestTradeExpectSum]
  have hxi (v : Profile N) :
      (∑ a, ∑ e, XiAgent N z a (v a) e * m.q v e) =
      ∑ e, (XiAgent N z (.inl (N.buyer e)) (v (.inl (N.buyer e))) e +
        XiAgent N z (.inr (N.seller e)) (v (.inr (N.seller e))) e) * m.q v e := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, secondBestTradeSumXi]
  simp only [expect, GFT]
  simp only [expect, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [← Finset.mul_sum]
  rw [mul_left_comm (z.tau : ℝ) (prior N v)]
  simp only [← mul_add]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.mul_sum, add_mul, Xi, hxi]
  simp_rw [show ∀ e, m.q v e * gains N v e = gains N v e * m.q v e from fun e => mul_comm _ _]
  ring

private theorem tradeMaxBound (N : Market) (q w : Trade N → ℝ) (hq : q ∈ allocationPolytope N) :
    (∑ e, q e * w e) ≤ maxSurplus N w := by
  classical
  let l : (Trade N → ℝ) → ℝ := fun x => ∑ e, x e * w e
  have lin : IsLinearMap ℝ l := by
    constructor
    · intro x y; simp [l, add_mul, Finset.sum_add_distrib]
    · intro c x; simp [l, mul_assoc, Finset.mul_sum]
  apply (convexHull_min (t := {x | l x ≤ maxSurplus N w}) ?_ (convex_halfSpace_le lin _)) hq
  rintro x ⟨X,hX,rfl⟩
  change (∑ e, indicator N X e * w e) ≤ _
  have eq : (∑ e, indicator N X e * w e) = ∑ e ∈ X, w e := by
    simp [indicator, ite_mul, Finset.sum_ite_mem]
  rw [eq]
  exact Finset.le_sup' (fun X => ∑ e ∈ X, w e) hX

private theorem tradeFiniteSup (N : Market) (z : Dual N) (hz : useful N z) :
    lagrangianSup N z = (XiObjective N z : EReal) := by
  classical
  have eq (m : SignedMechanism N) : lagrangian N z m =
      expect N (fun v => ∑ e, Xi N z v e * m.q v e) := by
    have noPay (a : Agent N) (v : Profile N) :
        (z.tau : ℝ) + (inflow N z a (v a) - outflow N z a (v a)) / N.mass a (v a) = 0 := by
      rw [hz a (v a)]
      field_simp [(N.mass_pos a (v a)).ne'] <;> ring
    simp only [secondBestTradeLagrangianExpansion, noPay, zero_mul, Finset.sum_const_zero, add_zero]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨m,hm,rfl⟩
    rw [eq]
    apply EReal.coe_le_coe_iff.mpr
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun a _ => (N.mass_pos a _).le))
    simpa only [mul_comm] using tradeMaxBound N (m.q v) (Xi N z v) (hm v)
  · have witness (v : Profile N) : ∃ X ∈ N.family, maxSurplus N (Xi N z v) = ∑ e ∈ X, Xi N z v e :=
      Finset.exists_mem_eq_sup' N.family_nonempty (fun X => ∑ e ∈ X, Xi N z v e)
    choose X hX hmax using witness
    let m : SignedMechanism N := ⟨fun v => indicator N (X v), fun _ _ => 0⟩
    have hm : feasible N m.q := fun v => subset_convexHull ℝ _ ⟨X v,hX v,rfl⟩
    have heq : lagrangian N z m = XiObjective N z := by
      rw [eq]
      unfold XiObjective expect
      apply Finset.sum_congr rfl
      intro v _
      dsimp only
      rw [hmax v]
      simp [m, indicator, mul_ite, Finset.sum_ite_mem]
    exact le_sSup ⟨m, hm, by rw [heq]⟩

private theorem tradeZeroAllocation (N : Market) : feasible N (fun _ _ => 0) := by
  intro v
  obtain ⟨X,hX⟩ := N.family_nonempty
  apply subset_convexHull
  refine ⟨∅, N.downward X hX ∅ (Finset.empty_subset X), ?_⟩
  funext e
  simp [indicator]

private theorem tradeInfiniteSup (N : Market) (z : Dual N) (hz : ¬ useful N z) :
    lagrangianSup N z = ⊤ := by
  classical
  have hcoef := fun hv => hz ((secondBestTradeCoefficients N z).mp hv)
  change ¬ ∀ a v, paymentCoeff N z a v = 0 at hcoef
  push_neg at hcoef
  obtain ⟨a,w,hcc⟩ := hcoef
  let c := (z.tau : ℝ) + (inflow N z a (w a) - outflow N z a (w a)) / N.mass a (w a)
  have hp : 0 < prior N w := Finset.prod_pos fun b _ => N.mass_pos b _
  have hc : c ≠ 0 := by
    intro hc
    apply hcc
    unfold paymentCoeff
    dsimp [c] at hc
    field_simp [(N.mass_pos a _).ne'] at hc
    have : (z.tau : ℝ) * N.mass a (w a) - outflow N z a (w a) + inflow N z a (w a) = 0 := by linarith
    rw [this, mul_zero]
  have unbounded (R : ℝ) : (R : EReal) ≤ lagrangianSup N z := by
    let m : SignedMechanism N := ⟨fun _ _ => 0, fun b v => if v = w ∧ b = a then R / (prior N w * c) else 0⟩
    have val : lagrangian N z m = R := by
      rw [secondBestTradeLagrangianExpansion]
      unfold expect
      rw [Finset.sum_eq_single w]
      · simp only [m, mul_zero, Finset.sum_const_zero, zero_add, true_and, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        change prior N w * (c * (R / (prior N w * c))) = R
        field_simp [hp.ne', hc]
      · intro v _ h
        simp [m,h]
      · simp
    exact le_sSup ⟨m, tradeZeroAllocation N, by rw [val]⟩
  by_contra h
  have hbot : lagrangianSup N z ≠ ⊥ := by
    intro hb
    have hn := unbounded 0
    simp [hb] at hn
  have finite := EReal.coe_toReal h hbot
  have hlarge := unbounded ((lagrangianSup N z).toReal + 1)
  rw [← finite] at hlarge
  have impossible : (lagrangianSup N z).toReal + 1 ≤ (lagrangianSup N z).toReal := by exact_mod_cast hlarge
  linarith

theorem solution (N : Market) (z : Dual N) :
    ((∃ r : ℝ, lagrangianSup N z = (r : EReal)) ↔ useful N z) ∧
    (¬ useful N z → lagrangianSup N z = ⊤) := by
  refine ⟨⟨?_, fun hu => ⟨_,tradeFiniteSup N z hu⟩⟩, tradeInfiniteSup N z⟩
  rintro ⟨r, hr⟩
  by_contra hu
  exact EReal.coe_ne_top r (hr.symm.trans (tradeInfiniteSup N z hu))
