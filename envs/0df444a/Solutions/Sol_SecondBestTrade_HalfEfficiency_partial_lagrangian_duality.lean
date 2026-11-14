-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.partial_lagrangian_duality
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:28:00.816813+00:00
-- url     : https://prove2.me/submissions/75fb8e20-1b46-46c9-b3d0-6e4580a37d17

import Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

/-- Positivity of all atom probabilities makes the flow balance equivalent to
vanishing of all the payment coefficients, even when type supports differ. -/
theorem secondBestTradeCoefficients (N : Market) (z : Dual N) :
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

theorem tradeFiniteSup (N : Market) (z : Dual N) (hz : useful N z) :
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

theorem tradeInfiniteSup (N : Market) (z : Dual N) (hz : ¬ useful N z) :
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


theorem secondBestTradePartialDualityPointwise (N : Market) (z : Dual N) :
    lagrangianSup N z ≠ ⊥ ∧ (lagrangianSup N z < ⊤ ↔ coefficientsVanish N z) ∧
      (coefficientsVanish N z → lagrangianSup N z = (XiObjective N z : EReal)) := by
  by_cases h : useful N z
  · rw [tradeFiniteSup N z h]
    exact ⟨EReal.coe_ne_bot _, ⟨fun _ => (secondBestTradeCoefficients N z).mpr h, fun _ => EReal.coe_lt_top _⟩, fun _ => rfl⟩
  · rw [tradeInfiniteSup N z h]
    have hc : ¬ coefficientsVanish N z := fun hc => h ((secondBestTradeCoefficients N z).mp hc)
    simp [hc]

theorem secondBestTradeWeakDuality (N : Market) (z : Dual N) : (OPT N : EReal) ≤ lagrangianSup N z := by
  by_cases h : useful N z
  · rw [tradeFiniteSup N z h]
    apply EReal.coe_le_coe_iff.mpr
    apply csSup_le
    · refine ⟨_,zeroSigned N, ?_,rfl⟩
      refine ⟨tradeZeroAllocation N, by simp [WBB, zeroSigned, expect], ?_⟩
      intro a t r
      cases a <;> cases r <;>
        simp [reportUtility, U, expect, valueUtility, zeroSigned, nullAllocation, nullTransfer]
    · rintro _ ⟨m,hm,rfl⟩
      have lb : GFT N m.q ≤ lagrangian N z m := by
        have hb : 0 ≤ (z.tau : ℝ) * expect N (fun v => ∑ a, m.t a v) := mul_nonneg z.tau.2 hm.2.1
        have hi : 0 ≤ ∑ a, ∑ t, ∑ r : Option (Ty N a), (z.flow a t r : ℝ) *
            (U N m a t t - reportUtility N m a t r) :=
          Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun r _ =>
            mul_nonneg (z.flow a t r).2 (sub_nonneg.mpr (hm.2.2 a t r)))))
        unfold lagrangian
        linarith
      have le : (lagrangian N z m : EReal) ≤ lagrangianSup N z := le_sSup ⟨m,hm.1,rfl⟩
      rw [tradeFiniteSup N z h] at le
      exact lb.trans (EReal.coe_le_coe_iff.mp le)
  · rw [tradeInfiniteSup N z h]
    exact le_top

namespace Primal


theorem secondBestTradeVariableCard (N : Market) :
    Fintype.card (Variable N) = (N.ne + N.nb + N.ns) * Fintype.card (Profile N) := by
  simp only [Variable, Agent, Trade, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

private theorem emptyFeasible (N : Market) : (∅ : Finset (Trade N)) ∈ N.family := by
  obtain ⟨X,hX⟩ := N.family_nonempty
  exact N.downward X hX ∅ (Finset.empty_subset X)

theorem secondBestTradeZeroFeasible (N : Market) : programFeasible N (zeroSigned N) := by
  refine ⟨fun v => ?_, ?_, ?_⟩
  · apply subset_convexHull
    refine ⟨∅, emptyFeasible N, ?_⟩
    ext e
    simp [zeroSigned, indicator]
  · simp [WBB, zeroSigned, expect]
  · intro a t r
    cases a <;> cases r <;>
      simp [reportUtility, U, expect, valueUtility, zeroSigned, nullAllocation, nullTransfer]

private theorem surplus_le_max (N : Market) (q w : Trade N → ℝ) (hq : q ∈ allocationPolytope N) :
    (∑ e, q e * w e) ≤ maxSurplus N w := by
  classical
  let l : (Trade N → ℝ) → ℝ := fun x => ∑ e, x e * w e
  have lin : IsLinearMap ℝ l := by
    constructor
    · intro x y
      simp [l, add_mul, Finset.sum_add_distrib]
    · intro c x
      simp [l, mul_assoc, Finset.mul_sum]
  apply (convexHull_min (t := {x | l x ≤ maxSurplus N w}) ?_ (convex_halfSpace_le lin _)) hq
  rintro x ⟨X,hX,rfl⟩
  change (∑ e, indicator N X e * w e) ≤ _
  have eq : (∑ e, indicator N X e * w e) = ∑ e ∈ X, w e := by
    simp [indicator, ite_mul, Finset.sum_ite_mem]
  rw [eq]
  exact Finset.le_sup' (fun X => ∑ e ∈ X, w e) hX

theorem secondBestTradeGainsBound (N : Market) (m : SignedMechanism N)
    (h : programFeasible N m) : GFT N m.q ≤ FB N := by
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (surplus_le_max N (m.q v) (gains N v) (h.1 v))
    (Finset.prod_nonneg (fun a _ => (N.mass_pos a (v a)).le))

namespace TradePolyhedra
open Set

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- A system of finitely many closed affine half spaces. -/
def Presented (P : E → Prop) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (A : I → E →ₗ[ℝ] ℝ) (b : I → ℝ),
    ∀ x, P x ↔ ∀ i, A i x ≤ b i

private theorem bounds {L U : Type} [Fintype L] [Fintype U]
    (l : L → ℝ) (u : U → ℝ) :
    (∃ x : ℝ, (∀ i, l i ≤ x) ∧ (∀ j, x ≤ u j)) ↔ ∀ i j, l i ≤ u j := by
  classical
  constructor
  · rintro ⟨x,h,k⟩ i j
    exact (h i).trans (k j)
  · intro h
    cases isEmpty_or_nonempty L with
    | inl he =>
      cases isEmpty_or_nonempty U with
      | inl hu => exact ⟨0,isEmptyElim,isEmptyElim⟩
      | inr hu =>
        obtain ⟨j,_,hj⟩ := Finset.exists_min_image (Finset.univ : Finset U) u Finset.univ_nonempty
        exact ⟨u j,isEmptyElim,fun j' => hj j' (Finset.mem_univ _)⟩
    | inr hl =>
      obtain ⟨i,_,hi⟩ := Finset.exists_max_image (Finset.univ : Finset L) l Finset.univ_nonempty
      exact ⟨l i,fun i' => hi i' (Finset.mem_univ _),h i⟩

/-- Eliminate one real variable by comparing every lower bound to every upper bound. -/
theorem projectScalar {P : ℝ × E → Prop} (hp : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  classical
  obtain ⟨I,inst,A,b,eq⟩ := hp
  let c := fun i => A i (1,0)
  let F := fun i => (A i).comp (LinearMap.inr ℝ ℝ E)
  have dec (i) (t : ℝ) (x : E) : A i (t,x) = c i * t + F i x := by
    have h : (t,x) = t • (1,0) + (0,x) := by simp
    rw [h, map_add, map_smul]
    change t * c i + F i x = _
    ring
  let Z := {i : I // c i = 0}
  let L := {i : I // c i < 0}
  let U := {i : I // 0 < c i}
  let A' : Z ⊕ L × U → E →ₗ[ℝ] ℝ := Sum.elim (fun i => F i.1) (fun p =>
    (c p.2.1)⁻¹ • F p.2.1 - (c p.1.1)⁻¹ • F p.1.1)
  let b' : Z ⊕ L × U → ℝ := Sum.elim (fun i => b i.1) (fun p =>
    b p.2.1 / c p.2.1 - b p.1.1 / c p.1.1)
  refine ⟨Z ⊕ L × U,inferInstance,A',b',fun x => ?_⟩
  let l := fun i : L => (b i.1 - F i.1 x) / c i.1
  let u := fun i : U => (b i.1 - F i.1 x) / c i.1
  have pair (i : L) (j : U) : A' (.inr (i,j)) x ≤ b' (.inr (i,j)) ↔ l i ≤ u j := by
    change (c j.1)⁻¹ * F j.1 x - (c i.1)⁻¹ * F i.1 x ≤ b j.1 / c j.1 - b i.1 / c i.1 ↔ _
    dsimp only [l,u]
    simp only [sub_div, div_eq_mul_inv]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨t,ht⟩ ij
    have row (i : I) := (eq _).mp ht i
    simp_rw [dec] at row
    cases ij with
    | inl i =>
      have h := row i.1
      change F i.1 x ≤ b i.1
      simpa only [i.property,zero_mul,zero_add] using h
    | inr p =>
      obtain ⟨i,j⟩ := p
      apply (pair i j).mpr
      exact le_trans (b := t) ((div_le_iff_of_neg i.property).mpr (by linarith [row i.1]))
        ((le_div_iff₀ j.property).mpr (by linarith [row j.1]))
  · intro h
    have hc := (bounds l u).mpr (fun i j => (pair i j).mp (h (.inr (i,j))))
    obtain ⟨t,hl,hu⟩ := hc
    refine ⟨t,(eq _).mpr (fun i => ?_)⟩
    rw [dec]
    rcases lt_trichotomy (c i) 0 with hi|hi|hi
    · have hr := (div_le_iff_of_neg hi).mp (hl ⟨i,hi⟩)
      linarith
    · simpa [hi,A',b'] using h (.inl ⟨i,hi⟩)
    · have hr := (le_div_iff₀ hi).mp (hu ⟨i,hi⟩)
      linarith

theorem preimage {F : Type} [AddCommGroup F] [Module ℝ F] {P : E → Prop}
    (h : Presented P) (f : F →ₗ[ℝ] E) : Presented (fun x => P (f x)) := by
  obtain ⟨I,inst,A,b,eq⟩ := h
  exact ⟨I,inst,fun i => (A i).comp f,b,fun x => eq (f x)⟩

theorem congr {P Q : E → Prop} (h : Presented P) (eq : ∀ x, P x ↔ Q x) : Presented Q := by
  obtain ⟨I,inst,A,b,rows⟩ := h
  exact ⟨I,inst,A,b,fun x => (eq x).symm.trans (rows x)⟩

theorem projectFin {n : ℕ} {P : (Fin n → ℝ) × E → Prop} (h : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  induction n generalizing E with
  | zero =>
    have h' := preimage h (LinearMap.inr ℝ (Fin 0 → ℝ) E)
    apply congr h'
    intro x
    constructor
    · exact fun hp => ⟨0,hp⟩
    · rintro ⟨t,ht⟩
      change P (0,x)
      simpa only [Subsingleton.elim t 0] using ht
  | succ n ih =>
    let f : ℝ × ((Fin n → ℝ) × E) →ₗ[ℝ] (Fin (n+1) → ℝ) × E :=
      (LinearMap.vecCons (LinearMap.fst ℝ _ _) ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _))).prod
        ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))
    have h' := ih (projectScalar (preimage h f))
    apply congr h'
    intro x
    constructor
    · rintro ⟨t,s,ht⟩
      exact ⟨_,ht⟩
    · rintro ⟨t,ht⟩
      refine ⟨Fin.tail t,t 0,?_⟩
      change P (Fin.cons (t 0) (Fin.tail t),x)
      simpa only [Fin.cons_self_tail] using ht

theorem project {J : Type} [Fintype J] {P : (J → ℝ) × E → Prop} (h : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  classical
  let e := Fintype.equivFin J
  let f : (Fin (Fintype.card J) → ℝ) × E →ₗ[ℝ] (J → ℝ) × E :=
    { toFun := fun p => (p.1 ∘ e,p.2), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply congr (projectFin (preimage h f))
  intro x
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨_,ht⟩
  · rintro ⟨t,ht⟩
    refine ⟨t ∘ e.symm,?_⟩
    change P ((fun j => t (e.symm (e j))),x)
    simpa only [Equiv.symm_apply_apply] using ht

theorem halfspace (f : E →ₗ[ℝ] ℝ) (b : ℝ) : Presented (fun x => f x ≤ b) :=
  ⟨Unit,inferInstance,fun _ => f,fun _ => b,fun _ => ⟨fun h _ => h,fun h => h ()⟩⟩

theorem intersection {P Q : E → Prop} (hp : Presented P) (hq : Presented Q) :
    Presented (fun x => P x ∧ Q x) := by
  obtain ⟨I,_,A,b,p⟩ := hp
  obtain ⟨J,_,B,c,q⟩ := hq
  refine ⟨I ⊕ J,inferInstance,Sum.elim A B,Sum.elim b c,fun x => ?_⟩
  change (P x ∧ Q x) ↔ _
  rw [p,q,Sum.forall]
  rfl

theorem equality (f : E →ₗ[ℝ] ℝ) (b : ℝ) : Presented (fun x => f x = b) := by
  apply congr (intersection (halfspace f b) (halfspace (-f) (-b)))
  intro x
  simp [le_antisymm_iff]

theorem forallFinite {I : Type} [Fintype I] {P : I → E → Prop} (h : ∀ i, Presented (P i)) :
    Presented (fun x => ∀ i, P i x) := by
  classical
  choose J inst A b eq using h
  letI : ∀ i, Fintype (J i) := inst
  refine ⟨Σ i, J i,inferInstance,fun ij => A ij.1 ij.2,fun ij => b ij.1 ij.2,fun x => ?_⟩
  simp only [eq,Sigma.forall]

theorem isClosed {P : ℝ → Prop} (h : Presented P) : IsClosed {x | P x} := by
  obtain ⟨I,_,A,b,eq⟩ := h
  have setEq : {x | P x} = ⋂ i, {x | A i x ≤ b i} := by ext x; simpa only [Set.mem_setOf_eq,Set.mem_iInter] using eq x
  rw [setEq]
  exact isClosed_iInter (fun i => isClosed_le (A i).continuous_of_finiteDimensional continuous_const)

theorem attain {J : Type} [Fintype J] {P : (J → ℝ) → Prop} (h : Presented P)
    (f : (J → ℝ) →ₗ[ℝ] ℝ) (hn : ∃ x, P x) (hb : BddAbove {r | ∃ x, P x ∧ r = f x}) :
    ∃ x, P x ∧ f x = sSup {r | ∃ x, P x ∧ r = f x} := by
  let g : ((J → ℝ) × ℝ) →ₗ[ℝ] ℝ := (LinearMap.snd ℝ _ _) - f.comp (LinearMap.fst ℝ _ _)
  have proj := project (intersection (preimage h (LinearMap.fst ℝ _ ℝ)) (equality g 0))
  have pres : Presented (fun r => ∃ x, P x ∧ r = f x) := by
    apply congr proj
    intro r
    exact exists_congr (fun x => by change P x ∧ r - f x = 0 ↔ _; rw [sub_eq_zero])
  obtain ⟨x,hx⟩ := hn
  obtain ⟨y,hy,eq⟩ := (isClosed pres).csSup_mem ⟨f x,x,hx,rfl⟩ hb
  exact ⟨y,hy,eq.symm⟩

/-- Finite vertex descriptions have finite inequality presentations in the original
coordinates, by eliminating the convex-combination coefficients. -/
theorem finiteHull {J : Type} [Fintype J] (V : Finset (J → ℝ)) :
    Presented (fun x => x ∈ convexHull ℝ (V : Set (J → ℝ))) := by
  classical
  let W := (↑V : Type) → ℝ
  let eval : ∀ i : ↑V, (W × (J → ℝ)) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun p => p.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let get : ∀ j : J, (W × (J → ℝ)) →ₗ[ℝ] ℝ := fun j =>
    { toFun := fun p => p.2 j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let one : W × (J → ℝ) →ₗ[ℝ] ℝ := ∑ i, eval i
  let combo (j : J) : W × (J → ℝ) →ₗ[ℝ] ℝ := ∑ i : ↑V, (i.1 j) • eval i
  have hp := project (intersection (forallFinite (fun i : ↑V => halfspace (-eval i) 0))
    (intersection (equality one 1) (forallFinite (fun j : J => equality (combo j - get j) 0))))
  apply congr hp
  intro x
  constructor
  · rintro ⟨w,hn,hs,he⟩
    apply mem_convexHull_of_exists_fintype w (fun i : ↑V => i.1)
    · intro i
      simpa [eval] using hn i
    · simpa [one,eval,LinearMap.sum_apply] using hs
    · exact fun i => i.2
    · ext j
      have h := he j
      simp only [combo,get,eval,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,
        LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul,sub_eq_zero] at h
      simpa [Finset.sum_apply,Pi.smul_apply,mul_comm] using h
  · intro hx
    obtain ⟨w,hn,hs,he⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun i => w i.1,fun i => ?_,?_,fun j => ?_⟩
    · simpa [eval] using hn i.1 i.2
    · simpa [one,eval,LinearMap.sum_apply,Finset.sum_attach] using hs
    · have h := congrFun he j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h
      rw [← Finset.sum_attach V (fun y => w y * y j)] at h
      simpa [combo,eval,get,LinearMap.sum_apply,sub_eq_zero,mul_comm] using h


/-- A bounded, attained objective has nonnegative prices for its auxiliary linear
constraints. Projection exposes a supporting row at the optimum. -/
theorem multiplierBound {J K : Type} [Fintype J] [Fintype K]
    {P : (J → ℝ) → Prop} (hp : Presented P) (g : K → (J → ℝ) →ₗ[ℝ] ℝ)
    (f : (J → ℝ) →ₗ[ℝ] ℝ) (v : ℝ)
    (att : ∃ x, P x ∧ (∀ k, 0 ≤ g k x) ∧ f x = v)
    (upper : ∀ x, P x → (∀ k, 0 ≤ g k x) → f x ≤ v) :
    ∃ price : K → ℝ, (∀ k, 0 ≤ price k) ∧
      ∀ x, P x → f x + ∑ k, price k * (g k x) ≤ v := by
  classical
  let T := (K → ℝ) × ℝ
  let fstX := LinearMap.fst ℝ (J → ℝ) T
  let sk : ∀ k : K, (J → ℝ) × T →ₗ[ℝ] ℝ := fun k =>
    { toFun := fun p => p.2.1 k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ht : (J → ℝ) × T →ₗ[ℝ] ℝ :=
    { toFun := fun p => p.2.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Q := fun (p : T) => ∃ x, P x ∧ (∀ k, p.1 k ≤ g k x) ∧ p.2 ≤ f x
  have qpres : Presented Q := by
    have h := project (intersection (preimage hp fstX) (intersection
      (forallFinite (fun k => halfspace (sk k - (g k).comp fstX) 0))
      (halfspace (ht - f.comp fstX) 0)))
    apply congr h
    intro p
    apply exists_congr
    intro x
    simp only [Q,sk,ht,fstX,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.fst_apply,
      LinearMap.coe_mk,AddHom.coe_mk,sub_nonpos]
  obtain ⟨I,inst,A,b,rows⟩ := qpres
  obtain ⟨x₀,hx₀,hg₀,hf₀⟩ := att
  have qv : Q (0,v) := ⟨x₀,hx₀,hg₀,hf₀.ge⟩
  let c := fun i => A i (0,1)
  have eval (i) (r : ℝ) : A i (0,r) = r * c i := by
    have e : ((0 : K → ℝ),r) = r • (0,1) := by simp
    rw [e,map_smul]
    rfl
  have r0 (i) : v * c i ≤ b i := (eval i v) ▸ (rows _).mp qv i
  have impossible {r : ℝ} (hr : v < r) : ¬ Q (0,r) := by
    rintro ⟨x,hx,hg,hu⟩
    exact hr.not_ge (hu.trans (upper x hx hg))
  let U := {i : I // 0 < c i}
  have hU : Nonempty U := by
    by_contra! h
    apply impossible (lt_add_one v)
    apply (rows _).mpr
    intro i
    rw [eval]
    have hci : c i ≤ 0 := le_of_not_gt (fun hh => h.false ⟨i,hh⟩)
    nlinarith only [r0 i,hci]
  letI : Nonempty U := hU
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset U) (fun i => b i.1 / c i.1) Finset.univ_nonempty
  have bmin : v ≤ b i.1 / c i.1 := (le_div_iff₀ i.property).mpr (r0 i.1)
  have tight : b i.1 = v * c i.1 := by
    have ub : b i.1 / c i.1 ≤ v := by
      by_contra! hv
      apply impossible hv
      apply (rows _).mpr
      intro j
      rw [eval]
      by_cases hj : 0 < c j
      · exact (le_div_iff₀ hj).mp (hi ⟨j,hj⟩ (Finset.mem_univ _))
      · exact (mul_le_mul_of_nonpos_right bmin (le_of_not_gt hj)).trans (r0 j)
    exact ((div_eq_iff i.property.ne').mp (le_antisymm ub bmin))
  let L := A i.1
  let d := fun k : K => L (Pi.single k 1,0)
  have decomp (s : K → ℝ) (r : ℝ) : L (s,r) = (∑ k, d k * s k) + r * c i.1 := by
    have e : (s,r) = (∑ k : K, s k • (Pi.single k (1 : ℝ), (0 : ℝ))) + (0,r) := by
      apply Prod.ext
      · funext k
        simp [Prod.fst_sum,Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq', smul_eq_mul, mul_ite]
      · simp [Prod.snd_sum]
    rw [e,map_add,map_sum,eval]
    simp only [map_smul,smul_eq_mul]
    simp only [d,L,mul_comm]
  have dnn (k : K) : 0 ≤ d k := by
    have mq : Q (-Pi.single k 1,v) := by
      refine ⟨x₀,hx₀,fun j => ?_,hf₀.ge⟩
      exact le_trans (neg_nonpos.mpr (by simp [Pi.single_apply]; split <;> norm_num)) (hg₀ j)
    have h := (rows _).mp mq i.1
    change L (-Pi.single k 1,v) ≤ b i.1 at h
    rw [decomp,tight] at h
    simpa [Pi.single_apply,Finset.sum_ite_eq',mul_ite] using h
  refine ⟨fun k => d k / c i.1,fun k => div_nonneg (dnn k) i.property.le,fun x hx => ?_⟩
  have p : Q (fun k => g k x, f x) := ⟨x,hx,fun _ => le_rfl,le_rfl⟩
  have h := (rows _).mp p i.1
  change L (fun k => g k x, f x) ≤ b i.1 at h
  rw [decomp,tight] at h
  have rearr (k : K) : d k / c i.1 * g k x = d k * g k x / c i.1 := by ring
  simp_rw [rearr]
  rw [← Finset.sum_div,add_div',div_le_iff₀ i.property]
  · linarith only [h]
  · exact i.property.ne'

end TradePolyhedra


private def xRead (N : Market) (v : Profile N) : LPVector N →ₗ[ℝ] (Trade N → ℝ) where
  toFun := fun u e => u (v,.inl e)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def tRead (N : Market) (a : Agent N) (v : Profile N) : LPVector N →ₗ[ℝ] ℝ :=
  LinearMap.proj (v,.inr a)

private def expectedRow (N : Market) (f : Profile N → (LPVector N →ₗ[ℝ] ℝ)) :
    LPVector N →ₗ[ℝ] ℝ := ∑ v, prior N v • f v

private theorem expectedRow_apply (N : Market) (f : Profile N → (LPVector N →ₗ[ℝ] ℝ))
    (u : LPVector N) : expectedRow N f u = expect N (fun v => f v u) := by
  simp only [expectedRow,expect,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

private def vRow (N : Market) (a : Agent N) (t : Ty N a) (v : Profile N) : LPVector N →ₗ[ℝ] ℝ :=
  Sum.elim (fun _ => ∑ e, coord N a t e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))
    (fun _ => -(∑ e, coord N a t e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))) a

private theorem vRow_apply (N : Market) (a : Agent N) (t : Ty N a) (v : Profile N) (u : LPVector N) :
    vRow N a t v u = valueUtility N a t ((decode N u).q v) := by
  cases a <;> simp [vRow,valueUtility,decode,LinearMap.sum_apply]

private def uRow (N : Market) (a : Agent N) (t r : Ty N a) : LPVector N →ₗ[ℝ] ℝ :=
  expectedRow N (fun v => vRow N a t (overwrite N v a r) - tRead N a (overwrite N v a r))

private theorem uRow_apply (N : Market) (a : Agent N) (t r : Ty N a) (u : LPVector N) :
    uRow N a t r u = U N (decode N u) a t r := by
  simp only [uRow,expectedRow_apply,LinearMap.sub_apply,vRow_apply,U,tRead,LinearMap.proj_apply,decode]

private def rRow (N : Market) (a : Agent N) (t : Ty N a) (r : Option (Ty N a)) : LPVector N →ₗ[ℝ] ℝ :=
  r.elim 0 (uRow N a t)

private theorem rRow_apply (N : Market) (a : Agent N) (t : Ty N a) (r : Option (Ty N a)) (u : LPVector N) :
    rRow N a t r u = reportUtility N (decode N u) a t r := by
  cases r with
  | none => cases a <;> simp [rRow,reportUtility,valueUtility,nullAllocation,nullTransfer]
  | some r => exact uRow_apply N a t r u

private def gainRow (N : Market) : LPVector N →ₗ[ℝ] ℝ :=
  expectedRow N (fun v => ∑ e, gains N v e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))

private theorem gainRow_apply (N : Market) (u : LPVector N) : gainRow N u = GFT N (decode N u).q := by
  unfold gainRow GFT
  rw [expectedRow_apply]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul,decode]
  simp only [mul_comm]

private theorem programPresented (N : Market) : TradePolyhedra.Presented (fun u => programFeasible N (decode N u)) := by
  classical
  let V := N.family.image (indicator N)
  have hull : TradePolyhedra.Presented (fun y => y ∈ allocationPolytope N) := by
    have h : (V : Set (Trade N → ℝ)) = {y | ∃ X ∈ N.family, y = indicator N X} := by
      ext y
      simp [V,eq_comm]
    simpa only [h,allocationPolytope] using TradePolyhedra.finiteHull V
  have alloc := TradePolyhedra.forallFinite (fun v : Profile N => TradePolyhedra.preimage hull (xRead N v))
  let budget := expectedRow N (fun v => ∑ a, tRead N a v)
  have ic := TradePolyhedra.forallFinite (fun a : Agent N => TradePolyhedra.forallFinite (fun t : Ty N a =>
    TradePolyhedra.forallFinite (fun r : Option (Ty N a) => TradePolyhedra.halfspace (rRow N a t r - uRow N a t t) 0)))
  apply TradePolyhedra.congr (TradePolyhedra.intersection alloc (TradePolyhedra.intersection (TradePolyhedra.halfspace (-budget) 0) ic))
  intro u
  change (feasible N (decode N u).q ∧ (-budget) u ≤ 0 ∧
    ∀ a t r, (rRow N a t r - uRow N a t t) u ≤ 0) ↔ _
  simp only [programFeasible,WBB,budget,LinearMap.neg_apply,expectedRow_apply,LinearMap.sum_apply,
    tRead,LinearMap.proj_apply,neg_nonpos,LinearMap.sub_apply,rRow_apply,uRow_apply,sub_nonpos,decode]

private def encodeTrade (N : Market) (m : SignedMechanism N) : LPVector N :=
  fun w => Sum.elim (fun e => m.q w.1 e) (fun a => m.t a w.1) w.2

private theorem decode_encode (N : Market) (m : SignedMechanism N) : decode N (encodeTrade N m) = m := by
  cases m
  rfl

private theorem primal (N : Market) :
    finiteLPPresentation N ∧
    Fintype.card (Variable N) = (N.ne + N.nb + N.ns) * Fintype.card (Profile N) ∧
    programFeasible N (zeroSigned N) ∧
    (∀ m : SignedMechanism N, programFeasible N m → GFT N m.q ≤ FB N) ∧
    ∃ m : SignedMechanism N, programFeasible N m ∧ GFT N m.q = OPT N := by
  classical
  have presentation := programPresented N
  refine ⟨?_, secondBestTradeVariableCard N, secondBestTradeZeroFeasible N, secondBestTradeGainsBound N, ?_⟩
  · obtain ⟨I,inst,A,b,h⟩ := presentation
    let e := Fintype.equivFin I
    refine ⟨Fintype.card I, fun j => A (e.symm j), fun j => b (e.symm j), gainRow N, ?_, gainRow_apply N⟩
    intro u
    refine (h u).trans ?_
    exact ⟨fun h j => h _,fun h i => by simpa only [Equiv.symm_apply_apply] using h (e i)⟩
  · have ne : ∃ u, programFeasible N (decode N u) :=
      ⟨encodeTrade N (zeroSigned N),by rw [decode_encode]; exact secondBestTradeZeroFeasible N⟩
    have hb : BddAbove {r | ∃ u, programFeasible N (decode N u) ∧ r = gainRow N u} := by
      refine ⟨FB N,?_⟩
      rintro r ⟨u,hu,rfl⟩
      rw [gainRow_apply]
      exact secondBestTradeGainsBound N _ hu
    obtain ⟨u,hu,he⟩ := TradePolyhedra.attain presentation (gainRow N) ne hb
    refine ⟨decode N u,hu,?_⟩
    rw [← gainRow_apply,he]
    unfold OPT
    congr 1
    ext r
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨decode N y,hy,gainRow_apply N y⟩
    · rintro ⟨m,hm,rfl⟩
      refine ⟨encodeTrade N m,by rwa [decode_encode],?_⟩
      rw [gainRow_apply,decode_encode]

end Primal

private abbrev Condition (N : Market) := Unit ⊕ Σ a : Agent N, Ty N a × Option (Ty N a)

private def slackRow (N : Market) : Condition N → LPVector N →ₗ[ℝ] ℝ
  | .inl _ => Primal.expectedRow N (fun v => ∑ a, Primal.tRead N a v)
  | .inr ⟨a,t,r⟩ => Primal.uRow N a t t - Primal.rRow N a t r

private theorem allSlack (N : Market) (u : LPVector N) :
    (∀ k, 0 ≤ slackRow N k u) ↔
      WBB N (decode N u) ∧ ∀ a t r, reportUtility N (decode N u) a t r ≤ U N (decode N u) a t t := by
  constructor
  · intro h
    refine ⟨?_,fun a t r => ?_⟩
    · have h' := h (.inl ())
      simpa only [slackRow,Primal.expectedRow_apply,LinearMap.sum_apply,Primal.tRead,LinearMap.proj_apply,WBB,decode] using h'
    · simpa only [slackRow,LinearMap.sub_apply,Primal.uRow_apply,Primal.rRow_apply,sub_nonneg] using h (.inr ⟨a,t,r⟩)
  · rintro ⟨hb,hi⟩ (unit|⟨a,t,r⟩)
    · simpa only [slackRow,Primal.expectedRow_apply,LinearMap.sum_apply,Primal.tRead,LinearMap.proj_apply,WBB,decode] using hb
    · simpa only [slackRow,LinearMap.sub_apply,Primal.uRow_apply,Primal.rRow_apply,sub_nonneg] using hi a t r

private theorem optimalDual (N : Market) : ∃ z : Dual N, lagrangianSup N z = (OPT N : EReal) := by
  classical
  have presentation : Primal.TradePolyhedra.Presented (fun u : LPVector N => feasible N (decode N u).q) := by
    let V := N.family.image (indicator N)
    have hull : Primal.TradePolyhedra.Presented (fun y => y ∈ allocationPolytope N) := by
      have h : (V : Set (Trade N → ℝ)) = {y | ∃ X ∈ N.family, y = indicator N X} := by
        ext y
        simp [V,eq_comm]
      simpa only [h,allocationPolytope] using Primal.TradePolyhedra.finiteHull V
    exact Primal.TradePolyhedra.forallFinite (fun v : Profile N => Primal.TradePolyhedra.preimage hull (Primal.xRead N v))
  obtain ⟨m,hm,he⟩ := (Primal.primal N).2.2.2.2
  have att : ∃ x : LPVector N, feasible N (decode N x).q ∧ (∀ k, 0 ≤ slackRow N k x) ∧ Primal.gainRow N x = OPT N := by
    refine ⟨Primal.encodeTrade N m,by rw [Primal.decode_encode]; exact hm.1, (allSlack N _).mpr ?_,?_⟩
    · rw [Primal.decode_encode]
      exact hm.2
    · rwa [Primal.gainRow_apply,Primal.decode_encode]
  have upper (u : LPVector N) (hu : feasible N (decode N u).q) (hg : ∀ k, 0 ≤ slackRow N k u) :
      Primal.gainRow N u ≤ OPT N := by
    rw [Primal.gainRow_apply]
    apply le_csSup
    · refine ⟨FB N,?_⟩
      rintro r ⟨m,hm,rfl⟩
      exact Primal.secondBestTradeGainsBound N m hm
    · exact ⟨_,⟨hu,(allSlack N u).mp hg⟩,rfl⟩
  obtain ⟨price,hp,ub⟩ := Primal.TradePolyhedra.multiplierBound presentation (slackRow N) (Primal.gainRow N) (OPT N) att upper
  let z : Dual N := ⟨⟨price (.inl ()),hp _⟩,fun a t r => ⟨price (.inr ⟨a,t,r⟩),hp _⟩⟩
  refine ⟨z,le_antisymm ?_ (secondBestTradeWeakDuality N z)⟩
  apply sSup_le
  rintro w ⟨m,hx,rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  let u := Primal.encodeTrade N m
  have hd : decode N u = m := Primal.decode_encode N m
  have h := ub u (by rwa [hd])
  rw [Fintype.sum_sum_type,Fintype.sum_sigma] at h
  simp only [Fintype.sum_prod_type, Fintype.sum_unique,slackRow,Primal.expectedRow_apply,
    LinearMap.sum_apply,Primal.gainRow_apply,LinearMap.sub_apply,Primal.uRow_apply,Primal.rRow_apply,hd] at h
  change GFT N m.q + price (.inl ()) * expect N (fun v => ∑ a, m.t a v) +
    ∑ a, ∑ t, ∑ r : Option (Ty N a), price (.inr ⟨a,t,r⟩) * (U N m a t t - reportUtility N m a t r) ≤ _
  have ht (a : Agent N) (v : Profile N) : Primal.tRead N a v u = m.t a v := rfl
  simp only [ht] at h
  linarith only [h]

theorem solution (N : Market) :
    (∀ z : Dual N, (OPT N : EReal) ≤ lagrangianSup N z) ∧
    (∀ z : Dual N, lagrangianSup N z ≠ ⊥ ∧
      (lagrangianSup N z < ⊤ ↔ coefficientsVanish N z) ∧
      (coefficientsVanish N z → lagrangianSup N z = (XiObjective N z : EReal))) ∧
    ∃ z : Dual N, lagrangianSup N z = (OPT N : EReal) :=
  ⟨secondBestTradeWeakDuality N,secondBestTradePartialDualityPointwise N,optimalDual N⟩
