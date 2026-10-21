-- Prove2me | solution 1 for ParamMCF.MCA.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:08:15.144403+00:00
-- url     : https://prove2.me/submissions/69d23610-c857-436c-85b0-71a12a7c6b40

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model
import Theorems.Thm_ParamMCF_MCA_eq_17
import Theorems.Thm_ParamMCF_MCA_case_16
import Theorems.Thm_ParamMCF_MCA_edge_flow_bound

namespace ParamMCF.MCA

/-- A continuous function that is nonpositive on negatives is nonpositive at zero. -/
lemma pmcf_nonpos_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, s < 0 → φ s ≤ 0) :
    φ 0 ≤ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Iio 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A continuous function that is nonnegative on positives is nonnegative at zero. -/
lemma pmcf_nonneg_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, 0 < s → 0 ≤ φ s) :
    0 ≤ φ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

lemma pmcf_F_hasDeriv (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (edgeCost g) (g t) t :=
  (hg.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma pmcf_F_cont (g : ℝ → ℝ) (hg : Continuous g) : Continuous (edgeCost g) :=
  continuous_iff_continuousAt.2 fun t => (pmcf_F_hasDeriv g hg t).continuousAt

lemma pmcf_F_strict (g : ℝ → ℝ) (hg : IsContinuousMarginalCost g) :
    StrictMonoOn (edgeCost g) (Set.Ici 0) ∧ StrictAntiOn (edgeCost g) (Set.Iic 0) := by
  have h0a : 0 ≤ g 0 := pmcf_nonneg_at_zero g hg.1.continuousAt hg.2.2.1
  have h0b : g 0 ≤ 0 := pmcf_nonpos_at_zero g hg.1.continuousAt hg.2.2.2
  have hc : ∀ s, ContinuousOn (edgeCost g) s := fun s => (pmcf_F_cont g hg.1).continuousOn
  constructor
  · refine strictMonoOn_of_deriv_pos (convex_Ici 0) (hc _) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(pmcf_F_hasDeriv g hg.1 t).deriv]
    have := hg.2.1 (Set.mem_Ioi.1 ht)
    linarith
  · refine strictAntiOn_of_deriv_neg (convex_Iic 0) (hc _) fun t ht => ?_
    rw [interior_Iic] at ht
    rw [(pmcf_F_hasDeriv g hg.1 t).deriv]
    have := hg.2.1 (Set.mem_Iio.1 ht)
    linarith

lemma pmcf_F_nonneg (g : ℝ → ℝ) (hg : IsContinuousMarginalCost g) (t : ℝ) :
    0 ≤ edgeCost g t := by
  have h00 : edgeCost g 0 = 0 := by simp [edgeCost]
  obtain ⟨h1, h2⟩ := pmcf_F_strict g hg
  rcases le_total 0 t with h | h
  · rw [← h00]; exact h1.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
  · rw [← h00]; exact h2.antitoneOn (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h

/-- Moving a flow value toward `0` (without crossing it) does not increase the edge cost,
and strictly decreases it if the value changes. -/
lemma pmcf_F_between (g : ℝ → ℝ) (hg : IsContinuousMarginalCost g) (s t : ℝ)
    (h : (0 ≤ t ∧ t ≤ s) ∨ (s ≤ t ∧ t ≤ 0)) :
    edgeCost g t ≤ edgeCost g s ∧ (t ≠ s → edgeCost g t < edgeCost g s) := by
  obtain ⟨h1, h2⟩ := pmcf_F_strict g hg
  rcases h with ⟨ht, hts⟩ | ⟨hst, ht⟩
  · have hs : 0 ≤ s := ht.trans hts
    refine ⟨h1.monotoneOn (Set.mem_Ici.2 ht) (Set.mem_Ici.2 hs) hts, fun hne => ?_⟩
    exact h1 (Set.mem_Ici.2 ht) (Set.mem_Ici.2 hs) (lt_of_le_of_ne hts hne)
  · have hs : s ≤ 0 := hst.trans ht
    refine ⟨h2.antitoneOn (Set.mem_Iic.2 hs) (Set.mem_Iic.2 ht) hst, fun hne => ?_⟩
    exact h2 (Set.mem_Iic.2 hs) (Set.mem_Iic.2 ht) (lt_of_le_of_ne hst (Ne.symm hne))

/-- Edge costs are coercive: sublevel sets are bounded. -/
lemma pmcf_F_coercive (g : ℝ → ℝ) (hg : IsContinuousMarginalCost g) (c : ℝ) :
    ∃ R, ∀ t, edgeCost g t ≤ c → |t| ≤ R := by
  have h0a : 0 ≤ g 0 := pmcf_nonneg_at_zero g hg.1.continuousAt hg.2.2.1
  have h0b : g 0 ≤ 0 := pmcf_nonpos_at_zero g hg.1.continuousAt hg.2.2.2
  have hp : 0 < g 1 := by have := hg.2.1 (show (0 : ℝ) < 1 by norm_num); linarith
  have hn : g (-1) < 0 := by have := hg.2.1 (show (-1 : ℝ) < 0 by norm_num); linarith
  have hd := pmcf_F_hasDeriv g hg.1
  -- right tail
  have hR : ∀ t, 1 ≤ t → g 1 * (t - 1) ≤ edgeCost g t := by
    have hphi : ∀ t, HasDerivAt (fun t => edgeCost g t - g 1 * (t - 1)) (g t - g 1) t := by
      intro t
      exact ((hd t).sub (((hasDerivAt_id' t).sub_const 1).const_mul (g 1))).congr_deriv
        (by ring)
    have hmono : MonotoneOn (fun t => edgeCost g t - g 1 * (t - 1)) (Set.Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
        (fun t _ => (hphi t).continuousAt.continuousWithinAt)
        (fun t _ => (hphi t).differentiableAt.differentiableWithinAt) fun t ht => ?_
      rw [interior_Ici] at ht
      rw [(hphi t).deriv]
      linarith [hg.2.1 (Set.mem_Ioi.1 ht)]
    intro t ht
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    simp only at this
    linarith [pmcf_F_nonneg g hg 1]
  -- left tail
  have hL : ∀ t, t ≤ -1 → g (-1) * (t + 1) ≤ edgeCost g t := by
    have hphi : ∀ t, HasDerivAt (fun t => edgeCost g t - g (-1) * (t + 1)) (g t - g (-1)) t := by
      intro t
      exact ((hd t).sub (((hasDerivAt_id' t).add_const 1).const_mul (g (-1)))).congr_deriv
        (by ring)
    have hanti : AntitoneOn (fun t => edgeCost g t - g (-1) * (t + 1)) (Set.Iic (-1)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic (-1))
        (fun t _ => (hphi t).continuousAt.continuousWithinAt)
        (fun t _ => (hphi t).differentiableAt.differentiableWithinAt) fun t ht => ?_
      rw [interior_Iic] at ht
      rw [(hphi t).deriv]
      linarith [hg.2.1 (Set.mem_Iio.1 ht)]
    intro t ht
    have := hanti (Set.mem_Iic.2 ht) (Set.mem_Iic.2 le_rfl) ht
    simp only at this
    linarith [pmcf_F_nonneg g hg (-1)]
  refine ⟨1 + |c| / g 1 + |c| / (-g (-1)), fun t ht => ?_⟩
  have h1 : 0 ≤ |c| / g 1 := div_nonneg (abs_nonneg _) hp.le
  have h2 : 0 ≤ |c| / (-g (-1)) := div_nonneg (abs_nonneg _) (by linarith)
  rw [abs_le]
  constructor
  · by_contra hcon
    push_neg at hcon
    have ht1 : t ≤ -1 := by linarith
    have := hL t ht1
    have hne : g (-1) ≠ 0 := hn.ne
    have hk : (-g (-1)) * (|c| / (-g (-1))) = |c| := by field_simp
    have : (-g (-1)) * (-t - 1) ≤ c := by linarith
    have : (-g (-1)) * (|c| / (-g (-1))) < (-g (-1)) * (-t - 1) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    linarith [le_abs_self c]
  · by_contra hcon
    push_neg at hcon
    have ht1 : 1 ≤ t := by linarith
    have := hR t ht1
    have hk : g 1 * (|c| / g 1) = |c| := by field_simp
    have : g 1 * (|c| / g 1) < g 1 * (t - 1) := mul_lt_mul_of_pos_left (by linarith) hp
    linarith [le_abs_self c]

lemma pmcf_feasible_closed {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (d : V → ℝ) :
    IsClosed {y : E → ℝ | Feasible G directed d y} := by
  have hnet : ∀ v, Continuous (fun y : E → ℝ => netInflow G y v) := by
    intro v
    unfold netInflow
    exact (continuous_finset_sum _ fun e _ => continuous_apply e).sub
      (continuous_finset_sum _ fun e _ => continuous_apply e)
  have h1 : IsClosed {y : E → ℝ | ∀ v, netInflow G y v = d v} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun v => isClosed_eq (hnet v) continuous_const
  cases directed with
  | false => simpa [Feasible] using h1
  | true =>
    have h2 : IsClosed {y : E → ℝ | ∀ e, 0 ≤ y e} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
    have : {y : E → ℝ | Feasible G true d y} =
        {y | ∀ v, netInflow G y v = d v} ∩ {y | ∀ e, 0 ≤ y e} := by
      ext y; simp [Feasible]
    rw [this]; exact h1.inter h2

/-- A minimum-cost flow exists as soon as a feasible flow exists. -/
lemma pmcf_exists_min {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (f : E → ℝ → ℝ)
    (hf : ∀ e, IsContinuousMarginalCost (f e)) (d : V → ℝ) (y0 : E → ℝ)
    (hy0 : Feasible G directed d y0) : ∃ xs, IsMinCostFlow G directed f d xs := by
  classical
  set c0 := cost f y0
  have hcont : Continuous (cost f) := by
    unfold cost
    exact continuous_finset_sum _ fun e _ => (pmcf_F_cont (f e) (hf e).1).comp (continuous_apply e)
  choose R hR using fun e => pmcf_F_coercive (f e) (hf e) c0
  set S := {y : E → ℝ | Feasible G directed d y} ∩ {y | cost f y ≤ c0} with hS
  have hSc : IsClosed S :=
    (pmcf_feasible_closed G directed d).inter (isClosed_le hcont continuous_const)
  have hsub : S ⊆ Set.pi Set.univ (fun e => Set.Icc (-R e) (R e)) := by
    intro y hy e _
    have h1 : edgeCost (f e) (y e) ≤ cost f y :=
      Finset.single_le_sum (f := fun e => edgeCost (f e) (y e))
        (fun e _ => pmcf_F_nonneg (f e) (hf e) (y e)) (Finset.mem_univ e)
    exact abs_le.1 (hR e (y e) (h1.trans hy.2))
  have hK : IsCompact S :=
    (isCompact_univ_pi fun e => isCompact_Icc).of_isClosed_subset hSc hsub
  obtain ⟨xs, hxsS, hmin⟩ := hK.exists_isMinOn ⟨y0, hy0, show cost f y0 ≤ c0 from le_rfl⟩ hcont.continuousOn
  refine ⟨xs, hxsS.1, fun y hy => ?_⟩
  by_cases hyc : cost f y ≤ c0
  · exact hmin ⟨hy, hyc⟩
  · push_neg at hyc
    exact hxsS.2.trans hyc.le

theorem lemma_4_red {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f ft : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hft : ∀ e, IsContinuousMarginalCost (ft e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (hclose :
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |ft e x - f e x| ≤
          (alpha - 1) / (1 + alpha) * |f e x| +
            beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax)) ∨
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |f e x| ≤ |ft e x| ∧
          |ft e x - f e x| ≤
            (alpha - 1) * |f e x| +
              beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax)))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed ft (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt  := by
  classical
  intro lam hlam
  set X := xmax b0 b lamMax with hXdef
  set d := demand b0 b lam with hd
  have hxtl := hxt lam hlam
  refine ⟨hxtl.1, ?_⟩
  have hfc : ∀ e, IsContinuousMarginalCost (f e) := fun e =>
    ⟨(hf e).2.1.continuous, (hf e).1, (hf e).2.2.1, (hf e).2.2.2⟩
  obtain ⟨xs, hxs⟩ := pmcf_exists_min G directed f hfc d (xt lam) hxtl.1
  have hbt : ∀ e, |xt lam e| ≤ X :=
    edge_flow_bound G directed ft hft b0 b hb0 hb lamMax lam hlamMax hlam (xt lam) hxtl
  have hbs : ∀ e, |xs e| ≤ X :=
    edge_flow_bound G directed f hfc b0 b hb0 hb lamMax lam hlamMax hlam xs hxs
  have hopt : optCost G directed f d = cost f xs := by
    unfold optCost
    refine IsLeast.csInf_eq ⟨⟨xs, hxs.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hxs.2 y hy
  rw [hopt]
  have hcomp : cost ft (xt lam) ≤ cost ft xs := hxtl.2 xs hxs.1
  have hmemt : ∀ e, xt lam e ∈ Set.Icc (-X) X := fun e => abs_le.1 (hbt e)
  have hmems : ∀ e, xs e ∈ Set.Icc (-X) X := fun e => abs_le.1 (hbs e)
  rcases Nat.eq_zero_or_pos (Fintype.card E) with hm0 | hmpos
  · have hE : IsEmpty E := Fintype.card_eq_zero_iff.1 hm0
    have h1 : cost f (xt lam) = 0 := by simp [cost]
    have h2 : cost f xs = 0 := by simp [cost]
    rw [h1, h2]; linarith
  set m : ℝ := (Fintype.card E : ℝ) with hmdef
  have hm : 0 < m := by rw [hmdef]; exact_mod_cast hmpos
  have hsumc : ∀ (k c : ℝ) (u : E → ℝ), ∑ e, (k * u e + c) = k * ∑ e, u e + m * c := by
    intro k c u
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have ha1 : 0 < 1 + alpha := by linarith
  rcases hclose with h15 | h16
  · have h17 := fun e => eq_17 (f e) (ft e) (hf e) (hft e).1 alpha beta m X halpha hbeta hm hX
      (fun s hs => h15 e s hs)
    have hA : cost f (xt lam) ≤ ∑ e, ((1 + alpha) / 2 * edgeCost (ft e) (xt lam e) +
        beta / (2 * m)) := by
      unfold cost
      refine Finset.sum_le_sum fun e _ => ?_
      have h := (h17 e (xt lam e) (hmemt e)).1
      have hk : (1 + alpha) / 2 * (2 / (1 + alpha) * edgeCost (f e) (xt lam e) -
          beta / ((1 + alpha) * m)) = edgeCost (f e) (xt lam e) - beta / (2 * m) := by
        field_simp
      have := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ (1 + alpha) / 2)
      rw [hk] at this
      linarith
    have hB : (1 + alpha) / 2 * cost ft xs ≤ ∑ e, (alpha * edgeCost (f e) (xs e) +
        beta / (2 * m)) := by
      unfold cost
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      have h := (h17 e (xs e) (hmems e)).2
      have hk : (1 + alpha) / 2 * (2 * alpha / (1 + alpha) * edgeCost (f e) (xs e) +
          beta / ((1 + alpha) * m)) = alpha * edgeCost (f e) (xs e) + beta / (2 * m) := by
        field_simp
      have := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ (1 + alpha) / 2)
      rw [hk] at this
      exact this
    rw [hsumc] at hA hB
    have hmb : m * (beta / (2 * m)) = beta / 2 := by field_simp
    have hcomp' := mul_le_mul_of_nonneg_left hcomp (by linarith : (0 : ℝ) ≤ (1 + alpha) / 2)
    unfold cost at hcomp' hA hB ⊢
    linarith
  · have h16' := fun e => case_16 (f e) (ft e) (hf e) ⟨(hft e).1, (hft e).2.2.1, (hft e).2.2.2⟩
      alpha beta m X halpha hbeta hm hX (fun s hs => (h16 e s hs).1) (fun s hs => (h16 e s hs).2)
    have hA : cost f (xt lam) ≤ cost ft (xt lam) :=
      Finset.sum_le_sum fun e _ => (h16' e (xt lam e) (hmemt e)).1
    have hB : cost ft xs ≤ ∑ e, (alpha * edgeCost (f e) (xs e) + beta / m) :=
      Finset.sum_le_sum fun e _ => (h16' e (xs e) (hmems e)).2
    rw [hsumc] at hB
    have hmb : m * (beta / m) = beta := by field_simp
    unfold cost at hA hB hcomp ⊢
    linarith

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f ft : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hft : ∀ e, IsContinuousMarginalCost (ft e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (hclose :
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |ft e x - f e x| ≤
          (alpha - 1) / (1 + alpha) * |f e x| +
            beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax)) ∨
      (∀ e x, x ∈ Set.Icc (-(xmax b0 b lamMax)) (xmax b0 b lamMax) →
        |f e x| ≤ |ft e x| ∧
          |ft e x - f e x| ≤
            (alpha - 1) * |f e x| +
              beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax)))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed ft (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt :=
  lemma_4_red G hG directed f ft hf hft b0 b hb0 hb alpha beta lamMax halpha hbeta hlamMax hX hclose xt hxt
