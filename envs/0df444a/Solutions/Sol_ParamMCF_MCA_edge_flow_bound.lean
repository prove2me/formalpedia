-- Prove2me | solution 1 for ParamMCF.MCA.edge_flow_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:04:50.067333+00:00
-- url     : https://prove2.me/submissions/18d71f37-810f-4c62-a2e5-c8abda11b40e

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

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

section NetLemmas
variable {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]

lemma pmcf_net_add (G : Network V E) (c c' : E → ℝ) (v : V) :
    netInflow G (fun e => c e + c' e) v = netInflow G c v + netInflow G c' v := by
  unfold netInflow
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; ring

lemma pmcf_net_sub_smul (G : Network V E) (c c' : E → ℝ) (ε : ℝ) (v : V) :
    netInflow G (fun e => c e - ε * c' e) v = netInflow G c v - ε * netInflow G c' v := by
  unfold netInflow
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

lemma pmcf_net_single (G : Network V E) (e : E) (σ : ℝ) (v : V) :
    netInflow G (fun e' => if e' = e then σ else 0) v =
      σ * ((if v = G.tgt e then 1 else 0) - (if v = G.src e then 1 else 0)) := by
  unfold netInflow
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, @eq_comm _ (G.tgt e) v,
    @eq_comm _ (G.src e) v]
  split_ifs <;> ring

lemma pmcf_sum_net (G : Network V E) (x : E → ℝ) (T : Finset V) :
    ∑ v ∈ T, netInflow G x v =
      ∑ e, ((if G.tgt e ∈ T then x e else 0) - (if G.src e ∈ T then x e else 0)) := by
  unfold netInflow
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  · simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp

/-- A path in the flow-direction graph carries a unit flow agreeing in sign with `x`. -/
lemma pmcf_path_flow (G : Network V E) (x : E → ℝ) (q : V) (w : V)
    (h : Relation.ReflTransGen (fun u w => ∃ e, (0 < x e ∧ G.src e = u ∧ G.tgt e = w) ∨
      (x e < 0 ∧ G.tgt e = u ∧ G.src e = w)) q w) :
    ∃ c : E → ℝ, (∀ v, netInflow G c v = (if v = w then 1 else 0) - (if v = q then 1 else 0)) ∧
      (∀ e, 0 ≤ c e * x e) ∧ (∀ e, x e = 0 → c e = 0) := by
  induction h with
  | refl =>
    refine ⟨fun _ => 0, fun v => ?_, fun e => by simp, fun e _ => rfl⟩
    unfold netInflow; simp
  | @tail u w' _ hR ih =>
    obtain ⟨c, hc1, hc2, hc3⟩ := ih
    obtain ⟨e, he⟩ := hR
    rcases he with ⟨hx, hs, ht⟩ | ⟨hx, ht, hs⟩
    · refine ⟨fun e' => c e' + (if e' = e then 1 else 0), fun v => ?_, fun e' => ?_, fun e' h0 => ?_⟩
      · rw [pmcf_net_add, hc1, pmcf_net_single, hs, ht]
        split_ifs <;> norm_num
      · by_cases h : e' = e
        · subst h; simp; nlinarith [hc2 e']
        · simp [h]; exact hc2 e'
      · have : e' ≠ e := by rintro rfl; linarith
        simp [this, hc3 e' h0]
    · refine ⟨fun e' => c e' + (if e' = e then -1 else 0), fun v => ?_, fun e' => ?_, fun e' h0 => ?_⟩
      · rw [pmcf_net_add, hc1, pmcf_net_single, hs, ht]
        split_ifs <;> norm_num
      · by_cases h : e' = e
        · subst h; simp; nlinarith [hc2 e']
        · simp [h]; exact hc2 e'
      · have : e' ≠ e := by rintro rfl; linarith
        simp [this, hc3 e' h0]

end NetLemmas

/-- `½ ∑ |d_v| ≤ x^max` for every admissible parameter. -/
lemma pmcf_half_le_xmax {V : Type*} [Fintype V] (b0 b : V → ℝ) (lamMax lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 lamMax) :
    (1 / 2 : ℝ) * ∑ v, |b0 v + lam * b v| ≤ xmax b0 b lamMax := by
  unfold xmax
  refine le_csSup ?_ ⟨lam, hlam, rfl⟩
  have hc : Continuous (fun lam : ℝ => (1 / 2 : ℝ) * ∑ v, |b0 v + lam * b v|) := by fun_prop
  exact (isCompact_Icc.image hc).bddAbove

/-- For balanced `d`, any partial sum of `d` is at most `½ ∑ |d_v|`. -/
lemma pmcf_partial_le {V : Type*} [Fintype V] (d : V → ℝ) (hsum : ∑ v, d v = 0)
    (T : Finset V) : ∑ v ∈ T, d v ≤ (1 / 2 : ℝ) * ∑ v, |d v| := by
  have h1 : ∑ v ∈ T, d v ≤ ∑ v ∈ T, max (d v) 0 := Finset.sum_le_sum fun v _ => le_max_left _ _
  have h2 : ∑ v ∈ T, max (d v) 0 ≤ ∑ v, max (d v) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => le_max_right _ _
  have h3 : ∑ v, max (d v) 0 = (1 / 2 : ℝ) * ∑ v, |d v| := by
    have : ∀ v, max (d v) 0 = (|d v| + d v) / 2 := by
      intro v
      rcases le_total 0 (d v) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]; ring
      · rw [max_eq_right h, abs_of_nonpos h]; ring
    simp_rw [this]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  linarith

theorem edge_flow_bound_sol {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (directed : Bool) (g : E → ℝ → ℝ)
    (hg : ∀ e, IsContinuousMarginalCost (g e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (lamMax lam : ℝ) (hlamMax : 0 < lamMax) (hlam : lam ∈ Set.Icc 0 lamMax)
    (x : E → ℝ)
    (hx : IsMinCostFlow G directed g (demand b0 b lam) x) :
    ∀ e, |x e| ≤ xmax b0 b lamMax := by
  classical
  set d := demand b0 b lam with hd
  have hsum : ∑ v, d v = 0 := by
    simp only [hd, demand, Finset.sum_add_distrib, ← Finset.mul_sum, hb0, hb]; ring
  have hX : (1 / 2 : ℝ) * ∑ v, |d v| ≤ xmax b0 b lamMax := pmcf_half_le_xmax b0 b lamMax lam hlam
  have hX0 : 0 ≤ (1 / 2 : ℝ) * ∑ v, |d v| :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun v _ => abs_nonneg _)
  intro e0
  by_contra hcon
  push_neg at hcon
  have hx0 : x e0 ≠ 0 := by
    intro h; rw [h, abs_zero] at hcon; linarith
  set R : V → V → Prop := fun u w => ∃ e, (0 < x e ∧ G.src e = u ∧ G.tgt e = w) ∨
      (x e < 0 ∧ G.tgt e = u ∧ G.src e = w) with hR
  set p : V := if 0 < x e0 then G.src e0 else G.tgt e0 with hp
  set q : V := if 0 < x e0 then G.tgt e0 else G.src e0 with hq
  set σ : ℝ := if 0 < x e0 then 1 else -1 with hσ
  have hσx : 0 < σ * x e0 := by
    by_cases h : 0 < x e0
    · simp [hσ, h]
    · have : x e0 < 0 := lt_of_le_of_ne (not_lt.1 h) hx0
      simp [hσ, h]; linarith
  have hRpq : R p q := by
    refine ⟨e0, ?_⟩
    by_cases h : 0 < x e0
    · left; simp [hp, hq, h]
    · right; refine ⟨lt_of_le_of_ne (not_lt.1 h) hx0, ?_, ?_⟩ <;> simp [hp, hq, h]
  by_cases hpS : Relation.ReflTransGen R q p
  · -- a cycle in the flow-direction graph: cancel it
    obtain ⟨c, hc1, hc2, hc3⟩ := pmcf_path_flow G x q p hpS
    set ct : E → ℝ := fun e => c e + (if e = e0 then σ else 0) with hct
    have hct1 : ∀ v, netInflow G ct v = 0 := by
      intro v
      rw [hct, pmcf_net_add, hc1, pmcf_net_single]
      by_cases h : 0 < x e0
      · simp only [hp, hq, hσ, h, if_true]
        split_ifs <;> norm_num
      · simp only [hp, hq, hσ, h, if_false]
        split_ifs <;> norm_num
    have hct2 : ∀ e, 0 ≤ ct e * x e := by
      intro e
      by_cases h : e = e0
      · rw [h]; simp only [hct]; rw [if_pos trivial]; nlinarith [hc2 e0]
      · simp only [hct, h, if_false, add_zero]; exact hc2 e
    have hct3 : ∀ e, x e = 0 → ct e = 0 := by
      intro e h0
      have : e ≠ e0 := by rintro rfl; exact hx0 h0
      simp [hct, this, hc3 e h0]
    have hct0 : 0 < ct e0 * x e0 := by
      simp only [hct]; rw [if_pos trivial]; nlinarith [hc2 e0]
    -- a small step size
    have hev : ∀ e, ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε * |ct e| ≤ |x e| := by
      intro e
      by_cases h0 : x e = 0
      · exact Filter.Eventually.of_forall fun ε => by simp [hct3 e h0, h0]
      · have ht : Filter.Tendsto (fun ε : ℝ => ε * |ct e|) (nhds 0) (nhds 0) := by
          have := (Filter.tendsto_id (x := nhds (0 : ℝ))).mul_const |ct e|
          simpa using this
        have hpos : 0 < |x e| := abs_pos.2 h0
        exact ((ht.eventually (gt_mem_nhds hpos)).mono fun ε h => h.le).filter_mono
          nhdsWithin_le_nhds
    obtain ⟨ε, hε, hεpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
    have hεpos' : 0 < ε := hεpos
    set y : E → ℝ := fun e => x e - ε * ct e with hy
    have hbetw : ∀ e, (0 ≤ y e ∧ y e ≤ x e) ∨ (x e ≤ y e ∧ y e ≤ 0) := by
      intro e
      have h1 := hε e
      have h2 := hct2 e
      rcases lt_trichotomy (x e) 0 with hneg | hz | hpos
      · right
        have hc : ct e ≤ 0 := by nlinarith
        rw [abs_of_nonpos hc, abs_of_neg hneg] at h1
        simp only [hy]; constructor <;> nlinarith
      · left; simp [hy, hz, hct3 e hz]
      · left
        have hc : 0 ≤ ct e := by nlinarith
        rw [abs_of_nonneg hc, abs_of_pos hpos] at h1
        simp only [hy]; constructor <;> nlinarith
    have hyfeas : Feasible G directed d y := by
      refine ⟨fun v => ?_, fun hdir e => ?_⟩
      · rw [hy, pmcf_net_sub_smul, hct1, hx.1.1 v]; ring
      · rcases hbetw e with h | h
        · exact h.1
        · have := hx.1.2 hdir e; linarith [h.1]
    have hlt : cost g y < cost g x := by
      unfold cost
      apply Finset.sum_lt_sum
      · intro e _; exact (pmcf_F_between (g e) (hg e) (x e) (y e) (hbetw e)).1
      · refine ⟨e0, Finset.mem_univ _, (pmcf_F_between (g e0) (hg e0) (x e0) (y e0)
          (hbetw e0)).2 ?_⟩
        simp only [hy]
        intro h
        have : ε * ct e0 = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · rw [h', zero_mul] at hct0; exact lt_irrefl _ hct0
    exact absurd (hx.2 y hyfeas) (not_le.2 hlt)
  · -- the reachable set is closed under flow arcs: count the net inflow into it
    set S : Finset V := Finset.univ.filter (fun w => Relation.ReflTransGen R q w) with hS
    have hmem : ∀ w, w ∈ S ↔ Relation.ReflTransGen R q w := by simp [hS]
    have hclosed : ∀ u w, u ∈ S → R u w → w ∈ S := fun u w hu hr =>
      (hmem w).2 (((hmem u).1 hu).tail hr)
    have hqS : q ∈ S := (hmem q).2 Relation.ReflTransGen.refl
    have hpS' : p ∉ S := fun h => hpS ((hmem p).1 h)
    have hterm : ∀ e, 0 ≤ (if G.tgt e ∈ S then x e else 0) - (if G.src e ∈ S then x e else 0) := by
      intro e
      by_cases ht : G.tgt e ∈ S <;> by_cases hs : G.src e ∈ S <;> simp only [ht, hs, if_true,
        if_false, sub_self, le_refl, sub_zero, zero_sub]
      · by_contra hneg
        push_neg at hneg
        exact hs (hclosed _ _ ht ⟨e, Or.inr ⟨hneg, rfl, rfl⟩⟩)
      · by_contra hneg
        push_neg at hneg
        exact ht (hclosed _ _ hs ⟨e, Or.inl ⟨neg_neg_iff_pos.1 (by linarith), rfl, rfl⟩⟩)
    have hterm0 : (if G.tgt e0 ∈ S then x e0 else 0) - (if G.src e0 ∈ S then x e0 else 0) =
        |x e0| := by
      by_cases h : 0 < x e0
      · have h1 : G.tgt e0 ∈ S := by simpa [hq, h] using hqS
        have h2 : G.src e0 ∉ S := by simpa [hp, h] using hpS'
        simp [h1, h2, abs_of_pos h]
      · have hn : x e0 < 0 := lt_of_le_of_ne (not_lt.1 h) hx0
        have h1 : G.src e0 ∈ S := by simpa [hq, h] using hqS
        have h2 : G.tgt e0 ∉ S := by simpa [hp, h] using hpS'
        simp [h1, h2, abs_of_neg hn]
    have hsumS : ∑ v ∈ S, d v = ∑ v ∈ S, netInflow G x v :=
      Finset.sum_congr rfl fun v _ => (hx.1.1 v).symm
    rw [pmcf_sum_net] at hsumS
    have hge : |x e0| ≤ ∑ v ∈ S, d v := by
      rw [hsumS, ← hterm0]
      exact Finset.single_le_sum (fun e _ => hterm e) (Finset.mem_univ e0)
    have := pmcf_partial_le d hsum S
    linarith


end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (directed : Bool) (g : E → ℝ → ℝ)
    (hg : ∀ e, IsContinuousMarginalCost (g e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (lamMax lam : ℝ) (hlamMax : 0 < lamMax) (hlam : lam ∈ Set.Icc 0 lamMax)
    (x : E → ℝ)
    (hx : IsMinCostFlow G directed g (demand b0 b lam) x) :
    ∀ e, |x e| ≤ xmax b0 b lamMax :=
  edge_flow_bound_sol G directed g hg b0 b hb0 hb lamMax lam hlamMax hlam x hx
