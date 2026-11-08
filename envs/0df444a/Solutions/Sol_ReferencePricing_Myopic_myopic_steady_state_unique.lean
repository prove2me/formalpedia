-- Prove2me | solution 1 for ReferencePricing.Myopic.myopic_steady_state_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:30:07.248204+00:00
-- url     : https://prove2.me/submissions/e440101f-d06e-4d7a-887c-28f4eeacab83

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_optPrice
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

open Filter Topology

namespace RefMyopicAux
open ReferencePricing.Myopic

/-! ### Generic argmax facts -/

lemma argmax_mem (f : ℝ → ℝ) (pbar : ℝ) (hpbar : 0 ≤ pbar)
    (hf : ContinuousOn f (Set.Icc 0 pbar)) :
    sSup {p | p ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, f p' ≤ f p} ∈
      {p | p ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, f p' ≤ f p} := by
  obtain ⟨p0, hp0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hpbar) hf
  have hS : {p | p ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, f p' ≤ f p} =
      Set.Icc 0 pbar ∩ f ⁻¹' Set.Ici (f p0) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨hp, h⟩; exact ⟨hp, h p0 hp0⟩
    · rintro ⟨hp, h⟩; exact ⟨hp, fun p' hp' => (hmax hp').trans h⟩
  rw [hS]
  apply IsClosed.csSup_mem
  · exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  · exact ⟨p0, hp0, show f p0 ≤ f p0 from le_rfl⟩
  · exact ⟨pbar, fun p hp => hp.1.2⟩

lemma argmax_Icc (f : ℝ → ℝ) (pbar : ℝ) (hpbar : 0 ≤ pbar) :
    sSup {p | p ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, f p' ≤ f p} ∈
      Set.Icc 0 pbar := by
  set S := {p | p ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, f p' ≤ f p} with hSdef
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]; exact ⟨le_refl _, hpbar⟩
  · exact ⟨(h.some_mem.1.1).trans (le_csSup ⟨pbar, fun p hp => hp.1.2⟩ h.some_mem),
      csSup_le h (fun p hp => hp.1.2)⟩

/-! ### Profit -/

lemma profit_contOn (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hA1 : Assumption1 d R pbar) :
    ContinuousOn (Function.uncurry (profit d R)) (Set.Icc (0:ℝ) pbar ×ˢ Set.Icc (0:ℝ) pbar) := by
  have : Function.uncurry (profit d R) =
      fun x : ℝ × ℝ => x.1 * Function.uncurry (demand d R) x := by
    funext x; rfl
  rw [this]
  exact continuous_fst.continuousOn.mul hA1.demand_continuous

lemma profit_contOn_p (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hA1 : Assumption1 d R pbar)
    (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) pbar) :
    ContinuousOn (fun p => profit d R p r) (Set.Icc 0 pbar) :=
  (profit_contOn d R pbar hA1).comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hp => ⟨hp, hr⟩)

lemma profit_contOn_r (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hA1 : Assumption1 d R pbar)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) pbar) :
    ContinuousOn (fun r => profit d R p r) (Set.Icc 0 pbar) :=
  (profit_contOn d R pbar hA1).comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hr => ⟨hp, hr⟩)

lemma myopic_mem (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hpbar : 0 < pbar)
    (hA1 : Assumption1 d R pbar) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) pbar) :
    myopicPrice (profit d R) pbar r ∈ Set.Icc (0:ℝ) pbar ∧
      ∀ p' ∈ Set.Icc (0:ℝ) pbar,
        profit d R p' r ≤ profit d R (myopicPrice (profit d R) pbar r) r :=
  argmax_mem (fun p => profit d R p r) pbar hpbar.le (profit_contOn_p d R pbar hA1 r hr)

lemma myopic_Icc (prof : ℝ → ℝ → ℝ) (pbar : ℝ) (hpbar : 0 < pbar) (r : ℝ) :
    myopicPrice prof pbar r ∈ Set.Icc (0:ℝ) pbar :=
  argmax_Icc (fun p => prof p r) pbar hpbar.le

lemma profit_split (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (p r : ℝ) :
    profit d R p r = baseProfit d p + refProfit R p r := by
  simp only [profit, demand, baseProfit, refProfit]; ring

/-! ### Lemma 1 -/

theorem lemma1 (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hpbar : 0 < pbar)
    (hA1 : Assumption1 d R pbar) (hA3 : Assumption3 d R pbar) :
    MonotoneOn (myopicPrice (profit d R) pbar) (Set.Icc 0 pbar) := by
  intro r1 hr1 r2 hr2 hr
  obtain ⟨h1, m1⟩ := myopic_mem d R pbar hpbar hA1 r1 hr1
  obtain ⟨h2, m2⟩ := myopic_mem d R pbar hpbar hA1 r2 hr2
  by_contra hlt
  replace hlt := not_le.mp hlt
  set p1 := myopicPrice (profit d R) pbar r1
  set p2 := myopicPrice (profit d R) pbar r2
  have hs := hA3.refProfit_supermodular p2 h2 p1 h1 r1 hr1 r2 hr2 hlt.le hr
  have a := m1 p2 h2
  rw [profit_split, profit_split] at a
  have hmax : ∀ p' ∈ Set.Icc (0:ℝ) pbar, profit d R p' r2 ≤ profit d R p1 r2 := by
    intro p' hp'
    refine (m2 p' hp').trans ?_
    rw [profit_split, profit_split]
    linarith
  have : p1 ≤ p2 := le_csSup ⟨pbar, fun p hp => hp.1.2⟩ ⟨h1, hmax⟩
  linarith

/-! ### Paths -/

lemma refPath_Icc (α pbar : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (r : ℝ)
    (hr : r ∈ Set.Icc (0:ℝ) pbar) (p : ℕ → Set.Icc (0 : ℝ) pbar) (t : ℕ) :
    refPath α r (fun s => (p s : ℝ)) t ∈ Set.Icc (0 : ℝ) pbar := by
  induction t with
  | zero => exact hr
  | succ t ih =>
    simp only [refPath]
    have hp := (p t).2
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hp
    constructor
    · nlinarith
    · nlinarith

lemma refPath_diff (α r r' : ℝ) (p : ℕ → ℝ) (t : ℕ) :
    refPath α r p t - refPath α r' p t = α ^ t * (r - r') := by
  induction t with
  | zero => simp [refPath]
  | succ t ih => simp only [refPath, pow_succ]; linear_combination α * ih

/-! ### Continuity of the value function -/

lemma value_le_add (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 d R pbar) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r ∈ Set.Icc (0:ℝ) pbar, ∀ r' ∈ Set.Icc (0:ℝ) pbar, |r - r'| < δ →
      value (profit d R) α β pbar r ≤ value (profit d R) α β pbar r' + ε := by
  obtain ⟨M, hM⟩ := hA1.demand_bounded
  have hprof_nn : ∀ q ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar, 0 ≤ profit d R q r :=
    fun q hq r hr => mul_nonneg hq.1 (hA1.demand_nonneg q hq r hr)
  have hprof_le : ∀ q ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar,
      profit d R q r ≤ pbar * M := by
    intro q hq r hr
    unfold profit
    have h0 := hA1.demand_nonneg q hq r hr
    have h1 := hM q hq r hr
    exact mul_le_mul hq.2 h1 h0 hpbar.le
  have hgeo := summable_geometric_of_lt_one hβ₀.le hβ₁
  have hsum : ∀ r ∈ Set.Icc (0 : ℝ) pbar, ∀ p : ℕ → Set.Icc (0 : ℝ) pbar,
      Summable (fun t => β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t)) := by
    intro r hr p
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ₀.le t)
      (hprof_nn _ (p t).2 _ (refPath_Icc α pbar hα₀ hα₁ r hr p t)))
      (fun t => mul_le_mul_of_nonneg_left
      (hprof_le _ (p t).2 _ (refPath_Icc α pbar hα₀ hα₁ r hr p t)) (pow_nonneg hβ₀.le t))
      (hgeo.mul_right (pbar * M))
  have hbdd : ∀ r ∈ Set.Icc (0 : ℝ) pbar, ∀ p : ℕ → Set.Icc (0 : ℝ) pbar,
      ∑' t, β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t) ≤
        ∑' t : ℕ, β ^ t * (pbar * M) := by
    intro r hr p
    exact (hsum r hr p).tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left
      (hprof_le _ (p t).2 _ (refPath_Icc α pbar hα₀ hα₁ r hr p t)) (pow_nonneg hβ₀.le t))
      (hgeo.mul_right (pbar * M))
  have hU := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (profit_contOn d R pbar hA1)
  rw [Metric.uniformContinuousOn_iff] at hU
  have hε' : 0 < ε * (1 - β) := mul_pos hε (by linarith)
  obtain ⟨δ, hδ, hU⟩ := hU _ hε'
  refine ⟨δ, hδ, fun r hr r' hr' hrr' => ?_⟩
  have : Nonempty (ℕ → Set.Icc (0 : ℝ) pbar) := ⟨fun _ => ⟨0, le_refl _, hpbar.le⟩⟩
  unfold value
  apply ciSup_le
  intro p
  have hterm : ∀ t, β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t) ≤
      β ^ t * profit d R (p t) (refPath α r' (fun s => (p s : ℝ)) t) + β ^ t * (ε * (1 - β)) := by
    intro t
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ₀.le t)
    have hx : ((p t : ℝ), refPath α r (fun s => (p s : ℝ)) t) ∈
        Set.Icc (0:ℝ) pbar ×ˢ Set.Icc (0:ℝ) pbar := ⟨(p t).2, refPath_Icc α pbar hα₀ hα₁ r hr p t⟩
    have hy : ((p t : ℝ), refPath α r' (fun s => (p s : ℝ)) t) ∈
        Set.Icc (0:ℝ) pbar ×ˢ Set.Icc (0:ℝ) pbar := ⟨(p t).2, refPath_Icc α pbar hα₀ hα₁ r' hr' p t⟩
    have hd : dist ((p t : ℝ), refPath α r (fun s => (p s : ℝ)) t)
        ((p t : ℝ), refPath α r' (fun s => (p s : ℝ)) t) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, refPath_diff, abs_mul, abs_pow,
        abs_of_nonneg hα₀]
      have : α ^ t ≤ 1 := pow_le_one₀ hα₀ hα₁.le
      have h0 : 0 ≤ |r - r'| := abs_nonneg _
      rw [max_eq_right (by positivity)]
      calc α ^ t * |r - r'| ≤ 1 * |r - r'| := mul_le_mul_of_nonneg_right this h0
        _ < δ := by linarith
    have := hU _ hx _ hy hd
    rw [Real.dist_eq] at this
    simp only [Function.uncurry_apply_pair] at this
    have := (abs_lt.1 this).2
    linarith
  have hs2 : Summable (fun t => β ^ t * (ε * (1 - β))) := hgeo.mul_right _
  calc ∑' t, β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t)
      ≤ ∑' t, (β ^ t * profit d R (p t) (refPath α r' (fun s => (p s : ℝ)) t)
          + β ^ t * (ε * (1 - β))) :=
        (hsum r hr p).tsum_le_tsum hterm ((hsum r' hr' p).add hs2)
    _ = ∑' t, β ^ t * profit d R (p t) (refPath α r' (fun s => (p s : ℝ)) t) + ε := by
        rw [(hsum r' hr' p).tsum_add hs2, tsum_mul_right, tsum_geometric_of_lt_one hβ₀.le hβ₁]
        congr 1
        have h1b : (1 - β) ≠ 0 := ne_of_gt (by linarith)
        field_simp
    _ ≤ (⨆ p : ℕ → Set.Icc (0 : ℝ) pbar,
          ∑' t, β ^ t * profit d R (p t) (refPath α r' (fun s => (p s : ℝ)) t)) + ε := by
        gcongr
        exact le_ciSup (f := fun p : ℕ → Set.Icc (0 : ℝ) pbar =>
          ∑' t, β ^ t * profit d R (p t) (refPath α r' (fun s => (p s : ℝ)) t))
          ⟨_, by rintro _ ⟨q, rfl⟩; exact hbdd r' hr' q⟩ p

lemma value_contOn (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 d R pbar) :
    ContinuousOn (value (profit d R) α β pbar) (Set.Icc 0 pbar) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨δ, hδ, h⟩ := value_le_add d R α β pbar hpbar hα₀ hα₁ hβ₀ hβ₁ hA1 (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have h1 := h a ha b hb hab
  have h2 := h b hb a ha (by rwa [abs_sub_comm])
  rw [abs_lt]; constructor <;> linarith

lemma opt_mem (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 d R pbar) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) pbar) :
    optPrice (profit d R) α β pbar r ∈ Set.Icc (0:ℝ) pbar ∧
      ∀ p' ∈ Set.Icc (0:ℝ) pbar,
        bellmanObjective (profit d R) α β pbar p' r ≤
          bellmanObjective (profit d R) α β pbar (optPrice (profit d R) α β pbar r) r := by
  apply argmax_mem (fun p => bellmanObjective (profit d R) α β pbar p r) pbar hpbar.le
  unfold bellmanObjective
  apply (profit_contOn_p d R pbar hA1 r hr).add
  apply ContinuousOn.mul continuousOn_const
  apply (value_contOn d R α β pbar hpbar hα₀ hα₁ hβ₀ hβ₁ hA1).comp
    ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn)
  intro p hp
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨h3, h4⟩ := hp
  have ha : 0 ≤ 1 - α := by linarith
  show 0 ≤ α * r + (1 - α) * p ∧ α * r + (1 - α) * p ≤ pbar
  constructor
  · nlinarith [mul_nonneg hα₀ h1, mul_nonneg ha h3]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hα₀, mul_le_mul_of_nonneg_left h4 ha]

lemma opt_Icc (prof : ℝ → ℝ → ℝ) (α β pbar : ℝ) (hpbar : 0 < pbar) (r : ℝ) :
    optPrice prof α β pbar r ∈ Set.Icc (0:ℝ) pbar :=
  argmax_Icc (fun p => bellmanObjective prof α β pbar p r) pbar hpbar.le


/-! ### §A.1 second paragraph -/

lemma myopicState_Icc (prof : ℝ → ℝ → ℝ) (α pbar : ℝ) (hpbar : 0 < pbar)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Icc (0:ℝ) pbar) (t : ℕ) :
    myopicState prof α pbar r₀ t ∈ Set.Icc (0:ℝ) pbar := by
  induction t with
  | zero => exact hr₀
  | succ t ih =>
    simp only [myopicState]
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := myopic_Icc prof pbar hpbar (myopicState prof α pbar r₀ t)
    have ha : 0 ≤ 1 - α := by linarith
    constructor
    · nlinarith [mul_nonneg hα₀ h1, mul_nonneg ha h3]
    · nlinarith [mul_le_mul_of_nonneg_left h2 hα₀, mul_le_mul_of_nonneg_left h4 ha]

lemma statePath_Icc (prof : ℝ → ℝ → ℝ) (α β pbar : ℝ) (hpbar : 0 < pbar)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Icc (0:ℝ) pbar) (t : ℕ) :
    statePath prof α β pbar r₀ t ∈ Set.Icc (0:ℝ) pbar := by
  induction t with
  | zero => exact hr₀
  | succ t ih =>
    simp only [statePath, optRef]
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := opt_Icc prof α β pbar hpbar (statePath prof α β pbar r₀ t)
    have ha : 0 ≤ 1 - α := by linarith
    constructor
    · nlinarith [mul_nonneg hα₀ h1, mul_nonneg ha h3]
    · nlinarith [mul_le_mul_of_nonneg_left h2 hα₀, mul_le_mul_of_nonneg_left h4 ha]

theorem along_paths (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hmono : MonotoneOn (myopicPrice (profit d R) pbar) (Set.Icc 0 pbar))
    (hle : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
      myopicPrice (profit d R) pbar r ≤ optPrice (profit d R) α β pbar r) :
    ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, ∀ t : ℕ,
      myopicState (profit d R) α pbar r₀ t ≤ statePath (profit d R) α β pbar r₀ t ∧
        myopicPricePath (profit d R) α pbar r₀ t ≤ pricePath (profit d R) α β pbar r₀ t := by
  intro r₀ hr₀ t
  have hp : ∀ t, myopicState (profit d R) α pbar r₀ t ≤ statePath (profit d R) α β pbar r₀ t →
      myopicPricePath (profit d R) α pbar r₀ t ≤ pricePath (profit d R) α β pbar r₀ t := by
    intro t ht
    unfold myopicPricePath pricePath
    exact (hmono (myopicState_Icc _ α pbar hpbar hα₀ hα₁ r₀ hr₀ t)
      (statePath_Icc _ α β pbar hpbar hα₀ hα₁ r₀ hr₀ t) ht).trans
      (hle _ (statePath_Icc _ α β pbar hpbar hα₀ hα₁ r₀ hr₀ t))
  have hs : ∀ t, myopicState (profit d R) α pbar r₀ t ≤ statePath (profit d R) α β pbar r₀ t := by
    intro t
    induction t with
    | zero => exact le_refl _
    | succ t ih =>
      have h := hp t ih
      unfold myopicPricePath pricePath at h
      simp only [myopicState, statePath, optRef]
      have ha : 0 ≤ 1 - α := by linarith
      nlinarith [mul_le_mul_of_nonneg_left ih hα₀, mul_le_mul_of_nonneg_left h ha]
  exact ⟨hs t, hp t (hs t)⟩

/-! ### §A.1 third paragraph: monotone paths -/

lemma state_monotone (prof : ℝ → ℝ → ℝ) (α pbar : ℝ) (hpbar : 0 < pbar)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hmono : MonotoneOn (myopicPrice prof pbar) (Set.Icc 0 pbar))
    (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Icc (0:ℝ) pbar) :
    (r₀ ≤ myopicPrice prof pbar r₀ → Monotone (myopicState prof α pbar r₀)) ∧
      (myopicPrice prof pbar r₀ ≤ r₀ → Antitone (myopicState prof α pbar r₀)) := by
  have ha : 0 ≤ 1 - α := by linarith
  have hI := myopicState_Icc prof α pbar hpbar hα₀ hα₁ r₀ hr₀
  constructor
  · intro h0
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero =>
      show r₀ ≤ α * r₀ + (1 - α) * myopicPrice prof pbar r₀
      nlinarith [mul_le_mul_of_nonneg_left h0 ha]
    | succ n ih =>
      have h := hmono (hI n) (hI (n+1)) ih
      show α * myopicState prof α pbar r₀ n + (1 - α) * myopicPrice prof pbar (myopicState prof α pbar r₀ n) ≤
        α * myopicState prof α pbar r₀ (n+1) + (1 - α) * myopicPrice prof pbar (myopicState prof α pbar r₀ (n+1))
      nlinarith [mul_le_mul_of_nonneg_left ih hα₀, mul_le_mul_of_nonneg_left h ha]
  · intro h0
    apply antitone_nat_of_succ_le
    intro n
    induction n with
    | zero =>
      show α * r₀ + (1 - α) * myopicPrice prof pbar r₀ ≤ r₀
      nlinarith [mul_le_mul_of_nonneg_left h0 ha]
    | succ n ih =>
      have h := hmono (hI (n+1)) (hI n) ih
      show α * myopicState prof α pbar r₀ (n+1) + (1 - α) * myopicPrice prof pbar (myopicState prof α pbar r₀ (n+1)) ≤
        α * myopicState prof α pbar r₀ n + (1 - α) * myopicPrice prof pbar (myopicState prof α pbar r₀ n)
      nlinarith [mul_le_mul_of_nonneg_left ih hα₀, mul_le_mul_of_nonneg_left h ha]

theorem path_monotone (prof : ℝ → ℝ → ℝ) (α pbar : ℝ) (hpbar : 0 < pbar)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hmono : MonotoneOn (myopicPrice prof pbar) (Set.Icc 0 pbar)) :
    ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
      (r₀ ≤ myopicPrice prof pbar r₀ → Monotone (myopicPricePath prof α pbar r₀)) ∧
        (myopicPrice prof pbar r₀ ≤ r₀ → Antitone (myopicPricePath prof α pbar r₀)) := by
  intro r₀ hr₀
  have hI := myopicState_Icc prof α pbar hpbar hα₀ hα₁ r₀ hr₀
  obtain ⟨h1, h2⟩ := state_monotone prof α pbar hpbar hα₀ hα₁ hmono r₀ hr₀
  exact ⟨fun h a b hab => hmono (hI a) (hI b) (h1 h hab),
    fun h a b hab => hmono (hI b) (hI a) (h2 h hab)⟩

/-! ### Steady state: first-order conditions -/

lemma hasDeriv_profit (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (hR0 : ∀ r, R 0 r = 0)
    (hd : Differentiable ℝ d) (hA2 : Assumption2 R) (L : ℝ) :
    HasDerivAt (fun p => profit d R p L) (deriv (baseProfit d) L - L * refSlope R L) L := by
  have hφ : DifferentiableAt ℝ (fun x => R x L) 0 := by
    have h1 := hA2.1 ((0 : ℝ), L)
    have h2 : DifferentiableAt ℝ (fun x : ℝ => ((x, L) : ℝ × ℝ)) 0 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    exact h1.comp (0 : ℝ) h2
  have hφ' : HasDerivAt (fun x => R x L) (refSlope R L) (L - L) := by
    rw [sub_self]; exact hφ.hasDerivAt
  have hlin : HasDerivAt (fun p : ℝ => L - p) (-1) L := by
    simpa using (hasDerivAt_id' L).const_sub L
  have hcomp : HasDerivAt (fun p => R (L - p) L) (refSlope R L * -1) L := hφ'.comp L hlin
  have hb : HasDerivAt (baseProfit d) (deriv (baseProfit d) L) L := by
    have : DifferentiableAt ℝ (baseProfit d) L := by
      unfold baseProfit; exact differentiableAt_id.mul (hd L)
    exact this.hasDerivAt
  have hprod : HasDerivAt (fun p => p * R (L - p) L)
      (1 * R (L - L) L + L * (refSlope R L * -1)) L := (hasDerivAt_id' L).mul hcomp
  have hsum := hb.add hprod
  have e : (fun p => profit d R p L) = fun p => baseProfit d p + p * R (L - p) L := by
    funext p; simp only [profit, demand, baseProfit]; ring
  have hc : deriv (baseProfit d) L - L * refSlope R L =
      deriv (baseProfit d) L + (1 * R (L - L) L + L * (refSlope R L * -1)) := by
    rw [sub_self, hR0]; ring
  rw [e, hc]
  exact hsum

lemma kkt (f : ℝ → ℝ) (c L pbar : ℝ) (hf : HasDerivAt f c L) (hL : L ∈ Set.Icc (0:ℝ) pbar)
    (hmax : ∀ p ∈ Set.Icc (0:ℝ) pbar, f p ≤ f L) :
    (L < pbar → c ≤ 0) ∧ (0 < L → 0 ≤ c) := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  constructor
  · intro hlt
    have h1 : Tendsto (slope f L) (𝓝[>] L) (𝓝 c) :=
      hs.mono_left (nhdsWithin_mono _ (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)))
    apply le_of_tendsto h1
    filter_upwards [Ioo_mem_nhdsGT hlt] with p hp
    rw [slope_def_field]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [hmax p ⟨by linarith [hL.1, hp.1], hp.2.le⟩]
    · linarith [hp.1]
  · intro hpos
    have h1 : Tendsto (slope f L) (𝓝[<] L) (𝓝 c) :=
      hs.mono_left (nhdsWithin_mono _ (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_lt hx)))
    apply ge_of_tendsto h1
    filter_upwards [Ioo_mem_nhdsLT hpos] with p hp
    rw [slope_def_field]
    apply div_nonneg_of_nonpos
    · linarith [hmax p ⟨hp.1.le, by linarith [hL.2, hp.2]⟩]
    · linarith [hp.2]

/-- Uniqueness of a price that maximizes `Π(·, L)` at its own reference price `L`. -/
theorem selfmax_unique (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) (L1 L2 : ℝ)
    (h1 : L1 ∈ Set.Icc (0:ℝ) pbar) (h2 : L2 ∈ Set.Icc (0:ℝ) pbar)
    (m1 : ∀ p ∈ Set.Icc (0:ℝ) pbar, profit d R p L1 ≤ profit d R L1 L1)
    (m2 : ∀ p ∈ Set.Icc (0:ℝ) pbar, profit d R p L2 ≤ profit d R L2 L2) : L1 = L2 := by
  have k1 := kkt _ _ _ _ (hasDeriv_profit d R hR0 hd hA2 L1) h1 m1
  have k2 := kkt _ _ _ _ (hasDeriv_profit d R hR0 hd hA2 L2) h2 m2
  rcases lt_trichotomy L1 L2 with h | h | h
  · exfalso
    have a := k1.1 (by linarith [h2.2])
    have b := k2.2 (by linarith [h1.1])
    have c := hA3.marginal_strictAnti h1 h2 h
    simp only at c
    linarith
  · exact h
  · exfalso
    have a := k2.1 (by linarith [h1.2])
    have b := k1.2 (by linarith [h2.1])
    have c := hA3.marginal_strictAnti h2 h1 h
    simp only at c
    linarith

theorem steady_unique (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ)
    (hpbar : 0 < pbar) (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ q ∈ Set.Icc (0 : ℝ) pbar,
      myopicPrice (profit d R) pbar p = p → myopicPrice (profit d R) pbar q = q → p = q := by
  intro p hp q hq ep eq
  have mp := (myopic_mem d R pbar hpbar hA1 p hp).2
  have mq := (myopic_mem d R pbar hpbar hA1 q hq).2
  rw [ep] at mp
  rw [eq] at mq
  exact selfmax_unique d R pbar hR0 hd hA2 hA3 p q hp hq mp mq

/-! ### Limits -/

lemma limit_selfmax (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) (hA1 : Assumption1 d R pbar)
    (r p : ℕ → ℝ) (L : ℝ) (hr : ∀ t, r t ∈ Set.Icc (0:ℝ) pbar)
    (hp : ∀ t, p t ∈ Set.Icc (0:ℝ) pbar)
    (hrL : Tendsto r atTop (𝓝 L)) (hpL : Tendsto p atTop (𝓝 L))
    (hmax : ∀ t, ∀ p' ∈ Set.Icc (0:ℝ) pbar, profit d R p' (r t) ≤ profit d R (p t) (r t)) :
    L ∈ Set.Icc (0:ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0:ℝ) pbar, profit d R p' L ≤ profit d R L L := by
  have hL : L ∈ Set.Icc (0:ℝ) pbar := isClosed_Icc.mem_of_tendsto hrL (Eventually.of_forall hr)
  refine ⟨hL, fun p' hp' => ?_⟩
  have t1 : Tendsto (fun t => profit d R p' (r t)) atTop (𝓝 (profit d R p' L)) := by
    have hc := (profit_contOn_r d R pbar hA1 p' hp') L hL
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hrL, Eventually.of_forall hr⟩)
  have t2 : Tendsto (fun t => profit d R (p t) (r t)) atTop (𝓝 (profit d R L L)) := by
    have hc := (profit_contOn d R pbar hA1) (L, L) ⟨hL, hL⟩
    have := hc.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hpL.prodMk_nhds hrL, Eventually.of_forall (fun t => ⟨hp t, hr t⟩)⟩)
    exact this
  exact le_of_tendsto_of_tendsto' t1 t2 (fun t => hmax t p' hp')

lemma path_converges (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hA1 : Assumption1 d R pbar)
    (hmono : MonotoneOn (myopicPrice (profit d R) pbar) (Set.Icc 0 pbar))
    (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Icc (0:ℝ) pbar) :
    (Monotone (myopicPricePath (profit d R) α pbar r₀) ∨
        Antitone (myopicPricePath (profit d R) α pbar r₀)) ∧
      ∃ L, (L ∈ Set.Icc (0:ℝ) pbar ∧
          ∀ p' ∈ Set.Icc (0:ℝ) pbar, profit d R p' L ≤ profit d R L L) ∧
        Tendsto (myopicPricePath (profit d R) α pbar r₀) atTop (𝓝 L) := by
  set r := myopicState (profit d R) α pbar r₀
  set p := myopicPricePath (profit d R) α pbar r₀
  have hrI : ∀ t, r t ∈ Set.Icc (0:ℝ) pbar := myopicState_Icc _ α pbar hpbar hα₀ hα₁ r₀ hr₀
  have hpI : ∀ t, p t ∈ Set.Icc (0:ℝ) pbar := fun t => myopic_Icc _ pbar hpbar _
  have hbddA : ∀ f : ℕ → ℝ, (∀ t, f t ∈ Set.Icc (0:ℝ) pbar) → BddAbove (Set.range f) :=
    fun f hf => ⟨pbar, by rintro _ ⟨t, rfl⟩; exact (hf t).2⟩
  have hbddB : ∀ f : ℕ → ℝ, (∀ t, f t ∈ Set.Icc (0:ℝ) pbar) → BddBelow (Set.range f) :=
    fun f hf => ⟨0, by rintro _ ⟨t, rfl⟩; exact (hf t).1⟩
  obtain ⟨sm, sa⟩ := state_monotone (profit d R) α pbar hpbar hα₀ hα₁ hmono r₀ hr₀
  obtain ⟨pm, pa⟩ := path_monotone (profit d R) α pbar hpbar hα₀ hα₁ hmono r₀ hr₀
  have key : ∀ Lr Lp, Tendsto r atTop (𝓝 Lr) → Tendsto p atTop (𝓝 Lp) →
      ∃ L, (L ∈ Set.Icc (0:ℝ) pbar ∧
          ∀ p' ∈ Set.Icc (0:ℝ) pbar, profit d R p' L ≤ profit d R L L) ∧
        Tendsto p atTop (𝓝 L) := by
    intro Lr Lp hr hp
    have hr1 : Tendsto (fun t => r (t + 1)) atTop (𝓝 Lr) := (tendsto_add_atTop_iff_nat 1).2 hr
    have hr2 : Tendsto (fun t => r (t + 1)) atTop (𝓝 (α * Lr + (1 - α) * Lp)) := by
      have : (fun t => r (t + 1)) = fun t => α * r t + (1 - α) * p t := by
        funext t; rfl
      rw [this]
      exact (hr.const_mul α).add (hp.const_mul (1 - α))
    have he := tendsto_nhds_unique hr1 hr2
    have hLL : Lr = Lp := by
      have : (1 - α) * (Lr - Lp) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · linarith
    subst hLL
    refine ⟨Lr, limit_selfmax d R pbar hA1 r p Lr hrI hpI hr hp
      (fun t => (myopic_mem d R pbar hpbar hA1 (r t) (hrI t)).2), hp⟩
  rcases le_total r₀ (myopicPrice (profit d R) pbar r₀) with h | h
  · refine ⟨Or.inl (pm h), ?_⟩
    exact key _ _ (tendsto_atTop_ciSup (sm h) (hbddA r hrI))
      (tendsto_atTop_ciSup (pm h) (hbddA p hpI))
  · refine ⟨Or.inr (pa h), ?_⟩
    exact key _ _ (tendsto_atTop_ciInf (sa h) (hbddB r hrI))
      (tendsto_atTop_ciInf (pa h) (hbddB p hpI))

theorem part3 (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar)
    (hmono : MonotoneOn (myopicPrice (profit d R) pbar) (Set.Icc 0 pbar)) :
    ∃ pM ∈ Set.Icc (0 : ℝ) pbar, ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        (Monotone (myopicPricePath (profit d R) α pbar r₀) ∨
            Antitone (myopicPricePath (profit d R) α pbar r₀)) ∧
          Tendsto (myopicPricePath (profit d R) α pbar r₀) atTop (𝓝 pM) := by
  obtain ⟨-, L0, ⟨hL0, m0⟩, -⟩ :=
    path_converges d R α pbar hpbar hα₀ hα₁ hA1 hmono 0 ⟨le_refl _, hpbar.le⟩
  refine ⟨L0, hL0, fun r₀ hr₀ => ?_⟩
  obtain ⟨hmon, L, ⟨hL, m⟩, ht⟩ := path_converges d R α pbar hpbar hα₀ hα₁ hA1 hmono r₀ hr₀
  have := selfmax_unique d R pbar hR0 hd hA2 hA3 L L0 hL hL0 m m0
  subst this
  exact ⟨hmon, ht⟩

end RefMyopicAux

open ReferencePricing.Myopic in
theorem solution (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ)
    (hpbar : 0 < pbar) (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ q ∈ Set.Icc (0 : ℝ) pbar,
      myopicPrice (profit d R) pbar p = p → myopicPrice (profit d R) pbar q = q → p = q :=
  RefMyopicAux.steady_unique d R pbar hpbar hR0 hd hA1 hA2 hA3
