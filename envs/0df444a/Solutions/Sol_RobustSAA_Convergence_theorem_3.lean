-- Prove2me | solution 1 for RobustSAA.Convergence.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:18:47.662501+00:00
-- url     : https://prove2.me/submissions/4672d387-2fc0-41aa-9fec-d042c479e9e8

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Convergence_Consistency
import Theorems.Thm_RobustSAA_Convergence_proposition_9

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open RobustSAA.Convergence

namespace RSAAThm3Aux

variable {d dx : ℕ} {Ξ : Set (Pt d)}

lemma unif_close {X : Set (Pt dx)} {c : Pt dx → ↥Ξ → ℝ}
    (hA1 : Assumption1 X c) (x : Pt dx) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ ξ, |c y ξ - c x ξ| < ε := by
  have h := (equicontinuousOn_univ _).1 hA1 x
  rw [Metric.equicontinuousAt_iff_right] at h
  filter_upwards [h ε hε] with y hy ξ
  have := hy ξ
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

lemma trueObj_close {F : ProbabilityMeasure ↥Ξ} {X : Set (Pt dx)} {c : Pt dx → ↥Ξ → ℝ}
    (hS : Standing F X c) {x y : Pt dx} (hx : x ∈ X) (hy : y ∈ X) {δ : ℝ}
    (h : ∀ ξ, |c y ξ - c x ξ| ≤ δ) : |trueObj F c y - trueObj F c x| ≤ δ := by
  unfold trueObj
  rw [← integral_sub (hS.2 _ hy).1 (hS.2 _ hx).1]
  have hb : ‖∫ ξ, (c y ξ - c x ξ) ∂(F : Measure ↥Ξ)‖ ≤ δ * (F : Measure ↥Ξ).real Set.univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact h ξ)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at hb

/-- `E_G f ≤ E_G g + δ` when `f, g` are continuous and `|f - g| ≤ δ`. -/
lemma expect_le_add (G : ProbabilityMeasure ↥Ξ) {f g : ↥Ξ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {δ : ℝ} (h : ∀ ξ, |f ξ - g ξ| ≤ δ) :
    expect G f ≤ expect G g + (δ : EReal) := by
  classical
  unfold expect
  by_cases hgi : Integrable g (G : Measure ↥Ξ)
  · have hd : Integrable (fun ξ => f ξ - g ξ) (G : Measure ↥Ξ) :=
      Integrable.of_bound ((hf.sub hg).aestronglyMeasurable) δ
        (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact h ξ)
    have hfi : Integrable f (G : Measure ↥Ξ) := by
      have := hgi.add hd
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp
    rw [if_pos hfi, if_pos hgi, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hm : ∫ ξ, f ξ ∂(G : Measure ↥Ξ) ≤ ∫ ξ, (g ξ + δ) ∂(G : Measure ↥Ξ) :=
      integral_mono hfi (hgi.add (integrable_const δ)) (fun ξ => by
        have := h ξ; rw [abs_le] at this; linarith)
    rw [integral_add hgi (integrable_const δ), integral_const, probReal_univ, one_smul] at hm
    exact hm
  · rw [if_neg hgi, EReal.top_add_coe]
    exact le_top

lemma worstCase_le_add (𝒢 : Set (ProbabilityMeasure ↥Ξ)) {f g : ↥Ξ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {δ : ℝ} (h : ∀ ξ, |f ξ - g ξ| ≤ δ) :
    worstCase 𝒢 f ≤ worstCase 𝒢 g + (δ : EReal) := by
  unfold worstCase
  refine iSup₂_le fun G hG => (expect_le_add G hf hg h).trans ?_
  gcongr
  exact le_iSup₂ (f := fun G (_ : G ∈ 𝒢) => expect G g) G hG

lemma expect_le_worstCase {𝒢 : Set (ProbabilityMeasure ↥Ξ)} {G : ProbabilityMeasure ↥Ξ}
    (hG : G ∈ 𝒢) (f : ↥Ξ → ℝ) : expect G f ≤ worstCase 𝒢 f :=
  le_iSup₂ (f := fun G (_ : G ∈ 𝒢) => expect G f) G hG

/-- EReal arithmetic helper. -/
lemma lt_of_lt_add_real {u v : EReal} {r δ : ℝ} (h : (((r + δ : ℝ)) : EReal) < v)
    (h' : v ≤ u + (δ : EReal)) : (r : EReal) < u := by
  induction u using EReal.rec with
  | bot => rw [EReal.bot_add] at h'; exact absurd (h.trans_le h') (not_lt_bot)
  | coe w =>
    have := h.trans_le h'
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at this
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  | top => exact EReal.coe_lt_top r

lemma lt_of_le_add_real {u v : EReal} {r δ : ℝ} (h : v < (((r - δ : ℝ)) : EReal))
    (h' : u ≤ v + (δ : EReal)) : u < (r : EReal) := by
  induction v using EReal.rec with
  | bot => rw [EReal.bot_add] at h'; exact (le_bot_iff.1 h') ▸ EReal.bot_lt_coe r
  | coe w =>
    rw [EReal.coe_lt_coe_iff] at h
    rw [← EReal.coe_add] at h'
    exact h'.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
  | top => exact absurd h (not_lt.2 le_top)

/-- Pointwise convergence of the worst case from convergence along every selection. -/
lemma worstCase_tendsto {𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)} (F₀ : ProbabilityMeasure ↥Ξ)
    (hne : ∀ᶠ N in atTop, (𝒢 N).Nonempty) {f : ↥Ξ → ℝ} {a : ℝ}
    (H : ∀ G : ℕ → ProbabilityMeasure ↥Ξ, (∀ᶠ N in atTop, G N ∈ 𝒢 N) →
      Tendsto (fun N => expect (G N) f) atTop (𝓝 (a : EReal))) :
    Tendsto (fun N => worstCase (𝒢 N) f) atTop (𝓝 (a : EReal)) := by
  classical
  let G₀ : ℕ → ProbabilityMeasure ↥Ξ := fun N => if h : (𝒢 N).Nonempty then h.some else F₀
  have hG₀ : ∀ᶠ N in atTop, G₀ N ∈ 𝒢 N := by
    filter_upwards [hne] with N hN
    simp only [G₀, dif_pos hN]; exact hN.some_mem
  rw [tendsto_order]
  constructor
  · intro b hb
    have h := H G₀ hG₀
    filter_upwards [(tendsto_order.1 h).1 b hb, hG₀] with N hN hN'
    exact hN.trans_le (expect_le_worstCase hN' f)
  · intro b hb
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    by_contra hcon
    rw [not_eventually] at hcon
    let G : ℕ → ProbabilityMeasure ↥Ξ := fun N =>
      if h : ∃ G ∈ 𝒢 N, (r : EReal) < expect G f then h.choose else G₀ N
    have hGmem : ∀ᶠ N in atTop, G N ∈ 𝒢 N := by
      filter_upwards [hG₀] with N hN
      by_cases h : ∃ G ∈ 𝒢 N, (r : EReal) < expect G f
      · simp only [G, dif_pos h]; exact h.choose_spec.1
      · simp only [G, dif_neg h]; exact hN
    have h1 := (tendsto_order.1 (H G hGmem)).2 r hr1
    obtain ⟨N, hN1, hN2⟩ := (hcon.and_eventually h1).exists
    have hex : ∃ G ∈ 𝒢 N, (r : EReal) < expect G f := by
      have : (r : EReal) < worstCase (𝒢 N) f := hr2.trans_le (not_lt.1 hN1)
      exact lt_biSup_iff.1 this
    simp only [G, dif_pos hex] at hN2
    exact absurd hex.choose_spec.2 (not_lt.2 hN2.le)

/-- Convergence of the worst case along a convergent sequence of decisions. -/
lemma worstCase_seq_tendsto {F : ProbabilityMeasure ↥Ξ} {X : Set (Pt dx)}
    {c : Pt dx → ↥Ξ → ℝ} (hS : Standing F X c) (hA1 : Assumption1 X c)
    {𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)} {xs : ℕ → Pt dx} {x : Pt dx} (hx : x ∈ X)
    (hxs : ∀ N, xs N ∈ X) (hlim : Tendsto xs atTop (𝓝 x))
    (hW : Tendsto (fun N => worstCase (𝒢 N) (c x)) atTop (𝓝 ((trueObj F c x : ℝ) : EReal))) :
    Tendsto (fun N => worstCase (𝒢 N) (c (xs N))) atTop
      (𝓝 ((trueObj F c x : ℝ) : EReal)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    rw [EReal.coe_lt_coe_iff] at hr2
    set δ := (trueObj F c x - r) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have e1 := (tendsto_order.1 hW).1 (((r + δ : ℝ)) : EReal)
      (EReal.coe_lt_coe_iff.2 (by rw [hδ]; linarith))
    have e2 := hlim.eventually (unif_close hA1 x hδpos)
    filter_upwards [e1, e2] with N h1 h2
    refine lt_trans hr1 (lt_of_lt_add_real h1 ?_)
    exact worstCase_le_add (𝒢 N) (hS.2 x hx).2 (hS.2 _ (hxs N)).2
      (fun ξ => by rw [abs_sub_comm]; exact (h2 ξ).le)
  · intro b hb
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    rw [EReal.coe_lt_coe_iff] at hr1
    set δ := (r - trueObj F c x) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have e1 := (tendsto_order.1 hW).2 (((r - δ : ℝ)) : EReal)
      (EReal.coe_lt_coe_iff.2 (by rw [hδ]; linarith))
    have e2 := hlim.eventually (unif_close hA1 x hδpos)
    filter_upwards [e1, e2] with N h1 h2
    refine lt_trans (lt_of_le_add_real h1 ?_) hr2
    exact worstCase_le_add (𝒢 N) (hS.2 _ (hxs N)).2 (hS.2 x hx).2 (fun ξ => (h2 ξ).le)

/-- Lower bound used for `D`-uniform coerciveness (Assumption 2b). -/
lemma expect_ge_of_split (G : ProbabilityMeasure ↥Ξ) {f : ↥Ξ → ℝ} (hf : Continuous f)
    {D : Set ↥Ξ} (hD : MeasurableSet D) {M B : ℝ} (hM0 : 0 ≤ M) (hB0 : B ≤ 0)
    (hMD : ∀ ξ ∈ D, M ≤ f ξ) (hBD : ∀ ξ ∉ D, B ≤ f ξ) :
    (((M * (G : Measure ↥Ξ).real D + B : ℝ)) : EReal) ≤ expect G f := by
  classical
  unfold expect
  by_cases hfi : Integrable f (G : Measure ↥Ξ)
  · rw [if_pos hfi, EReal.coe_le_coe_iff]
    have hint : Integrable (fun ξ => D.indicator (fun _ => M) ξ + B) (G : Measure ↥Ξ) :=
      ((integrable_const M).indicator hD).add (integrable_const B)
    have hm := integral_mono hint hfi (fun ξ => by
      by_cases hξ : ξ ∈ D
      · simp only [Set.indicator_of_mem hξ]; linarith [hMD ξ hξ]
      · simp only [Set.indicator_of_notMem hξ]; linarith [hBD ξ hξ])
    rw [integral_add ((integrable_const M).indicator hD) (integrable_const B),
      integral_indicator_const _ hD, integral_const, probReal_univ, one_smul, smul_eq_mul] at hm
    linarith
  · rw [if_neg hfi]; exact le_top

/-- Assumption 2 together with, in case (b), a selection from `𝒢 N` charging `D` with at least
half of `F(D)` for all large `N`. -/
def A2sel {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)) : Prop :=
  IsClosed X ∧
    (Bornology.IsBounded X ∨
      ∃ D : Set ↥Ξ, IsOpen D ∧ 0 < (F : Measure ↥Ξ) D ∧
        (∀ M : ℝ, ∀ᶠ x in Bornology.cobounded (Pt dx), ∀ ξ ∈ D, M ≤ c x ξ) ∧
        (∃ B : ℝ, ∀ᶠ x in Bornology.cobounded (Pt dx), ∀ ξ ∉ D, B ≤ c x ξ) ∧
        ∀ᶠ N in atTop, ∃ G ∈ 𝒢 N, (F : Measure ↥Ξ) D / 2 < (G : Measure ↥Ξ) D)

/-- Minimizers stay bounded (the boundedness step of the source's proof, under Assumption 2). -/
lemma bounded_minimizers {F : ProbabilityMeasure ↥Ξ} {X : Set (Pt dx)} {c : Pt dx → ↥Ξ → ℝ}
    {𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)} (hS : Standing F X c) (hA2 : A2sel F X c 𝒢)
    (HW : ∀ x ∈ X, Tendsto (fun N => worstCase (𝒢 N) (c x)) atTop
      (𝓝 ((trueObj F c x : ℝ) : EReal)))
    {x₀ : Pt dx} (hx₀ : x₀ ∈ X) :
    ∃ R : ℝ, ‖x₀‖ ≤ R ∧ (∀ y ∈ X, R < ‖y‖ → trueObj F c x₀ < trueObj F c y) ∧
      ∀ᶠ N in atTop, ∀ y ∈ X, R < ‖y‖ → worstCase (𝒢 N) (c x₀) < worstCase (𝒢 N) (c y) := by
  rcases hA2.2 with hb | ⟨D, hDo, hDpos, hM, ⟨B, hB⟩, hsel⟩
  · obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    refine ⟨max R ‖x₀‖, le_max_right _ _, fun y hy hlt => ?_,
      Eventually.of_forall fun N y hy hlt => ?_⟩
    · have := mem_closedBall_zero_iff.1 (hR hy); linarith [le_max_left R ‖x₀‖]
    · have := mem_closedBall_zero_iff.1 (hR hy); linarith [le_max_left R ‖x₀‖]
  · set pD := (F : Measure ↥Ξ).real D with hpDdef
    have hpD : 0 < pD := ENNReal.toReal_pos hDpos.ne' (measure_ne_top _ _)
    set q := pD / 2 with hq
    have hqpos : 0 < q := by rw [hq]; linarith
    set B' := min B 0 with hB'
    set m := trueObj F c x₀ with hm
    set val := (m + 2 - B') / q with hval
    set M := max 0 val with hMdef
    have hev := (hM M).and hB
    obtain ⟨R0, -, hR0⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
    set R := max R0 ‖x₀‖ with hR
    have hbound : ∀ G : ProbabilityMeasure ↥Ξ, q ≤ (G : Measure ↥Ξ).real D →
        ∀ y ∈ X, R < ‖y‖ → (((m + 2 : ℝ)) : EReal) ≤ expect G (c y) := by
      intro G hG y hy hlt
      have hy' := hR0 (show R0 ≤ ‖y‖ by linarith [le_max_left R0 ‖x₀‖])
      refine le_trans ?_ (expect_ge_of_split G (hS.2 y hy).2 hDo.measurableSet
        (le_max_left 0 val) (min_le_right B 0) hy'.1
        (fun ξ hξ => (min_le_left B 0).trans (hy'.2 ξ hξ)))
      rw [EReal.coe_le_coe_iff]
      have h1 : val * q = m + 2 - B' := by rw [hval]; field_simp
      have h2 : val * q ≤ M * q := mul_le_mul_of_nonneg_right (le_max_right 0 val) hqpos.le
      have h3 : M * q ≤ M * (G : Measure ↥Ξ).real D :=
        mul_le_mul_of_nonneg_left hG (le_max_left 0 val)
      linarith
    refine ⟨R, le_max_right _ _, fun y hy hlt => ?_, ?_⟩
    · have h := hbound F (by rw [hq, ← hpDdef]; linarith) y hy hlt
      unfold expect at h
      rw [if_pos (hS.2 y hy).1, EReal.coe_le_coe_iff] at h
      have : trueObj F c y = ∫ ξ, c y ξ ∂(F : Measure ↥Ξ) := rfl
      linarith
    · have e2 := (tendsto_order.1 (HW x₀ hx₀)).2 (((m + 1 : ℝ)) : EReal)
        (EReal.coe_lt_coe_iff.2 (by linarith))
      filter_upwards [hsel, e2] with N ⟨G, hGN, h1⟩ h2 y hy hlt
      have hq' : q ≤ (G : Measure ↥Ξ).real D := by
        have := ENNReal.toReal_mono (measure_ne_top _ _) h1.le
        rw [ENNReal.toReal_div] at this
        simpa [hq, hpDdef, Measure.real] using this
      have h3 := hbound _ hq' y hy hlt
      calc worstCase (𝒢 N) (c x₀) < (((m + 1 : ℝ)) : EReal) := h2
        _ < (((m + 2 : ℝ)) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
        _ ≤ expect G (c y) := h3
        _ ≤ worstCase (𝒢 N) (c y) := expect_le_worstCase hGN _

/-- The deterministic core: on the a.s. event of (54) and of the selection property,
conditions (18)–(20) hold. -/
lemma det_main {F : ProbabilityMeasure ↥Ξ} {X : Set (Pt dx)} {c : Pt dx → ↥Ξ → ℝ}
    {𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)}
    (hS : Standing F X c) (hA1 : Assumption1 X c) (hA2 : A2sel F X c 𝒢)
    (hne : ∀ᶠ N in atTop, (𝒢 N).Nonempty)
    (H8 : ∀ x ∈ X, ∀ G : ℕ → ProbabilityMeasure ↥Ξ, (∀ᶠ N in atTop, G N ∈ 𝒢 N) →
      Tendsto (fun N => expect (G N) (c x)) atTop (𝓝 ((trueObj F c x : ℝ) : EReal))) :
    Conditions F X c 𝒢 := by
  have HW : ∀ x ∈ X, Tendsto (fun N => worstCase (𝒢 N) (c x)) atTop
      (𝓝 ((trueObj F c x : ℝ) : EReal)) := fun x hx => worstCase_tendsto F hne (H8 x hx)
  have h18 : ObjConv F X c 𝒢 := proposition_9 F X c 𝒢 hS hA1
    (fun xs x hx hxs hlim => worstCase_seq_tendsto hS hA1 hx hxs hlim (HW x hx))
  refine ⟨h18, ?_⟩
  rcases X.eq_empty_or_nonempty with hX | ⟨x₀, hx₀⟩
  · subst hX
    refine ⟨?_, ?_⟩
    · unfold ValConv
      simp only [Set.mem_empty_iff_false, iInf_false, iInf_top]
      exact tendsto_const_nhds
    · intro xs hxs
      obtain ⟨N, hN, -⟩ := hxs.exists
      exact absurd hN (Set.notMem_empty _)
  obtain ⟨R, hR0, hRt, hRW⟩ := bounded_minimizers hS hA2 HW hx₀
  set K := X ∩ Metric.closedBall (0 : Pt dx) R with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Pt dx) R).inter_left hS.1
  have hKX : K ⊆ X := Set.inter_subset_left
  have hx₀K : x₀ ∈ K := ⟨hx₀, mem_closedBall_zero_iff.2 hR0⟩
  have hcont : ContinuousOn (trueObj F c) K := by
    intro y hy
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (unif_close hA1 y (half_pos hε))
    refine ⟨δ, hδ, fun {x} hx hxy => ?_⟩
    rw [Real.dist_eq]
    have := trueObj_close hS (hKX hy) (hKX hx) (fun ξ => (hball hxy ξ).le)
    linarith
  obtain ⟨x₁, hx₁K, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hcont
  have hx₁X : x₁ ∈ X := hKX hx₁K
  have hx₁min : ∀ y ∈ X, trueObj F c x₁ ≤ trueObj F c y := by
    intro y hy
    by_cases h : ‖y‖ ≤ R
    · exact hmin ⟨hy, mem_closedBall_zero_iff.2 h⟩
    · exact (hmin hx₀K).trans (hRt y hy (lt_of_not_ge h)).le
  have hinfz : (⨅ x ∈ X, ((trueObj F c x : ℝ) : EReal)) = ((trueObj F c x₁ : ℝ) : EReal) :=
    le_antisymm (iInf₂_le x₁ hx₁X)
      (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hx₁min y hy))
  have hbounds : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (((trueObj F c x₁ - ε : ℝ)) : EReal) ≤ ⨅ x ∈ X, worstCase (𝒢 N) (c x) ∧
      (⨅ x ∈ X, worstCase (𝒢 N) (c x)) ≤ (((trueObj F c x₁ + ε : ℝ)) : EReal) := by
    intro ε hε
    filter_upwards [h18 K hKX hKc ε hε, hRW] with N h1 h2
    refine ⟨le_iInf₂ fun y hy => ?_, (iInf₂_le x₁ hx₁X).trans (h1 x₁ hx₁K).1⟩
    by_cases h : ‖y‖ ≤ R
    · exact (EReal.coe_le_coe_iff.2 (by linarith [hx₁min y hy])).trans
        (h1 y ⟨hy, mem_closedBall_zero_iff.2 h⟩).2
    · exact ((EReal.coe_le_coe_iff.2 (by linarith [hx₁min x₀ hx₀])).trans
        (h1 x₀ hx₀K).2).trans (h2 y hy (lt_of_not_ge h)).le
  refine ⟨?_, ?_⟩
  · unfold ValConv
    rw [hinfz, tendsto_order]
    constructor
    · intro b hb
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
      rw [EReal.coe_lt_coe_iff] at hr2
      filter_upwards [hbounds (trueObj F c x₁ - r) (by linarith)] with N h
      exact hr1.trans_le ((EReal.coe_le_coe_iff.2 (by linarith)).trans h.1)
    · intro b hb
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
      rw [EReal.coe_lt_coe_iff] at hr1
      filter_upwards [hbounds (r - trueObj F c x₁) (by linarith)] with N h
      exact (h.2.trans (EReal.coe_le_coe_iff.2 (by linarith))).trans_lt hr2
  · intro xs hxs
    have hK_ev : ∀ᶠ N in atTop, xs N ∈ K := by
      filter_upwards [hxs, hRW] with N hN h2
      refine ⟨hN.1, mem_closedBall_zero_iff.2 (not_lt.1 fun hlt => ?_)⟩
      have := h2 (xs N) hN.1 hlt
      rw [hN.2] at this
      exact absurd (iInf₂_le x₀ hx₀) (not_le.2 this)
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨y, -, hy⟩ := hKc.exists_mapClusterPt_of_frequently hK_ev.frequently
      exact ⟨y, hy⟩
    have hyK : y ∈ K := by
      by_contra h
      obtain ⟨N, h1, h2⟩ :=
        ((hy.frequently (hKc.isClosed.isOpen_compl.mem_nhds h)).and_eventually hK_ev).exists
      exact h1 h2
    refine ⟨hKX hyK, fun z hz => ?_⟩
    suffices h : trueObj F c y ≤ trueObj F c x₁ from h.trans (hx₁min z hz)
    by_contra hlt
    push Not at hlt
    set δ := (trueObj F c y - trueObj F c x₁) / 4 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨N, h1, h2, hKN, h3⟩ := ((hy.frequently (unif_close hA1 y hδpos)).and_eventually
      (hxs.and (hK_ev.and (h18 K hKX hKc δ hδpos)))).exists
    have ht := trueObj_close hS (hKX hyK) (hKX hKN) (fun ξ => (h1 ξ).le)
    have hchain : (((trueObj F c (xs N) - δ : ℝ)) : EReal) ≤ (((trueObj F c x₁ + δ : ℝ)) : EReal) :=
      calc (((trueObj F c (xs N) - δ : ℝ)) : EReal) ≤ worstCase (𝒢 N) (c (xs N)) := (h3 _ hKN).2
        _ = ⨅ x ∈ X, worstCase (𝒢 N) (c x) := h2.2
        _ ≤ worstCase (𝒢 N) (c x₁) := iInf₂_le x₁ hx₁X
        _ ≤ (((trueObj F c x₁ + δ : ℝ)) : EReal) := (h3 x₁ hx₁K).1
    rw [EReal.coe_le_coe_iff] at hchain
    rw [abs_le] at ht
    linarith


instance dataLaw_isProb (F : ProbabilityMeasure ↥Ξ) : IsProbabilityMeasure (dataLaw F) := by
  unfold dataLaw; infer_instance

lemma dataLaw_map_eval (F : ProbabilityMeasure ↥Ξ) (i : ℕ) :
    (dataLaw F).map (fun ω => ω i) = (F : Measure ↥Ξ) := by
  unfold dataLaw
  exact Measure.infinitePi_map_eval _ i

/-- Strong law of large numbers for the empirical mass of a measurable set `D`. -/
lemma slln_empirical (F : ProbabilityMeasure ↥Ξ) {D : Set ↥Ξ} (hD : MeasurableSet D) :
    ∀ᵐ ω ∂(dataLaw F), Tendsto (fun N => empiricalMeasure (sample ω N) D) atTop
      (𝓝 ((F : Measure ↥Ξ) D)) := by
  have hφm : Measurable (D.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hD
  set Y : ℕ → (ℕ → ↥Ξ) → ℝ := fun i ω => D.indicator (fun _ => (1 : ℝ)) (ω i) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => hφm.comp (measurable_pi_apply i)
  have hmap : ∀ i, (dataLaw F).map (Y i) =
      (F : Measure ↥Ξ).map (D.indicator (fun _ => (1 : ℝ))) := by
    intro i
    rw [← dataLaw_map_eval F i, Measure.map_map hφm (measurable_pi_apply i)]
    rfl
  have hint : Integrable (Y 0) (dataLaw F) := by
    have h1 : Integrable (D.indicator (fun _ => (1 : ℝ))) (F : Measure ↥Ξ) :=
      (integrable_const (1 : ℝ)).indicator hD
    rw [← dataLaw_map_eval F 0] at h1
    exact (integrable_map_measure hφm.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 h1
  have hindep : Pairwise (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) (dataLaw F)) := by
    have := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure ↥Ξ))
      (X := fun _ ξ => D.indicator (fun _ => (1 : ℝ)) ξ) (fun _ => hφm)
    exact fun i j hij => this.indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) (dataLaw F) (dataLaw F) :=
    fun i => ⟨(hYm i).aemeasurable, (hYm 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  have hsl := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hmean : ∫ x, Y 0 x ∂(dataLaw F) = ((F : Measure ↥Ξ) D).toReal := by
    have h := integral_map (μ := dataLaw F) (φ := fun ω : ℕ → ↥Ξ => ω 0)
      (measurable_pi_apply 0).aemeasurable (f := D.indicator (fun _ => (1 : ℝ)))
      (by rw [dataLaw_map_eval]; exact hφm.aestronglyMeasurable)
    rw [dataLaw_map_eval, integral_indicator_const _ hD, smul_eq_mul, mul_one] at h
    exact h.symm
  filter_upwards [hsl] with ω hω
  rw [hmean] at hω
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp hω
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at h2
  refine h2.congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Function.comp, empiricalMeasure, sample, hY, Measure.smul_apply,
    Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hD]
  rw [Fin.sum_univ_eq_sum_range (fun i => D.indicator (1 : ↥Ξ → ℝ≥0∞) (ω i))]
  have hcast : ∀ i, D.indicator (1 : ↥Ξ → ℝ≥0∞) (ω i) =
      ENNReal.ofReal (D.indicator (fun _ => (1 : ℝ)) (ω i)) := by
    intro i
    by_cases h : ω i ∈ D <;> simp [h]
  simp_rw [hcast]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _),
    div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg N)),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

end RSAAThm3Aux

open RSAAThm3Aux

theorem solution {d dx : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (hS : Standing F X c) (hA1 : Assumption1 X c) (hA2 : Assumption2 F X c)
    (hA3 : Assumption3 F 𝓕 X c)
    (hemp : ∀ (N : ℕ), 0 < N → ∀ s : Fin N → ↥Ξ,
      ∃ G ∈ 𝓕 N s, (G : Measure ↥Ξ) = empiricalMeasure s)
    (hc : IsCConsistent X c 𝓕) :
    ∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N)) := by
  -- the a.s. event of `A2sel`
  have hsel : ∀ᵐ ω ∂(dataLaw F), A2sel F X c (fun N => 𝓕 N (sample ω N)) := by
    rcases hA2 with ⟨hXc, hb | ⟨D, hDo, hDpos, hM, hB⟩⟩
    · exact ae_of_all _ fun ω => ⟨hXc, Or.inl hb⟩
    · filter_upwards [slln_empirical F hDo.measurableSet] with ω hω
      refine ⟨hXc, Or.inr ⟨D, hDo, hDpos, hM, hB, ?_⟩⟩
      have hlt : (F : Measure ↥Ξ) D / 2 < (F : Measure ↥Ξ) D :=
        ENNReal.half_lt_self hDpos.ne' (measure_ne_top _ _)
      filter_upwards [hω.eventually (lt_mem_nhds hlt), eventually_ge_atTop 1] with N hN hN1
      obtain ⟨G, hG, hGe⟩ := hemp N hN1 (sample ω N)
      exact ⟨G, hG, by rw [hGe]; exact hN⟩
  filter_upwards [hc F, hsel] with ω hω hsω
  refine det_main hS hA1 hsω ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨G, hG, -⟩ := hemp N hN (sample ω N)
    exact ⟨G, hG⟩
  · intro x hx G hG
    have hcc : CConverges X c G F := by
      by_contra h
      obtain ⟨N, h1, h2⟩ := ((hω G h).and_eventually hG).exists
      exact h1 h2
    have := hcc x hx
    unfold expect at this
    rw [if_pos (hS.2 x hx).1] at this
    exact this
