-- Prove2me | solution 1 for SellingData.ListsRotation.proposition5_lists_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T17:13:06.41359+00:00
-- url     : https://prove2.me/submissions/3d31895b-0070-4210-8ff6-7178c3fd6649

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

set_option autoImplicit false

namespace SellingData.ListsRotation.P5Aux

open SellingData.ListsRotation Set Filter Topology MeasureTheory

lemma Icc_sub (M : Model) : Icc M.aLo M.aHi ⊆ Ioo (0:ℝ) 1 := fun _ hx =>
  ⟨lt_of_lt_of_le M.aLo_pos hx.1, lt_of_le_of_lt hx.2 M.aHi_lt_one⟩

lemma cL_mem (M : Model) : M.cL ∈ Icc M.vLo M.vHi :=
  ⟨M.vLo_lt_cL.le, (M.cL_lt_cH.trans M.cH_lt_vHi).le⟩

lemma cH_mem (M : Model) : M.cH ∈ Icc M.vLo M.vHi :=
  ⟨(M.vLo_lt_cL.trans M.cL_lt_cH).le, M.cH_lt_vHi.le⟩

lemma H_ii (M : Model) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {a b : ℝ} (ha : M.vLo ≤ a)
    (hb : b ≤ M.vHi) (hab : a ≤ b) : IntervalIntegrable (fun v => M.H v α) volume a b :=
  ((M.H_cont α hα).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

lemma Hα_cont_v (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) :
    ContinuousOn (fun v => M.Hα v α) (Icc M.vLo M.vHi) := by
  have h1 : ContinuousOn (fun v : ℝ => ((v, α) : ℝ × ℝ)) (Icc M.vLo M.vHi) :=
    continuousOn_id.prodMk continuousOn_const
  exact hHα.comp h1 (fun v hv => ⟨hv, hα⟩)

lemma Hα_ii (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (ha : M.vLo ≤ a) (hb : b ≤ M.vHi) (hab : a ≤ b) :
    IntervalIntegrable (fun v => M.Hα v α) volume a b :=
  ((Hα_cont_v M hHα hα).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

/-- `Φ(c, α) = ∫_{v̲}^{c} H(v, α) dv` -/
noncomputable def Phi (M : Model) (c α : ℝ) : ℝ := ∫ v in M.vLo..c, M.H v α

/-- `D(c, α) = ∫_{v̲}^{c} ∂H/∂α (v, α) dv` -/
noncomputable def D (M : Model) (c α : ℝ) : ℝ := ∫ v in M.vLo..c, M.Hα v α

lemma Phi_hasDerivAt (M : Model) (hHα : M.HαContinuous) {c : ℝ} (hc : c ∈ Icc M.vLo M.vHi)
    {α₀ : ℝ} (hα₀ : α₀ ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun β => Phi M c β) (D M c α₀) α₀ := by
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.closedBall α₀ ε ⊆ Ioo (0:ℝ) 1 := by
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 isOpen_Ioo α₀ hα₀
    exact ⟨ε / 2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans h⟩
  have hK : IsCompact (Icc M.vLo M.vHi ×ˢ Metric.closedBall α₀ ε) :=
    isCompact_Icc.prod (isCompact_closedBall α₀ ε)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hHα.mono (prod_mono subset_rfl hball))
  have hsub : Set.uIoc M.vLo c ⊆ Icc M.vLo M.vHi := by
    rw [uIoc_of_le hc.1]; exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hc.2)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := M.vLo) (b := c)
    (F := fun β v => M.H v β) (F' := fun β v => M.Hα v β) (bound := fun _ => C)
    (s := Metric.ball α₀ ε) (x₀ := α₀) (Metric.ball_mem_nhds α₀ hε)
    (by
      filter_upwards [Metric.ball_mem_nhds α₀ hε] with x hx
      exact ((M.H_cont x (hball (Metric.ball_subset_closedBall hx))).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    (H_ii M hα₀ le_rfl hc.2 hc.1)
    (((Hα_cont_v M hHα hα₀).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun t ht x hx =>
      hC (t, x) ⟨hsub ht, Metric.ball_subset_closedBall hx⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx =>
      M.H_hasDerivAt_α t (hsub ht) x (hball (Metric.ball_subset_closedBall hx)))
  exact key.2

lemma payoff_eq (M : Model) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {c : ℝ} (hc : c ∈ Icc M.vLo M.vHi) :
    M.payoff α c = M.uHat - c + Phi M c α := by
  have hhc : ContinuousOn (fun v => M.h v α) (Icc M.vLo M.vHi) := M.h_cont α hα
  have hcont : ContinuousOn (fun v => (v - c) * M.h v α) (Icc M.vLo M.vHi) :=
    (continuousOn_id.sub continuousOn_const).mul hhc
  have hii : ∀ a b, M.vLo ≤ a → b ≤ M.vHi → a ≤ b →
      IntervalIntegrable (fun v => (v - c) * M.h v α) volume a b := fun a b ha hb hab =>
    (hcont.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hsplit : (∫ v in M.vLo..c, (v - c) * M.h v α) + ∫ v in c..M.vHi, (v - c) * M.h v α
      = ∫ v in M.vLo..M.vHi, (v - c) * M.h v α :=
    intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl hc.2 hc.1)
      (hii _ _ hc.1 le_rfl hc.2)
  have hint_h : ∫ v in M.vLo..M.vHi, M.h v α = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le M.vLo_lt_vHi.le (M.H_cont α hα)
      (fun v hv => M.H_hasDerivAt α hα v hv) (hhc.intervalIntegrable_of_Icc M.vLo_lt_vHi.le)]
    rw [M.H_vHi α hα, M.H_vLo α hα]; ring
  have hvh : IntervalIntegrable (fun v => v * M.h v α) volume M.vLo M.vHi :=
    ((continuousOn_id.mul hhc)).intervalIntegrable_of_Icc M.vLo_lt_vHi.le
  have hch : IntervalIntegrable (fun v => c * M.h v α) volume M.vLo M.vHi :=
    ((continuousOn_const.mul hhc)).intervalIntegrable_of_Icc M.vLo_lt_vHi.le
  have htot : ∫ v in M.vLo..M.vHi, (v - c) * M.h v α = M.uHat - c := by
    have e : (fun v => (v - c) * M.h v α) = fun v => v * M.h v α - c * M.h v α := by
      funext v; ring
    rw [e, intervalIntegral.integral_sub hvh hch, intervalIntegral.integral_const_mul, hint_h,
      M.mean_eq α hα]; ring
  have hmm : min M.vLo c = M.vLo := min_eq_left hc.1
  have hMM : max M.vLo c = c := max_eq_right hc.1
  have hparts : ∫ v in M.vLo..c, (v - c) * M.h v α
      = (c - c) * M.H c α - (M.vLo - c) * M.H M.vLo α - ∫ v in M.vLo..c, (1:ℝ) * M.H v α :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun v => v - c) (v := fun v => M.H v α) (u' := fun _ => (1:ℝ))
      (v' := fun v => M.h v α)
      ((continuousOn_id.sub continuousOn_const))
      (by rw [uIcc_of_le hc.1]; exact (M.H_cont α hα).mono (Icc_subset_Icc le_rfl hc.2))
      (fun x _ => (hasDerivAt_id' x).sub_const c)
      (fun x hx => by
        rw [hmm, hMM] at hx
        exact M.H_hasDerivAt α hα x ⟨hx.1, lt_of_lt_of_le hx.2 hc.2⟩)
      intervalIntegrable_const
      ((hhc.mono (Icc_subset_Icc le_rfl hc.2)).intervalIntegrable_of_Icc hc.1)
  unfold Model.payoff Phi
  have e2 : ∫ v in c..M.vHi, (v - c) * M.h v α
      = (M.uHat - c) - ∫ v in M.vLo..c, (v - c) * M.h v α := by linarith
  rw [e2, hparts, M.H_vLo α hα]
  simp only [one_mul, sub_self, zero_mul, mul_zero]
  ring

lemma payoff_hasDerivAt (M : Model) (hHα : M.HαContinuous) {c : ℝ} (hc : c ∈ Icc M.vLo M.vHi)
    {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun β => M.payoff β c) (D M c α) α := by
  have h1 := (Phi_hasDerivAt M hHα hc hα).const_add (M.uHat - c)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
  exact payoff_eq M hβ hc

lemma payoff_contOn (M : Model) (hHα : M.HαContinuous) {c : ℝ} (hc : c ∈ Icc M.vLo M.vHi) :
    ContinuousOn (fun β => M.payoff β c) (Icc M.aLo M.aHi) := fun β hβ =>
  (payoff_hasDerivAt M hHα hc (Icc_sub M hβ)).continuousAt.continuousWithinAt

lemma payoff_nonneg (M : Model) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {c : ℝ}
    (hc : c ∈ Icc M.vLo M.vHi) : 0 ≤ M.payoff α c := by
  unfold Model.payoff
  exact intervalIntegral.integral_nonneg hc.2 (fun v hv =>
    mul_nonneg (sub_nonneg.2 hv.1) (M.h_pos α hα v ⟨hc.1.trans hv.1, hv.2⟩).le)

lemma H_le_one (M : Model) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {v : ℝ}
    (hv : v ∈ Icc M.vLo M.vHi) : M.H v α ≤ 1 := by
  have hmono : StrictMonoOn (fun x => M.H x α) (Icc M.vLo M.vHi) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) (M.H_cont α hα)
      (f' := fun x => M.h x α)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (M.H_hasDerivAt α hα x hx).hasDerivWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact M.h_pos α hα x (Ioo_subset_Icc_self hx))
  have := hmono.monotoneOn hv ⟨M.vLo_lt_vHi.le, le_rfl⟩ hv.2
  rw [M.H_vHi α hα] at this
  exact this

/-- the information rent `U_LL - U_LH` of the low-cost type -/
noncomputable def R (M : Model) (α : ℝ) : ℝ := M.payoff α M.cL - M.payoff α M.cH

noncomputable def Fh (M : Model) (α : ℝ) : ℝ := M.payoff α M.cH - M.k α

noncomputable def G (M : Model) (α : ℝ) : ℝ := M.θ * Fh M α - (1 - M.θ) * R M α

noncomputable def Hp (M : Model) (α : ℝ) : ℝ := (1 - M.θ) * (M.payoff α M.cL - M.k α)

def IsMx (M : Model) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  x ∈ Icc M.aLo M.aHi ∧ ∀ y ∈ Icc M.aLo M.aHi, f y ≤ f x

noncomputable def mk (M : Model) (x y : ℝ) : Menu :=
  ⟨M.payoff x M.cH, x, M.payoff y M.cL - R M x, y⟩

lemma R_nonneg (M : Model) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) : 0 ≤ R M α := by
  unfold R
  rw [payoff_eq M hα (cL_mem M), payoff_eq M hα (cH_mem M)]
  unfold Phi
  have hsub := intervalIntegral.integral_interval_sub_left
    (H_ii M hα le_rfl (cH_mem M).2 (cH_mem M).1) (H_ii M hα le_rfl (cL_mem M).2 (cL_mem M).1)
  have hle : ∫ v in M.cL..M.cH, M.H v α ≤ ∫ v in M.cL..M.cH, (1:ℝ) :=
    intervalIntegral.integral_mono_on M.cL_lt_cH.le
      (H_ii M hα (cL_mem M).1 (cH_mem M).2 M.cL_lt_cH.le) intervalIntegrable_const
      (fun v hv => H_le_one M hα ⟨(cL_mem M).1.trans hv.1, hv.2.trans (cH_mem M).2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
  linarith

lemma exists_max (M : Model) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc M.aLo M.aHi)) :
    ∃ x, IsMx M f x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 M.aLo_lt_aHi.le) hf
  exact ⟨x, hx, fun y hy => hmax hy⟩

lemma G_contOn (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) :
    ContinuousOn (G M) (Icc M.aLo M.aHi) := by
  have h1 := payoff_contOn M hHα (cH_mem M)
  have h2 := payoff_contOn M hHα (cL_mem M)
  exact (continuousOn_const.mul (h1.sub hk.1)).sub (continuousOn_const.mul (h2.sub h1))

lemma Hp_contOn (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) :
    ContinuousOn (Hp M) (Icc M.aLo M.aHi) :=
  continuousOn_const.mul ((payoff_contOn M hHα (cL_mem M)).sub hk.1)

lemma feasible_mk (M : Model) {x y : ℝ} (hx : x ∈ Icc M.aLo M.aHi) (hy : y ∈ Icc M.aLo M.aHi)
    (hR : R M x ≤ R M y) : M.Feasible (mk M x y) := by
  have p1 := payoff_nonneg M (Icc_sub M hx) (cH_mem M)
  have p2 := payoff_nonneg M (Icc_sub M hy) (cH_mem M)
  have r0 := R_nonneg M (Icc_sub M hx)
  unfold R at hR r0
  refine ⟨p1, ?_, hx, hy, ?_, ?_⟩
  · show 0 ≤ M.payoff y M.cL - R M x
    unfold R; linarith
  · rintro (_ | _)
    · simp only [Model.U, Menu.T, Menu.α, Model.c, mk]; linarith
    · simp only [Model.U, Menu.T, Menu.α, Model.c, mk, R]; linarith
  · rintro (_ | _) (_ | _) hne
    · exact absurd rfl hne
    · simp only [Model.U, Menu.T, Menu.α, Model.c, mk, R]; linarith
    · simp only [Model.U, Menu.T, Menu.α, Model.c, mk, R]; linarith
    · exact absurd rfl hne

lemma profit_mk (M : Model) (x y : ℝ) : M.profit (mk M x y) = G M x + Hp M y := by
  simp only [Model.profit, mk, G, Hp, Fh, R]; ring

lemma profit_le (M : Model) {m : Menu} (hm : M.Feasible m) :
    M.profit m ≤ G M m.αH + Hp M m.αL := by
  obtain ⟨_, _, _, _, hIR, hIC⟩ := hm
  have h1 := hIR SellingData.ListsBinary.CostType.H
  have h2 := hIC SellingData.ListsBinary.CostType.L SellingData.ListsBinary.CostType.H
    (by decide)
  simp only [Model.U, Menu.T, Menu.α, Model.c] at h1 h2
  simp only [Model.profit, G, Hp, Fh, R]
  nlinarith [mul_nonneg (sub_nonneg.2 M.θ_lt_one.le) (sub_nonneg.2 h2), M.θ_pos, M.θ_lt_one]

lemma rev_pref (M : Model) {x y : ℝ} (hx : IsMx M (G M) x) (hy : IsMx M (Hp M) y) :
    R M x ≤ R M y := by
  have h1 := hx.2 y hy.1
  have h2 := hy.2 x hx.1
  simp only [G, Hp, Fh, R] at h1 h2
  have ht := M.θ_pos
  have ht1 : 0 < 1 - M.θ := sub_pos.2 M.θ_lt_one
  have h2' : M.payoff x M.cL - M.k x ≤ M.payoff y M.cL - M.k y :=
    le_of_mul_le_mul_left h2 ht1
  unfold R
  nlinarith [mul_le_mul_of_nonneg_left h2' ht.le]

lemma optimal_mk (M : Model) {x y : ℝ} (hx : IsMx M (G M) x) (hy : IsMx M (Hp M) y) :
    M.IsOptimalMenu (mk M x y) := by
  refine ⟨feasible_mk M hx.1 hy.1 (rev_pref M hx hy), fun m' hm' => ?_⟩
  rw [profit_mk]
  have := profit_le M hm'
  have a1 := hx.2 m'.αH hm'.2.2.1
  have a2 := hy.2 m'.αL hm'.2.2.2.1
  linarith

lemma optimal_char (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) {m : Menu}
    (hm : M.IsOptimalMenu m) : IsMx M (G M) m.αH ∧ IsMx M (Hp M) m.αL := by
  obtain ⟨x, hx⟩ := exists_max M (G_contOn M hk hHα)
  obtain ⟨y, hy⟩ := exists_max M (Hp_contOn M hk hHα)
  have h1 := hm.2 _ (optimal_mk M hx hy).1
  rw [profit_mk] at h1
  have h2 := profit_le M hm.1
  have hH := hm.1.2.2.1
  have hL := hm.1.2.2.2.1
  have a1 := hx.2 _ hH
  have a2 := hy.2 _ hL
  refine ⟨⟨hH, fun z hz => ?_⟩, ⟨hL, fun z hz => ?_⟩⟩
  · have := hx.2 z hz; linarith
  · have := hy.2 z hz; linarith

lemma effL_iff (M : Model) (a : ℝ) : M.IsEfficient (1 - M.θ) M.cL a ↔ IsMx M (Hp M) a :=
  Iff.rfl

lemma effH (M : Model) {a : ℝ} (h : M.IsEfficient M.θ M.cH a) : IsMx M (Fh M) a :=
  ⟨h.1, fun y hy => le_of_mul_le_mul_left (h.2 y hy) M.θ_pos⟩

lemma weak (M : Model) {a x : ℝ} (ha : IsMx M (Fh M) a) (hx : IsMx M (G M) x) :
    R M x ≤ R M a := by
  have h1 := hx.2 a ha.1
  have h2 := ha.2 x hx.1
  simp only [G] at h1
  have ht1 : 0 < 1 - M.θ := sub_pos.2 M.θ_lt_one
  nlinarith [mul_le_mul_of_nonneg_left h2 M.θ_pos.le]

lemma not_max_lo {f : ℝ → ℝ} {f' lo hi : ℝ} (hlt : lo < hi)
    (hf : HasDerivWithinAt f f' (Ici lo) lo) (hpos : 0 < f')
    (hmax : ∀ y ∈ Icc lo hi, f y ≤ f lo) : False := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 hf
  have hset : Ici lo \ {lo} = Ioi lo := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h1; exact ⟨h1.le, ne_of_gt h1⟩
  rw [hset] at ht
  have e1 : ∀ᶠ z in nhdsWithin lo (Ioi lo), 0 < slope f lo z :=
    (tendsto_order.1 ht).1 0 hpos
  have e2 : ∀ᶠ z in nhdsWithin lo (Ioi lo), z ∈ Ioo lo hi := Ioo_mem_nhdsGT hlt
  obtain ⟨z, hz1, hz2⟩ := (e1.and e2).exists
  have hz0 : 0 < z - lo := by linarith [hz2.1]
  rw [slope_def_field] at hz1
  have := hmax z ⟨hz2.1.le, hz2.2.le⟩
  have : (f z - f lo) / (z - lo) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hz0.le
  linarith

lemma not_max_hi {f f' : ℝ → ℝ} {lo hi : ℝ} (hlt : lo < hi) (hc : ContinuousOn f (Icc lo hi))
    (hd : ∀ z ∈ Ioo lo hi, HasDerivAt f (f' z) z) (hev : ∀ᶠ z in 𝓝[<] hi, f' z < 0)
    (hmax : ∀ y ∈ Icc lo hi, f y ≤ f hi) : False := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hx0lt : max l lo < hi := max_lt hl hlt
  obtain ⟨c, hc', hdc⟩ := exists_hasDerivAt_eq_slope f f' hx0lt
    (hc.mono (Icc_subset_Icc (le_max_right _ _) le_rfl))
    (fun z hz => hd z ⟨lt_of_le_of_lt (le_max_right _ _) hz.1, hz.2⟩)
  have hneg : f' c < 0 := hsub ⟨lt_of_le_of_lt (le_max_left _ _) hc'.1, hc'.2⟩
  have hm := hmax (max l lo) ⟨le_max_right _ _, hx0lt.le⟩
  have hpos : 0 < hi - max l lo := by linarith
  rw [hdc] at hneg
  have : 0 ≤ (f hi - f (max l lo)) / (hi - max l lo) := div_nonneg (by linarith) hpos.le
  linarith

lemma R_hasDerivAt (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (R M) (D M M.cL α - D M M.cH α) α :=
  (payoff_hasDerivAt M hHα (cL_mem M) hα).sub (payoff_hasDerivAt M hHα (cH_mem M) hα)

lemma Fh_hasDerivAt (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) {α : ℝ}
    (hα : α ∈ Ioo M.aLo M.aHi) :
    HasDerivAt (Fh M) (D M M.cH α - deriv M.k α) α :=
  (payoff_hasDerivAt M hHα (cH_mem M) (Icc_sub M (Ioo_subset_Icc_self hα))).sub
    (hk.2.1 α hα).hasDerivAt

lemma R_contOn (M : Model) (hHα : M.HαContinuous) : ContinuousOn (R M) (Icc M.aLo M.aHi) :=
  fun β hβ => (R_hasDerivAt M hHα (Icc_sub M hβ)).continuousAt.continuousWithinAt

lemma D_sub (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (ha : a ∈ Icc M.vLo M.vHi) (hb : b ∈ Icc M.vLo M.vHi) :
    D M b α - D M a α = ∫ v in a..b, M.Hα v α := by
  unfold D
  exact intervalIntegral.integral_interval_sub_left (Hα_ii M hHα hα le_rfl hb.2 hb.1)
    (Hα_ii M hHα hα le_rfl ha.2 ha.1)

lemma D_vHi (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) :
    D M M.vHi α = 0 := by
  have hmem : M.vHi ∈ Icc M.vLo M.vHi := ⟨M.vLo_lt_vHi.le, le_rfl⟩
  have h1 := Phi_hasDerivAt M hHα hmem hα
  have h2 : HasDerivAt (fun β => Phi M M.vHi β) 0 α := by
    refine (hasDerivAt_const α (M.vHi - M.uHat)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
    have := payoff_eq M hβ hmem
    unfold Model.payoff at this
    rw [intervalIntegral.integral_same] at this
    linarith
  exact h1.unique h2

lemma int_pos (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (ha : M.vLo ≤ a) (hab : a < b) (hb : b ≤ M.vPlus) : 0 < ∫ v in a..b, M.Hα v α :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (Hα_ii M hHα hα ha (hb.trans M.vPlus_mem.2.le) hab.le)
    (fun v hv => (M.rotation α hα).1 v ⟨lt_of_le_of_lt ha hv.1, lt_of_lt_of_le hv.2 hb⟩) hab

lemma int_neg (M : Model) (hHα : M.HαContinuous) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (ha : M.vPlus ≤ a) (hab : a < b) (hb : b ≤ M.vHi) : ∫ v in a..b, M.Hα v α < 0 := by
  have hi : IntervalIntegrable (fun v => -M.Hα v α) volume a b :=
    (Hα_ii M hHα hα (M.vPlus_mem.1.le.trans ha) hb hab.le).neg
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun v hv => neg_pos.2 ((M.rotation α hα).2 v ⟨lt_of_le_of_lt ha hv.1, lt_of_lt_of_le hv.2 hb⟩))
    hab
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- the strict part: an efficient level for `c_H` is never a maximizer of the virtual objective -/
lemma ne_of_max (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) {a : ℝ}
    (ha : IsMx M (Fh M) a) (hx : IsMx M (G M) a)
    (hR' : ∀ α ∈ Ioo (0:ℝ) 1, D M M.cL α - D M M.cH α ≠ 0) (hD : 0 < D M M.cH M.aLo) :
    False := by
  have hlt := M.aLo_lt_aHi
  rcases eq_or_lt_of_le ha.1.1 with hlo | hlo
  · -- a = aLo
    subst hlo
    have hder : HasDerivWithinAt (Fh M) (D M M.cH M.aLo - 0) (Ici M.aLo) M.aLo :=
      (payoff_hasDerivAt M hHα (cH_mem M) (Icc_sub M ha.1)).hasDerivWithinAt.sub hk.2.2.1
    exact not_max_lo hlt hder (by linarith) ha.2
  rcases eq_or_lt_of_le ha.1.2 with hhi | hhi
  · -- a = aHi
    subst hhi
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (hHα.mono (prod_mono (subset_rfl : Icc M.vLo M.vHi ⊆ _) (Icc_sub M)))
    have hsub : Set.uIoc M.vLo M.cH ⊆ Icc M.vLo M.vHi := by
      rw [uIoc_of_le (cH_mem M).1]
      exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (cH_mem M).2)
    have hDb : ∀ z ∈ Icc M.aLo M.aHi, D M M.cH z ≤ C * |M.cH - M.vLo| := by
      intro z hz
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := M.vLo) (b := M.cH)
        (f := fun v => M.Hα v z) (C := C) (fun v hv => hC (v, z) ⟨hsub hv, hz⟩)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have e1 : ∀ᶠ z in 𝓝[<] M.aHi, C * |M.cH - M.vLo| < deriv M.k z :=
      hk.2.2.2.eventually (eventually_gt_atTop _)
    have e2 : ∀ᶠ z in 𝓝[<] M.aHi, z ∈ Ioo M.aLo M.aHi := Ioo_mem_nhdsLT hlt
    have hev : ∀ᶠ z in 𝓝[<] M.aHi, D M M.cH z - deriv M.k z < 0 := by
      filter_upwards [e1, e2] with z hz1 hz2
      have := hDb z (Ioo_subset_Icc_self hz2)
      linarith
    have hcont : ContinuousOn (Fh M) (Icc M.aLo M.aHi) :=
      (payoff_contOn M hHα (cH_mem M)).sub hk.1
    exact not_max_hi hlt hcont (fun z hz => Fh_hasDerivAt M hk hHα hz) hev ha.2
  · -- interior
    have hI : Icc M.aLo M.aHi ∈ 𝓝 a := Icc_mem_nhds hlo hhi
    have hF := Fh_hasDerivAt M hk hHα ⟨hlo, hhi⟩
    have hRd := R_hasDerivAt M hHα (Icc_sub M ha.1)
    have hGd : HasDerivAt (G M) (M.θ * (D M M.cH a - deriv M.k a) -
        (1 - M.θ) * (D M M.cL a - D M M.cH a)) a :=
      (hF.const_mul M.θ).sub (hRd.const_mul (1 - M.θ))
    have l1 : IsLocalMax (Fh M) a := Filter.mem_of_superset hI (fun y hy => ha.2 y hy)
    have l2 : IsLocalMax (G M) a := Filter.mem_of_superset hI (fun y hy => hx.2 y hy)
    have z1 := l1.hasDerivAt_eq_zero hF
    have z2 := l2.hasDerivAt_eq_zero hGd
    rw [z1, mul_zero, zero_sub, neg_eq_zero] at z2
    rcases mul_eq_zero.1 z2 with h | h
    · linarith [M.θ_lt_one]
    · exact hR' a (Icc_sub M ha.1) h

theorem main (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αL = a) ↔ M.IsEfficient (1 - M.θ) M.cL a) ∧
    (M.cL < M.cH ∧ M.cH < M.vPlus →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → a < m.αH) ∧
    (M.vPlus < M.cL ∧ M.cL < M.cH →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → m.αH < a) := by
  obtain ⟨x0, hx0⟩ := exists_max M (G_contOn M hk hHα)
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨m, hm, rfl⟩
    exact (effL_iff M m.αL).2 (optimal_char M hk hHα hm).2
  · intro ha
    exact ⟨mk M x0 a, optimal_mk M hx0 ((effL_iff M a).1 ha), rfl⟩
  · rintro ⟨-, h2⟩ m hm a ha
    have hA := effH M ha
    have hX := (optimal_char M hk hHα hm).1
    have hw := weak M hA hX
    -- `R` is strictly decreasing
    have hRd : ∀ α ∈ Ioo (0:ℝ) 1, D M M.cL α - D M M.cH α < 0 := by
      intro α hα
      have := D_sub M hHα hα (cL_mem M) (cH_mem M)
      have := int_pos M hHα hα (cL_mem M).1 M.cL_lt_cH h2.le
      linarith
    have hanti : StrictAntiOn (R M) (Icc M.aLo M.aHi) :=
      strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) (R_contOn M hHα)
        (f' := fun α => D M M.cL α - D M M.cH α)
        (fun α hα => (R_hasDerivAt M hHα (Icc_sub M (interior_subset hα))).hasDerivWithinAt)
        (fun α hα => hRd α (Icc_sub M (interior_subset hα)))
    have hD : 0 < D M M.cH M.aLo := by
      have := D_sub M hHα (Icc_sub M ⟨le_rfl, M.aLo_lt_aHi.le⟩)
        (⟨le_rfl, M.vLo_lt_vHi.le⟩ : M.vLo ∈ Icc M.vLo M.vHi) (cH_mem M)
      have h0 : D M M.vLo M.aLo = 0 := by unfold D; exact intervalIntegral.integral_same
      have := int_pos M hHα (Icc_sub M ⟨le_rfl, M.aLo_lt_aHi.le⟩) le_rfl
        (M.vLo_lt_cL.trans M.cL_lt_cH) h2.le
      linarith
    rcases lt_trichotomy a m.αH with h | h | h
    · exact h
    · exact (ne_of_max M hk hHα hA (by rw [h]; exact hX) (fun α hα => (hRd α hα).ne) hD).elim
    · have := hanti hX.1 hA.1 h
      linarith
  · rintro ⟨h1, -⟩ m hm a ha
    have hA := effH M ha
    have hX := (optimal_char M hk hHα hm).1
    have hw := weak M hA hX
    have hRd : ∀ α ∈ Ioo (0:ℝ) 1, 0 < D M M.cL α - D M M.cH α := by
      intro α hα
      have := D_sub M hHα hα (cL_mem M) (cH_mem M)
      have := int_neg M hHα hα h1.le M.cL_lt_cH (cH_mem M).2
      linarith
    have hmono : StrictMonoOn (R M) (Icc M.aLo M.aHi) :=
      strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) (R_contOn M hHα)
        (f' := fun α => D M M.cL α - D M M.cH α)
        (fun α hα => (R_hasDerivAt M hHα (Icc_sub M (interior_subset hα))).hasDerivWithinAt)
        (fun α hα => hRd α (Icc_sub M (interior_subset hα)))
    have hD : 0 < D M M.cH M.aLo := by
      have hα0 := Icc_sub M ⟨le_rfl, M.aLo_lt_aHi.le⟩
      have := D_sub M hHα hα0 (cH_mem M) (⟨M.vLo_lt_vHi.le, le_rfl⟩ : M.vHi ∈ Icc M.vLo M.vHi)
      have := D_vHi M hHα hα0
      have := int_neg M hHα hα0 (h1.trans M.cL_lt_cH).le M.cH_lt_vHi le_rfl
      linarith
    rcases lt_trichotomy m.αH a with h | h | h
    · exact h
    · exact (ne_of_max M hk hHα hA (by rw [← h]; exact hX) (fun α hα => (hRd α hα).ne') hD).elim
    · have := hmono hA.1 hX.1 h
      linarith

end SellingData.ListsRotation.P5Aux

open SellingData.ListsRotation in
theorem solution (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αL = a) ↔ M.IsEfficient (1 - M.θ) M.cL a) ∧
    (M.cL < M.cH ∧ M.cH < M.vPlus →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → a < m.αH) ∧
    (M.vPlus < M.cL ∧ M.cL < M.cH →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → m.αH < a) := by
  exact P5Aux.main M hk hHα
