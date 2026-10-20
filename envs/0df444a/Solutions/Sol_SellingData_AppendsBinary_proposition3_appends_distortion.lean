-- Prove2me | solution 1 for SellingData.AppendsBinary.proposition3_appends_distortion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:56:57.557015+00:00
-- url     : https://prove2.me/submissions/9b564e5d-a848-4a6a-baf8-770a3e09ec3a

import Mathlib
import Definitions.Def_SellingData_AppendsBinary_Setting

set_option autoImplicit false

namespace SellingData.AppendsBinary.P3Aux

open SellingData.AppendsBinary

/-- affine form of the gross payoff `σ_h(α)[v_h(α) - c]` -/
def Q (M : Model) (c x : ℝ) : ℝ :=
  M.φ * x * (M.uHi - c) + (1 - M.φ) * (1 - x) * (M.uLo - c)

/-- slope of the affine payoff in `α` -/
def B (M : Model) (c : ℝ) : ℝ :=
  M.φ * (M.uHi - c) - (1 - M.φ) * (M.uLo - c)

lemma Q_eq (M : Model) (c x : ℝ) : Q M c x = (1 - M.φ) * (M.uLo - c) + B M c * x := by
  unfold Q B; ring

lemma sigmaH_pos (M : Model) {x : ℝ} (hx : x ∈ Set.Icc M.aLo M.aHi) :
    0 < SellingData.ListsBinary.sigmaH M.φ x := by
  have h1 := M.φ_pos; have h2 := M.φ_lt_one; have h3 := M.half_lt_aLo
  have h4 := M.aHi_lt_one
  obtain ⟨hx1, hx2⟩ := hx
  unfold SellingData.ListsBinary.sigmaH
  have : 0 < M.φ * x := mul_pos h1 (by linarith)
  have : 0 < (1 - M.φ) * (1 - x) := mul_pos (by linarith) (by linarith)
  linarith

lemma sigmaL_pos (M : Model) {x : ℝ} (hx : x ∈ Set.Icc M.aLo M.aHi) :
    0 < 1 - SellingData.ListsBinary.sigmaH M.φ x := by
  have h1 := M.φ_pos; have h2 := M.φ_lt_one; have h3 := M.half_lt_aLo
  have h4 := M.aHi_lt_one
  obtain ⟨hx1, hx2⟩ := hx
  unfold SellingData.ListsBinary.sigmaH
  have : 0 < M.φ * (1 - x) := mul_pos h1 (by linarith)
  have : 0 < (1 - M.φ) * x := mul_pos (by linarith) (by linarith)
  nlinarith

lemma payoff_eq (M : Model) (c : ℝ) {x : ℝ} (hx : x ∈ Set.Icc M.aLo M.aHi) :
    M.payoff x c = Q M c x := by
  have hs := sigmaH_pos M hx
  unfold Model.payoff Model.σh Model.vh vHigh SellingData.ListsBinary.phiH Q
  unfold SellingData.ListsBinary.sigmaH at hs ⊢
  field_simp
  ring

lemma std_lo (M : Model) (c : ℝ)
    (hc : vLow M.uLo M.uHi M.φ M.aLo < c ∧ c < vHigh M.uLo M.uHi M.φ M.aLo) :
    (1 - M.aLo) * (M.φ * (M.uHi - c)) - M.aLo * ((1 - M.φ) * (c - M.uLo)) < 0 ∧
    0 < M.aLo * (M.φ * (M.uHi - c)) - (1 - M.aLo) * ((1 - M.φ) * (c - M.uLo)) := by
  have h1 := M.φ_pos; have h2 := M.φ_lt_one; have h3 := M.half_lt_aLo
  have h4 := M.aHi_lt_one; have h5 := M.aLo_lt_aHi
  obtain ⟨hl, hh⟩ := hc
  set a := M.aLo
  have hsH : 0 < M.φ * a + (1 - M.φ) * (1 - a) := by
    have : 0 < M.φ * a := mul_pos h1 (by linarith)
    have : 0 < (1 - M.φ) * (1 - a) := mul_pos (by linarith) (by linarith)
    linarith
  have hsL : 0 < M.φ * (1 - a) + (1 - M.φ) * a := by
    have : 0 < M.φ * (1 - a) := mul_pos h1 (by linarith)
    have : 0 < (1 - M.φ) * a := mul_pos (by linarith) (by linarith)
    linarith
  have eH : (M.φ * a + (1 - M.φ) * (1 - a)) * (vHigh M.uLo M.uHi M.φ a - c)
      = a * (M.φ * (M.uHi - c)) - (1 - a) * ((1 - M.φ) * (c - M.uLo)) := by
    unfold vHigh SellingData.ListsBinary.phiH; field_simp; ring
  have eL : (M.φ * (1 - a) + (1 - M.φ) * a) * (vLow M.uLo M.uHi M.φ a - c)
      = (1 - a) * (M.φ * (M.uHi - c)) - a * ((1 - M.φ) * (c - M.uLo)) := by
    have hp : SellingData.ListsBinary.phiL M.φ a * (M.φ * (1 - a) + (1 - M.φ) * a)
        = M.φ * (1 - a) := div_mul_cancel₀ _ hsL.ne'
    unfold vLow
    linear_combination (M.uHi - M.uLo) * hp
  have pH : 0 < (M.φ * a + (1 - M.φ) * (1 - a)) * (vHigh M.uLo M.uHi M.φ a - c) :=
    mul_pos hsH (by linarith)
  have pL : (M.φ * (1 - a) + (1 - M.φ) * a) * (vLow M.uLo M.uHi M.φ a - c) < 0 :=
    mul_neg_of_pos_of_neg hsL (by linarith)
  rw [eH] at pH; rw [eL] at pL
  exact ⟨pL, pH⟩

lemma B_pos (M : Model) (c : ℝ)
    (hc : vLow M.uLo M.uHi M.φ M.aLo < c ∧ c < vHigh M.uLo M.uHi M.φ M.aLo) : 0 < B M c := by
  obtain ⟨pL, pH⟩ := std_lo M c hc
  have h3 := M.half_lt_aLo
  have key : 0 < (2 * M.aLo - 1) * (M.φ * (M.uHi - c) + (1 - M.φ) * (c - M.uLo)) := by
    nlinarith
  have h2a : 0 < 2 * M.aLo - 1 := by linarith
  have := (pos_iff_pos_of_mul_pos key).1 h2a
  unfold B; linarith

/-- the low-signal payoff `Q c z - (û - c) = σ_l(z)(c - v_l(z)) > 0` -/
lemma TL_pos (M : Model) (c : ℝ)
    (hc : vLow M.uLo M.uHi M.φ M.aLo < c ∧ c < vHigh M.uLo M.uHi M.φ M.aLo)
    {z : ℝ} (hz : z ∈ Set.Icc M.aLo M.aHi) : 0 < Q M c z - (M.uHat - c) := by
  have h0 := (std_lo M c hc).1
  have hB := B_pos M c hc
  have e : Q M c z - (M.uHat - c) =
      -((1 - M.aLo) * (M.φ * (M.uHi - c)) - M.aLo * ((1 - M.φ) * (c - M.uLo)))
        + (z - M.aLo) * B M c := by
    unfold Q Model.uHat B; ring
  rw [e]
  have : 0 ≤ (z - M.aLo) * B M c := mul_nonneg (by linarith [hz.1]) hB.le
  linarith

/-- `x` maximizes `b * y - k y` on `[α̲, ᾱ]`. -/
def MaxSlope (M : Model) (b x : ℝ) : Prop :=
  x ∈ Set.Icc M.aLo M.aHi ∧ ∀ y ∈ Set.Icc M.aLo M.aHi, b * y - M.k y ≤ b * x - M.k x

lemma exists_maxSlope (M : Model) (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (b : ℝ) : ∃ x, MaxSlope M b x := by
  have hne : (Set.Icc M.aLo M.aHi).Nonempty := Set.nonempty_Icc.2 M.aLo_lt_aHi.le
  have hc : ContinuousOn (fun y => b * y - M.k y) (Set.Icc M.aLo M.aHi) :=
    (continuousOn_const.mul continuousOn_id).sub hk_cont
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  exact ⟨x, hx, fun y hy => hmax hy⟩

lemma maxSlope_mono (M : Model) {b1 b2 x1 x2 : ℝ} (h1 : MaxSlope M b1 x1)
    (h2 : MaxSlope M b2 x2) : 0 ≤ (b2 - b1) * (x2 - x1) := by
  have a := h1.2 x2 h2.1
  have b := h2.2 x1 h1.1
  nlinarith

lemma not_maxSlope_lo (M : Model)
    (hk_left : HasDerivWithinAt M.k 0 (Set.Ici M.aLo) M.aLo) {b : ℝ} (hb : 0 < b)
    (h : MaxSlope M b M.aLo) : False := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.1 hk_left)
  have hset : Set.Ici M.aLo \ {M.aLo} = Set.Ioi M.aLo := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h1; exact ⟨h1.le, ne_of_gt h1⟩
  rw [hset] at ht
  have e1 : ∀ᶠ z in nhdsWithin M.aLo (Set.Ioi M.aLo), slope M.k M.aLo z < b :=
    (tendsto_order.1 ht).2 b hb
  have e2 : ∀ᶠ z in nhdsWithin M.aLo (Set.Ioi M.aLo), z ∈ Set.Ioo M.aLo M.aHi :=
    Ioo_mem_nhdsGT M.aLo_lt_aHi
  obtain ⟨z, hz1, hz2⟩ := (e1.and e2).exists
  have hz0 : 0 < z - M.aLo := by linarith [hz2.1]
  rw [slope_def_field, div_lt_iff₀ hz0] at hz1
  have := h.2 z ⟨hz2.1.le, hz2.2.le⟩
  linarith

lemma not_maxSlope_hi (M : Model)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a)
    (hk_right : Filter.Tendsto (deriv M.k) (nhdsWithin M.aHi (Set.Iio M.aHi)) Filter.atTop)
    {b : ℝ} (h : MaxSlope M b M.aHi) : False := by
  have e1 : ∀ᶠ z in nhdsWithin M.aHi (Set.Iio M.aHi), b + 1 ≤ deriv M.k z :=
    Filter.tendsto_atTop.1 hk_right (b + 1)
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset.1 e1)
  set x0 := max l M.aLo with hx0
  have hx0lt : x0 < M.aHi := max_lt hl M.aLo_lt_aHi
  have hcont : ContinuousOn M.k (Set.Icc x0 M.aHi) :=
    hk_cont.mono (Set.Icc_subset_Icc (le_max_right _ _) le_rfl)
  have hdiff : DifferentiableOn ℝ M.k (Set.Ioo x0 M.aHi) := fun z hz =>
    (hk_diff z ⟨lt_of_le_of_lt (le_max_right _ _) hz.1, hz.2⟩).differentiableWithinAt
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope M.k hx0lt hcont hdiff
  have hcl : c ∈ Set.Ioo l M.aHi := ⟨lt_of_le_of_lt (le_max_left _ _) hc.1, hc.2⟩
  have hge : b + 1 ≤ deriv M.k c := hsub hcl
  have hpos : 0 < M.aHi - x0 := by linarith
  rw [hdc, le_div_iff₀ hpos] at hge
  have := h.2 x0 ⟨le_max_right _ _, hx0lt.le⟩
  nlinarith

lemma maxSlope_unique (M : Model)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a)
    (hk_left : HasDerivWithinAt M.k 0 (Set.Ici M.aLo) M.aLo)
    (hk_right : Filter.Tendsto (deriv M.k) (nhdsWithin M.aHi (Set.Iio M.aHi)) Filter.atTop)
    {B0 b a : ℝ} (hB : 0 < B0) (h1 : MaxSlope M B0 a) (h2 : MaxSlope M b a) : b = B0 := by
  have ha := h1.1
  rcases eq_or_lt_of_le ha.1 with hlo | hlo
  · exact (not_maxSlope_lo M hk_left hB (hlo ▸ h1)).elim
  rcases eq_or_lt_of_le ha.2 with hhi | hhi
  · exact (not_maxSlope_hi M hk_cont hk_diff hk_right (hhi ▸ h1)).elim
  have hI : Set.Icc M.aLo M.aHi ∈ nhds a := Icc_mem_nhds hlo hhi
  have hd := (hk_diff a ⟨hlo, hhi⟩).hasDerivAt
  have fermat : ∀ c : ℝ, MaxSlope M c a → c = deriv M.k a := by
    intro c hc
    have hloc : IsLocalMax (fun y => c * y - M.k y) a :=
      Filter.mem_of_superset hI (fun y hy => hc.2 y hy)
    have hder : HasDerivAt (fun y => c * y - M.k y) (c * 1 - deriv M.k a) a :=
      (hasDerivAt_id a |>.const_mul c).sub hd
    have := hloc.hasDerivAt_eq_zero hder
    linarith
  rw [fermat b h2, fermat B0 h1]

/-- a function whose increments are a positive multiple of those of `b * y - k y` has the same
maximizers -/
lemma maxSlope_iff (M : Model) {F : ℝ → ℝ} {w b x : ℝ} (hw : 0 < w)
    (hx : x ∈ Set.Icc M.aLo M.aHi)
    (hF : ∀ z ∈ Set.Icc M.aLo M.aHi, F z - F x = w * ((b * z - M.k z) - (b * x - M.k x))) :
    MaxSlope M b x ↔ ∀ z ∈ Set.Icc M.aLo M.aHi, F z ≤ F x := by
  constructor
  · intro h z hz
    have h1 := h.2 z hz
    have h2 := hF z hz
    have : w * ((b * z - M.k z) - (b * x - M.k x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hw.le (by linarith)
    linarith
  · intro h
    refine ⟨hx, fun z hz => ?_⟩
    have h1 := h z hz
    have h2 := hF z hz
    by_contra hne
    push Not at hne
    have : 0 < w * ((b * z - M.k z) - (b * x - M.k x)) := mul_pos hw (by linarith)
    linarith

/-- `G` : the `α_H` part of the bound on profit -/
def G (M : Model) (x : ℝ) : ℝ := M.θ * (Q M M.cH x - M.k x)

/-- `Hf` : the `α_L` part of the bound on profit (IR_L and IC_{H,L} binding) -/
def Hf (M : Model) (y : ℝ) : ℝ :=
  Q M M.cL y - (M.uHat - M.cL) - M.θ * Q M M.cH y - (1 - M.θ) * M.k y

/-- the virtual slope for type `L` -/
noncomputable def bL (M : Model) : ℝ :=
  B M M.cL + M.θ / (1 - M.θ) * (M.cH - M.cL) * (2 * M.φ - 1)

lemma G_diff (M : Model) (x z : ℝ) :
    G M z - G M x = M.θ * ((B M M.cH * z - M.k z) - (B M M.cH * x - M.k x)) := by
  unfold G
  rw [Q_eq, Q_eq]
  ring

lemma H_diff (M : Model) (x z : ℝ) :
    Hf M z - Hf M x = (1 - M.θ) * ((bL M * z - M.k z) - (bL M * x - M.k x)) := by
  have hθ : 1 - M.θ ≠ 0 := by linarith [M.θ_lt_one]
  unfold Hf bL
  simp only [Q_eq]
  unfold B
  field_simp
  ring

lemma U_eq (M : Model) (m : Menu) (i j : SellingData.ListsBinary.CostType)
    (h : m.α j ∈ Set.Icc M.aLo M.aHi) :
    M.U m i j = -(m.T j) + Q M (M.c i) (m.α j) := by
  unfold Model.U
  rw [payoff_eq M _ h]

lemma outside_eq (M : Model) {c : ℝ} (hc : c ≤ M.uHat) : M.outside c = M.uHat - c := by
  unfold Model.outside
  exact max_eq_left (by linarith)

lemma profit_eq (M : Model) (m : Menu) :
    M.profit m = M.θ * (m.TH - M.k m.αH) + (1 - M.θ) * (m.TL - M.k m.αL) := by
  unfold Model.profit
  rw [show (Finset.univ : Finset SellingData.ListsBinary.CostType) =
      {SellingData.ListsBinary.CostType.H, SellingData.ListsBinary.CostType.L} from rfl,
    Finset.sum_pair (by decide)]
  rfl

/-- the menu built from a pair of informativeness levels, with `IR_L` and `IC_{H,L}` binding -/
def mk (M : Model) (x y : ℝ) : Menu :=
  ⟨(Q M M.cL y - (M.uHat - M.cL)) + Q M M.cH x - Q M M.cH y, x,
    Q M M.cL y - (M.uHat - M.cL), y⟩

lemma feasible_mk (M : Model) (hcH : M.cH < M.uHat) {x y : ℝ}
    (hx : x ∈ Set.Icc M.aLo M.aHi)
    (hy : y ∈ Set.Icc M.aLo M.aHi) (hmon : 0 ≤ (2 * M.φ - 1) * (y - x)) :
    M.Feasible (mk M x y) := by
  have hΔ : 0 < M.cH - M.cL := by linarith [M.cL_lt_cH]
  have hcL : M.cL ≤ M.uHat := by linarith [M.cL_lt_cH]
  have hσy := sigmaL_pos M hy
  have hTx := TL_pos M M.cL M.standing_cL hx
  have hTy := TL_pos M M.cL M.standing_cL hy
  have eσ : SellingData.ListsBinary.sigmaH M.φ y - SellingData.ListsBinary.sigmaH M.φ x
      = (2 * M.φ - 1) * (y - x) := by
    unfold SellingData.ListsBinary.sigmaH; ring
  have eQ : ∀ z, Q M M.cL z - Q M M.cH z
      = SellingData.ListsBinary.sigmaH M.φ z * (M.cH - M.cL) := by
    intro z; unfold Q SellingData.ListsBinary.sigmaH; ring
  have hxH : (mk M x y).α .H ∈ Set.Icc M.aLo M.aHi := hx
  have hyL : (mk M x y).α .L ∈ Set.Icc M.aLo M.aHi := hy
  have uHH := U_eq M (mk M x y) .H .H hxH
  have uLH := U_eq M (mk M x y) .L .H hxH
  have uHL := U_eq M (mk M x y) .H .L hyL
  have uLL := U_eq M (mk M x y) .L .L hyL
  simp only [mk, Menu.T, Menu.α, Model.c] at uHH uLH uHL uLL
  have eQy := eQ y
  have eQx := eQ x
  have hm := mul_nonneg hmon hΔ.le
  have hs := mul_nonneg hσy.le hΔ.le
  refine ⟨fun j => ?_, fun i => ?_, fun i i' hii => ?_⟩
  · cases j
    · refine ⟨?_, hx⟩
      show 0 ≤ (Q M M.cL y - (M.uHat - M.cL)) + Q M M.cH x - Q M M.cH y
      nlinarith
    · exact ⟨hTy.le, hy⟩
  · cases i
    · simp only [mk, Model.c]
      rw [uHH, outside_eq M hcH.le]
      nlinarith
    · simp only [mk, Model.c]
      rw [uLL, outside_eq M hcL]
      linarith
  · simp only [mk]
    cases i <;> cases i'
    · exact (hii rfl).elim
    · rw [uHL, uHH]; nlinarith
    · rw [uLH, uLL]; nlinarith
    · exact (hii rfl).elim

lemma profit_mk (M : Model) (x y : ℝ) : M.profit (mk M x y) = G M x + Hf M y := by
  rw [profit_eq]
  simp only [mk, G, Hf]
  ring

lemma profit_le (M : Model) (hcH : M.cH < M.uHat) {m : Menu} (hm : M.Feasible m) :
    M.profit m ≤ G M m.αH + Hf M m.αL := by
  obtain ⟨hT, hIR, hIC⟩ := hm
  have hcL : M.cL ≤ M.uHat := by linarith [M.cL_lt_cH]
  have hxH' : m.α .H ∈ Set.Icc M.aLo M.aHi := (hT .H).2
  have hyL' : m.α .L ∈ Set.Icc M.aLo M.aHi := (hT .L).2
  have iL := hIR .L
  have ic := hIC .H .L (by decide)
  rw [U_eq M m _ _ hyL'] at iL
  rw [U_eq M m _ _ hxH', U_eq M m _ _ hyL'] at ic
  simp only [Menu.T, Menu.α, Model.c] at iL ic
  rw [outside_eq M hcL] at iL
  have hθ := M.θ_pos
  have hθ1 : 0 ≤ 1 - M.θ := by linarith [M.θ_lt_one]
  have h1 := mul_le_mul_of_nonneg_left ic hθ.le
  rw [profit_eq]
  simp only [G, Hf]
  nlinarith

lemma bL_sub_bH (M : Model) :
    bL M - B M M.cH = (M.cH - M.cL) * (2 * M.φ - 1) / (1 - M.θ) := by
  have hθ : 1 - M.θ ≠ 0 := by linarith [M.θ_lt_one]
  unfold bL B
  field_simp
  ring

lemma mon_of_maxSlope (M : Model) {x y : ℝ} (hx : MaxSlope M (B M M.cH) x)
    (hy : MaxSlope M (bL M) y) : 0 ≤ (2 * M.φ - 1) * (y - x) := by
  have h := maxSlope_mono M hx hy
  rw [bL_sub_bH] at h
  have hΔ : 0 < M.cH - M.cL := by linarith [M.cL_lt_cH]
  have hθ : 0 < 1 - M.θ := by linarith [M.θ_lt_one]
  have : (M.cH - M.cL) * (2 * M.φ - 1) / (1 - M.θ) * (y - x)
      = ((M.cH - M.cL) / (1 - M.θ)) * ((2 * M.φ - 1) * (y - x)) := by ring
  rw [this] at h
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg (div_pos hΔ hθ) hc
  linarith

lemma G_iff (M : Model) {x : ℝ} (hx : x ∈ Set.Icc M.aLo M.aHi) :
    MaxSlope M (B M M.cH) x ↔ ∀ z ∈ Set.Icc M.aLo M.aHi, G M z ≤ G M x :=
  maxSlope_iff M M.θ_pos hx (fun z _ => G_diff M x z)

lemma H_iff (M : Model) {x : ℝ} (hx : x ∈ Set.Icc M.aLo M.aHi) :
    MaxSlope M (bL M) x ↔ ∀ z ∈ Set.Icc M.aLo M.aHi, Hf M z ≤ Hf M x :=
  maxSlope_iff M (by linarith [M.θ_lt_one]) hx (fun z _ => H_diff M x z)

lemma optimal_mk (M : Model) (hcH : M.cH < M.uHat) {x y : ℝ} (hx : MaxSlope M (B M M.cH) x)
    (hy : MaxSlope M (bL M) y) : M.IsOptimalMenu (mk M x y) := by
  refine ⟨feasible_mk M hcH hx.1 hy.1 (mon_of_maxSlope M hx hy), fun m' hm' => ?_⟩
  rw [profit_mk]
  have h1 := profit_le M hcH hm'
  have h2 := (G_iff M hx.1).1 hx m'.αH (hm'.1 .H).2
  have h3 := (H_iff M hy.1).1 hy m'.αL (hm'.1 .L).2
  linarith

lemma maxSlope_of_optimal (M : Model) (hcH : M.cH < M.uHat)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    {m : Menu} (hm : M.IsOptimalMenu m) :
    MaxSlope M (B M M.cH) m.αH ∧ MaxSlope M (bL M) m.αL := by
  obtain ⟨x, hx⟩ := exists_maxSlope M hk_cont (B M M.cH)
  obtain ⟨y, hy⟩ := exists_maxSlope M hk_cont (bL M)
  have hfe := feasible_mk M hcH hx.1 hy.1 (mon_of_maxSlope M hx hy)
  have h1 := hm.2 _ hfe
  rw [profit_mk] at h1
  have h2 := profit_le M hcH hm.1
  have hxH : m.αH ∈ Set.Icc M.aLo M.aHi := (hm.1.1 .H).2
  have hyL : m.αL ∈ Set.Icc M.aLo M.aHi := (hm.1.1 .L).2
  have h3 := (G_iff M hx.1).1 hx m.αH hxH
  have h4 := (H_iff M hy.1).1 hy m.αL hyL
  refine ⟨(G_iff M hxH).2 fun z hz => ?_, (H_iff M hyL).2 fun z hz => ?_⟩
  · have := (G_iff M hx.1).1 hx z hz; linarith
  · have := (H_iff M hy.1).1 hy z hz; linarith

lemma bench_eq (M : Model) (i : SellingData.ListsBinary.CostType) {z : ℝ}
    (hz : z ∈ Set.Icc M.aLo M.aHi) :
    M.benchProfit i z = M.θi i * (Q M (M.c i) z - M.k z) := by
  rw [← payoff_eq M _ hz]
  rfl

lemma eff_iff (M : Model) (i : SellingData.ListsBinary.CostType) (a : ℝ) :
    M.IsEfficient i a ↔ MaxSlope M (B M (M.c i)) a := by
  have hw : 0 < M.θi i := by
    cases i
    · exact M.θ_pos
    · show 0 < 1 - M.θ
      linarith [M.θ_lt_one]
  constructor
  · rintro ⟨ha, h⟩
    refine (maxSlope_iff M (F := M.benchProfit i) hw ha (fun z hz => ?_)).2 h
    rw [bench_eq M i hz, bench_eq M i ha, Q_eq, Q_eq]
    ring
  · intro h
    refine ⟨h.1, (maxSlope_iff M (F := M.benchProfit i) hw h.1 (fun z hz => ?_)).1 h⟩
    rw [bench_eq M i hz, bench_eq M i h.1, Q_eq, Q_eq]
    ring

lemma bL_sub_bLo (M : Model) :
    bL M - B M M.cL = M.θ / (1 - M.θ) * (M.cH - M.cL) * (2 * M.φ - 1) := by
  unfold bL; ring

end SellingData.AppendsBinary.P3Aux

namespace SellingData.AppendsBinary.P3Aux

open SellingData.AppendsBinary Model Filter Topology

theorem main (M : Model) (hcH : M.cH < M.uHat)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a)
    (hk_lo : HasDerivWithinAt M.k 0 (Set.Ici M.aLo) M.aLo)
    (hk_hi : Tendsto (deriv M.k) (𝓝[<] M.aHi) atTop) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αH = a) ↔ M.IsEfficient SellingData.ListsBinary.CostType.H a) ∧
      (M.φ < 1 / 2 → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → m.αL < a) ∧
      (1 / 2 < M.φ → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → a < m.αL) := by
  have hBL := B_pos M M.cL M.standing_cL
  have hc : 0 < M.θ / (1 - M.θ) * (M.cH - M.cL) :=
    mul_pos (div_pos M.θ_pos (by linarith [M.θ_lt_one])) (by linarith [M.cL_lt_cH])
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨m, hm, rfl⟩
    exact (eff_iff M .H _).2 (maxSlope_of_optimal M hcH hk_cont hm).1
  · intro ha
    obtain ⟨y, hy⟩ := exists_maxSlope M hk_cont (bL M)
    exact ⟨mk M a y, optimal_mk M hcH ((eff_iff M .H a).1 ha) hy, rfl⟩
  · intro hφ m hm a ha
    have h1 := (maxSlope_of_optimal M hcH hk_cont hm).2
    have h2 : MaxSlope M (B M M.cL) a := (eff_iff M .L a).1 ha
    have hd : bL M - B M M.cL < 0 := by
      rw [bL_sub_bLo]; nlinarith
    have hmono := maxSlope_mono M h2 h1
    rcases lt_or_eq_of_le (show m.αL ≤ a from by
      by_contra hlt; push Not at hlt; nlinarith) with hlt | heq
    · exact hlt
    · rw [heq] at h1
      have := maxSlope_unique M hk_cont hk_diff hk_lo hk_hi hBL h2 h1
      linarith
  · intro hφ m hm a ha
    have h1 := (maxSlope_of_optimal M hcH hk_cont hm).2
    have h2 : MaxSlope M (B M M.cL) a := (eff_iff M .L a).1 ha
    have hd : 0 < bL M - B M M.cL := by
      rw [bL_sub_bLo]; nlinarith
    have hmono := maxSlope_mono M h2 h1
    rcases lt_or_eq_of_le (show a ≤ m.αL from by
      by_contra hlt; push Not at hlt; nlinarith) with hlt | heq
    · exact hlt
    · rw [← heq] at h1
      have := maxSlope_unique M hk_cont hk_diff hk_lo hk_hi hBL h2 h1
      linarith

end SellingData.AppendsBinary.P3Aux

open SellingData.AppendsBinary SellingData.AppendsBinary.Model Filter Topology in
theorem solution (M : Model) (hcH : M.cH < M.uHat)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a)
    (hk_lo : HasDerivWithinAt M.k 0 (Set.Ici M.aLo) M.aLo)
    (hk_hi : Tendsto (deriv M.k) (𝓝[<] M.aHi) atTop) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αH = a) ↔ M.IsEfficient SellingData.ListsBinary.CostType.H a) ∧
      (M.φ < 1 / 2 → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → m.αL < a) ∧
      (1 / 2 < M.φ → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → a < m.αL) := by
  exact SellingData.AppendsBinary.P3Aux.main M hcH hk_cont hk_diff hk_lo hk_hi
