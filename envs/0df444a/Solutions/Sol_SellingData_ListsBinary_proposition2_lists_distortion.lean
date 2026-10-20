-- Prove2me | solution 1 for SellingData.ListsBinary.proposition2_lists_distortion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:43:38.306601+00:00
-- url     : https://prove2.me/submissions/e55688a1-a1f2-4df5-8089-63ee38ecdc4d

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

set_option autoImplicit false

namespace SellingData.ListsBinary.P2Aux

open SellingData.ListsBinary

/-- affine form of the gross payoff `σ_h(α)[v_h(α) - c]` -/
def Q (S : Screening) (c x : ℝ) : ℝ :=
  S.phi * x * (S.uHi - c) + (1 - S.phi) * (1 - x) * (S.uLo - c)

/-- slope of the affine payoff in `α` -/
def B (S : Screening) (c : ℝ) : ℝ :=
  S.phi * (S.uHi - c) - (1 - S.phi) * (S.uLo - c)

lemma Q_eq (S : Screening) (c x : ℝ) : Q S c x = (1 - S.phi) * (S.uLo - c) + B S c * x := by
  unfold Q B; ring

lemma sigmaH_pos (S : Screening) {x : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi) :
    0 < sigmaH S.phi x := by
  have h1 := S.phi_pos; have h2 := S.phi_lt_one; have h3 := S.half_lt_aLo
  have h4 := S.aHi_lt_one
  obtain ⟨hx1, hx2⟩ := hx
  unfold sigmaH
  have : 0 < S.phi * x := mul_pos h1 (by linarith)
  have : 0 < (1 - S.phi) * (1 - x) := mul_pos (by linarith) (by linarith)
  linarith

lemma payoff_eq (S : Screening) (c : ℝ) {x : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi) :
    S.payoff x c = Q S c x := by
  have hs := sigmaH_pos S hx
  unfold Model.payoff Q vH phiH
  unfold sigmaH at hs ⊢
  field_simp
  ring

lemma B_pos (S : Screening) (c : ℝ)
    (hc : vL S.uLo S.uHi S.phi S.aLo < c ∧ c < vH S.uLo S.uHi S.phi S.aLo) : 0 < B S c := by
  have h1 := S.phi_pos; have h2 := S.phi_lt_one; have h3 := S.half_lt_aLo
  have h4 := S.aHi_lt_one; have h5 := S.aLo_lt_aHi
  obtain ⟨hl, hh⟩ := hc
  set a := S.aLo
  have hsH : 0 < S.phi * a + (1 - S.phi) * (1 - a) := by
    have : 0 < S.phi * a := mul_pos h1 (by linarith)
    have : 0 < (1 - S.phi) * (1 - a) := mul_pos (by linarith) (by linarith)
    linarith
  have hsL : 0 < S.phi * (1 - a) + (1 - S.phi) * a := by
    have : 0 < S.phi * (1 - a) := mul_pos h1 (by linarith)
    have : 0 < (1 - S.phi) * a := mul_pos (by linarith) (by linarith)
    linarith
  -- σ_h (v_h - c) > 0 and σ_l (v_l - c) < 0
  have eH : (S.phi * a + (1 - S.phi) * (1 - a)) * (vH S.uLo S.uHi S.phi a - c)
      = a * (S.phi * (S.uHi - c)) - (1 - a) * ((1 - S.phi) * (c - S.uLo)) := by
    unfold vH phiH; field_simp; ring
  have eL : (S.phi * (1 - a) + (1 - S.phi) * a) * (vL S.uLo S.uHi S.phi a - c)
      = (1 - a) * (S.phi * (S.uHi - c)) - a * ((1 - S.phi) * (c - S.uLo)) := by
    have hp : phiL S.phi a * (S.phi * (1 - a) + (1 - S.phi) * a) = S.phi * (1 - a) :=
      div_mul_cancel₀ _ hsL.ne'
    unfold vL
    linear_combination (S.uHi - S.uLo) * hp
  have pH : 0 < (S.phi * a + (1 - S.phi) * (1 - a)) * (vH S.uLo S.uHi S.phi a - c) :=
    mul_pos hsH (by linarith)
  have pL : (S.phi * (1 - a) + (1 - S.phi) * a) * (vL S.uLo S.uHi S.phi a - c) < 0 :=
    mul_neg_of_pos_of_neg hsL (by linarith)
  rw [eH] at pH; rw [eL] at pL
  have key : 0 < (2 * a - 1) * (S.phi * (S.uHi - c) + (1 - S.phi) * (c - S.uLo)) := by
    nlinarith
  have h2a : 0 < 2 * a - 1 := by linarith
  have := (pos_iff_pos_of_mul_pos key).1 h2a
  unfold B; linarith

/-- `x` maximizes `b * y - k y` on `[α̲, ᾱ]`. -/
def MaxSlope (S : Screening) (b x : ℝ) : Prop :=
  x ∈ Set.Icc S.aLo S.aHi ∧ ∀ y ∈ Set.Icc S.aLo S.aHi, b * y - S.k y ≤ b * x - S.k x

lemma exists_maxSlope (S : Screening) (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    (b : ℝ) : ∃ x, MaxSlope S b x := by
  have hne : (Set.Icc S.aLo S.aHi).Nonempty := Set.nonempty_Icc.2 S.aLo_lt_aHi.le
  have hc : ContinuousOn (fun y => b * y - S.k y) (Set.Icc S.aLo S.aHi) :=
    (continuousOn_const.mul continuousOn_id).sub hk_cont
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  exact ⟨x, hx, fun y hy => hmax hy⟩

lemma maxSlope_mono (S : Screening) {b1 b2 x1 x2 : ℝ} (h1 : MaxSlope S b1 x1)
    (h2 : MaxSlope S b2 x2) : 0 ≤ (b2 - b1) * (x2 - x1) := by
  have a := h1.2 x2 h2.1
  have b := h2.2 x1 h1.1
  nlinarith

lemma not_maxSlope_lo (S : Screening)
    (hk_left : HasDerivWithinAt S.k 0 (Set.Ici S.aLo) S.aLo) {b : ℝ} (hb : 0 < b)
    (h : MaxSlope S b S.aLo) : False := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.1 hk_left)
  have hset : Set.Ici S.aLo \ {S.aLo} = Set.Ioi S.aLo := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h1; exact ⟨h1.le, ne_of_gt h1⟩
  rw [hset] at ht
  have e1 : ∀ᶠ z in nhdsWithin S.aLo (Set.Ioi S.aLo), slope S.k S.aLo z < b :=
    (tendsto_order.1 ht).2 b hb
  have e2 : ∀ᶠ z in nhdsWithin S.aLo (Set.Ioi S.aLo), z ∈ Set.Ioo S.aLo S.aHi :=
    Ioo_mem_nhdsGT S.aLo_lt_aHi
  obtain ⟨z, hz1, hz2⟩ := (e1.and e2).exists
  have hz0 : 0 < z - S.aLo := by linarith [hz2.1]
  rw [slope_def_field, div_lt_iff₀ hz0] at hz1
  have := h.2 z ⟨hz2.1.le, hz2.2.le⟩
  linarith

lemma not_maxSlope_hi (S : Screening)
    (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo S.aLo S.aHi, DifferentiableAt ℝ S.k a)
    (hk_right : Filter.Tendsto (deriv S.k) (nhdsWithin S.aHi (Set.Iio S.aHi)) Filter.atTop)
    {b : ℝ} (h : MaxSlope S b S.aHi) : False := by
  have e1 : ∀ᶠ z in nhdsWithin S.aHi (Set.Iio S.aHi), b + 1 ≤ deriv S.k z :=
    Filter.tendsto_atTop.1 hk_right (b + 1)
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset.1 e1)
  set x0 := max l S.aLo with hx0
  have hx0lt : x0 < S.aHi := max_lt hl S.aLo_lt_aHi
  have hcont : ContinuousOn S.k (Set.Icc x0 S.aHi) :=
    hk_cont.mono (Set.Icc_subset_Icc (le_max_right _ _) le_rfl)
  have hdiff : DifferentiableOn ℝ S.k (Set.Ioo x0 S.aHi) := fun z hz =>
    (hk_diff z ⟨lt_of_le_of_lt (le_max_right _ _) hz.1, hz.2⟩).differentiableWithinAt
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope S.k hx0lt hcont hdiff
  have hcl : c ∈ Set.Ioo l S.aHi := ⟨lt_of_le_of_lt (le_max_left _ _) hc.1, hc.2⟩
  have hge : b + 1 ≤ deriv S.k c := hsub hcl
  have hpos : 0 < S.aHi - x0 := by linarith
  rw [hdc, le_div_iff₀ hpos] at hge
  have := h.2 x0 ⟨le_max_right _ _, hx0lt.le⟩
  nlinarith

lemma maxSlope_unique (S : Screening)
    (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo S.aLo S.aHi, DifferentiableAt ℝ S.k a)
    (hk_left : HasDerivWithinAt S.k 0 (Set.Ici S.aLo) S.aLo)
    (hk_right : Filter.Tendsto (deriv S.k) (nhdsWithin S.aHi (Set.Iio S.aHi)) Filter.atTop)
    {B0 b a : ℝ} (hB : 0 < B0) (h1 : MaxSlope S B0 a) (h2 : MaxSlope S b a) : b = B0 := by
  have ha := h1.1
  rcases eq_or_lt_of_le ha.1 with hlo | hlo
  · exact (not_maxSlope_lo S hk_left hB (hlo ▸ h1)).elim
  rcases eq_or_lt_of_le ha.2 with hhi | hhi
  · exact (not_maxSlope_hi S hk_cont hk_diff hk_right (hhi ▸ h1)).elim
  have hI : Set.Icc S.aLo S.aHi ∈ nhds a := Icc_mem_nhds hlo hhi
  have hd := (hk_diff a ⟨hlo, hhi⟩).hasDerivAt
  have fermat : ∀ c : ℝ, MaxSlope S c a → c = deriv S.k a := by
    intro c hc
    have hloc : IsLocalMax (fun y => c * y - S.k y) a :=
      Filter.mem_of_superset hI (fun y hy => hc.2 y hy)
    have hder : HasDerivAt (fun y => c * y - S.k y) (c * 1 - deriv S.k a) a :=
      (hasDerivAt_id a |>.const_mul c).sub hd
    have := hloc.hasDerivAt_eq_zero hder
    linarith
  rw [fermat b h2, fermat B0 h1]

end SellingData.ListsBinary.P2Aux

namespace SellingData.ListsBinary.P2Aux

open SellingData.ListsBinary

lemma Q_pos (S : Screening) (c : ℝ)
    (hc : vL S.uLo S.uHi S.phi S.aLo < c ∧ c < vH S.uLo S.uHi S.phi S.aLo)
    {x : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi) : 0 < Q S c x := by
  have hlo : S.aLo ∈ Set.Icc S.aLo S.aHi := ⟨le_rfl, S.aLo_lt_aHi.le⟩
  have h0 : 0 < Q S c S.aLo := by
    rw [← payoff_eq S c hlo]
    unfold Model.payoff
    exact mul_pos (sigmaH_pos S hlo) (by linarith [hc.2])
  have hB := B_pos S c hc
  rw [Q_eq] at h0 ⊢
  nlinarith [hx.1]

/-- `G` : the `α_H` part of the reduced objective (7) -/
def G (S : Screening) (x : ℝ) : ℝ :=
  S.θ * (Q S S.cH x - S.k x) - (1 - S.θ) * (sigmaH S.phi x * (S.cH - S.cL))

/-- `H` : the `α_L` part of the reduced objective (7) -/
def H (S : Screening) (y : ℝ) : ℝ := (1 - S.θ) * (Q S S.cL y - S.k y)

/-- the virtual slope for type `H` -/
noncomputable def bg (S : Screening) : ℝ :=
  B S S.cH - (1 - S.θ) / S.θ * (S.cH - S.cL) * (2 * S.phi - 1)

lemma G_diff (S : Screening) (x z : ℝ) :
    G S z - G S x = S.θ * ((bg S * z - S.k z) - (bg S * x - S.k x)) := by
  have hθ : S.θ ≠ 0 := S.θ_pos.ne'
  unfold G bg
  rw [Q_eq, Q_eq]
  unfold sigmaH
  field_simp
  ring

lemma H_diff (S : Screening) (x z : ℝ) :
    H S z - H S x = (1 - S.θ) * ((B S S.cL * z - S.k z) - (B S S.cL * x - S.k x)) := by
  unfold H
  rw [Q_eq, Q_eq]
  ring

lemma maxSlope_of_G (S : Screening) {x : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi)
    (h : ∀ z ∈ Set.Icc S.aLo S.aHi, G S z ≤ G S x) : MaxSlope S (bg S) x := by
  refine ⟨hx, fun z hz => ?_⟩
  have h1 := h z hz
  have h2 := G_diff S x z
  have hθ := S.θ_pos
  by_contra hne
  push_neg at hne
  have : 0 < S.θ * ((bg S * z - S.k z) - (bg S * x - S.k x)) := mul_pos hθ (by linarith)
  linarith

lemma G_le_of_maxSlope (S : Screening) {x : ℝ} (h : MaxSlope S (bg S) x)
    {z : ℝ} (hz : z ∈ Set.Icc S.aLo S.aHi) : G S z ≤ G S x := by
  have h1 := h.2 z hz
  have h2 := G_diff S x z
  have hθ := S.θ_pos
  have : S.θ * ((bg S * z - S.k z) - (bg S * x - S.k x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ.le (by linarith)
  linarith

lemma maxSlope_of_H (S : Screening) {x : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi)
    (h : ∀ z ∈ Set.Icc S.aLo S.aHi, H S z ≤ H S x) : MaxSlope S (B S S.cL) x := by
  refine ⟨hx, fun z hz => ?_⟩
  have h1 := h z hz
  have h2 := H_diff S x z
  have hθ : 0 < 1 - S.θ := by linarith [S.θ_lt_one]
  by_contra hne
  push_neg at hne
  have : 0 < (1 - S.θ) * ((B S S.cL * z - S.k z) - (B S S.cL * x - S.k x)) :=
    mul_pos hθ (by linarith)
  linarith

lemma H_le_of_maxSlope (S : Screening) {x : ℝ} (h : MaxSlope S (B S S.cL) x)
    {z : ℝ} (hz : z ∈ Set.Icc S.aLo S.aHi) : H S z ≤ H S x := by
  have h1 := h.2 z hz
  have h2 := H_diff S x z
  have hθ : 0 < 1 - S.θ := by linarith [S.θ_lt_one]
  have : (1 - S.θ) * ((B S S.cL * z - S.k z) - (B S S.cL * x - S.k x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ.le (by linarith)
  linarith

lemma U_eq (S : Screening) (m : Menu) (i j : CostType) (h : m.α j ∈ Set.Icc S.aLo S.aHi) :
    S.U m i j = -(m.T j) + Q S (S.cost i) (m.α j) := by
  unfold Screening.U
  rw [payoff_eq S _ h]

/-- the menu built from a pair of informativeness levels, with `IR_H` and `IC_L` binding -/
def mk (S : Screening) (x y : ℝ) : Menu :=
  ⟨Q S S.cH x, x, Q S S.cL y - sigmaH S.phi x * (S.cH - S.cL), y⟩

lemma feasible_mk (S : Screening) {x y : ℝ} (hx : x ∈ Set.Icc S.aLo S.aHi)
    (hy : y ∈ Set.Icc S.aLo S.aHi) (hmon : 0 ≤ (2 * S.phi - 1) * (y - x)) :
    S.Feasible (mk S x y) := by
  have hΔ : 0 < S.cH - S.cL := by linarith [S.cL_lt_cH]
  have hsx := sigmaH_pos S hx
  have hQx := Q_pos S S.cH S.cH_admissible hx
  have hQy := Q_pos S S.cH S.cH_admissible hy
  have eσ : sigmaH S.phi y - sigmaH S.phi x = (2 * S.phi - 1) * (y - x) := by
    unfold sigmaH; ring
  have eQ : ∀ z, Q S S.cL z - sigmaH S.phi z * (S.cH - S.cL) = Q S S.cH z := by
    intro z; unfold Q sigmaH; ring
  have hxH : (mk S x y).α .H ∈ Set.Icc S.aLo S.aHi := hx
  have hyL : (mk S x y).α .L ∈ Set.Icc S.aLo S.aHi := hy
  have uHH := U_eq S (mk S x y) .H .H hxH
  have uLH := U_eq S (mk S x y) .L .H hxH
  have uHL := U_eq S (mk S x y) .H .L hyL
  have uLL := U_eq S (mk S x y) .L .L hyL
  simp only [mk, Menu.T, Menu.α, Screening.cost] at uHH uLH uHL uLL
  have eQy := eQ y
  have eQx := eQ x
  refine ⟨hQx.le, ?_, hx, hy, ?_, ?_⟩
  · show 0 ≤ Q S S.cL y - sigmaH S.phi x * (S.cH - S.cL)
    nlinarith
  · intro i
    simp only [mk]
    cases i
    · rw [uHH]; linarith
    · rw [uLL]; nlinarith
  · intro i i' hii
    simp only [mk]
    cases i <;> cases i'
    · exact (hii rfl).elim
    · rw [uHL, uHH]; nlinarith
    · rw [uLH, uLL]; nlinarith
    · exact (hii rfl).elim

lemma profit_mk (S : Screening) (x y : ℝ) : S.profit (mk S x y) = G S x + H S y := by
  simp only [Screening.profit, Screening.weight, Menu.T, Menu.α, mk, G, H]
  ring

lemma profit_le (S : Screening) {m : Menu} (hm : S.Feasible m) :
    S.profit m ≤ G S m.αH + H S m.αL := by
  obtain ⟨_, _, hxH, hyL, hIR, hIC⟩ := hm
  have hxH' : m.α .H ∈ Set.Icc S.aLo S.aHi := hxH
  have hyL' : m.α .L ∈ Set.Icc S.aLo S.aHi := hyL
  have iH := hIR .H
  have ic := hIC .L .H (by decide)
  rw [U_eq S m _ _ hxH'] at iH
  rw [U_eq S m _ _ hxH', U_eq S m _ _ hyL'] at ic
  simp only [Menu.T, Menu.α, Screening.cost] at iH ic
  have hθ : 0 ≤ 1 - S.θ := by linarith [S.θ_lt_one]
  have e : Q S S.cL m.αH - Q S S.cH m.αH = sigmaH S.phi m.αH * (S.cH - S.cL) := by
    unfold Q sigmaH; ring
  simp only [Screening.profit, Screening.weight, Menu.T, Menu.α, G, H]
  nlinarith [mul_nonneg hθ (sub_nonneg.2 ic)]

lemma bL_sub_bg (S : Screening) :
    B S S.cL - bg S = (S.cH - S.cL) * (2 * S.phi - 1) / S.θ := by
  have hθ : S.θ ≠ 0 := S.θ_pos.ne'
  unfold bg B
  field_simp
  ring

lemma mon_of_maxSlope (S : Screening) {x y : ℝ} (hx : MaxSlope S (bg S) x)
    (hy : MaxSlope S (B S S.cL) y) : 0 ≤ (2 * S.phi - 1) * (y - x) := by
  have h := maxSlope_mono S hx hy
  rw [bL_sub_bg] at h
  have hΔ : 0 < S.cH - S.cL := by linarith [S.cL_lt_cH]
  have hθ := S.θ_pos
  have : (S.cH - S.cL) * (2 * S.phi - 1) / S.θ * (y - x)
      = ((S.cH - S.cL) / S.θ) * ((2 * S.phi - 1) * (y - x)) := by ring
  rw [this] at h
  by_contra hc
  push_neg at hc
  have := mul_neg_of_pos_of_neg (div_pos hΔ hθ) hc
  linarith

lemma optimal_mk (S : Screening) {x y : ℝ} (hx : MaxSlope S (bg S) x)
    (hy : MaxSlope S (B S S.cL) y) : S.IsOptimalMenu (mk S x y) := by
  refine ⟨feasible_mk S hx.1 hy.1 (mon_of_maxSlope S hx hy), fun m' hm' => ?_⟩
  rw [profit_mk]
  have h1 := profit_le S hm'
  have h2 := G_le_of_maxSlope S hx hm'.2.2.1
  have h3 := H_le_of_maxSlope S hy hm'.2.2.2.1
  linarith

lemma maxSlope_of_optimal (S : Screening) (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    {m : Menu} (hm : S.IsOptimalMenu m) :
    MaxSlope S (bg S) m.αH ∧ MaxSlope S (B S S.cL) m.αL := by
  obtain ⟨x, hx⟩ := exists_maxSlope S hk_cont (bg S)
  obtain ⟨y, hy⟩ := exists_maxSlope S hk_cont (B S S.cL)
  have hfe := feasible_mk S hx.1 hy.1 (mon_of_maxSlope S hx hy)
  have h1 := hm.2 _ hfe
  rw [profit_mk] at h1
  have h2 := profit_le S hm.1
  have hxH := hm.1.2.2.1
  have hyL := hm.1.2.2.2.1
  have h3 := G_le_of_maxSlope S hx hxH
  have h4 := H_le_of_maxSlope S hy hyL
  refine ⟨maxSlope_of_G S hxH fun z hz => ?_, maxSlope_of_H S hyL fun z hz => ?_⟩
  · have := G_le_of_maxSlope S hx hz; linarith
  · have := H_le_of_maxSlope S hy hz; linarith

lemma effL_iff (S : Screening) (a : ℝ) :
    S.IsEfficientType .L a ↔ MaxSlope S (B S S.cL) a := by
  have hθ : 0 < 1 - S.θ := by linarith [S.θ_lt_one]
  unfold Screening.IsEfficientType Model.IsEfficient
  simp only [Screening.weight, Screening.cost]
  constructor
  · rintro ⟨ha, h⟩
    refine maxSlope_of_H S ha fun z hz => ?_
    have := h z hz
    unfold Model.benchProfit at this
    have e1 := payoff_eq S S.cL hz
    have e2 := payoff_eq S S.cL ha
    unfold Model.payoff at e1 e2
    unfold H
    rw [← e1, ← e2]
    exact this
  · intro h
    refine ⟨h.1, fun z hz => ?_⟩
    have := H_le_of_maxSlope S h hz
    unfold Model.benchProfit
    have e1 := payoff_eq S S.cL hz
    have e2 := payoff_eq S S.cL h.1
    unfold Model.payoff at e1 e2
    unfold H at this
    rw [e1, e2]
    exact this

lemma maxSlope_of_effH (S : Screening) {a : ℝ} (h : S.IsEfficientType .H a) :
    MaxSlope S (B S S.cH) a := by
  have hθ := S.θ_pos
  unfold Screening.IsEfficientType Model.IsEfficient at h
  simp only [Screening.weight, Screening.cost] at h
  obtain ⟨ha, h⟩ := h
  refine ⟨ha, fun z hz => ?_⟩
  have h1 := h z hz
  unfold Model.benchProfit at h1
  have e1 := payoff_eq S S.cH hz
  have e2 := payoff_eq S S.cH ha
  unfold Model.payoff at e1 e2
  rw [e1, e2, Q_eq, Q_eq] at h1
  by_contra hne
  push_neg at hne
  have : 0 < S.θ * ((B S S.cH * z - S.k z) - (B S S.cH * a - S.k a)) := mul_pos hθ (by linarith)
  nlinarith

lemma bg_sub_bH (S : Screening) :
    bg S - B S S.cH = -((1 - S.θ) / S.θ * (S.cH - S.cL)) * (2 * S.phi - 1) := by
  unfold bg; ring

end SellingData.ListsBinary.P2Aux

open SellingData.ListsBinary.P2Aux in
open SellingData.ListsBinary in
theorem solution (S : Screening)
    (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo S.aLo S.aHi, DifferentiableAt ℝ S.k a)
    (hk_left : HasDerivWithinAt S.k 0 (Set.Ici S.aLo) S.aLo)
    (hk_right : Filter.Tendsto (deriv S.k) (nhdsWithin S.aHi (Set.Iio S.aHi)) Filter.atTop) :
    (∀ a : ℝ, (∃ m : Menu, S.IsOptimalMenu m ∧ m.αL = a) ↔ S.IsEfficientType .L a) ∧
    (S.phi < 1 / 2 →
      ∀ m : Menu, S.IsOptimalMenu m → ∀ a : ℝ, S.IsEfficientType .H a → a < m.αH) ∧
    (1 / 2 < S.phi →
      ∀ m : Menu, S.IsOptimalMenu m → ∀ a : ℝ, S.IsEfficientType .H a → m.αH < a) := by
  have hBH := B_pos S S.cH S.cH_admissible
  have hc : 0 < (1 - S.θ) / S.θ * (S.cH - S.cL) :=
    mul_pos (div_pos (by linarith [S.θ_lt_one]) S.θ_pos) (by linarith [S.cL_lt_cH])
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨m, hm, rfl⟩
    exact (effL_iff S _).2 (maxSlope_of_optimal S hk_cont hm).2
  · intro ha
    obtain ⟨x, hx⟩ := exists_maxSlope S hk_cont (bg S)
    exact ⟨mk S x a, optimal_mk S hx ((effL_iff S a).1 ha), rfl⟩
  · intro hφ m hm a ha
    have h1 := (maxSlope_of_optimal S hk_cont hm).1
    have h2 := maxSlope_of_effH S ha
    have hd : 0 < bg S - B S S.cH := by
      rw [bg_sub_bH]; nlinarith
    have hmono := maxSlope_mono S h2 h1
    rcases lt_or_eq_of_le (show a ≤ m.αH from by
      by_contra hlt; push_neg at hlt; nlinarith) with hlt | heq
    · exact hlt
    · rw [← heq] at h1
      have := maxSlope_unique S hk_cont hk_diff hk_left hk_right hBH h2 h1
      linarith
  · intro hφ m hm a ha
    have h1 := (maxSlope_of_optimal S hk_cont hm).1
    have h2 := maxSlope_of_effH S ha
    have hd : bg S - B S S.cH < 0 := by
      rw [bg_sub_bH]; nlinarith
    have hmono := maxSlope_mono S h2 h1
    rcases lt_or_eq_of_le (show m.αH ≤ a from by
      by_contra hlt; push_neg at hlt; nlinarith) with hlt | heq
    · exact hlt
    · rw [heq] at h1
      have := maxSlope_unique S hk_cont hk_diff hk_left hk_right hBH h2 h1
      linarith
