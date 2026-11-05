-- Prove2me | solution 1 for TikhonovHDD.Ergodic.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:17:16.85428+00:00
-- url     : https://prove2.me/submissions/d24738f6-b8cc-40d7-8844-b7e7cc77a7fe

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting
import Theorems.Thm_TikhonovHDD_Ergodic_lemma_4_1

open Set Filter Topology MeasureTheory

namespace TikhEq46Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Gradient inequality of a differentiable convex function. -/
lemma grad_ineq [CompleteSpace H] (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (hdiff : Differentiable ℝ g)
    (a b : H) : g a + inner ℝ (gradient g a) (b - a) ≤ g b := by
  set φ : ℝ → ℝ := fun τ => g (a + τ • (b - a)) with hφ
  have hφc : ConvexOn ℝ univ φ := by
    refine ⟨convex_univ, fun r _ s _ p q hp hq hpq => ?_⟩
    have h := hconv.2 (mem_univ (a + r • (b - a))) (mem_univ (a + s • (b - a))) hp hq hpq
    have heq : p • (a + r • (b - a)) + q • (a + s • (b - a)) = a + (p • r + q • s) • (b - a) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hpq, one_smul,
        ← add_smul]
      simp [smul_eq_mul]
    simp only [hφ]
    rw [← heq]
    exact h
  have hline : HasDerivAt (fun τ : ℝ => a + τ • (b - a)) (b - a) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a
    simpa using this
  have hd : HasDerivAt φ (inner ℝ (gradient g a) (b - a)) 0 := by
    have h1 := (hdiff (a + (0:ℝ) • (b - a))).hasGradientAt.hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
    simp only [zero_smul, add_zero] at h1
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
  have := hφc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simp [slope, hφ] at this
  have e1 : inner ℝ (gradient g a) (b - a) = fderiv ℝ g a b - fderiv ℝ g a a := by
    rw [inner_gradient_left, map_sub]
  linarith

end TikhEq46Aux

open TikhonovHDD.Ergodic TikhEq46Aux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (xε : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd)
    (hdiv : Tendsto (fun T => ∫ t in t₀..T, ε t / t) atTop atTop)
    (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar)
    (hxε : ∀ e > 0, IsTikhonovPoint g e (xε e)) :
    ∃ C > 0, ∀ t ≥ t₀,
      ∫ s in t₀..t, ε s / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε (ε s)‖ ^ 2))
        ≤ C := by
  obtain ⟨-, hL2, hL3⟩ := lemma_4_1 g α β t₀ ε ε' u₀ v₀ x xd xdd ht₀ hα hβ hg hε hx
  obtain ⟨C3, hC3⟩ := hL3 xstar hxstar.1
  obtain ⟨hconv, hdiff, hdiff2, -, -⟩ := id hg
  obtain ⟨hεd, -, hεnn, hεanti, -⟩ := id hε
  obtain ⟨hxode, hxddc, -, -⟩ := id hx
  have gcont : Continuous g := hdiff.continuous
  have Gcont : Continuous (gradient g) := hdiff2.continuous
  have xcont : ContinuousOn x (Ici t₀) := fun t ht => (hxode t ht).1.continuousWithinAt
  have xdcont : ContinuousOn xd (Ici t₀) := fun t ht => (hxode t ht).2.1.continuousWithinAt
  have εcont : ContinuousOn ε (Ici t₀) := fun t ht => (hεd t ht).continuousWithinAt
  have spos : ∀ s, t₀ ≤ s → 0 < s := fun s hs => lt_of_lt_of_le ht₀ hs
  have hsub : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b → uIcc a b ⊆ Ici t₀ :=
    fun a b ha hb s hs => le_trans (le_min ha hb) hs.1
  -- positivity of ε
  have wcont : ContinuousOn (fun s => ε s / s) (Ici t₀) :=
    εcont.div continuousOn_id (fun s hs => ne_of_gt (spos s hs))
  have wII : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b → IntervalIntegrable (fun s => ε s / s) volume a b :=
    fun a b ha hb => (wcont.mono (hsub a b ha hb)).intervalIntegrable
  have hpos : ∀ s, t₀ ≤ s → 0 < ε s := by
    intro s1 hs1
    by_contra hc
    have hz : ε s1 = 0 := le_antisymm (not_lt.mp hc) (hεnn s1 hs1)
    have hzero : ∀ T, s1 ≤ T → ∫ t in t₀..T, ε t / t = ∫ t in t₀..s1, ε t / t := by
      intro T hT
      rw [← intervalIntegral.integral_add_adjacent_intervals (wII t₀ s1 le_rfl hs1)
        (wII s1 T hs1 (hs1.trans hT))]
      have : ∫ t in s1..T, ε t / t = 0 := by
        have hc0 : ∫ t in s1..T, ε t / t = ∫ t in s1..T, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hT] at ht
          have h1 : ε t ≤ ε s1 := hεanti (show s1 ∈ Ici t₀ from hs1)
            (show t ∈ Ici t₀ from hs1.trans ht.1) ht.1
          have h2 := hεnn t (hs1.trans ht.1)
          have : ε t = 0 := by linarith
          simp [this]
        rw [hc0]; simp
      rw [this, add_zero]
    obtain ⟨T, hT1, hT2⟩ := ((hdiv.eventually_gt_atTop (∫ t in t₀..s1, ε t / t)).and
      (eventually_ge_atTop s1)).exists
    rw [hzero T hT2] at hT1
    exact lt_irrefl _ hT1
  -- monotonicity of the Tikhonov norms
  have hanti : ∀ a b : ℝ, 0 < b → b ≤ a → ‖xε a‖ ^ 2 ≤ ‖xε b‖ ^ 2 := by
    intro a b hb hba
    rcases eq_or_lt_of_le hba with hab | hab
    · rw [hab]
    · have ha : 0 < a := hb.trans hab
      have h1 := hxε a ha (xε b)
      have h2 := hxε b hb (xε a)
      by_contra hc
      push Not at hc
      have : 0 < (a - b) * (‖xε a‖ ^ 2 - ‖xε b‖ ^ 2) := mul_pos (by linarith) (by linarith)
      nlinarith
  set φ : ℝ → ℝ := fun s => ‖xstar‖ ^ 2 - ‖xε (ε s)‖ ^ 2 with hφ
  have φanti : AntitoneOn φ (Ici t₀) := by
    intro s1 hs1 s2 hs2 h12
    have := hanti (ε s1) (ε s2) (hpos s2 hs2) (hεanti hs1 hs2 h12)
    simp only [hφ]; linarith
  -- the functions
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, q = fun r => g (x r) - inner ℝ (gradient g (x r)) (x r - xstar) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun r =>
    inner ℝ (xdd r + (α / r) • xd r + gradient g (x r) + ε r • x r) (x r - xstar) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = fun r =>
    hDot x xd xstar r / r + (α + 1) * hFun x xstar r / r ^ 2 - β * (q r - g xstar) / r :=
    ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : ℝ → ℝ, E' = fun r =>
    (‖xd r‖ ^ 2 + inner ℝ (xdd r) (x r - xstar)) / r - hDot x xd xstar r / r ^ 2
      + (α + 1) * (hDot x xd xstar r / r ^ 2 - 2 * hFun x xstar r / r ^ 3)
      - P r / r + β * (q r - g xstar) / r ^ 2 := ⟨_, rfl⟩
  -- derivative of E
  have hEd : ∀ s ∈ Ici t₀, HasDerivWithinAt E (E' s) (Ici t₀) s := by
    intro s hs
    have s0 : s ≠ 0 := ne_of_gt (spos s hs)
    obtain ⟨hx1, hx2, hode⟩ := hxode s hs
    have hu : HasDerivWithinAt (fun r => x r - xstar) (xd s) (Ici t₀) s := hx1.sub_const xstar
    have hD : HasDerivWithinAt (fun r => hDot x xd xstar r)
        (inner ℝ (xd s) (xd s) + inner ℝ (xdd s) (x s - xstar)) (Ici t₀) s := hx2.inner ℝ hu
    have hh : HasDerivWithinAt (fun r => hFun x xstar r) (hDot x xd xstar s) (Ici t₀) s := by
      have := (hu.norm_sq).const_mul (1/2 : ℝ)
      refine this.congr_deriv ?_
      show _ = inner ℝ (xd s) (x s - xstar)
      rw [real_inner_comm]; ring
    have hGd : HasDerivWithinAt (fun r => gradient g (x r)) (fderiv ℝ (gradient g) (x s) (xd s)) (Ici t₀) s :=
      (hdiff2 (x s)).hasFDerivAt.comp_hasDerivWithinAt s hx1
    have hgd : HasDerivWithinAt (fun r => g (x r)) (inner ℝ (gradient g (x s)) (xd s)) (Ici t₀) s := by
      have := (hdiff (x s)).hasFDerivAt.comp_hasDerivWithinAt s hx1
      rw [inner_gradient_left]
      exact this
    have hqd : HasDerivWithinAt (fun r => g (x r) - inner ℝ (gradient g (x r)) (x r - xstar))
        (inner ℝ (gradient g (x s)) (xd s) - (inner ℝ (gradient g (x s)) (xd s) +
          inner ℝ (fderiv ℝ (gradient g) (x s) (xd s)) (x s - xstar))) (Ici t₀) s :=
      hgd.sub (hGd.inner ℝ hu)
    have hPeq : β * (-inner ℝ (fderiv ℝ (gradient g) (x s) (xd s)) (x s - xstar)) = P s := by
      have hv : β • fderiv ℝ (gradient g) (x s) (xd s) =
          -(xdd s + (α / s) • xd s + gradient g (x s) + ε s • x s) := by
        rw [eq_neg_iff_add_eq_zero]
        rw [← hode]; abel
      have hv' : xdd s + (α / s) • xd s + gradient g (x s) + ε s • x s =
          -(β • fderiv ℝ (gradient g) (x s) (xd s)) := by rw [hv, neg_neg]
      rw [hP]
      show _ = inner ℝ (xdd s + (α / s) • xd s + gradient g (x s) + ε s • x s) (x s - xstar)
      rw [hv', inner_neg_left, inner_smul_left]
      simp
    have hid : HasDerivWithinAt (fun r : ℝ => r) 1 (Ici t₀) s := hasDerivWithinAt_id s _
    have hid2 : HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * s) (Ici t₀) s := by
      have := (hasDerivAt_pow 2 s).hasDerivWithinAt (s := Ici t₀)
      simpa using this
    have hall := ((hD.div hid s0).add ((hh.const_mul (α + 1)).div hid2 (pow_ne_zero 2 s0))).sub
      (((hqd.sub_const (g xstar)).const_mul β).div hid s0)
    rw [hE, hE', hq]
    refine hall.congr_deriv ?_
    beta_reduce
    rw [real_inner_self_eq_norm_sq, ← hPeq]
    field_simp
    ring
  -- continuity of E'
  have Pcont : ContinuousOn P (Ici t₀) := by
    simp only [hP]
    refine ContinuousOn.inner ?_ (xcont.sub continuousOn_const)
    refine (((hxddc.add ?_).add (Gcont.comp_continuousOn xcont)).add ((εcont.smul xcont)))
    exact (continuousOn_const.div continuousOn_id fun s hs => ne_of_gt (spos s hs)).smul xdcont
  have qcont : ContinuousOn q (Ici t₀) := by
    simp only [hq]
    exact (gcont.comp_continuousOn xcont).sub
      ((Gcont.comp_continuousOn xcont).inner (xcont.sub continuousOn_const))
  have hDcont : ContinuousOn (fun r => hDot x xd xstar r) (Ici t₀) := by
    simp only [hDot]; exact xdcont.inner (xcont.sub continuousOn_const)
  have hhcont : ContinuousOn (fun r => hFun x xstar r) (Ici t₀) := by
    simp only [hFun]
    exact continuousOn_const.mul ((continuous_norm.comp_continuousOn
      (xcont.sub continuousOn_const)).pow 2)
  have hne : ∀ (n : ℕ), ∀ s ∈ Ici t₀, s ^ n ≠ 0 := fun n s hs => pow_ne_zero n (ne_of_gt (spos s hs))
  have E'cont : ContinuousOn E' (Ici t₀) := by
    rw [hE']
    have c1 : ContinuousOn (fun r => (‖xd r‖ ^ 2 + inner ℝ (xdd r) (x r - xstar)) / r) (Ici t₀) :=
      (((continuous_norm.comp_continuousOn xdcont).pow 2).add
        (hxddc.inner (xcont.sub continuousOn_const))).div continuousOn_id
        (fun s hs => ne_of_gt (spos s hs))
    have c2 : ContinuousOn (fun r => hDot x xd xstar r / r ^ 2) (Ici t₀) :=
      hDcont.div (continuousOn_id.pow 2) (hne 2)
    have c3 : ContinuousOn (fun r => 2 * hFun x xstar r / r ^ 3) (Ici t₀) :=
      (continuousOn_const.mul hhcont).div (continuousOn_id.pow 3) (hne 3)
    have c4 : ContinuousOn (fun r => P r / r) (Ici t₀) :=
      Pcont.div continuousOn_id (fun s hs => ne_of_gt (spos s hs))
    have c5 : ContinuousOn (fun r => β * (q r - g xstar) / r ^ 2) (Ici t₀) :=
      (continuousOn_const.mul (qcont.sub continuousOn_const)).div (continuousOn_id.pow 2) (hne 2)
    exact (((c1.sub c2).add (continuousOn_const.mul (c2.sub c3))).sub c4).add c5
  have Econt : ContinuousOn E (Ici t₀) := fun s hs => (hEd s hs).continuousWithinAt
  -- integrability of the kinetic term
  set I1 := ∫ s in Ici t₀, ‖xd s‖ ^ 2 / s
  have kcont : ContinuousOn (fun s => ‖xd s‖ ^ 2 / s) (Ici t₀) :=
    ((continuous_norm.comp_continuousOn xdcont).pow 2).div continuousOn_id
      (fun s hs => ne_of_gt (spos s hs))
  have hk : ∀ t, t₀ ≤ t → ∫ s in t₀..t, ‖xd s‖ ^ 2 / s ≤ I1 := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht]
    apply setIntegral_mono_set hL2
    · exact (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun s hs =>
        div_nonneg (sq_nonneg _) (spos s hs).le)
    · exact (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self : Ioc t₀ t ⊆ Ici t₀).eventuallyLE
  -- pointwise inequality
  have hpt : ∀ s, t₀ ≤ s →
      ε s / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε (ε s)‖ ^ 2))
        ≤ ‖xd s‖ ^ 2 / s - E' s := by
    intro s hs
    have sp := spos s hs
    have ep := hpos s hs
    set u := x s - xstar with hu
    set e := ε s
    have F1 := grad_ineq g hconv hdiff (x s) xstar
    have F2 := hxε e ep (x s)
    have F3 := hxstar.1 (xε e)
    have hxs : xstar = x s - u := by simp [hu]
    have hnx : ‖xstar‖ ^ 2 = ‖x s‖ ^ 2 - 2 * inner ℝ (x s) u + ‖u‖ ^ 2 := by
      rw [hxs, norm_sub_sq_real]
    have F1' : xstar - x s = -u := by simp [hu]
    rw [F1', inner_neg_right] at F1
    have hPs : P s = inner ℝ (xdd s) u + (α / s) * hDot x xd xstar s + inner ℝ (gradient g (x s)) u
        + e * inner ℝ (x s) u := by
      rw [hP]
      simp only [hDot, inner_add_left, inner_smul_left]
      simp [hu, e]
    have hqs : q s = g (x s) - inner ℝ (gradient g (x s)) u := by rw [hq]
    have hfs : hFun x xstar s = 1 / 2 * ‖u‖ ^ 2 := rfl
    have hq_le : q s - g xstar ≤ 0 := by rw [hqs]; linarith
    -- key: e * (h - φ/2) ≤ ⟪G,u⟫ + e⟪x,u⟫
    have hstar : e * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε e‖ ^ 2)) ≤
        inner ℝ (gradient g (x s)) u + e * inner ℝ (x s) u := by
      rw [hfs, hnx]
      nlinarith
    have hE's : ‖xd s‖ ^ 2 / s - E' s = -inner ℝ (xdd s) u / s
        - α * hDot x xd xstar s / s ^ 2 + 2 * (α + 1) * hFun x xstar s / s ^ 3 + P s / s
        - β * (q s - g xstar) / s ^ 2 := by
      rw [hE']
      field_simp
      ring
    rw [hE's]
    have t1 : 0 ≤ 2 * (α + 1) * hFun x xstar s / s ^ 3 := by
      rw [hfs]; positivity
    have t2 : 0 ≤ -(β * (q s - g xstar) / s ^ 2) := by
      rw [neg_div', le_div_iff₀ (by positivity)]
      nlinarith
    have key : e / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε e‖ ^ 2)) ≤
        -inner ℝ (xdd s) u / s - α * hDot x xd xstar s / s ^ 2 + P s / s := by
      rw [hPs]
      have : -inner ℝ (xdd s) u / s - α * hDot x xd xstar s / s ^ 2 +
          (inner ℝ (xdd s) u + α / s * hDot x xd xstar s + inner ℝ (gradient g (x s)) u
            + e * inner ℝ (x s) u) / s
          = (inner ℝ (gradient g (x s)) u + e * inner ℝ (x s) u) / s := by
        field_simp; ring
      rw [this, div_mul_eq_mul_div, div_le_div_iff_of_pos_right sp]
      exact hstar
    linarith
  -- integrability of the left integrand
  have lII : ∀ t, t₀ ≤ t → IntervalIntegrable
      (fun s => ε s / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε (ε s)‖ ^ 2))) volume t₀ t := by
    intro t ht
    have hsb := hsub t₀ t le_rfl ht
    have i1 : IntervalIntegrable (fun s => ε s / s * hFun x xstar s) volume t₀ t :=
      ((wcont.mul hhcont).mono hsb).intervalIntegrable
    have i2 : IntervalIntegrable (fun s => ε s / s * φ s) volume t₀ t :=
      (AntitoneOn.intervalIntegrable (φanti.mono hsb)).continuousOn_mul (wcont.mono hsb)
    have := i1.sub (i2.const_mul (1/2 : ℝ))
    refine this.congr ?_
    intro s _
    simp only [hφ]; ring
  obtain hC3' : ∀ t, t₀ ≤ t → |hDot x xd xstar t| / t ≤ C3 :=
    fun t ht => hC3 (mem_image_of_mem _ (show t ∈ Ici t₀ from ht))
  refine ⟨max 1 (I1 + C3 + E t₀), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro t ht
  have hsb := hsub t₀ t le_rfl ht
  have kII : IntervalIntegrable (fun s => ‖xd s‖ ^ 2 / s) volume t₀ t :=
    (kcont.mono hsb).intervalIntegrable
  have E'II : IntervalIntegrable E' volume t₀ t := (E'cont.mono hsb).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on ht (lII t ht) (kII.sub E'II)
    (fun s hs => hpt s hs.1)
  rw [intervalIntegral.integral_sub kII E'II] at hmono
  have hftc : ∫ s in t₀..t, E' s = E t - E t₀ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (Econt.mono Icc_subset_Ici_self)
    · intro s hs
      exact (hEd s (le_of_lt hs.1)).hasDerivAt (Ici_mem_nhds hs.1)
    · exact E'II
  rw [hftc] at hmono
  have hk' := hk t ht
  -- bound on -E t
  have tp := spos t ht
  have hEt : -E t ≤ C3 := by
    have hq_le : q t - g xstar ≤ 0 := by
      have F1 := grad_ineq g hconv hdiff (x t) xstar
      have F1' : xstar - x t = -(x t - xstar) := by abel
      rw [F1', inner_neg_right] at F1
      rw [hq]; show g (x t) - _ - g xstar ≤ 0; linarith
    have h1 : -(hDot x xd xstar t / t) ≤ |hDot x xd xstar t| / t := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (neg_le_abs _) tp.le
    have h2 : 0 ≤ (α + 1) * hFun x xstar t / t ^ 2 := by
      simp only [hFun]; positivity
    have h3 : β * (q t - g xstar) / t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ hq_le) tp.le
    have := hC3' t ht
    rw [hE]
    show -(hDot x xd xstar t / t + (α + 1) * hFun x xstar t / t ^ 2 - β * (q t - g xstar) / t) ≤ C3
    linarith
  have := le_max_right 1 (I1 + C3 + E t₀)
  linarith
