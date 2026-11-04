-- Prove2me | solution 1 for ThirdPartyPricing.General.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:48:18.669062+00:00
-- url     : https://prove2.me/submissions/369112a5-2061-4dec-ac62-25d67542518b

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives Set Filter Topology
open scoped Interval

namespace T2Aux

/-! ## Generic one-dimensional optimisation lemmas -/

lemma foc_right_nonpos {g : ℝ → ℝ} {l u m d : ℝ} (hm : m ∈ Icc l u) (hmu : m < u)
    (hmax : IsMaxOn g (Icc l u) m) (hd : HasDerivAt g d m) : d ≤ 0 := by
  have ht : Tendsto (slope g m) (𝓝[>] m) (𝓝 d) := by
      have := (hasDerivWithinAt_iff_tendsto_slope (f := g) (s := Ioi m) (x := m) (f' := d)).1
        hd.hasDerivWithinAt
      simpa using this
  apply le_of_tendsto ht
  have hev : ∀ᶠ y in 𝓝[>] m, y ∈ Ioo m u := Ioo_mem_nhdsGT hmu
  filter_upwards [hev] with y hy
  rw [slope_def_field]
  have hy' : y ∈ Icc l u := ⟨le_trans hm.1 hy.1.le, hy.2.le⟩
  have := hmax hy'
  simp only [mem_ofPred_eq] at this
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith [hy.1]

lemma foc_left_nonneg {g : ℝ → ℝ} {l u m d : ℝ} (hm : m ∈ Icc l u) (hlm : l < m)
    (hmax : IsMaxOn g (Icc l u) m) (hd : HasDerivAt g d m) : 0 ≤ d := by
  have ht : Tendsto (slope g m) (𝓝[<] m) (𝓝 d) := by
      have := (hasDerivWithinAt_iff_tendsto_slope (f := g) (s := Iio m) (x := m) (f' := d)).1
        hd.hasDerivWithinAt
      simpa using this
  apply ge_of_tendsto ht
  have hev : ∀ᶠ y in 𝓝[<] m, y ∈ Ioo l m := Ioo_mem_nhdsLT hlm
  filter_upwards [hev] with y hy
  rw [slope_def_field]
  have hy' : y ∈ Icc l u := ⟨hy.1.le, le_trans hy.2.le hm.2⟩
  have := hmax hy'
  simp only [mem_ofPred_eq] at this
  apply div_nonneg_of_nonpos <;> linarith [hy.2]

/-- If `g` has positive slope at `l` and negative slope at `u`, a maximiser on `[l,u]` is
interior and satisfies the first-order condition. -/
lemma foc_interior {g : ℝ → ℝ} {l u m dl du d : ℝ} (hlu : l < u) (hm : m ∈ Icc l u)
    (hmax : IsMaxOn g (Icc l u) m) (hl : HasDerivAt g dl l) (hdl : 0 < dl)
    (hu : HasDerivAt g du u) (hdu : du < 0) (hd : HasDerivAt g d m) :
    m ∈ Ioo l u ∧ d = 0 := by
  have h1 : l < m := by
    rcases eq_or_lt_of_le hm.1 with h | h
    · subst h
      have := foc_right_nonpos hm hlu hmax hl
      linarith
    · exact h
  have h2 : m < u := by
    rcases eq_or_lt_of_le hm.2 with h | h
    · subst h
      have := foc_left_nonneg hm hlu hmax hu
      linarith
    · exact h
  exact ⟨⟨h1, h2⟩, le_antisymm (foc_right_nonpos hm h2 hmax hd) (foc_left_nonneg hm h1 hmax hd)⟩

lemma strictConcave_unique {g : ℝ → ℝ} {s : Set ℝ} (hg : StrictConcaveOn ℝ s g) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hmx : IsMaxOn g s x) (hmy : IsMaxOn g s y) : x = y := by
  by_contra hne
  have := hg.2 hx hy hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hmem : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ s :=
    hg.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmx hmem
  have h2 := hmy hx
  simp only [mem_ofPred_eq, smul_eq_mul] at h1 h2 this
  linarith

/-- Comparison: nonnegative slope at `m` forces the (unique) maximiser to lie weakly above. -/
lemma le_argmax {g : ℝ → ℝ} {l u m m' d : ℝ} (hc : ConcaveOn ℝ (Icc l u) g)
    (hm : m ∈ Icc l u) (hm' : m' ∈ Icc l u) (hmax : IsMaxOn g (Icc l u) m')
    (huniq : ∀ y ∈ Icc l u, IsMaxOn g (Icc l u) y → y = m')
    (hd : HasDerivAt g d m) (h0 : 0 ≤ d) : m ≤ m' := by
  by_contra hlt
  push Not at hlt
  have hs := hc.le_slope_of_hasDerivAt hm' hm hlt hd
  rw [slope_def_field] at hs
  have hpos : 0 < m - m' := by linarith
  have : g m' ≤ g m := by
    have := (le_div_iff₀ hpos).1 hs
    nlinarith
  have hmaxm : IsMaxOn g (Icc l u) m := fun z hz => le_trans (hmax hz) this
  have := huniq m hm hmaxm
  linarith

lemma argmax_le {g : ℝ → ℝ} {l u m m' d : ℝ} (hc : ConcaveOn ℝ (Icc l u) g)
    (hm : m ∈ Icc l u) (hm' : m' ∈ Icc l u) (hmax : IsMaxOn g (Icc l u) m')
    (huniq : ∀ y ∈ Icc l u, IsMaxOn g (Icc l u) y → y = m')
    (hd : HasDerivAt g d m) (h0 : d ≤ 0) : m' ≤ m := by
  by_contra hlt
  push Not at hlt
  have hs := hc.slope_le_of_hasDerivAt hm hm' hlt hd
  rw [slope_def_field] at hs
  have hpos : 0 < m' - m := by linarith
  have : g m' ≤ g m := by
    have := (div_le_iff₀ hpos).1 hs
    nlinarith
  have hmaxm : IsMaxOn g (Icc l u) m := fun z hz => le_trans (hmax hz) this
  have := huniq m hm hmaxm
  linarith

lemma lt_argmax {g : ℝ → ℝ} {l u m m' d : ℝ} (hc : ConcaveOn ℝ (Icc l u) g)
    (hm : m ∈ Icc l u) (hmu : m < u) (hm' : m' ∈ Icc l u) (hmax : IsMaxOn g (Icc l u) m')
    (huniq : ∀ y ∈ Icc l u, IsMaxOn g (Icc l u) y → y = m')
    (hd : HasDerivAt g d m) (h0 : 0 < d) : m < m' := by
  have hle := le_argmax hc hm hm' hmax huniq hd h0.le
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    have := foc_right_nonpos hm hmu hmax hd
    linarith
  · exact h

lemma argmax_lt {g : ℝ → ℝ} {l u m m' d : ℝ} (hc : ConcaveOn ℝ (Icc l u) g)
    (hm : m ∈ Icc l u) (hlm : l < m) (hm' : m' ∈ Icc l u) (hmax : IsMaxOn g (Icc l u) m')
    (huniq : ∀ y ∈ Icc l u, IsMaxOn g (Icc l u) y → y = m')
    (hd : HasDerivAt g d m) (h0 : d < 0) : m' < m := by
  have hle := argmax_le hc hm hm' hmax huniq hd h0.le
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    have := foc_left_nonneg hm hlm hmax hd
    linarith
  · exact h

/-- Berge-type continuity of a unique maximiser. -/
lemma argmax_continuousOn {S K : Set ℝ} (hK : IsCompact K) (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2)) (m : ℝ → ℝ)
    (hm : ∀ x ∈ S, m x ∈ K ∧ ∀ y ∈ K, F x y ≤ F x (m x))
    (huniq : ∀ x ∈ S, ∀ y ∈ K, (∀ z ∈ K, F x z ≤ F x y) → y = m x) : ContinuousOn m S := by
  intro x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set K' := K ∩ {y | ε ≤ dist y (m x)} with hK'def
  have hK'c : IsCompact K' := hK.inter_right (isClosed_le continuous_const
    (continuous_id.dist continuous_const))
  rcases K'.eq_empty_or_nonempty with hE | hne
  · filter_upwards [self_mem_nhdsWithin] with x' hx'
    by_contra hcon
    push Not at hcon
    have : m x' ∈ K' := ⟨(hm x' hx').1, hcon⟩
    rw [hE] at this
    exact this
  · have hV : Continuous fun x' => sSup ((fun y => F x' y) '' K') :=
      hK'c.continuous_sSup (f := F) hF
    obtain ⟨y0, hy0, hy0eq⟩ := hK'c.exists_sSup_image_eq hne
      ((show Continuous (fun y => F x y) from hF.comp (Continuous.prodMk_right x)).continuousOn)
    have hlt : sSup ((fun y => F x y) '' K') < F x (m x) := by
      rw [hy0eq]
      rcases lt_or_eq_of_le ((hm x hx).2 y0 hy0.1) with h | h
      · exact h
      · exfalso
        have hmx : ∀ z ∈ K, F x z ≤ F x y0 := fun z hz => h ▸ (hm x hx).2 z hz
        have := huniq x hx y0 hy0.1 hmx
        have h2 := hy0.2
        simp only [mem_ofPred_eq] at h2
        rw [this, dist_self] at h2
        linarith
    have hcont : Continuous fun x' => F x' (m x) - sSup ((fun y => F x' y) '' K') :=
      (hF.comp (Continuous.prodMk_left (m x))).sub hV
    have hev : ∀ᶠ x' in 𝓝 x, 0 < F x' (m x) - sSup ((fun y => F x' y) '' K') :=
      hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x' h1 hx'
    by_contra hcon
    push Not at hcon
    have hmem : m x' ∈ K' := ⟨(hm x' hx').1, hcon⟩
    have hbdd : BddAbove ((fun y => F x' y) '' K') :=
      (hK'c.image (hF.comp (Continuous.prodMk_right x'))).bddAbove
    have h3 : F x' (m x') ≤ sSup ((fun y => F x' y) '' K') :=
      le_csSup hbdd ⟨m x', hmem, rfl⟩
    have h4 := (hm x' hx').2 (m x) (hm x hx).1
    linarith


/-! ## Calculus of the primitives -/

section Calc
variable (P : Primitives)

def G : ℝ × ℝ × ℝ → ℝ := fun x => P.D x.1 x.2.1 x.2.2
noncomputable def d1 (p q a : ℝ) : ℝ := fderiv ℝ (G P) (p, q, a) ((1:ℝ), (0:ℝ), (0:ℝ))
noncomputable def d2 (p q a : ℝ) : ℝ := fderiv ℝ (G P) (p, q, a) ((0:ℝ), (1:ℝ), (0:ℝ))
noncomputable def d12 (p q a : ℝ) : ℝ := deriv (fun y => d1 P p y a) q
noncomputable def e1 (p q a : ℝ) : ℝ := P.D p q a + (p - P.c) * d1 P p q a
noncomputable def Jd (p a : ℝ) : ℝ := P.D p p a + (p - P.c) * (d1 P p p a + d2 P p p a)
noncomputable def Od (β pt a p : ℝ) : ℝ := (1 - β) * e1 P p pt a + β * Jd P p a

variable {P}

lemma G_diff (hP : P.Standing) : Differentiable ℝ (G P) :=
  hP.smooth.differentiable (by norm_num)

lemma G_cont (hP : P.Standing) : Continuous (G P) := hP.smooth.continuous

lemma D_cont3 (hP : P.Standing) {X : Type*} [TopologicalSpace X] {u v w : X → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => P.D (u x) (v x) (w x)) :=
  (G_cont hP).comp (hu.prodMk (hv.prodMk hw))

lemma d1_cont3 (hP : P.Standing) {X : Type*} [TopologicalSpace X] {u v w : X → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => d1 P (u x) (v x) (w x)) := by
  have h : Continuous (fun y : ℝ × ℝ × ℝ => fderiv ℝ (G P) y ((1:ℝ), (0:ℝ), (0:ℝ))) :=
    (hP.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h.comp (hu.prodMk (hv.prodMk hw))

lemma d2_cont3 (hP : P.Standing) {X : Type*} [TopologicalSpace X] {u v w : X → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => d2 P (u x) (v x) (w x)) := by
  have h : Continuous (fun y : ℝ × ℝ × ℝ => fderiv ℝ (G P) y ((0:ℝ), (1:ℝ), (0:ℝ))) :=
    (hP.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h.comp (hu.prodMk (hv.prodMk hw))

lemma e1_cont3 (hP : P.Standing) {X : Type*} [TopologicalSpace X] {u v w : X → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => e1 P (u x) (v x) (w x)) := by
  unfold e1
  exact (D_cont3 hP hu hv hw).add ((hu.sub continuous_const).mul (d1_cont3 hP hu hv hw))

lemma D_contOn3 (hP : P.Standing) {s : Set ℝ} {u v w : ℝ → ℝ}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) (hw : ContinuousOn w s) :
    ContinuousOn (fun x => P.D (u x) (v x) (w x)) s :=
  (G_cont hP).comp_continuousOn (hu.prodMk (hv.prodMk hw))

lemma e1_contOn3 (hP : P.Standing) {s : Set ℝ} {u v w : ℝ → ℝ}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) (hw : ContinuousOn w s) :
    ContinuousOn (fun x => e1 P (u x) (v x) (w x)) s := by
  have h : Continuous (fun y : ℝ × ℝ × ℝ => e1 P y.1 y.2.1 y.2.2) :=
    e1_cont3 hP continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  exact h.comp_continuousOn (hu.prodMk (hv.prodMk hw))

lemma hasDerivAt_D1 (hP : P.Standing) (p q a : ℝ) :
    HasDerivAt (fun x => P.D x q a) (d1 P p q a) p := by
  have h1 : HasDerivAt (fun x : ℝ => ((x, q, a) : ℝ × ℝ × ℝ)) ((1:ℝ), (0:ℝ), (0:ℝ)) p :=
    (hasDerivAt_id' p).prodMk ((hasDerivAt_const p q).prodMk (hasDerivAt_const p a))
  exact ((G_diff hP) _).hasFDerivAt.comp_hasDerivAt p h1

lemma hasDerivAt_D2 (hP : P.Standing) (p q a : ℝ) :
    HasDerivAt (fun y => P.D p y a) (d2 P p q a) q := by
  have h1 : HasDerivAt (fun y : ℝ => ((p, y, a) : ℝ × ℝ × ℝ)) ((0:ℝ), (1:ℝ), (0:ℝ)) q :=
    (hasDerivAt_const q p).prodMk ((hasDerivAt_id' q).prodMk (hasDerivAt_const q a))
  exact ((G_diff hP) _).hasFDerivAt.comp_hasDerivAt q h1

lemma hasDerivAt_Ddiag (hP : P.Standing) (p a : ℝ) :
    HasDerivAt (fun x => P.D x x a) (d1 P p p a + d2 P p p a) p := by
  have h1 : HasDerivAt (fun x : ℝ => ((x, x, a) : ℝ × ℝ × ℝ)) ((1:ℝ), (1:ℝ), (0:ℝ)) p :=
    (hasDerivAt_id' p).prodMk ((hasDerivAt_id' p).prodMk (hasDerivAt_const p a))
  have := ((G_diff hP) _).hasFDerivAt.comp_hasDerivAt p h1
  have heq : (fderiv ℝ (G P) (p, p, a)) ((1:ℝ), (1:ℝ), (0:ℝ)) = d1 P p p a + d2 P p p a := by
    unfold d1 d2
    rw [← map_add]
    congr 1
    ext <;> simp
  exact heq ▸ this

lemma differentiableAt_d1_q (hP : P.Standing) (p q a : ℝ) :
    DifferentiableAt ℝ (fun y => d1 P p y a) q := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ (G P)) := hP.smooth.fderiv_right (by norm_num)
  have hc : DifferentiableAt ℝ (fun y : ℝ => fderiv ℝ (G P) (p, y, a)) q :=
    ((hfd.differentiable (by norm_num)) _).comp q
      ((differentiableAt_const p).prodMk ((differentiableAt_id).prodMk
        (differentiableAt_const a)))
  exact hc.clm_apply (differentiableAt_const _)

lemma hasDerivAt_d1_q (hP : P.Standing) (p q a : ℝ) :
    HasDerivAt (fun y => d1 P p y a) (d12 P p q a) q :=
  (differentiableAt_d1_q hP p q a).hasDerivAt

lemma hasDerivAt_pi1 (hP : P.Standing) (p q a : ℝ) :
    HasDerivAt (fun x => P.π₁ x q a) (e1 P p q a) p := by
  have : HasDerivAt (fun x => (x - P.c) * P.D x q a) (1 * P.D p q a + (p - P.c) * d1 P p q a) p :=
    ((hasDerivAt_id' p).sub_const P.c).mul (hasDerivAt_D1 hP p q a)
  unfold Primitives.π₁ e1
  convert this using 1
  ring

lemma hasDerivAt_J (hP : P.Standing) (p a : ℝ) :
    HasDerivAt (fun x => P.π₁ x x a) (Jd P p a) p := by
  have : HasDerivAt (fun x => (x - P.c) * P.D x x a)
      (1 * P.D p p a + (p - P.c) * (d1 P p p a + d2 P p p a)) p :=
    ((hasDerivAt_id' p).sub_const P.c).mul (hasDerivAt_Ddiag hP p a)
  unfold Primitives.π₁ Jd
  convert this using 1
  ring

lemma hasDerivAt_tp (hP : P.Standing) (β pt a p : ℝ) :
    HasDerivAt (P.tpObj β pt a) (Od P β pt a p) p := by
  have := ((hasDerivAt_pi1 hP p pt a).const_mul (1 - β)).add ((hasDerivAt_J hP p a).const_mul β)
  unfold Primitives.tpObj Od
  exact this

lemma hasDerivAt_e1_q (hP : P.Standing) (p q a : ℝ) :
    HasDerivAt (fun y => e1 P p y a) (d2 P p q a + (p - P.c) * d12 P p q a) q := by
  unfold e1
  exact (hasDerivAt_D2 hP p q a).add ((hasDerivAt_d1_q hP p q a).const_mul (p - P.c))

lemma Jd_eq (p a : ℝ) : Jd P p a = e1 P p p a + (p - P.c) * d2 P p p a := by
  unfold Jd e1; ring

lemma d2_pos (hP : P.Standing) {p q a : ℝ} (hp : p ∈ P.prices) (hq : q ∈ P.prices)
    (ha : a ∈ P.states) : 0 < d2 P p q a := by
  have := hP.dD_p2 p hp q hq a ha
  rwa [(hasDerivAt_D2 hP p q a).deriv] at this

lemma d1_neg (hP : P.Standing) {p q a : ℝ} (hp : p ∈ P.prices) (hq : q ∈ P.prices)
    (ha : a ∈ P.states) : d1 P p q a < 0 := by
  have := hP.dD_p1 p hp q hq a ha
  rwa [(hasDerivAt_D1 hP p q a).deriv] at this

lemma d12_nonneg (hP : P.Standing) {p q a : ℝ} (hp : p ∈ P.prices) (hq : q ∈ P.prices)
    (ha : a ∈ P.states) : 0 ≤ d12 P p q a := by
  have h := hP.d2D_p1p2 p hp q hq a ha
  have hfun : (fun y => deriv (fun x => P.D x y a) p) = fun y => d1 P p y a :=
    funext fun y => (hasDerivAt_D1 hP p y a).deriv
  rw [hfun] at h
  exact h

lemma e1_strictMono (hP : P.Standing) {p a : ℝ} (hp : p ∈ P.prices) (ha : a ∈ P.states) :
    StrictMonoOn (fun y => e1 P p y a) P.prices := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (e1_cont3 hP continuous_const continuous_id continuous_const).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hxp : x ∈ P.prices := Ioo_subset_Icc_self hx
    rw [(hasDerivAt_e1_q hP p x a).deriv]
    have h1 := d2_pos hP hp hxp ha
    have h2 := d12_nonneg hP hp hxp ha
    have h3 : 0 ≤ p - P.c := by have := hp.1; linarith
    nlinarith

lemma D_strictMono_q (hP : P.Standing) {p a : ℝ} (hp : p ∈ P.prices) (ha : a ∈ P.states) :
    StrictMonoOn (fun y => P.D p y a) P.prices := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (D_cont3 hP continuous_const continuous_id continuous_const).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_D2 hP p x a).deriv]
    exact d2_pos hP hp (Ioo_subset_Icc_self hx) ha

lemma D_strictAnti_p (hP : P.Standing) {q a : ℝ} (hq : q ∈ P.prices) (ha : a ∈ P.states) :
    StrictAntiOn (fun x => P.D x q a) P.prices := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (D_cont3 hP continuous_id continuous_const continuous_const).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_D1 hP x q a).deriv]
    exact d1_neg hP (Ioo_subset_Icc_self hx) hq ha

lemma c_mem (hP : P.Standing) : P.c ∈ P.prices := ⟨le_rfl, hP.c_lt_pmax.le⟩
lemma pmax_mem (hP : P.Standing) : P.pmax ∈ P.prices := ⟨hP.c_lt_pmax.le, le_rfl⟩

lemma pM_mem (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) : P.pM a ∈ P.prices :=
  Ioo_subset_Icc_self (hP.pM_interior a ha)

lemma D_c_pos (hP : P.Standing) {q a : ℝ} (hq : q ∈ P.prices) (ha : a ∈ P.states) :
    0 < P.D P.c q a := by
  have h1 : P.D P.c P.c a ≤ P.D P.c q a :=
    (D_strictMono_q hP (c_mem hP) ha).monotoneOn (c_mem hP) hq hq.1
  have h2 : P.D (P.pM a) P.c a < P.D P.c P.c a :=
    D_strictAnti_p hP (c_mem hP) ha (c_mem hP) (pM_mem hP ha) (hP.pM_interior a ha).1
  have h3 := hP.demand_pos a ha
  linarith

lemma e1_c_pos (hP : P.Standing) {q a : ℝ} (hq : q ∈ P.prices) (ha : a ∈ P.states) :
    0 < e1 P P.c q a := by
  unfold e1; simp only [sub_self, zero_mul, add_zero]; exact D_c_pos hP hq ha

lemma e1_pmax_neg (hP : P.Standing) {q a : ℝ} (hq : q ∈ P.prices) (ha : a ∈ P.states) :
    e1 P P.pmax q a < 0 := by
  have := hP.interior_pmax q hq a ha
  rwa [(hasDerivAt_pi1 hP P.pmax q a).deriv] at this

/-! ### The joint-profit function -/

lemma J_strictConcave (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) :
    StrictConcaveOn ℝ P.prices (fun x => P.π₁ x x a) := hP.concave_joint a ha

lemma J_max (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) :
    IsMaxOn (fun x => P.π₁ x x a) P.prices (P.pM a) := hP.pM_max a ha

lemma J_unique (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) :
    ∀ y ∈ Icc P.c P.pmax, IsMaxOn (fun x => P.π₁ x x a) (Icc P.c P.pmax) y → y = P.pM a :=
  fun y hy hmy => strictConcave_unique (J_strictConcave hP ha) hy (pM_mem hP ha) hmy
    (J_max hP ha)

lemma Jd_pM (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) : Jd P (P.pM a) a = 0 := by
  have hint := hP.pM_interior a ha
  have hloc : IsLocalMax (fun x => P.π₁ x x a) (P.pM a) :=
    (J_max hP ha).isLocalMax (Icc_mem_nhds hint.1 hint.2)
  exact hloc.hasDerivAt_eq_zero (hasDerivAt_J hP _ a)

lemma Jd_pos_of_lt (hP : P.Standing) {p a : ℝ} (hp : p ∈ P.prices) (ha : a ∈ P.states)
    (hlt : p < P.pM a) : 0 < Jd P p a := by
  by_contra h
  push Not at h
  have := argmax_le (J_strictConcave hP ha).concaveOn hp (pM_mem hP ha) (J_max hP ha)
    (J_unique hP ha) (hasDerivAt_J hP p a) h
  linarith

lemma Jd_pmax_neg (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) : Jd P P.pmax a < 0 := by
  by_contra h
  push Not at h
  have := le_argmax (J_strictConcave hP ha).concaveOn (pmax_mem hP) (pM_mem hP ha) (J_max hP ha)
    (J_unique hP ha) (hasDerivAt_J hP P.pmax a) h
  have := (hP.pM_interior a ha).2
  linarith

lemma Jd_c_pos (hP : P.Standing) {a : ℝ} (ha : a ∈ P.states) : 0 < Jd P P.c a := by
  unfold Jd; simp only [sub_self, zero_mul, add_zero]; exact D_c_pos hP (c_mem hP) ha

end Calc


/-! ## The third party's algorithm -/

section ThirdParty
variable {P : Primitives}

lemma cc_pos {β x y : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    0 < (1 - β) * x + β * y := by
  rcases le_total x y with h | h
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 h)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h)]

lemma cc_neg {β x y : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) (hx : x < 0) (hy : y < 0) :
    (1 - β) * x + β * y < 0 := by
  have := cc_pos h0 h1 (neg_pos.2 hx) (neg_pos.2 hy)
  nlinarith

open Classical in
noncomputable def phiT (P : Primitives) (β pt a : ℝ) : ℝ :=
  if h : ∃ m ∈ P.prices, IsMaxOn (P.tpObj β pt a) P.prices m then h.choose else P.c

lemma tp_cont (hP : P.Standing) (β pt : ℝ) :
    Continuous (fun z : ℝ × ℝ => P.tpObj β pt z.1 z.2) := by
  unfold Primitives.tpObj Primitives.π₁
  exact (continuous_const.mul ((continuous_snd.sub continuous_const).mul
    (D_cont3 hP continuous_snd continuous_const continuous_fst))).add
    (continuous_const.mul ((continuous_snd.sub continuous_const).mul
    (D_cont3 hP continuous_snd continuous_snd continuous_fst)))

lemma tp_strictConcave (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) :
    StrictConcaveOn ℝ P.prices (P.tpObj β pt a) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy s t hs ht hst
  have h1 := (hP.concave_own pt hpt a ha).2 hx hy hxy hs ht hst
  have h2 := (hP.concave_joint a ha).2 hx hy hxy hs ht hst
  simp only [smul_eq_mul] at h1 h2 ⊢
  unfold Primitives.tpObj Primitives.π₁ at *
  rcases hβ with ⟨h0, h1'⟩
  rcases lt_or_eq_of_le h1' with hb | hb
  · nlinarith [mul_pos (sub_pos.2 hb) (sub_pos.2 h1), mul_nonneg h0 (sub_nonneg.2 h2.le)]
  · subst hb
    nlinarith

lemma phiT_spec (hP : P.Standing) {β pt a : ℝ} :
    phiT P β pt a ∈ P.prices ∧ IsMaxOn (P.tpObj β pt a) P.prices (phiT P β pt a) := by
  have hex : ∃ m ∈ P.prices, IsMaxOn (P.tpObj β pt a) P.prices m :=
    isCompact_Icc.exists_isMaxOn ⟨P.c, c_mem hP⟩
      ((tp_cont hP β pt).comp (Continuous.prodMk_right a)).continuousOn
  unfold phiT
  rw [dif_pos hex]
  exact hex.choose_spec

lemma phiT_unique (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) :
    ∀ y ∈ Icc P.c P.pmax, IsMaxOn (P.tpObj β pt a) (Icc P.c P.pmax) y → y = phiT P β pt a :=
  fun _ hy hmy => strictConcave_unique (tp_strictConcave hP hβ hpt ha) hy
    (phiT_spec hP).1 hmy (phiT_spec hP).2

lemma phiT_foc (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) :
    phiT P β pt a ∈ Ioo P.c P.pmax ∧ Od P β pt a (phiT P β pt a) = 0 :=
  foc_interior hP.c_lt_pmax (phiT_spec hP).1 (phiT_spec hP).2 (hasDerivAt_tp hP β pt a P.c)
    (cc_pos hβ.1 hβ.2 (e1_c_pos hP hpt ha) (Jd_c_pos hP ha)) (hasDerivAt_tp hP β pt a P.pmax)
    (cc_neg hβ.1 hβ.2 (e1_pmax_neg hP hpt ha) (Jd_pmax_neg hP ha)) (hasDerivAt_tp hP β pt a _)

lemma phiT_mono_pt (hP : P.Standing) {β pt pt' a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (hpt' : pt' ∈ P.prices) (ha : a ∈ P.states) (hle : pt ≤ pt') :
    phiT P β pt a ≤ phiT P β pt' a := by
  have hfoc := (phiT_foc hP hβ hpt ha).2
  have hm := (phiT_spec hP (β := β) (pt := pt) (a := a)).1
  have he : e1 P (phiT P β pt a) pt a ≤ e1 P (phiT P β pt a) pt' a :=
    (e1_strictMono hP hm ha).monotoneOn hpt hpt' hle
  apply le_argmax (tp_strictConcave hP hβ hpt' ha).concaveOn hm (phiT_spec hP).1 (phiT_spec hP).2
    (phiT_unique hP hβ hpt' ha) (hasDerivAt_tp hP β pt' a _)
  unfold Od at *
  nlinarith [mul_nonneg (sub_nonneg.2 hβ.2) (sub_nonneg.2 he)]

lemma e1_pM_neg (hP : P.Standing) {pt a : ℝ} (hpt : pt ∈ P.prices) (ha : a ∈ P.states)
    (hle : pt ≤ P.pM a) : e1 P (P.pM a) pt a < 0 := by
  have h1 : e1 P (P.pM a) pt a ≤ e1 P (P.pM a) (P.pM a) a :=
    (e1_strictMono hP (pM_mem hP ha) ha).monotoneOn hpt (pM_mem hP ha) hle
  have h2 := Jd_eq (P := P) (P.pM a) a
  rw [Jd_pM hP ha] at h2
  have h3 := d2_pos hP (pM_mem hP ha) (pM_mem hP ha) ha
  have h4 := (hP.pM_interior a ha).1
  nlinarith [mul_pos (sub_pos.2 h4) h3]

lemma phiT_le_pM (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) (hle : pt ≤ P.pM a) :
    phiT P β pt a ≤ P.pM a := by
  apply argmax_le (tp_strictConcave hP hβ hpt ha).concaveOn (pM_mem hP ha) (phiT_spec hP).1
    (phiT_spec hP).2 (phiT_unique hP hβ hpt ha) (hasDerivAt_tp hP β pt a _)
  unfold Od
  rw [Jd_pM hP ha]
  have := e1_pM_neg hP hpt ha hle
  nlinarith [mul_nonneg (sub_nonneg.2 hβ.2) (neg_nonneg.2 this.le)]

lemma phiT_lt_pM (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) (hβ1 : β < 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) (hle : pt ≤ P.pM a) :
    phiT P β pt a < P.pM a := by
  apply argmax_lt (tp_strictConcave hP hβ hpt ha).concaveOn (pM_mem hP ha)
    (hP.pM_interior a ha).1 (phiT_spec hP).1
    (phiT_spec hP).2 (phiT_unique hP hβ hpt ha) (hasDerivAt_tp hP β pt a _)
  unfold Od
  rw [Jd_pM hP ha]
  have := e1_pM_neg hP hpt ha hle
  nlinarith [mul_pos (sub_pos.2 hβ1) (neg_pos.2 this)]

lemma phiT_strict_beta (hP : P.Standing) {β₁ β₂ pt a : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ < β₂)
    (h1 : β₂ ≤ 1) (hpt : pt ∈ P.prices) (ha : a ∈ P.states)
    (hlt : phiT P β₁ pt a < P.pM a) : phiT P β₁ pt a < phiT P β₂ pt a := by
  have hβ1 : β₁ ∈ Icc (0:ℝ) 1 := ⟨h0, by linarith⟩
  have hβ2 : β₂ ∈ Icc (0:ℝ) 1 := ⟨by linarith, h1⟩
  have hfoc := phiT_foc hP hβ1 hpt ha
  have hm := (phiT_spec hP (β := β₁) (pt := pt) (a := a)).1
  have hJ := Jd_pos_of_lt hP hm ha hlt
  apply lt_argmax (tp_strictConcave hP hβ2 hpt ha).concaveOn hm hfoc.1.2 (phiT_spec hP).1
    (phiT_spec hP).2 (phiT_unique hP hβ2 hpt ha) (hasDerivAt_tp hP β₂ pt a _)
  have h2 := hfoc.2
  unfold Od at *
  set e := e1 P (phiT P β₁ pt a) pt a
  set J := Jd P (phiT P β₁ pt a) a
  have he : e ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 (show β₁ < 1 by linarith)) hc, mul_nonneg h0 hJ.le]
  nlinarith [mul_pos (sub_pos.2 h12) (show 0 < J - e by linarith)]

lemma phiT_contOn (hP : P.Standing) {β pt : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) (hpt : pt ∈ P.prices) :
    ContinuousOn (fun a => phiT P β pt a) P.states := by
  apply argmax_continuousOn (K := Icc P.c P.pmax) isCompact_Icc (fun a p => P.tpObj β pt a p)
    (tp_cont hP β pt)
  · intro x _
    exact ⟨(phiT_spec hP).1, fun y hy => (phiT_spec hP).2 hy⟩
  · intro x hx y hy hmax
    exact phiT_unique hP hβ hpt hx y hy (isMaxOn_iff.2 hmax)

end ThirdParty


/-! ## The non-adopter -/

section NonAdopter
variable {P : Primitives} {alo ahi : ℝ} {f : ℝ → ℝ}

noncomputable def Psi (P : Primitives) (alo ahi : ℝ) (f φ : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ a in alo..ahi, e1 P p (φ a) a * f a

def Valid (P : Primitives) (alo ahi : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Icc alo ahi) ∧ ∀ a ∈ Icc alo ahi, φ a ∈ P.prices

lemma sub_states (hA : P.IsSupport alo ahi) {a : ℝ} (ha : a ∈ Icc alo ahi) : a ∈ P.states :=
  ⟨le_trans hA.1 ha.1, le_trans ha.2 hA.2.2⟩

lemma iint (hA : P.IsSupport alo ahi) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc alo ahi)) :
    IntervalIntegrable g MeasureTheory.volume alo ahi :=
  ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hA.2.1.le])

lemma pos_integral (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc alo ahi)) (hpos : ∀ a ∈ Icc alo ahi, 0 < h a) :
    0 < ∫ a in alo..ahi, h a * f a := by
  obtain ⟨a0, ha0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hA.2.1.le) hh
  have h1 : ∫ a in alo..ahi, h a0 * f a ≤ ∫ a in alo..ahi, h a * f a := by
    apply intervalIntegral.integral_mono_on hA.2.1.le
    · exact iint (P := P) hA (continuousOn_const.mul hf.1)
    · exact iint (P := P) hA (hh.mul hf.1)
    · intro x hx
      exact mul_le_mul_of_nonneg_right (hmin hx) (hf.2.1 x hx)
  rw [intervalIntegral.integral_const_mul, hf.2.2, mul_one] at h1
  have := hpos a0 ha0
  linarith

lemma neg_integral (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc alo ahi)) (hneg : ∀ a ∈ Icc alo ahi, h a < 0) :
    ∫ a in alo..ahi, h a * f a < 0 := by
  have := pos_integral (P := P) hA hf hh.neg (fun a ha => neg_pos.2 (hneg a ha))
  simp only [Pi.neg_apply, neg_mul, intervalIntegral.integral_neg] at this
  linarith

lemma pi2_contOn (hP : P.Standing) {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) (p : ℝ) :
    ContinuousOn (fun a => P.π₂ (φ a) p a) (Icc alo ahi) := by
  unfold Primitives.π₂
  exact continuousOn_const.mul (D_contOn3 hP continuousOn_const hφ.1 continuousOn_id)

lemma e1i_contOn (hP : P.Standing) {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) (p : ℝ) :
    ContinuousOn (fun a => e1 P p (φ a) a) (Icc alo ahi) :=
  e1_contOn3 hP continuousOn_const hφ.1 continuousOn_id

lemma hasDerivAt_N (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) (p0 : ℝ) :
    HasDerivAt (P.naProfit alo ahi f φ) (Psi P alo ahi f φ p0) p0 := by
  have hK : IsCompact ((Icc (p0 - 1) (p0 + 1)) ×ˢ (Icc P.c P.pmax ×ˢ Icc alo ahi)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (e1_cont3 hP continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd) (P := P)).continuousOn
  obtain ⟨Cf, hCf⟩ := (isCompact_Icc (a := alo) (b := ahi)).exists_bound_of_continuousOn hf.1
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (p0, P.c, alo)
    ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, hP.c_lt_pmax.le⟩, ⟨le_rfl, hA.2.1.le⟩⟩)
  have hIoc : Ι alo ahi = Ioc alo ahi := uIoc_of_le hA.2.1.le
  have hcontF : ∀ x, ContinuousOn (fun t => P.π₂ (φ t) x t * f t) (Icc alo ahi) :=
    fun x => (pi2_contOn hP hφ x).mul hf.1
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := alo) (b := ahi)
    (F := fun x t => P.π₂ (φ t) x t * f t) (F' := fun x t => e1 P x (φ t) t * f t)
    (x₀ := p0) (s := Icc (p0 - 1) (p0 + 1)) (bound := fun _ => C * Cf)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x => by
      rw [hIoc]
      exact ((hcontF x).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (iint (P := P) hA (hcontF p0))
    (by
      rw [hIoc]
      exact (((e1i_contOn hP hφ p0).mul hf.1).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc)
    (Eventually.of_forall fun t ht x hx => by
      rw [hIoc] at ht
      have ht' := Ioc_subset_Icc_self ht
      rw [norm_mul]
      exact mul_le_mul (hC (x, φ t, t) ⟨hx, hφ.2 t ht', ht'⟩) (hCf t ht') (norm_nonneg _) hC0)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x _ => (hasDerivAt_pi1 hP x (φ t) t).mul_const (f t))
  exact this.2

lemma N_strictConcave (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) :
    StrictConcaveOn ℝ P.prices (P.naProfit alo ahi f φ) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy s t hs ht hst
  simp only [smul_eq_mul]
  have key : 0 < ∫ a in alo..ahi,
      (P.π₂ (φ a) (s * x + t * y) a - (s * P.π₂ (φ a) x a + t * P.π₂ (φ a) y a)) * f a := by
    apply pos_integral (P := P) hA hf
    · exact (pi2_contOn hP hφ _).sub (((pi2_contOn hP hφ _).const_smul s).add
        ((pi2_contOn hP hφ _).const_smul t))
    · intro a ha
      have := (hP.concave_own (φ a) (hφ.2 a ha) a (sub_states hA ha)).2 hx hy hxy hs ht hst
      simp only [smul_eq_mul] at this
      unfold Primitives.π₂
      unfold Primitives.π₁ at this
      linarith
  have heq : (fun a => (P.π₂ (φ a) (s * x + t * y) a - (s * P.π₂ (φ a) x a +
      t * P.π₂ (φ a) y a)) * f a) = fun a => P.π₂ (φ a) (s * x + t * y) a * f a -
      (s * (P.π₂ (φ a) x a * f a) + t * (P.π₂ (φ a) y a * f a)) := by
    funext a; ring
  rw [heq, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  · unfold Primitives.naProfit
    linarith
  all_goals first
    | exact iint (P := P) hA ((pi2_contOn hP hφ _).mul hf.1)
    | exact iint (P := P) hA (continuousOn_const.mul ((pi2_contOn hP hφ _).mul hf.1))
    | exact (iint (P := P) hA (continuousOn_const.mul ((pi2_contOn hP hφ _).mul hf.1))).add
        (iint (P := P) hA (continuousOn_const.mul ((pi2_contOn hP hφ _).mul hf.1)))

open Classical in
noncomputable def br (P : Primitives) (alo ahi : ℝ) (f φ : ℝ → ℝ) : ℝ :=
  if h : ∃ m ∈ P.prices, IsMaxOn (P.naProfit alo ahi f φ) P.prices m then h.choose else P.c

lemma br_spec (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) :
    br P alo ahi f φ ∈ P.prices ∧ IsMaxOn (P.naProfit alo ahi f φ) P.prices (br P alo ahi f φ) := by
  have hex : ∃ m ∈ P.prices, IsMaxOn (P.naProfit alo ahi f φ) P.prices m :=
    isCompact_Icc.exists_isMaxOn ⟨P.c, c_mem hP⟩
      (fun x _ => (hasDerivAt_N hP hA hf hφ x).continuousAt.continuousWithinAt)
  unfold br
  rw [dif_pos hex]
  exact hex.choose_spec

lemma br_unique (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) :
    ∀ y ∈ Icc P.c P.pmax, IsMaxOn (P.naProfit alo ahi f φ) (Icc P.c P.pmax) y →
      y = br P alo ahi f φ :=
  fun _ hy hmy => strictConcave_unique (N_strictConcave hP hA hf hφ) hy
    (br_spec hP hA hf hφ).1 hmy (br_spec hP hA hf hφ).2

lemma br_foc (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ : ℝ → ℝ} (hφ : Valid P alo ahi φ) :
    br P alo ahi f φ ∈ Ioo P.c P.pmax ∧ Psi P alo ahi f φ (br P alo ahi f φ) = 0 :=
  foc_interior hP.c_lt_pmax (br_spec hP hA hf hφ).1 (br_spec hP hA hf hφ).2
    (hasDerivAt_N hP hA hf hφ P.c)
    (pos_integral (P := P) hA hf (e1i_contOn hP hφ _)
      (fun a ha => e1_c_pos hP (hφ.2 a ha) (sub_states hA ha)))
    (hasDerivAt_N hP hA hf hφ P.pmax)
    (neg_integral (P := P) hA hf (e1i_contOn hP hφ _)
      (fun a ha => e1_pmax_neg hP (hφ.2 a ha) (sub_states hA ha)))
    (hasDerivAt_N hP hA hf hφ _)

lemma br_mono (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ φ' : ℝ → ℝ} (hφ : Valid P alo ahi φ) (hφ' : Valid P alo ahi φ')
    (hle : ∀ a ∈ Icc alo ahi, φ a ≤ φ' a) : br P alo ahi f φ ≤ br P alo ahi f φ' := by
  have hfoc := br_foc hP hA hf hφ
  have hb := (br_spec hP hA hf hφ).1
  apply le_argmax (N_strictConcave hP hA hf hφ').concaveOn hb (br_spec hP hA hf hφ').1
    (br_spec hP hA hf hφ').2 (br_unique hP hA hf hφ') (hasDerivAt_N hP hA hf hφ' _)
  rw [← hfoc.2]
  apply intervalIntegral.integral_mono_on hA.2.1.le
  · exact iint (P := P) hA ((e1i_contOn hP hφ _).mul hf.1)
  · exact iint (P := P) hA ((e1i_contOn hP hφ' _).mul hf.1)
  · intro a ha
    apply mul_le_mul_of_nonneg_right _ (hf.2.1 a ha)
    exact (e1_strictMono hP hb (sub_states hA ha)).monotoneOn (hφ.2 a ha) (hφ'.2 a ha) (hle a ha)

lemma br_strict (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {φ φ' : ℝ → ℝ} (hφ : Valid P alo ahi φ) (hφ' : Valid P alo ahi φ')
    (hlt : ∀ a ∈ Icc alo ahi, φ a < φ' a) : br P alo ahi f φ < br P alo ahi f φ' := by
  have hfoc := br_foc hP hA hf hφ
  have hb := (br_spec hP hA hf hφ).1
  apply lt_argmax (N_strictConcave hP hA hf hφ').concaveOn hb hfoc.1.2 (br_spec hP hA hf hφ').1
    (br_spec hP hA hf hφ').2 (br_unique hP hA hf hφ') (hasDerivAt_N hP hA hf hφ' _)
  have key : 0 < ∫ a in alo..ahi,
      (e1 P (br P alo ahi f φ) (φ' a) a - e1 P (br P alo ahi f φ) (φ a) a) * f a := by
    apply pos_integral (P := P) hA hf ((e1i_contOn hP hφ' _).sub (e1i_contOn hP hφ _))
    intro a ha
    have := (e1_strictMono hP hb (sub_states hA ha)) (hφ.2 a ha) (hφ'.2 a ha) (hlt a ha)
    simp only [Pi.sub_apply] at this ⊢
    linarith
  simp only [sub_mul] at key
  have i1 : IntervalIntegrable (fun a => e1 P (br P alo ahi f φ) (φ' a) a * f a)
      MeasureTheory.volume alo ahi := iint (P := P) hA ((e1i_contOn hP hφ' _).mul hf.1)
  have i2 : IntervalIntegrable (fun a => e1 P (br P alo ahi f φ) (φ a) a * f a)
      MeasureTheory.volume alo ahi := iint (P := P) hA ((e1i_contOn hP hφ _).mul hf.1)
  rw [intervalIntegral.integral_sub i1 i2] at key
  have h2 := hfoc.2
  unfold Psi at h2 ⊢
  linarith

end NonAdopter


/-! ## Equilibria as fixed points; least fixed point (Tarski) -/

section Equilibrium
variable {P : Primitives} {alo ahi : ℝ} {f : ℝ → ℝ}

noncomputable def gmap (P : Primitives) (alo ahi : ℝ) (f : ℝ → ℝ) (β pt : ℝ) : ℝ :=
  br P alo ahi f (fun a => phiT P β pt a)

lemma phiT_valid (hP : P.Standing) (hA : P.IsSupport alo ahi) {β pt : ℝ}
    (hβ : β ∈ Icc (0:ℝ) 1) (hpt : pt ∈ P.prices) : Valid P alo ahi (fun a => phiT P β pt a) :=
  ⟨(phiT_contOn hP hβ hpt).mono (fun _ ha => sub_states hA ha), fun _ _ => (phiT_spec hP).1⟩

lemma gmap_mem (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β pt : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) (hpt : pt ∈ P.prices) : gmap P alo ahi f β pt ∈ P.prices :=
  (br_spec hP hA hf (phiT_valid hP hA hβ hpt)).1

lemma gmap_mono (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β pt pt' : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) (hpt : pt ∈ P.prices) (hpt' : pt' ∈ P.prices)
    (hle : pt ≤ pt') : gmap P alo ahi f β pt ≤ gmap P alo ahi f β pt' :=
  br_mono hP hA hf (phiT_valid hP hA hβ hpt) (phiT_valid hP hA hβ hpt')
    (fun a ha => phiT_mono_pt hP hβ hpt hpt' (sub_states hA ha) hle)

lemma naProfit_congr (hA : P.IsSupport alo ahi) {φ φ' : ℝ → ℝ}
    (h : ∀ a ∈ Icc alo ahi, φ a = φ' a) :
    P.naProfit alo ahi f φ = P.naProfit alo ahi f φ' := by
  funext x
  unfold Primitives.naProfit
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hA.2.1.le] at ha
  simp only [h a ha]

lemma eq_fwd (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) {φ : ℝ → ℝ} {p : ℝ}
    (hE : P.IsEquilibrium alo ahi f β φ p) :
    p ∈ P.prices ∧ (∀ a ∈ Icc alo ahi, φ a = phiT P β p a) ∧ gmap P alo ahi f β p = p := by
  obtain ⟨hp, hφ, hN⟩ := hE
  have hφeq : ∀ a ∈ Icc alo ahi, φ a = phiT P β p a := fun a ha =>
    phiT_unique hP hβ hp (sub_states hA ha) _ (hφ a ha).1 (hφ a ha).2
  refine ⟨hp, hφeq, ?_⟩
  rw [naProfit_congr hA hφeq] at hN
  exact (br_unique hP hA hf (phiT_valid hP hA hβ hp) p hp hN).symm

lemma eq_bwd (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ P.prices)
    (hfix : gmap P alo ahi f β p = p) :
    P.IsEquilibrium alo ahi f β (fun a => phiT P β p a) p := by
  refine ⟨hp, fun a _ => phiT_spec hP, ?_⟩
  have := (br_spec hP hA hf (phiT_valid hP hA hβ hp)).2
  unfold gmap at hfix
  rwa [hfix] at this

noncomputable def pstar (P : Primitives) (alo ahi : ℝ) (f : ℝ → ℝ) (β : ℝ) : ℝ :=
  sInf {p | p ∈ P.prices ∧ gmap P alo ahi f β p ≤ p}

lemma pstar_spec (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) :
    pstar P alo ahi f β ∈ P.prices ∧ gmap P alo ahi f β (pstar P alo ahi f β) =
      pstar P alo ahi f β ∧
      ∀ q ∈ P.prices, gmap P alo ahi f β q ≤ q → pstar P alo ahi f β ≤ q := by
  set S := {p | p ∈ P.prices ∧ gmap P alo ahi f β p ≤ p} with hS
  have hne : S.Nonempty := ⟨P.pmax, pmax_mem hP, (gmap_mem hP hA hf hβ (pmax_mem hP)).2⟩
  have hbdd : BddBelow S := ⟨P.c, fun q hq => hq.1.1⟩
  have hle : ∀ q ∈ P.prices, gmap P alo ahi f β q ≤ q → pstar P alo ahi f β ≤ q :=
    fun q hq hgq => csInf_le hbdd ⟨hq, hgq⟩
  have hmem : pstar P alo ahi f β ∈ P.prices :=
    ⟨le_csInf hne (fun q hq => hq.1.1), le_trans (hle _ (pmax_mem hP)
      (gmap_mem hP hA hf hβ (pmax_mem hP)).2) le_rfl⟩
  have hg1 : gmap P alo ahi f β (pstar P alo ahi f β) ≤ pstar P alo ahi f β := by
    apply le_csInf hne
    intro q hq
    exact le_trans (gmap_mono hP hA hf hβ hmem hq.1 (hle q hq.1 hq.2)) hq.2
  have hgm := gmap_mem hP hA hf hβ hmem
  have hg2 : pstar P alo ahi f β ≤ gmap P alo ahi f β (pstar P alo ahi f β) :=
    hle _ hgm (gmap_mono hP hA hf hβ hgm hmem hg1)
  exact ⟨hmem, le_antisymm hg1 hg2, hle⟩

lemma minimal_exists (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) :
    P.IsMinimalEquilibrium alo ahi f β (fun a => phiT P β (pstar P alo ahi f β) a)
      (pstar P alo ahi f β) := by
  obtain ⟨hmem, hfix, hle⟩ := pstar_spec hP hA hf hβ
  refine ⟨eq_bwd hP hA hf hβ hmem hfix, ?_⟩
  intro φ' p' hE
  obtain ⟨hp', _, hfix'⟩ := eq_fwd hP hA hf hβ hE
  exact hle p' hp' hfix'.le

lemma minimal_eq (hP : P.Standing) (hA : P.IsSupport alo ahi) (hf : IsDensity alo ahi f)
    {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) {φ : ℝ → ℝ} {p : ℝ}
    (hm : P.IsMinimalEquilibrium alo ahi f β φ p) :
    p = pstar P alo ahi f β ∧ ∀ a ∈ Icc alo ahi, φ a = phiT P β p a := by
  obtain ⟨hp, hφ, hfix⟩ := eq_fwd hP hA hf hβ hm.1
  refine ⟨le_antisymm (hm.2 _ _ (minimal_exists hP hA hf hβ).1)
    ((pstar_spec hP hA hf hβ).2.2 p hp hfix.le), hφ⟩

end Equilibrium

/-! ## Lemma 3: small spread keeps the minimal equilibrium below `pM alo` -/

section Lemma3
variable {P : Primitives}

lemma pM_contOn (hP : P.Standing) : ContinuousOn P.pM P.states := by
  apply argmax_continuousOn (K := Icc P.c P.pmax) isCompact_Icc (fun a p => P.π₁ p p a)
  · unfold Primitives.π₁
    exact (continuous_snd.sub continuous_const).mul
      (D_cont3 hP continuous_snd continuous_snd continuous_fst)
  · intro x hx
    exact ⟨pM_mem hP hx, fun y hy => J_max hP hx hy⟩
  · intro x hx y hy hmax
    exact J_unique hP hx y hy (isMaxOn_iff.2 hmax)

lemma lemma3_aux (hP : P.Standing) {alo : ℝ} (halo : alo ∈ Ico P.a₀ P.a₁) :
    ∃ δ > 0, ∀ ahi : ℝ, alo < ahi → ahi ≤ P.a₁ → ahi - alo < δ → ∀ f : ℝ → ℝ,
      IsDensity alo ahi f → ∀ β ∈ Icc (0:ℝ) 1,
        gmap P alo ahi f β (P.pM alo) < P.pM alo := by
  have hsalo : alo ∈ P.states := ⟨halo.1, halo.2.le⟩
  have hcont : ContinuousOn (fun a => e1 P (P.pM alo) (P.pM a) a) P.states :=
    e1_contOn3 hP continuousOn_const (pM_contOn hP) continuousOn_id
  have hneg : e1 P (P.pM alo) (P.pM alo) alo < 0 :=
    e1_pM_neg hP (pM_mem hP hsalo) hsalo le_rfl
  have hev : {a | e1 P (P.pM alo) (P.pM a) a < 0} ∈ 𝓝[P.states] alo :=
    (hcont alo hsalo).tendsto (Iio_mem_nhds hneg)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨δ, hδ, ?_⟩
  intro ahi h1 h2 h3 f hf β hβ
  have hA : P.IsSupport alo ahi := ⟨halo.1, h1, h2⟩
  have hpMa := pM_mem hP hsalo
  have hφ := phiT_valid hP hA hβ hpMa
  apply argmax_lt (N_strictConcave hP hA hf hφ).concaveOn hpMa (hP.pM_interior alo hsalo).1
    (br_spec hP hA hf hφ).1 (br_spec hP hA hf hφ).2 (br_unique hP hA hf hφ)
    (hasDerivAt_N hP hA hf hφ _)
  apply neg_integral (P := P) hA hf (e1i_contOn hP hφ _)
  intro a ha
  have has := sub_states hA ha
  have hmono : P.pM alo ≤ P.pM a := hP.pM_mono hsalo has ha.1
  have hle : phiT P β (P.pM alo) a ≤ P.pM a := phiT_le_pM hP hβ hpMa has hmono
  have h4 : e1 P (P.pM alo) (phiT P β (P.pM alo) a) a ≤ e1 P (P.pM alo) (P.pM a) a :=
    (e1_strictMono hP hpMa has).monotoneOn (phiT_spec hP).1 (pM_mem hP has) hle
  have h5 : a ∈ Metric.ball alo δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [ha.1])]
    linarith [ha.2]
  have h6 := hball ⟨h5, has⟩
  simp only [mem_ofPred_eq] at h6
  linarith

end Lemma3

end T2Aux

end ThirdPartyPricing.General


namespace ThirdPartyPricing.General
open Primitives Set Filter Topology
namespace T2Aux
variable {P : Primitives}

lemma pstar_lt_pM (hP : P.Standing) {alo : ℝ} (halo : alo ∈ Ico P.a₀ P.a₁) :
    ∃ δ > 0, ∀ ahi : ℝ, alo < ahi → ahi ≤ P.a₁ → ahi - alo < δ → ∀ f : ℝ → ℝ,
      IsDensity alo ahi f → ∀ β ∈ Icc (0:ℝ) 1, pstar P alo ahi f β < P.pM alo := by
  obtain ⟨δ, hδ, hL3⟩ := lemma3_aux hP halo
  refine ⟨δ, hδ, fun ahi h1 h2 h3 f hf β hβ => ?_⟩
  have hA : P.IsSupport alo ahi := ⟨halo.1, h1, h2⟩
  have hsalo : alo ∈ P.states := ⟨halo.1, halo.2.le⟩
  obtain ⟨hmem, hfix, hle⟩ := pstar_spec hP hA hf hβ
  have hpMa := pM_mem hP hsalo
  have hg := hL3 ahi h1 h2 h3 f hf β hβ
  have h4 := hle _ hpMa hg.le
  have h5 := gmap_mono hP hA hf hβ hmem hpMa h4
  rw [hfix] at h5
  linarith

lemma phiT_eq (hP : P.Standing) {β pt a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hpt : pt ∈ P.prices) (ha : a ∈ P.states) {m : ℝ} (hm : m ∈ P.prices)
    (hmax : IsMaxOn (P.tpObj β pt a) P.prices m) : m = phiT P β pt a :=
  phiT_unique hP hβ hpt ha m hm hmax

lemma phiT_strictMono_pt (hP : P.Standing) {β pt pt' a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1)
    (hβ1 : β < 1) (hpt : pt ∈ P.prices) (hpt' : pt' ∈ P.prices) (ha : a ∈ P.states)
    (hlt : pt < pt') : phiT P β pt a < phiT P β pt' a := by
  have hfoc := phiT_foc hP hβ hpt ha
  have hm := (phiT_spec hP (β := β) (pt := pt) (a := a)).1
  have he : e1 P (phiT P β pt a) pt a < e1 P (phiT P β pt a) pt' a :=
    (e1_strictMono hP hm ha) hpt hpt' hlt
  apply lt_argmax (tp_strictConcave hP hβ hpt' ha).concaveOn hm hfoc.1.2 (phiT_spec hP).1
    (phiT_spec hP).2 (phiT_unique hP hβ hpt' ha) (hasDerivAt_tp hP β pt' a _)
  have h2 := hfoc.2
  unfold Od at *
  nlinarith [mul_pos (sub_pos.2 hβ1) (sub_pos.2 he)]

lemma phiT_contOn_pt (hP : P.Standing) {β a : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) (ha : a ∈ P.states) :
    ContinuousOn (fun pt => phiT P β pt a) P.prices := by
  apply argmax_continuousOn (K := Icc P.c P.pmax) isCompact_Icc (fun pt p => P.tpObj β pt a p)
  · unfold Primitives.tpObj Primitives.π₁
    exact (continuous_const.mul ((continuous_snd.sub continuous_const).mul
      (D_cont3 hP continuous_snd continuous_fst continuous_const))).add
      (continuous_const.mul ((continuous_snd.sub continuous_const).mul
      (D_cont3 hP continuous_snd continuous_snd continuous_const)))
  · intro x _
    exact ⟨(phiT_spec hP).1, fun y hy => (phiT_spec hP).2 hy⟩
  · intro x hx y hy hmax
    exact phiT_unique hP hβ hx ha y hy (isMaxOn_iff.2 hmax)

noncomputable def pstarMax (P : Primitives) (alo ahi : ℝ) (f : ℝ → ℝ) (β : ℝ) : ℝ :=
  sSup {p | p ∈ P.prices ∧ p ≤ gmap P alo ahi f β p}

lemma pstarMax_spec (hP : P.Standing) {alo ahi : ℝ} {f : ℝ → ℝ} (hA : P.IsSupport alo ahi)
    (hf : IsDensity alo ahi f) {β : ℝ} (hβ : β ∈ Icc (0:ℝ) 1) :
    pstarMax P alo ahi f β ∈ P.prices ∧ gmap P alo ahi f β (pstarMax P alo ahi f β) =
      pstarMax P alo ahi f β ∧
      ∀ q ∈ P.prices, q ≤ gmap P alo ahi f β q → q ≤ pstarMax P alo ahi f β := by
  set S := {p | p ∈ P.prices ∧ p ≤ gmap P alo ahi f β p} with hS
  have hne : S.Nonempty := ⟨P.c, c_mem hP, (gmap_mem hP hA hf hβ (c_mem hP)).1⟩
  have hbdd : BddAbove S := ⟨P.pmax, fun q hq => hq.1.2⟩
  have hle : ∀ q ∈ P.prices, q ≤ gmap P alo ahi f β q → q ≤ pstarMax P alo ahi f β :=
    fun q hq hgq => le_csSup hbdd ⟨hq, hgq⟩
  have hmem : pstarMax P alo ahi f β ∈ P.prices :=
    ⟨le_trans le_rfl (hle _ (c_mem hP) (gmap_mem hP hA hf hβ (c_mem hP)).1),
      csSup_le hne (fun q hq => hq.1.2)⟩
  have hg1 : pstarMax P alo ahi f β ≤ gmap P alo ahi f β (pstarMax P alo ahi f β) := by
    apply csSup_le hne
    intro q hq
    exact le_trans hq.2 (gmap_mono hP hA hf hβ hq.1 hmem (hle q hq.1 hq.2))
  have hgm := gmap_mem hP hA hf hβ hmem
  have hg2 : gmap P alo ahi f β (pstarMax P alo ahi f β) ≤ pstarMax P alo ahi f β :=
    hle _ hgm (gmap_mono hP hA hf hβ hmem hgm hg1)
  exact ⟨hmem, le_antisymm hg2 hg1, hle⟩

end T2Aux
end ThirdPartyPricing.General

open Set ThirdPartyPricing.General ThirdPartyPricing.General.Primitives ThirdPartyPricing.General.T2Aux in
theorem solution (P : Primitives) (hP : P.Standing) (phiT : ℝ → ℝ → ℝ → ℝ) (hphiT : ∀ β ∈ Set.Icc (0:ℝ) 1, ∀ pt ∈ P.prices, ∀ a ∈ P.states, phiT β pt a ∈ P.prices ∧ IsMaxOn (P.tpObj β pt a) P.prices (phiT β pt a)) (a : ℝ) (ha : a ∈ P.states) (pt : ℝ) (hpt : pt ∈ P.prices) (β₁ β₂ : ℝ) (h0 : 0 ≤ β₁) (h12 : β₁ < β₂) (h1 : β₂ ≤ 1) (hbelow : ∀ β ∈ Set.Ico β₁ β₂, phiT β pt a < P.pM a) : phiT β₁ pt a < phiT β₂ pt a := by
  have hβ1 : β₁ ∈ Icc (0:ℝ) 1 := ⟨h0, by linarith⟩
  have hβ2 : β₂ ∈ Icc (0:ℝ) 1 := ⟨by linarith, h1⟩
  have e1 := T2Aux.phiT_eq hP hβ1 hpt ha (hphiT β₁ hβ1 pt hpt a ha).1 (hphiT β₁ hβ1 pt hpt a ha).2
  have e2 := T2Aux.phiT_eq hP hβ2 hpt ha (hphiT β₂ hβ2 pt hpt a ha).1 (hphiT β₂ hβ2 pt hpt a ha).2
  have hb := hbelow β₁ ⟨le_rfl, h12⟩
  rw [e1] at hb ⊢
  rw [e2]
  exact T2Aux.phiT_strict_beta hP h0 h12 h1 hpt ha hb
