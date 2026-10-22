-- Prove2me | solution 1 for ReadmissionsHRRP.HRRPI.proposition_1_ordering
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:39:14.43155+00:00
-- url     : https://prove2.me/submissions/ac63f1bb-2336-4973-a68b-3a5181898663

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

open Set Filter Topology

namespace HRRPAux
open ReadmissionsHRRP.HRRPI

/-- The cost as a function on the plane. -/
def F (M : Model) : ℝ × ℝ → ℝ := fun p => M.R p.1 p.2

lemma hasDerivAt_lineR (r c : ℝ) : HasDerivAt (fun s : ℝ => ((s, c) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) r :=
  (hasDerivAt_id r).prodMk (hasDerivAt_const r c)

lemma hasDerivAt_lineC (r c : ℝ) : HasDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) c :=
  (hasDerivAt_const c r).prodMk (hasDerivAt_id c)

section Calc

variable (M : Model) {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hCD : ContDiffOn ℝ 2 (F M) U)
include hUo hCD

lemma hasFDerivAt_F {q : ℝ × ℝ} (hq : q ∈ U) : HasFDerivAt (F M) (fderiv ℝ (F M) q) q :=
  ((hCD.contDiffAt (hUo.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt

lemma contDiffOn_DF : ContDiffOn ℝ 1 (fderiv ℝ (F M)) U :=
  hCD.fderiv_of_isOpen hUo (by norm_num)

lemma hasFDerivAt_DF {q : ℝ × ℝ} (hq : q ∈ U) :
    HasFDerivAt (fderiv ℝ (F M)) (fderiv ℝ (fderiv ℝ (F M)) q) q :=
  (((contDiffOn_DF M hUo hCD).contDiffAt (hUo.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt

lemma continuousOn_DF : ContinuousOn (fderiv ℝ (F M)) U :=
  (contDiffOn_DF M hUo hCD).continuousOn

lemma continuousOn_D2 : ContinuousOn (fderiv ℝ (fderiv ℝ (F M))) U :=
  ((contDiffOn_DF M hUo hCD).fderiv_of_isOpen hUo (m := 0) (by norm_num)).continuousOn

lemma symm_D2 {q : ℝ × ℝ} (hq : q ∈ U) (v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (F M)) q v w = fderiv ℝ (fderiv ℝ (F M)) q w v :=
  (hCD.contDiffAt (hUo.mem_nhds hq)).isSymmSndFDerivAt (by simp) v w

lemma hasDerivAt_F_comp {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (hγ : HasDerivAt γ v t)
    (ht : γ t ∈ U) : HasDerivAt (fun s => F M (γ s)) (fderiv ℝ (F M) (γ t) v) t :=
  (hasFDerivAt_F M hUo hCD ht).comp_hasDerivAt t hγ

lemma hasDerivAt_DF_comp {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (hγ : HasDerivAt γ v t)
    (ht : γ t ∈ U) (w : ℝ × ℝ) :
    HasDerivAt (fun s => fderiv ℝ (F M) (γ s) w) (fderiv ℝ (fderiv ℝ (F M)) (γ t) v w) t := by
  have h1 := (hasFDerivAt_DF M hUo hCD ht).comp_hasDerivAt t hγ
  have h2 := h1.clm_apply (hasDerivAt_const t w)
  simpa using h2

omit hCD in
lemma evR {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) : ∀ᶠ s in 𝓝 r, ((s, c) : ℝ × ℝ) ∈ U :=
  (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hUo.mem_nhds hq)

omit hCD in
lemma evC {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) : ∀ᶠ s in 𝓝 c, ((r, s) : ℝ × ℝ) ∈ U :=
  (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hUo.mem_nhds hq)

lemma hasDerivAt_R_r {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.R s c) (fderiv ℝ (F M) (r, c) (1, 0)) r :=
  hasDerivAt_F_comp M hUo hCD (hasDerivAt_lineR r c) hq

lemma hasDerivAt_R_c {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.R r s) (fderiv ℝ (F M) (r, c) (0, 1)) c :=
  hasDerivAt_F_comp M hUo hCD (hasDerivAt_lineC r c) hq

lemma Rr_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) : M.Rr r c = fderiv ℝ (F M) (r, c) (1, 0) :=
  (hasDerivAt_R_r M hUo hCD hq).deriv

lemma Rc_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) : M.Rc r c = fderiv ℝ (F M) (r, c) (0, 1) :=
  (hasDerivAt_R_c M hUo hCD hq).deriv

lemma hasDerivAt_Rr_r {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.Rr s c) (fderiv ℝ (fderiv ℝ (F M)) (r, c) (1, 0) (1, 0)) r := by
  have h := hasDerivAt_DF_comp M hUo hCD (hasDerivAt_lineR r c) hq (1, 0)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [evR hUo hq] with s hs
  exact Rr_eq M hUo hCD hs

lemma hasDerivAt_Rr_c {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.Rr r s) (fderiv ℝ (fderiv ℝ (F M)) (r, c) (0, 1) (1, 0)) c := by
  have h := hasDerivAt_DF_comp M hUo hCD (hasDerivAt_lineC r c) hq (1, 0)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [evC hUo hq] with s hs
  exact Rr_eq M hUo hCD hs

lemma hasDerivAt_Rc_r {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.Rc s c) (fderiv ℝ (fderiv ℝ (F M)) (r, c) (1, 0) (0, 1)) r := by
  have h := hasDerivAt_DF_comp M hUo hCD (hasDerivAt_lineR r c) hq (0, 1)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [evR hUo hq] with s hs
  exact Rc_eq M hUo hCD hs

lemma hasDerivAt_Rc_c {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    HasDerivAt (fun s => M.Rc r s) (fderiv ℝ (fderiv ℝ (F M)) (r, c) (0, 1) (0, 1)) c := by
  have h := hasDerivAt_DF_comp M hUo hCD (hasDerivAt_lineC r c) hq (0, 1)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [evC hUo hq] with s hs
  exact Rc_eq M hUo hCD hs

lemma Rrr_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    M.Rrr r c = fderiv ℝ (fderiv ℝ (F M)) (r, c) (1, 0) (1, 0) :=
  (hasDerivAt_Rr_r M hUo hCD hq).deriv

lemma Rrc_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    M.Rrc r c = fderiv ℝ (fderiv ℝ (F M)) (r, c) (0, 1) (1, 0) :=
  (hasDerivAt_Rr_c M hUo hCD hq).deriv

lemma Rcr_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    M.Rcr r c = fderiv ℝ (fderiv ℝ (F M)) (r, c) (1, 0) (0, 1) :=
  (hasDerivAt_Rc_r M hUo hCD hq).deriv

lemma Rcc_eq {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ U) :
    M.Rcc r c = fderiv ℝ (fderiv ℝ (F M)) (r, c) (0, 1) (0, 1) :=
  (hasDerivAt_Rc_c M hUo hCD hq).deriv

/-- `Rc`, as a function on the plane, is continuous at points of `U`. -/
lemma continuousAt_Rc {q : ℝ × ℝ} (hq : q ∈ U) :
    ContinuousAt (fun p : ℝ × ℝ => M.Rc p.1 p.2) q := by
  have h : ContinuousAt (fun p : ℝ × ℝ => fderiv ℝ (F M) p (0, 1)) q :=
    ((continuousOn_DF M hUo hCD).continuousAt (hUo.mem_nhds hq)).clm_apply continuousAt_const
  refine h.congr ?_
  filter_upwards [hUo.mem_nhds hq] with p hp
  exact (Rc_eq M hUo hCD (r := p.1) (c := p.2) hp).symm

lemma continuousAt_Rr {q : ℝ × ℝ} (hq : q ∈ U) :
    ContinuousAt (fun p : ℝ × ℝ => M.Rr p.1 p.2) q := by
  have h : ContinuousAt (fun p : ℝ × ℝ => fderiv ℝ (F M) p (1, 0)) q :=
    ((continuousOn_DF M hUo hCD).continuousAt (hUo.mem_nhds hq)).clm_apply continuousAt_const
  refine h.congr ?_
  filter_upwards [hUo.mem_nhds hq] with p hp
  exact (Rr_eq M hUo hCD (r := p.1) (c := p.2) hp).symm

lemma continuousAt_Rcc {q : ℝ × ℝ} (hq : q ∈ U) :
    ContinuousAt (fun p : ℝ × ℝ => M.Rcc p.1 p.2) q := by
  have h : ContinuousAt (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ (F M)) p (0, 1) (0, 1)) q :=
    (((continuousOn_D2 M hUo hCD).continuousAt (hUo.mem_nhds hq)).clm_apply
      continuousAt_const).clm_apply continuousAt_const
  refine h.congr ?_
  filter_upwards [hUo.mem_nhds hq] with p hp
  exact (Rcc_eq M hUo hCD (r := p.1) (c := p.2) hp).symm

lemma continuousAt_F {q : ℝ × ℝ} (hq : q ∈ U) : ContinuousAt (F M) q :=
  (hasFDerivAt_F M hUo hCD hq).continuousAt

end Calc

section OneD

lemma foc_1d {f : ℝ → ℝ} {a b x d : ℝ} (hx : x ∈ Icc a b) (hmax : ∀ y ∈ Icc a b, f y ≤ f x)
    (hd : HasDerivAt f d x) : ∀ y ∈ Icc a b, d * (y - x) ≤ 0 := by
  intro y hy
  have hmax' : IsLocalMaxOn f (Icc a b) x := eventually_nhdsWithin_of_forall hmax
  have h := hmax'.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc a b).segment_subset hx hy))
  simpa [mul_comm] using h

lemma deriv_zero_of_const {g : ℝ → ℝ} {a b m d K : ℝ} (hd : HasDerivAt g d m)
    (hconst : ∀ t ∈ Icc a b, g t = K) (hm : m ∈ Ioo a b) : d = 0 := by
  have h0 : HasDerivAt g 0 m := by
    refine (hasDerivAt_const m K).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hm.1 hm.2] with t ht
    exact hconst t ht
  exact hd.unique h0

lemma accPt_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) : AccPt x (𝓟 (Icc a b)) := by
  rw [accPt_iff_frequently_nhdsNE]
  rcases lt_or_eq_of_le hx.2 with h | h
  · have : ∀ᶠ y in 𝓝[>] x, y ∈ Icc a b := by
      filter_upwards [Ioo_mem_nhdsGT h] with y hy
      exact ⟨hx.1.trans hy.1.le, hy.2.le⟩
    exact this.frequently.filter_mono (nhdsGT_le_nhdsNE x)
  · rw [h]
    have : ∀ᶠ y in 𝓝[<] b, y ∈ Icc a b := by
      filter_upwards [Ioo_mem_nhdsLT hab] with y hy
      exact ⟨hy.1.le, hy.2.le⟩
    exact this.frequently.filter_mono (nhdsLT_le_nhdsNE b)

end OneD

section Standing

lemma box_mem (M : Model) {r c : ℝ} (hr : r ∈ Icc M.rmin M.rmax) (hc : c ∈ Icc M.cmin M.cmax) :
    ((r, c) : ℝ × ℝ) ∈ M.box := ⟨hr, hc⟩

variable (M : Model) (hM : M.Standing)
include hM

lemma convex_c {r : ℝ} (hr : r ∈ Icc M.rmin M.rmax) :
    ConvexOn ℝ (Icc M.cmin M.cmax) (fun c => M.R r c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hconv, -, -⟩ := hM
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hconv.2 (x := (r, x)) (y := (r, y)) ⟨hr, hx⟩ ⟨hr, hy⟩ ha hb hab
  have e : a • ((r, x) : ℝ × ℝ) + b • (r, y) = (r, a • x + b • y) := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    · simp
  rw [e] at h
  simpa using h

lemma Rc_mono_c {r c1 c2 : ℝ} (hr : r ∈ Icc M.rmin M.rmax) (hc1 : c1 ∈ Icc M.cmin M.cmax)
    (hc2 : c2 ∈ Icc M.cmin M.cmax) (h12 : c1 ≤ c2) : M.Rc r c1 ≤ M.Rc r c2 := by
  have hcv := convex_c M hM hr
  obtain ⟨hr0, hrr, hr1, hc0, hcc, hlam, ⟨U, hUo, hBU, hCD⟩, -⟩ := hM
  rcases eq_or_lt_of_le h12 with h | h
  · rw [h]
  have d1 := (hasDerivAt_R_c M hUo hCD (hBU (box_mem M hr hc1))).differentiableAt
  have d2 := (hasDerivAt_R_c M hUo hCD (hBU (box_mem M hr hc2))).differentiableAt
  exact (hcv.deriv_le_slope hc1 hc2 h d1).trans (hcv.slope_le_deriv hc1 hc2 h d2)

lemma Rc_mono_r {c r1 r2 : ℝ} (hc : c ∈ Icc M.cmin M.cmax) (hr1 : r1 ∈ Icc M.rmin M.rmax)
    (hr2 : r2 ∈ Icc M.rmin M.rmax) (h12 : r1 ≤ r2) : M.Rc r1 c ≤ M.Rc r2 c := by
  obtain ⟨-, -, -, -, -, -, ⟨U, hUo, hBU, hCD⟩, -, -, -, -, hcr⟩ := hM
  have hmono : MonotoneOn (fun r => M.Rc r c) (Icc M.rmin M.rmax) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro r hr
      have := continuousAt_Rc M hUo hCD (hBU (box_mem M hr hc))
      exact (this.comp (continuous_id.prodMk continuous_const).continuousAt
        (x := r)).continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hasDerivAt_Rc_r M hUo hCD (hBU (box_mem M (Ioo_subset_Icc_self hr) hc))).differentiableAt
        |>.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hq := hBU (box_mem M (Ioo_subset_Icc_self hr) hc)
      rw [(hasDerivAt_Rc_r M hUo hCD hq).deriv, ← Rcr_eq M hUo hCD hq]
      exact hcr (r, c) (box_mem M (Ioo_subset_Icc_self hr) hc)
  exact hmono hr1 hr2 h12

lemma Rcc_pos {q : ℝ × ℝ} (hq : q ∈ M.box) : 0 < M.Rcc q.1 q.2 := by
  have hM' := hM
  obtain ⟨hr0, hrr, hr1, hc0, hcc, hlam, ⟨U, hUo, hBU, hCD⟩, -, -, -, hhess, -⟩ := hM'
  have hnn : 0 ≤ M.Rcc q.1 q.2 := by
    have hU : ((q.1, q.2) : ℝ × ℝ) ∈ U := hBU hq
    have hd := hasDerivAt_Rc_c M hUo hCD hU
    rw [← Rcc_eq M hUo hCD hU] at hd
    have hmono : MonotoneOn (fun s => M.Rc q.1 s) (Icc M.cmin M.cmax) :=
      fun x hx y hy hxy => Rc_mono_c M hM hq.1 hx hy hxy
    exact hd.hasDerivWithinAt.nonneg_of_monotoneOn (accPt_Icc hcc hq.2) hmono
  have h := hhess q hq
  rcases eq_or_lt_of_le hnn with h0 | h0
  · rw [← h0, mul_zero] at h
    nlinarith [sq_nonneg (M.Rrc q.1 q.2 + M.lam)]
  · exact h0

lemma Rrr_pos {q : ℝ × ℝ} (hq : q ∈ M.box) : 0 < M.Rrr q.1 q.2 := by
  have h1 := Rcc_pos M hM hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hhess, -⟩ := hM
  have h := hhess q hq
  have : 0 < M.Rrr q.1 q.2 * M.Rcc q.1 q.2 := lt_of_le_of_lt (sq_nonneg _) h
  exact pos_of_mul_pos_left this h1.le

end Standing

section Game

open Function

/-- Profit of a hospital deviating to `y` when every rival plays `p` (for two hospitals: when the
rival plays `p`). -/
noncomputable def Φ (M : Model) (p y : ℝ × ℝ) : ℝ :=
  p.2 * M.lam * (1 + y.1) - 1 / p.1 * (y.1 - p.1) * (1 + y.1) * p.2 * M.lam + M.R p.1 p.2
    - y.2 * (1 + y.1) * M.lam - M.R y.1 y.2

lemma Φ_self (M : Model) (p : ℝ × ℝ) : Φ M p p = 0 := by
  unfold Φ; ring

lemma sum_erase_update {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ) (g : ℝ × ℝ → ℝ) :
    ∑ k ∈ Finset.univ.erase i, g (update x i y k) = ∑ k ∈ Finset.univ.erase i, g (x k) :=
  Finset.sum_congr rfl (fun k hk => by rw [update_of_ne (Finset.ne_of_mem_erase hk)])

lemma profitI_update (M : Model) {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ) :
    M.profitI N (update x i y) i =
      cbar N x i * M.lam * (1 + y.1) - 1 / rbar N x i * (y.1 - rbar N x i) * (1 + y.1)
        * cbar N x i * M.lam + M.Rbar N x i - y.2 * (1 + y.1) * M.lam - M.R y.1 y.2 := by
  have h1 : cbar N (update x i y) i = cbar N x i := by
    unfold cbar; rw [sum_erase_update x i y (fun q => q.2)]
  have h2 : rbar N (update x i y) i = rbar N x i := by
    unfold rbar; rw [sum_erase_update x i y (fun q => q.1)]
  have h3 : M.Rbar N (update x i y) i = M.Rbar N x i := by
    unfold Model.Rbar; rw [sum_erase_update x i y (fun q => M.R q.1 q.2)]
  unfold Model.profitI Model.TI
  rw [h1, h2, h3, update_self]

lemma avg_const {N : ℕ} (hN : 2 ≤ N) (i : Fin N) (a : ℝ) :
    (1 / ((N : ℝ) - 1)) * ∑ _k ∈ Finset.univ.erase i, a = a := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N)]
  have : ((N : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  push_cast
  field_simp

lemma profit_sym_update (M : Model) {N : ℕ} (hN : 2 ≤ N) (p : ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ) :
    M.profitI N (update (fun _ => p) i y) i = Φ M p y := by
  rw [profitI_update]
  have h1 : cbar N (fun _ => p) i = p.2 := avg_const hN i p.2
  have h2 : rbar N (fun _ => p) i = p.1 := avg_const hN i p.1
  have h3 : M.Rbar N (fun _ => p) i = M.R p.1 p.2 := avg_const hN i _
  rw [h1, h2, h3]; rfl

lemma profit_sym (M : Model) {N : ℕ} (hN : 2 ≤ N) (p : ℝ × ℝ) (i : Fin N) :
    M.profitI N (fun _ => p) i = 0 := by
  have : (fun _ : Fin N => p) = update (fun _ => p) i p := by
    ext k <;> by_cases hk : k = i <;> simp [hk]
  rw [this, profit_sym_update M hN, Φ_self]

lemma isSymEqI_iff (M : Model) {N : ℕ} (hN : 2 ≤ N) (p : ℝ × ℝ) :
    M.IsSymEqI N p ↔ p ∈ M.box ∧ ∀ y ∈ M.box, Φ M p y ≤ 0 := by
  unfold Model.IsSymEqI Model.IsEqI CarbonDoubleCount.Planner.IsPureNash
  constructor
  · rintro ⟨hm, hd⟩
    refine ⟨hm ⟨0, by omega⟩, fun y hy => ?_⟩
    have := hd ⟨0, by omega⟩ y hy
    beta_reduce at this
    rwa [profit_sym_update M hN, profit_sym M hN] at this
  · rintro ⟨hm, hd⟩
    refine ⟨fun _ => hm, fun i y hy => ?_⟩
    beta_reduce
    rw [profit_sym_update M hN, profit_sym M hN]
    exact hd y hy

lemma cbar_two (x : Fin 2 → ℝ × ℝ) : cbar 2 x 0 = (x 1).2 ∧ cbar 2 x 1 = (x 0).2 := by
  have e0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  unfold cbar; rw [e0, e1]; norm_num

lemma rbar_two (x : Fin 2 → ℝ × ℝ) : rbar 2 x 0 = (x 1).1 ∧ rbar 2 x 1 = (x 0).1 := by
  have e0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  unfold rbar; rw [e0, e1]; norm_num

lemma Rbar_two (M : Model) (x : Fin 2 → ℝ × ℝ) :
    M.Rbar 2 x 0 = M.R (x 1).1 (x 1).2 ∧ M.Rbar 2 x 1 = M.R (x 0).1 (x 0).2 := by
  have e0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  unfold Model.Rbar; rw [e0, e1]; norm_num

lemma profit_two_update0 (M : Model) (x : Fin 2 → ℝ × ℝ) (y : ℝ × ℝ) :
    M.profitI 2 (update x 0 y) 0 = Φ M (x 1) y := by
  rw [profitI_update, (cbar_two x).1, (rbar_two x).1, (Rbar_two M x).1]; rfl

lemma profit_two_update1 (M : Model) (x : Fin 2 → ℝ × ℝ) (y : ℝ × ℝ) :
    M.profitI 2 (update x 1 y) 1 = Φ M (x 0) y := by
  rw [profitI_update, (cbar_two x).2, (rbar_two x).2, (Rbar_two M x).2]; rfl

end Game

section Deriv

lemma foc_int {f : ℝ → ℝ} {a b x d : ℝ} (hx : x ∈ Ioo a b) (hmax : ∀ y ∈ Icc a b, f y ≤ f x)
    (hd : HasDerivAt f d x) : d = 0 := by
  have h1 := foc_1d (Ioo_subset_Icc_self hx) hmax hd a ⟨le_rfl, (hx.1.trans hx.2).le⟩
  have h2 := foc_1d (Ioo_subset_Icc_self hx) hmax hd b ⟨(hx.1.trans hx.2).le, le_rfl⟩
  have ha := hx.1; have hb := hx.2
  rcases lt_trichotomy d 0 with h | h | h
  · nlinarith
  · exact h
  · nlinarith

variable (M : Model) (hM : M.Standing)
include hM

lemma hasDerivAt_Rc' {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ M.box) :
    HasDerivAt (fun s => M.R r s) (M.Rc r c) c := by
  obtain ⟨-, -, -, -, -, -, ⟨U, hUo, hBU, hCD⟩, -⟩ := hM
  have h := hasDerivAt_R_c M hUo hCD (hBU hq)
  rwa [← Rc_eq M hUo hCD (hBU hq)] at h

lemma hasDerivAt_Rr' {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ M.box) :
    HasDerivAt (fun s => M.R s c) (M.Rr r c) r := by
  obtain ⟨-, -, -, -, -, -, ⟨U, hUo, hBU, hCD⟩, -⟩ := hM
  have h := hasDerivAt_R_r M hUo hCD (hBU hq)
  rwa [← Rr_eq M hUo hCD (hBU hq)] at h

lemma hasDerivAt_cfun (A : ℝ) {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ M.box) :
    HasDerivAt (fun s => A - s * (1 + r) * M.lam - M.R r s) (-(1 + r) * M.lam - M.Rc r c) c := by
  have h1 : HasDerivAt (fun s : ℝ => s * (1 + r) * M.lam) (1 * (1 + r) * M.lam) c :=
    ((hasDerivAt_id' c).mul_const (1 + r)).mul_const M.lam
  have h := ((hasDerivAt_const c A).sub h1).sub (hasDerivAt_Rc' M hM hq)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_S_r {r c : ℝ} (hq : ((r, c) : ℝ × ℝ) ∈ M.box) :
    HasDerivAt (fun s => M.S s c) (-c * M.lam - M.Rr r c) r := by
  have h1 : HasDerivAt (fun s : ℝ => c * (1 + s) * M.lam) (c * 1 * M.lam) r :=
    (((hasDerivAt_id' r).const_add 1).const_mul c).mul_const M.lam
  have h := ((hasDerivAt_const r M.V).sub h1).sub (hasDerivAt_Rr' M hM hq)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_Φ_r {p : ℝ × ℝ} (hp : p ∈ M.box) (hp1 : p.1 ≠ 0) :
    HasDerivAt (fun s => Φ M p (s, p.2)) (-(1 + p.1) * p.2 * M.lam / p.1 - M.Rr p.1 p.2) p.1 := by
  have h1 : HasDerivAt (fun s : ℝ => p.2 * M.lam * (1 + s)) (p.2 * M.lam * 1) p.1 :=
    ((hasDerivAt_id' p.1).const_add 1).const_mul (p.2 * M.lam)
  have h2 : HasDerivAt (fun s : ℝ => 1 / p.1 * (s - p.1) * (1 + s) * p.2 * M.lam)
      ((1 / p.1 * 1 * (1 + p.1) + 1 / p.1 * (p.1 - p.1) * 1) * p.2 * M.lam) p.1 :=
    (((((hasDerivAt_id' p.1).sub_const p.1).const_mul (1 / p.1)).mul
      ((hasDerivAt_id' p.1).const_add 1)).mul_const p.2).mul_const M.lam
  have h3 : HasDerivAt (fun s : ℝ => p.2 * (1 + s) * M.lam) (p.2 * 1 * M.lam) p.1 :=
    (((hasDerivAt_id' p.1).const_add 1).const_mul p.2).mul_const M.lam
  have h := (((h1.sub h2).add_const (M.R p.1 p.2)).sub h3).sub (hasDerivAt_Rr' M hM hp)
  exact h.congr_deriv (by field_simp; ring)

/-- First-order condition in `c` (over the interval) at readmission rate `r`. -/
def cFOC (r c : ℝ) : Prop :=
  c ∈ Icc M.cmin M.cmax ∧ ∀ c' ∈ Icc M.cmin M.cmax, (-(1 + r) * M.lam - M.Rc r c) * (c' - c) ≤ 0

omit hM in
lemma cFOC_def (r c : ℝ) : cFOC M r c ↔
    (c ∈ Icc M.cmin M.cmax ∧ ∀ c' ∈ Icc M.cmin M.cmax,
      (-(1 + r) * M.lam - M.Rc r c) * (c' - c) ≤ 0) := Iff.rfl

lemma cFOC_of_max {r c : ℝ} (hr : r ∈ Icc M.rmin M.rmax) (hc : c ∈ Icc M.cmin M.cmax) (A : ℝ)
    (hmax : ∀ c' ∈ Icc M.cmin M.cmax,
      A - c' * (1 + r) * M.lam - M.R r c' ≤ A - c * (1 + r) * M.lam - M.R r c) :
    cFOC M r c :=
  ⟨hc, foc_1d (f := fun s => A - s * (1 + r) * M.lam - M.R r s) hc hmax
    (hasDerivAt_cfun M hM A (box_mem M hr hc))⟩

lemma cFOC_unique_aux {r c1 c2 : ℝ} (hr : r ∈ Icc M.rmin M.rmax) (h1 : cFOC M r c1)
    (h2 : cFOC M r c2) (h : c1 < c2) : False := by
  have a1 := h1.2 c2 h2.1
  have a2 := h2.2 c1 h1.1
  have e1 : -(1 + r) * M.lam - M.Rc r c1 ≤ 0 := by
    by_contra hh; push Not at hh; nlinarith
  have e2 : 0 ≤ -(1 + r) * M.lam - M.Rc r c2 := by
    by_contra hh; push Not at hh; nlinarith
  have hc1 := h1.1; have hc2 := h2.1
  have hconst : ∀ s ∈ Icc c1 c2, M.Rc r s = M.Rc r c1 := by
    intro s hs
    have hs' : s ∈ Icc M.cmin M.cmax := ⟨hc1.1.trans hs.1, hs.2.trans hc2.2⟩
    have m1 := Rc_mono_c M hM hr hc1 hs' hs.1
    have m2 := Rc_mono_c M hM hr hs' hc2 hs.2
    linarith
  set m := (c1 + c2) / 2 with hm
  have hmI : m ∈ Ioo c1 c2 := ⟨by linarith, by linarith⟩
  have hmb : ((r, m) : ℝ × ℝ) ∈ M.box := box_mem M hr ⟨by linarith [hc1.1], by linarith [hc2.2]⟩
  have hpos := Rcc_pos M hM hmb
  obtain ⟨-, -, -, -, -, -, ⟨U, hUo, hBU, hCD⟩, -⟩ := hM
  have hd := hasDerivAt_Rc_c M hUo hCD (hBU hmb)
  rw [← Rcc_eq M hUo hCD (hBU hmb)] at hd
  have := deriv_zero_of_const hd hconst hmI
  simp only at hpos
  linarith

lemma cFOC_unique {r c1 c2 : ℝ} (hr : r ∈ Icc M.rmin M.rmax) (h1 : cFOC M r c1)
    (h2 : cFOC M r c2) : c1 = c2 := by
  rcases lt_trichotomy c1 c2 with h | h | h
  · exact (cFOC_unique_aux M hM hr h1 h2 h).elim
  · exact h
  · exact (cFOC_unique_aux M hM hr h2 h1 h).elim

lemma c_order {r1 r2 c1 c2 : ℝ} (hr1 : r1 ∈ Icc M.rmin M.rmax) (hr2 : r2 ∈ Icc M.rmin M.rmax)
    (h12 : r2 < r1) (h1 : cFOC M r1 c1) (h2 : cFOC M r2 c2) : c1 ≤ c2 := by
  by_contra h; push Not at h
  have a1 := h1.2 c2 h2.1
  have a2 := h2.2 c1 h1.1
  have e1 : 0 ≤ -(1 + r1) * M.lam - M.Rc r1 c1 := by
    by_contra hh; push Not at hh; nlinarith
  have e2 : -(1 + r2) * M.lam - M.Rc r2 c2 ≤ 0 := by
    by_contra hh; push Not at hh; nlinarith
  have m1 := Rc_mono_c M hM hr1 h2.1 h1.1 h.le
  have m2 := Rc_mono_r M hM h2.1 hr2 hr1 h12.le
  have hlam := hM.2.2.2.2.2.1
  nlinarith

end Deriv

section Ordering

theorem ordering (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ p : ℝ × ℝ, M.IsSymEqI N p →
      ∀ xs : ℝ × ℝ, M.IsFirstBest xs → p.1 < xs.1 ∧ xs.2 < p.2 := by
  intro p hp xs hxs
  rw [isSymEqI_iff M hN] at hp
  obtain ⟨hpb, hdev⟩ := hp
  have hM' := hM
  obtain ⟨hr0, hrr, hr1, hc0, hcc, hlam, -⟩ := hM'
  have hp1pos : 0 < p.1 := lt_of_lt_of_le hr0 hpb.1.1
  have hp1lt1 : p.1 < 1 := lt_of_le_of_lt hpb.1.2 hr1
  have hp2nn : 0 ≤ p.2 := le_trans hc0 hpb.2.1
  have hxsb := hxs.1
  obtain ⟨hxr, hxc⟩ := hA xs hxs
  have hx1pos : 0 < xs.1 := lt_of_lt_of_le hr0 hxsb.1.1
  have hr_lt : p.1 < xs.1 := by
    by_contra hcon; push Not at hcon
    have hS := hxs.2 p hpb
    have hΦ := hdev xs hxsb
    have hid : Φ M p xs = (M.S xs.1 xs.2 - M.S p.1 p.2)
        + p.2 * M.lam * (p.1 - xs.1) * (1 + xs.1 - p.1) / p.1 := by
      unfold Φ Model.S; field_simp; ring
    have hnn : 0 ≤ p.2 * M.lam * (p.1 - xs.1) * (1 + xs.1 - p.1) / p.1 := by
      apply div_nonneg _ hp1pos.le
      apply mul_nonneg (mul_nonneg (mul_nonneg hp2nn hlam.le) (by linarith)) (by linarith)
    have hpfb : M.IsFirstBest p := ⟨hpb, fun y hy => (hxs.2 y hy).trans (by linarith)⟩
    obtain ⟨hpr, hpc⟩ := hA p hpfb
    have d1 : -p.2 * M.lam - M.Rr p.1 p.2 = 0 :=
      foc_int (f := fun s => M.S s p.2) hpr (fun y hy => hpfb.2 (y, p.2) ⟨hy, hpb.2⟩)
        (hasDerivAt_S_r M hM hpb)
    have d2 : -(1 + p.1) * p.2 * M.lam / p.1 - M.Rr p.1 p.2 = 0 := by
      refine foc_int (f := fun s => Φ M p (s, p.2)) hpr (fun y hy => ?_)
        (hasDerivAt_Φ_r M hM hpb hp1pos.ne')
      have := hdev (y, p.2) ⟨hy, hpb.2⟩
      have e : Φ M p (p.1, p.2) = 0 := Φ_self M p
      show Φ M p (y, p.2) ≤ Φ M p (p.1, p.2)
      linarith
    have e : -(1 + p.1) * p.2 * M.lam / p.1 = -p.2 * M.lam - p.2 * M.lam / p.1 := by
      field_simp; ring
    have h0 : p.2 * M.lam / p.1 = 0 := by linarith
    have h00 : p.2 = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · linarith
      · linarith
    linarith [hpc.1]
  have hc_lt : xs.2 < p.2 := by
    by_contra hcon; push Not at hcon
    have d1 : -(1 + xs.1) * M.lam - M.Rc xs.1 xs.2 = 0 :=
      foc_int (f := fun s => M.V - s * (1 + xs.1) * M.lam - M.R xs.1 s) hxc
        (fun y hy => hxs.2 (xs.1, y) ⟨hxsb.1, hy⟩) (hasDerivAt_cfun M hM M.V hxsb)
    have hcf : cFOC M p.1 p.2 := by
      refine cFOC_of_max M hM hpb.1 hpb.2
        (p.2 * M.lam * (1 + p.1) - 1 / p.1 * (p.1 - p.1) * (1 + p.1) * p.2 * M.lam
          + M.R p.1 p.2) (fun c' hc' => ?_)
      have := hdev (p.1, c') ⟨hpb.1, hc'⟩
      have e : Φ M p p = 0 := Φ_self M p
      unfold Φ at this e
      simp only at this
      linarith
    have t := hcf.2 M.cmax ⟨hcc.le, le_rfl⟩
    have hgap : 0 < M.cmax - p.2 := by linarith [hxc.2]
    have e1 : -(1 + p.1) * M.lam - M.Rc p.1 p.2 ≤ 0 := by
      by_contra hh; push Not at hh; nlinarith
    have m1 := Rc_mono_c M hM hpb.1 hpb.2 hxsb.2 hcon
    have m2 := Rc_mono_r M hM hxsb.2 hpb.1 hxsb.1 hr_lt.le
    nlinarith
  exact ⟨hr_lt, hc_lt⟩

end Ordering

section Two

variable (M : Model) (hM : M.Standing)
include hM

lemma pair_asym {P Q : ℝ × ℝ} (hP : P ∈ M.box) (hQ : Q ∈ M.box) (h12 : Q.1 < P.1)
    (h1 : 0 ≤ Φ M Q P) (h2 : 0 ≤ Φ M P Q) (f1 : cFOC M P.1 P.2) (f2 : cFOC M Q.1 Q.2) : False := by
  have hc : P.2 ≤ Q.2 := c_order M hM hP.1 hQ.1 h12 f1 f2
  have hM' := hM
  obtain ⟨hr0, hrr, hr1, hc0, hcc, hlam, ⟨U, hUo, hBU, hCD⟩, hantr, -⟩ := hM'
  have hQ1 : 0 < Q.1 := lt_of_lt_of_le hr0 hQ.1.1
  have hP1 : 0 < P.1 := lt_of_lt_of_le hr0 hP.1.1
  have hP1' : P.1 < 1 := lt_of_le_of_lt hP.1.2 hr1
  have hQ1' : Q.1 < 1 := lt_of_le_of_lt hQ.1.2 hr1
  have hP2 : 0 ≤ P.2 := le_trans hc0 hP.2.1
  by_cases hc2 : 0 < Q.2
  · have hsum : (Φ M Q P + Φ M P Q) * (P.1 * Q.1) = (P.1 - Q.1) * M.lam *
        (P.2 * Q.1 * (1 + Q.1 - P.1) - Q.2 * P.1 * (1 + P.1 - Q.1)) := by
      unfold Φ; field_simp; ring
    have k1 : P.2 * Q.1 * (1 + Q.1 - P.1) ≤ Q.2 * Q.1 * (1 + Q.1 - P.1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hQ1.le) (by linarith)
    have k2e : Q.2 * P.1 * (1 + P.1 - Q.1) - Q.2 * Q.1 * (1 + Q.1 - P.1)
        = Q.2 * (P.1 - Q.1) * (1 + P.1 + Q.1) := by ring
    have k2p : 0 < Q.2 * (P.1 - Q.1) * (1 + P.1 + Q.1) :=
      mul_pos (mul_pos hc2 (by linarith)) (by linarith)
    have hneg : (P.1 - Q.1) * M.lam *
        (P.2 * Q.1 * (1 + Q.1 - P.1) - Q.2 * P.1 * (1 + P.1 - Q.1)) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) hlam) (by linarith)
    have hpos : 0 ≤ (Φ M Q P + Φ M P Q) * (P.1 * Q.1) :=
      mul_nonneg (by linarith) (mul_pos hP1 hQ1).le
    linarith
  · have hQ2 : Q.2 = M.cmin := le_antisymm (by linarith [hQ.2.1]) hQ.2.1
    have hPQ : P.2 = Q.2 := le_antisymm hc (hQ2 ▸ hP.2.1)
    have hz : Q.2 = 0 := by linarith [hQ.2.1]
    have e1 : Φ M Q P = M.R Q.1 Q.2 - M.R P.1 Q.2 := by
      unfold Φ; rw [hPQ, hz]; ring
    have e2 : Φ M P Q = M.R P.1 Q.2 - M.R Q.1 Q.2 := by
      unfold Φ; rw [hPQ, hz]; ring
    have hcQ : Q.2 ∈ Icc M.cmin M.cmax := hQ.2
    have hconst : ∀ s ∈ Icc Q.1 P.1, M.R s Q.2 = M.R Q.1 Q.2 := by
      intro s hs
      have hsI : s ∈ Icc M.rmin M.rmax := ⟨hQ.1.1.trans hs.1, hs.2.trans hP.1.2⟩
      have a1 := hantr Q.2 hcQ hQ.1 hsI hs.1
      have a2 := hantr Q.2 hcQ hsI hP.1 hs.2
      simp only at a1 a2
      linarith
    have hRr0 : ∀ t ∈ Ioo Q.1 P.1, M.Rr t Q.2 = 0 := by
      intro t ht
      have htI : t ∈ Icc M.rmin M.rmax := ⟨hQ.1.1.trans ht.1.le, ht.2.le.trans hP.1.2⟩
      exact deriv_zero_of_const (hasDerivAt_Rr' M hM (box_mem M htI hcQ)) hconst ht
    set m := (Q.1 + P.1) / 2 with hm
    have hmI : m ∈ Icc M.rmin M.rmax := ⟨by linarith [hQ.1.1], by linarith [hP.1.2]⟩
    have hmb : ((m, Q.2) : ℝ × ℝ) ∈ M.box := box_mem M hmI hcQ
    have hconst2 : ∀ t ∈ Icc ((Q.1 + m) / 2) ((m + P.1) / 2), M.Rr t Q.2 = 0 := by
      intro t ht
      exact hRr0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hd := hasDerivAt_Rr_r M hUo hCD (hBU hmb)
    rw [← Rrr_eq M hUo hCD (hBU hmb)] at hd
    have h0 := deriv_zero_of_const hd hconst2 ⟨by linarith, by linarith⟩
    have hpos := Rrr_pos M hM hmb
    simp only at hpos
    linarith

lemma pair_eq {P Q : ℝ × ℝ} (hP : P ∈ M.box) (hQ : Q ∈ M.box)
    (h1 : 0 ≤ Φ M Q P) (h2 : 0 ≤ Φ M P Q) (f1 : cFOC M P.1 P.2) (f2 : cFOC M Q.1 Q.2) : P = Q := by
  rcases lt_trichotomy P.1 Q.1 with h | h | h
  · exact (pair_asym M hM hQ hP h h2 h1 f2 f1).elim
  · have f2' : cFOC M P.1 Q.2 := h ▸ f2
    exact Prod.ext h (cFOC_unique M hM hP.1 f1 f2')
  · exact (pair_asym M hM hP hQ h h1 h2 f1 f2).elim

omit hM in
lemma eqI_two_dev (x : Fin 2 → ℝ × ℝ) (h : M.IsEqI 2 x) :
    x 0 ∈ M.box ∧ x 1 ∈ M.box ∧ (∀ y ∈ M.box, Φ M (x 1) y ≤ Φ M (x 1) (x 0)) ∧
      (∀ y ∈ M.box, Φ M (x 0) y ≤ Φ M (x 0) (x 1)) := by
  unfold Model.IsEqI CarbonDoubleCount.Planner.IsPureNash at h
  obtain ⟨hm, hd⟩ := h
  have p0 : M.profitI 2 x 0 = Φ M (x 1) (x 0) := by
    rw [← profit_two_update0 M x (x 0), Function.update_eq_self]
  have p1 : M.profitI 2 x 1 = Φ M (x 0) (x 1) := by
    rw [← profit_two_update1 M x (x 1), Function.update_eq_self]
  refine ⟨hm 0, hm 1, fun y hy => ?_, fun y hy => ?_⟩
  · have := hd 0 y hy
    beta_reduce at this
    rwa [profit_two_update0, p0] at this
  · have := hd 1 y hy
    beta_reduce at this
    rwa [profit_two_update1, p1] at this

theorem two_hospitals : ∀ x : Fin 2 → ℝ × ℝ, M.IsEqI 2 x → x 0 = x 1 := by
  intro x h
  obtain ⟨ha, hb, d0, d1⟩ := eqI_two_dev M x h
  have h1 : 0 ≤ Φ M (x 1) (x 0) := by have := d0 (x 1) hb; rwa [Φ_self] at this
  have h2 : 0 ≤ Φ M (x 0) (x 1) := by have := d1 (x 0) ha; rwa [Φ_self] at this
  have f1 : cFOC M (x 0).1 (x 0).2 :=
    cFOC_of_max M hM ha.1 ha.2 ((x 1).2 * M.lam * (1 + (x 0).1)
      - 1 / (x 1).1 * ((x 0).1 - (x 1).1) * (1 + (x 0).1) * (x 1).2 * M.lam
      + M.R (x 1).1 (x 1).2) (fun c' hc' => d0 ((x 0).1, c') ⟨ha.1, hc'⟩)
  have f2 : cFOC M (x 1).1 (x 1).2 :=
    cFOC_of_max M hM hb.1 hb.2 ((x 0).2 * M.lam * (1 + (x 1).1)
      - 1 / (x 0).1 * ((x 1).1 - (x 0).1) * (1 + (x 1).1) * (x 0).2 * M.lam
      + M.R (x 0).1 (x 0).2) (fun c' hc' => d1 ((x 1).1, c') ⟨hb.1, hc'⟩)
  exact pair_eq M hM ha hb h1 h2 f1 f2

end Two

end HRRPAux

open ReadmissionsHRRP.HRRPI in
theorem solution (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ p : ℝ × ℝ, M.IsSymEqI N p →
      ∀ xs : ℝ × ℝ, M.IsFirstBest xs → p.1 < xs.1 ∧ xs.2 < p.2 :=
  HRRPAux.ordering M hM hA N hN
