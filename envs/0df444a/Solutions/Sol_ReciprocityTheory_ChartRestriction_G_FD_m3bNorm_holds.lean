-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.m3bNorm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:35:34.707306+00:00
-- url     : https://prove2.me/submissions/88d20111-1aaa-40fb-ab7f-c08091737f13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TelescopingWeightedSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hG_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_down
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
  ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
private theorem log_min_max {q : ℝ} (hq : 0 < q) :
    Real.log (min q q⁻¹) = -|Real.log q| ∧ Real.log (max q q⁻¹) = |Real.log q| := by
  have hqi : 0 < q⁻¹ := inv_pos.mpr hq
  rcases le_total q q⁻¹ with h | h
  · have hl : Real.log q ≤ 0 := by
      have h1 := Real.log_le_log hq h
      rw [Real.log_inv] at h1
      linarith
    rw [min_eq_left h, max_eq_right h, Real.log_inv, abs_of_nonpos hl]
    constructor <;> ring
  · have hl : 0 ≤ Real.log q := by
      have h1 := Real.log_le_log hqi h
      rw [Real.log_inv] at h1
      linarith
    rw [min_eq_right h, max_eq_left h, Real.log_inv, abs_of_nonneg hl]
    constructor <;> ring
private theorem mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen {r p0 : ℕ} (hp0 : p0 ≤ r) (L l : ℕ → ℝ) (hL0 : L 0 = 0) (hLr : L r = 0)
    (hmono : ((∀ i, i < p0 → L i ≤ L (i + 1)) ∧ (∀ i, p0 ≤ i → i < r → L (i + 1) ≤ L i)) ∨
      ((∀ i, i < p0 → L (i + 1) ≤ L i) ∧ (∀ i, p0 ≤ i → i < r → L i ≤ L (i + 1))))
    (M μ : ℝ) (hl : ∀ i, i < r → μ ≤ l i ∧ l i ≤ M) :
    |∑ i ∈ Finset.range r, l i * (L (i + 1) - L i)| ≤ (M - μ) * |L p0| := by
  have htel : ∀ n, ∑ i ∈ Finset.range n, (L (i + 1) - L i) = L n - L 0 :=
    fun n => Finset.sum_range_sub L n
  have hsplit : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.range r, f i =
      ∑ i ∈ Finset.range p0, f i + ∑ i ∈ Finset.Ico p0 r, f i :=
    fun f => (Finset.sum_range_add_sum_Ico f hp0).symm
  have hIco : ∑ i ∈ Finset.Ico p0 r, (L (i + 1) - L i) = L r - L p0 := by
    have h1 := hsplit (fun i => L (i + 1) - L i)
    rw [htel r, htel p0] at h1
    linarith
  have hvar : ∑ i ∈ Finset.range r, |L (i + 1) - L i| = 2 * |L p0| := by
    rw [hsplit]
    rcases hmono with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : ∑ i ∈ Finset.range p0, |L (i + 1) - L i| = ∑ i ∈ Finset.range p0, (L (i + 1) - L i) :=
        Finset.sum_congr rfl fun i hi => abs_of_nonneg (sub_nonneg.2 (h1 i (Finset.mem_range.mp hi)))
      have e2 : ∑ i ∈ Finset.Ico p0 r, |L (i + 1) - L i| = ∑ i ∈ Finset.Ico p0 r, -(L (i + 1) - L i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [Finset.mem_Ico] at hi
          exact abs_of_nonpos (sub_nonpos.2 (h2 i hi.1 hi.2))
      rw [e1, e2, Finset.sum_neg_distrib, htel p0, hIco, hL0, hLr]
      have hp : 0 ≤ L p0 := by
        have h3 := Finset.sum_nonneg fun i (hi : i ∈ Finset.range p0) => sub_nonneg.2 (h1 i (Finset.mem_range.mp hi))
        rw [htel p0, hL0, sub_zero] at h3
        exact h3
      rw [abs_of_nonneg hp]
      ring
    · have e1 : ∑ i ∈ Finset.range p0, |L (i + 1) - L i| = ∑ i ∈ Finset.range p0, -(L (i + 1) - L i) :=
        Finset.sum_congr rfl fun i hi => abs_of_nonpos (sub_nonpos.2 (h1 i (Finset.mem_range.mp hi)))
      have e2 : ∑ i ∈ Finset.Ico p0 r, |L (i + 1) - L i| = ∑ i ∈ Finset.Ico p0 r, (L (i + 1) - L i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [Finset.mem_Ico] at hi
          exact abs_of_nonneg (sub_nonneg.2 (h2 i hi.1 hi.2))
      rw [e1, e2, Finset.sum_neg_distrib, htel p0, hIco, hL0, hLr]
      have hp : L p0 ≤ 0 := by
        have h3 := Finset.sum_nonpos fun i (hi : i ∈ Finset.range p0) => sub_nonpos.2 (h1 i (Finset.mem_range.mp hi))
        rw [htel p0, hL0, sub_zero] at h3
        exact h3
      rw [abs_of_nonpos hp]
      ring
  have hshift : ∑ i ∈ Finset.range r, l i * (L (i + 1) - L i) =
      ∑ i ∈ Finset.range r, (l i - (M + μ) / 2) * (L (i + 1) - L i) := by
    have h0 : ∑ i ∈ Finset.range r, (M + μ) / 2 * (L (i + 1) - L i) = 0 := by
      rw [← Finset.mul_sum, htel r, hL0, hLr, sub_zero, mul_zero]
    simp only [sub_mul, Finset.sum_sub_distrib, h0, sub_zero]
  rw [hshift]
  calc |∑ i ∈ Finset.range r, (l i - (M + μ) / 2) * (L (i + 1) - L i)|
      ≤ ∑ i ∈ Finset.range r, |(l i - (M + μ) / 2) * (L (i + 1) - L i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range r, (M - μ) / 2 * |L (i + 1) - L i| := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        obtain ⟨h1, h2⟩ := hl i (Finset.mem_range.mp hi)
        rw [abs_le]
        constructor <;> linarith
    _ = (M - μ) * |L p0| := by
        rw [← Finset.mul_sum, hvar]
        ring
private theorem ratio_tau {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e)
    (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom)
    (τ : X.Ψ) :
    0 ≤ min (1 + (s τ).im / X.ttV e x τ) (1 + (s τ).im / X.ttV e x τ)⁻¹ ^ (X.spread la τ / 2) ∧
    min (1 + (s τ).im / X.ttV e x τ) (1 + (s τ).im / X.ttV e x τ)⁻¹ ^ (X.spread la τ / 2) ≤
      (∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
        ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2)) ∧
    (∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
        ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2)) ≤
      max (1 + (s τ).im / X.ttV e x τ) (1 + (s τ).im / X.ttV e x τ)⁻¹ ^ (X.spread la τ / 2) := by
  classical
  have he0 : hermC τ.1 X.Gm (e τ) (e τ) = 0 := (he τ).1
  have hx' : ∀ τ' : X.Ψ, (mat x τ').det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ' i).re := hx
  have hT' : ∀ τ' : X.Ψ, (mat (X.flowV e s x) τ').det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ' i).re := hT
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, m = fun i => mN τ.1 X.Gm (mat x τ) (e τ) i := ⟨_, rfl⟩
  have hm' : ∀ i, m i = mN τ.1 X.Gm (mat x τ) (e τ) i := fun i => by rw [hm]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => 1 + 2 * X.c τ * (s τ).im * m i := ⟨_, rfl⟩
  have ha' : ∀ i, a i = 1 + 2 * X.c τ * (s τ).im * m i := fun i => by rw [ha]
  have hd' : ∀ i : Fin (r + 1),
      dmin X.Gm (X.flowV e s x) τ i = dmin X.Gm x τ i * ((a i : ℝ) : ℂ) := by
    intro i
    rw [dmin_eq, dmin_eq, dmin_flow (X := X) (he := he0) (s := s) (i := (i : ℕ)) (h := Nat.le_of_lt_succ i.isLt) .., ha', hm']
    all_goals first | exact hx | exact hT
  have hapos : ∀ i : ℕ, i ≤ r → 0 < a i := by
    intro i hi
    have h1 := (hx' τ).2 ⟨i, Nat.lt_succ_of_le hi⟩
    have h2 := (hT' τ).2 ⟨i, Nat.lt_succ_of_le hi⟩
    rw [hd'] at h2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Fin.val_mk] at h1 h2
    by_contra hle
    push_neg at hle
    nlinarith [mul_le_mul_of_nonneg_left hle h1.le]
  have hdne : ∀ i : Fin (r + 1), dmin X.Gm x τ i ≠ 0 := by
    intro i h
    have h1 := (hx' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  have hfac : ∀ i : Fin r,
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
        ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) = (a (i + 1) / a i) ^ ((la τ i : ℝ) / 2) := by
    intro i
    have hs := hapos (i + 1) i.isLt
    have hc := hapos i i.isLt.le
    have hX : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
      norm_pos_iff.mpr (div_ne_zero (hdne _) (hdne _))
    have hY : 0 < a (i + 1) / a i := div_pos hs hc
    rw [hd', hd', mul_div_mul_comm, ← Complex.ofReal_div, norm_mul, Complex.norm_real]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [Real.norm_of_nonneg hY.le, Real.mul_rpow hX.le hY.le, div_mul_eq_div_div, div_self (Real.rpow_pos_of_pos hX _).ne', one_div,
      ← Real.rpow_neg hY.le]
    congr 1
    ring
  have hq : 1 + (s τ).im / X.ttV e x τ = a X.p0 := by
    rw [ha', hm']
    unfold Data.ttV
    rw [div_div_eq_mul_div, div_one, maj_eq (X := X) (he := he0) ..]
    · ring
    all_goals first | exact hx | exact hT
  simp only [hfac]
  rw [hq]
  have hq0 : 0 < a X.p0 := hapos _ X.p0_le
  have hPpos : 0 < ∏ i : Fin r, (a (i + 1) / a i) ^ ((la τ i : ℝ) / 2) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (div_pos (hapos _ i.isLt) (hapos _ i.isLt.le)) _
  obtain ⟨l, hl⟩ : ∃ l : ℕ → ℝ, l = fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0 := ⟨_, rfl⟩
  have hli : ∀ i : Fin r, l i = (la τ i : ℝ) := by
    intro i
    rw [hl]
    simp [i.isLt]
  have hlogP : Real.log (∏ i : Fin r, (a (i + 1) / a i) ^ ((la τ i : ℝ) / 2)) =
      (∑ k ∈ Finset.range r, l k * (Real.log (a (k + 1)) - Real.log (a k))) / 2 := by
    rw [Real.log_prod (fun i _ =>
      (Real.rpow_pos_of_pos (div_pos (hapos _ i.isLt) (hapos _ i.isLt.le)) _).ne')]
    rw [Finset.sum_div,
      ← Fin.sum_univ_eq_sum_range (fun k => l k * (Real.log (a (k + 1)) - Real.log (a k)) / 2) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (div_pos (hapos _ i.isLt) (hapos _ i.isLt.le)),
      Real.log_div (hapos _ i.isLt).ne' (hapos _ i.isLt.le).ne', hli i]
    ring
  have hlb : ∀ k, k < r → (⨅ i, (la τ i : ℝ)) ≤ l k ∧ l k ≤ ⨆ i, (la τ i : ℝ) := by
    intro k hk
    have h1 := hli ⟨k, hk⟩
    simp only [Fin.val_mk] at h1
    rw [h1]
    exact ⟨ciInf_le (Finite.bddBelow_range _) _, le_ciSup (Finite.bddAbove_range (fun i => (la τ i : ℝ))) ⟨k, hk⟩⟩
  have hxg : ∀ (i : ℕ) (h : i ≤ r),
      0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
    intro i h
    have h1 := (hx' τ).2 ⟨i, Nat.lt_succ_of_le h⟩
    rw [dmin_eq] at h1
    exact h1
  have hL0 : Real.log (a 0) = 0 := by
    rw [ha', hm', mN_zero, mul_zero, add_zero, Real.log_one]
  have hLr : Real.log (a r) = 0 := by
    rw [ha', hm', mN_top (e := e τ) (p0 := X.p0) .., mul_zero, add_zero, Real.log_one]
    all_goals first | exact hxg | exact hG_of (X := X) τ | exact X.signature τ | exact X.p0_le | exact (hx' τ).1 | exact hx | exact he0
  have hL : ∀ i j, i ≤ r → j ≤ r → m i ≤ m j →
      ((0 ≤ 2 * X.c τ * (s τ).im → Real.log (a i) ≤ Real.log (a j)) ∧
        (2 * X.c τ * (s τ).im ≤ 0 → Real.log (a j) ≤ Real.log (a i))) := by
    intro i j hi hj hmij
    constructor
    · intro hκ
      apply Real.log_le_log (hapos i hi)
      rw [ha', ha']
      nlinarith [mul_nonneg hκ (sub_nonneg.2 hmij)]
    · intro hκ
      apply Real.log_le_log (hapos j hj)
      rw [ha', ha']
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hκ (sub_nonpos.2 hmij)]
  have hup : ∀ i, i < X.p0 → m i ≤ m (i + 1) := by
    intro i hi
    rw [hm', hm']
    apply mN_up (p0 := X.p0) (j := i + 1) (hj := hi) (i := i) (hi := Nat.le_succ i)
    all_goals first | exact hxg | exact hG_of (X := X) τ | exact X.signature τ | exact X.p0_le | exact (hx' τ).1 | exact hx | exact he0
  have hdown : ∀ i, X.p0 ≤ i → i < r → m (i + 1) ≤ m i := by
    intro i hi hir
    rw [hm', hm']
    apply mN_down (p0 := X.p0) (i := i) (hi := hi) (j := i + 1) (hij := Nat.le_succ i) (hj := hir)
    all_goals first | exact hxg | exact hG_of (X := X) τ | exact X.signature τ | exact X.p0_le | exact (hx' τ).1 | exact hx | exact he0
  have hp0r := X.p0_le
  have hmono : ((∀ i, i < X.p0 → Real.log (a i) ≤ Real.log (a (i + 1))) ∧
        (∀ i, X.p0 ≤ i → i < r → Real.log (a (i + 1)) ≤ Real.log (a i))) ∨
      ((∀ i, i < X.p0 → Real.log (a (i + 1)) ≤ Real.log (a i)) ∧
        (∀ i, X.p0 ≤ i → i < r → Real.log (a i) ≤ Real.log (a (i + 1)))) := by
    rcases le_total 0 (2 * X.c τ * (s τ).im) with hκ | hκ
    · left
      exact ⟨fun i hi => (hL i (i + 1) (by omega) (by omega) (hup i hi)).1 hκ,
        fun i hi hir => (hL (i + 1) i hir (by omega) (hdown i hi hir)).1 hκ⟩
    · right
      exact ⟨fun i hi => (hL i (i + 1) (by omega) (by omega) (hup i hi)).2 hκ,
        fun i hi hir => (hL (i + 1) i hir (by omega) (hdown i hi hir)).2 hκ⟩
  have hbound := mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen X.p0_le (fun k => Real.log (a k)) l hL0 hLr hmono
    (⨆ i, (la τ i : ℝ)) (⨅ i, (la τ i : ℝ)) hlb
  have hsp : X.spread la τ = (⨆ i, (la τ i : ℝ)) - ⨅ i, (la τ i : ℝ) := rfl
  obtain ⟨hmin, hmax⟩ := log_min_max hq0
  have hminpos : 0 < min (a X.p0) (a X.p0)⁻¹ := lt_min hq0 (inv_pos.mpr hq0)
  have hmaxpos : 0 < max (a X.p0) (a X.p0)⁻¹ := lt_max_of_lt_left hq0
  rw [abs_le] at hbound
  refine ⟨(Real.rpow_pos_of_pos hminpos _).le, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hminpos, ← Real.exp_log hPpos, Real.exp_le_exp, hlogP, hmin, hsp]
    nlinarith [hbound.1]
  · rw [Real.rpow_def_of_pos hmaxpos, ← Real.exp_log hPpos, Real.exp_le_exp, hlogP, hmax, hsp]
    nlinarith [hbound.2]
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
  ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : FlowNormRatio (E := E) := by
  intro r X e he la x hx s hT
  dsimp only
  have key : X.nfac la x / X.nfac la (X.flowV e s x) =
      ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
        ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) := by
    unfold Data.nfac
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_div_distrib]
  rw [key]
  constructor
  · exact Finset.prod_le_prod (fun τ _ => (ratio_tau X e he la hx s hT τ).1)
      (fun τ _ => (ratio_tau X e he la hx s hT τ).2.1)
  · exact Finset.prod_le_prod
      (fun τ _ => (ratio_tau X e he la hx s hT τ).1.trans (ratio_tau X e he la hx s hT τ).2.1)
      (fun τ _ => (ratio_tau X e he la hx s hT τ).2.2)
end ReciprocityTheory.ChartRestriction.G.FD
