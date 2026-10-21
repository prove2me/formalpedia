-- Prove2me | solution 1 for QueueScalp.Entry.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:27:38.710854+00:00
-- url     : https://prove2.me/submissions/a948a786-23da-4245-84d3-93a67be1ec50

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model
import Theorems.Thm_QueueScalp_Entry_pricing_problem
import Theorems.Thm_QueueScalp_Entry_lemma_A_1

open QueueScalp.Entry

namespace QSProp2Aux

noncomputable def g (mu Lam c x : ℝ) : ℝ :=
  Lam ^ 3 * c ^ 2 * x * (c - x) / (mu ^ 2 * (mu - Lam * x))

lemma core_id (mu Lam c s x : ℝ) (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) :
    (mu - s) ^ 2 * (mu - Lam * x) - Lam ^ 2 * x * (c - x) * mu =
      mu * (mu - s - Lam * x) ^ 2 := by
  linear_combination (-(Lam * x)) * hs2

lemma g_le (mu Lam c s x : ℝ) (hmu : 0 < mu) (hLam : 0 < Lam) (hc : 0 < c)
    (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) (hx : Lam * x < mu) :
    g mu Lam c x ≤ Lam * c ^ 2 * (mu - s) ^ 2 / mu ^ 3 := by
  unfold g
  have hd : 0 < mu - Lam * x := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := core_id mu Lam c s x hs2
  have h2 : Lam ^ 2 * x * (c - x) * mu ≤ (mu - s) ^ 2 * (mu - Lam * x) := by
    nlinarith [mul_nonneg hmu.le (sq_nonneg (mu - s - Lam * x))]
  have hk : 0 < Lam * c ^ 2 * mu ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hk.le
  nlinarith

lemma g_eq_iff (mu Lam c s x : ℝ) (hmu : 0 < mu) (hLam : 0 < Lam) (hc : 0 < c)
    (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) (hx : Lam * x < mu) :
    g mu Lam c x = Lam * c ^ 2 * (mu - s) ^ 2 / mu ^ 3 ↔ x = (mu - s) / Lam := by
  have hd : 0 < mu - Lam * x := by linarith
  have h := core_id mu Lam c s x hs2
  unfold g
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hk : 0 < Lam * c ^ 2 * mu ^ 2 := by positivity
  constructor
  · intro he
    have h2 : Lam ^ 2 * x * (c - x) * mu = (mu - s) ^ 2 * (mu - Lam * x) := by
      have : Lam * c ^ 2 * mu ^ 2 * (Lam ^ 2 * x * (c - x) * mu) =
          Lam * c ^ 2 * mu ^ 2 * ((mu - s) ^ 2 * (mu - Lam * x)) := by linear_combination he
      exact mul_left_cancel₀ hk.ne' this
    have h3 : mu * (mu - s - Lam * x) ^ 2 = 0 := by linarith
    have h4 : (mu - s - Lam * x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hmu.ne'
      · exact h
    have h5 : mu - s - Lam * x = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
    field_simp; linarith
  · intro hx'
    have e2 : mu - s - Lam * x = 0 := by rw [hx']; field_simp; ring
    rw [e2] at h
    have h' : Lam ^ 2 * x * (c - x) * mu = (mu - s) ^ 2 * (mu - Lam * x) := by
      linarith [h]
    linear_combination (Lam * c ^ 2 * mu ^ 2) * h'

lemma den_eq (mu Lam cS ct : ℝ) (hc : cS ≠ 0) :
    mu - Lam * cS + Lam * cS * ((cS - ct) / cS) = mu - Lam * ct := by
  field_simp; ring

lemma D_eq (mu Lam cS ct : ℝ) (hc : cS ≠ 0) :
    D mu (Lam * cS) ((cS - ct) / cS) = (Lam * cS / mu) ^ 2 / (mu - Lam * ct) := by
  unfold D W1 W2
  rw [den_eq mu Lam cS ct hc]
  have : (Lam * cS / mu) ^ 2 * ((cS - ct) / cS) / (mu - Lam * ct) +
      (Lam * cS / mu) ^ 2 * (1 - (cS - ct) / cS) / (mu - Lam * ct) =
      (Lam * cS / mu) ^ 2 / (mu - Lam * ct) := by
    rw [← add_div, ← mul_add]; congr 1; ring
  linarith

/-- price formula in terms of `c` and `s` -/
lemma price_eq (P : Params) (hS : P.Standing) (Lam : ℝ) (hLam : 0 < Lam) (c s : ℝ)
    (hc : c = cSOf P Lam) (hs : s = Real.sqrt (P.mu ^ 2 - Lam * c * P.mu)) (hs0 : 0 < s) :
    (P.mu - s) / Lam * ((Lam * c / P.mu) ^ 2 / s) = priceStar P Lam := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  by_cases h : Lam ≤ P.mu - 1 / P.V
  · have hc1 : c = 1 := by rw [hc]; simp only [cSOf, if_pos h]
    have hLm : Lam < P.mu := by have : 0 < 1 / P.V := by positivity
                                linarith
    simp only [priceStar, if_pos h]
    have es : s = Real.sqrt P.mu * Real.sqrt (P.mu - Lam) := by
      rw [hs, hc1, ← Real.sqrt_mul hmu.le]; congr 1; ring
    have ha : 0 < Real.sqrt (P.mu - Lam) := Real.sqrt_pos.2 (by linarith)
    have hm : 0 < Real.sqrt P.mu := Real.sqrt_pos.2 hmu
    have hm2 : Real.sqrt P.mu ^ 2 = P.mu := Real.sq_sqrt hmu.le
    rw [es, hc1]
    obtain ⟨m, hmd⟩ : ∃ m, m = Real.sqrt P.mu := ⟨_, rfl⟩
    obtain ⟨a, had⟩ : ∃ a, a = Real.sqrt (P.mu - Lam) := ⟨_, rfl⟩
    rw [← hmd, ← had]
    rw [← hmd] at hm hm2
    rw [← had] at ha
    rw [← hm2]
    have : m ≠ 0 := hm.ne'
    have : a ≠ 0 := ha.ne'
    field_simp
  · have hc2 : c = P.mu * P.V / (1 + Lam * P.V) := by rw [hc]; simp only [cSOf, if_neg h]
    simp only [priceStar, if_neg h]
    set t := Real.sqrt (Lam * P.V + 1) with htdef
    have ht2 : t ^ 2 = Lam * P.V + 1 := Real.sq_sqrt (by positivity)
    have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
    have es : s = P.mu / t := by
      rw [hs]
      have : P.mu ^ 2 - Lam * c * P.mu = (P.mu / t) ^ 2 := by
        rw [hc2, div_pow, ht2]; field_simp; ring
      rw [this, Real.sqrt_sq (by positivity)]
    rw [es, hc2, show 1 + Lam * P.V = t ^ 2 by linarith, show Lam * P.V + 1 = t ^ 2 by linarith]
    have : t ≠ 0 := ht0.ne'
    have : P.mu ≠ 0 := hmu.ne'
    field_simp

noncomputable def psi (t : ℝ) : ℝ := (t - 1) ^ 2 * (t + 1) / t ^ 4

noncomputable def sig : ℝ := (1 + Real.sqrt 17) / 2

lemma sig_sq : sig ^ 2 = sig + 4 := by
  unfold sig
  have : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma sig_gt : 2 < sig := by
  unfold sig
  have : 3 < Real.sqrt 17 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma psi_deriv (t : ℝ) (ht : t ≠ 0) :
    deriv psi t = (t - 1) * (4 + t - t ^ 2) / t ^ 5 := by
  have h := ((((hasDerivAt_id t).sub_const 1).pow 2).mul
    ((hasDerivAt_id t).add_const 1)).div ((hasDerivAt_id t).pow 4) (pow_ne_zero 4 ht)
  have e : psi = ((fun x => id x - 1) ^ 2 * (fun x => id x + 1) / id ^ 4) := by
    funext x; simp [psi]
  rw [e, h.deriv]
  simp
  field_simp
  ring

lemma psi_mono : StrictMonoOn psi (Set.Icc 1 sig) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro t ht
    have : t ≠ 0 := by linarith [ht.1]
    unfold psi
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero _ this))
  · intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [psi_deriv t ht0.ne']
    have h1 : 0 < t - 1 := by linarith [ht.1]
    have := sig_sq; have := sig_gt
    have h2 : 0 < 4 + t - t ^ 2 := by nlinarith [ht.2]
    positivity

lemma psi_anti : StrictAntiOn psi (Set.Ici sig) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro t ht
    have : t ≠ 0 := by have := sig_gt; linarith [Set.mem_Ici.1 ht]
    unfold psi
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero _ this))
  · intro t ht
    rw [interior_Ici] at ht
    have hg := sig_gt
    have hs := sig_sq
    have ht' : sig < t := ht
    have ht0 : 0 < t := by linarith
    rw [psi_deriv t ht0.ne']
    have h1 : 0 < t - 1 := by linarith
    have h2 : 4 + t - t ^ 2 < 0 := by nlinarith
    have h5 : 0 < t ^ 5 := by positivity
    apply div_neg_of_neg_of_pos _ h5
    nlinarith

lemma price_reg2 (P : Params) (hS : P.Standing) (L : ℝ) (hL : P.mu - 1 / P.V ≤ L) :
    priceStar P L = P.V * psi (Real.sqrt (L * P.V + 1)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hmV : 1 < P.mu * P.V := by
    have := (div_lt_iff₀ hmu).1 hV; linarith
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; linarith
  rcases eq_or_lt_of_le hL with h | h
  · subst h
    simp only [priceStar, if_pos (le_refl (P.mu - 1 / P.V))]
    set s := Real.sqrt (P.mu * P.V) with hs_def
    have hs2 : s ^ 2 = P.mu * P.V := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 < s := by nlinarith
    have e2 : Real.sqrt ((P.mu - 1 / P.V) * P.V + 1) = s := by
      rw [hs_def]; congr 1; field_simp; ring
    have e3 : P.mu - (P.mu - 1 / P.V) = 1 / P.V := by ring
    rw [e2, e3]
    set w := Real.sqrt P.V with hw
    have hw2 : w ^ 2 = P.V := Real.sq_sqrt hV0.le
    have hw0 : 0 < w := Real.sqrt_pos.2 hV0
    have e4 : Real.sqrt (1 / P.V) = 1 / w := by
      rw [Real.sqrt_div' _ hV0.le, Real.sqrt_one]
    have e5 : Real.sqrt P.mu = s / w := by
      rw [hs_def, Real.sqrt_mul hmu.le, ← hw]; field_simp
    rw [e4, e5]
    have hmu' : P.mu = s ^ 2 / w ^ 2 := by rw [hw2]; field_simp; linarith
    rw [hmu', ← hw2]
    unfold psi
    have : s ≠ 0 := by linarith
    have : w ≠ 0 := hw0.ne'
    have : s - 1 ≠ 0 := by linarith
    field_simp
    ring
  · have hn : ¬ L ≤ P.mu - 1 / P.V := not_le.2 h
    simp only [priceStar, if_neg hn]
    set t := Real.sqrt (L * P.V + 1)
    have ht2 : t ^ 2 = L * P.V + 1 := Real.sq_sqrt (by
      have : 0 < L := lt_trans hL0 h
      positivity)
    have ht0 : 0 < t := by
      have : 0 < L := lt_trans hL0 h
      exact Real.sqrt_pos.2 (by positivity)
    have hLt : L = (t ^ 2 - 1) / P.V := by field_simp; linarith
    rw [show L * P.V + 1 = t ^ 2 from ht2.symm, hLt]
    unfold psi
    have : t ≠ 0 := ht0.ne'
    have : P.V ≠ 0 := hV0.ne'
    field_simp
    ring

lemma price_mono1 (P : Params) (hS : P.Standing) :
    StrictMonoOn (priceStar P) (Set.Ioc 0 (P.mu - 1 / P.V)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  intro a ha b hb hab
  simp only [priceStar, if_pos ha.2, if_pos hb.2]
  have hbm : b < P.mu := by have : 0 < 1 / P.V := by positivity
                            linarith [hb.2]
  have ha0 := ha.1
  set m := Real.sqrt P.mu
  set xa := Real.sqrt (P.mu - a)
  set xb := Real.sqrt (P.mu - b)
  have hxb0 : 0 < xb := Real.sqrt_pos.2 (by linarith)
  have hxba : xb < xa := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hxam : xa < m := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hmu2 : 0 < P.mu ^ 2 := by positivity
  have hxa0 : 0 < xa := lt_trans hxb0 hxba
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  -- a (m - xa) xb < b (m - xb) xa  (times μ²)
  have key : a * (m - xa) * xb < b * (m - xb) * xa := by
    have h1 : (m - xa) * xb < (m - xb) * xa := by nlinarith
    have h2 : 0 < (m - xb) * xa := by nlinarith
    have h3 : 0 ≤ (m - xa) * xb := by nlinarith
    nlinarith
  nlinarith

lemma T_mono (V : ℝ) (hV : 0 < V) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Real.sqrt (a * V + 1) < Real.sqrt (b * V + 1) :=
  Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

lemma T_sig (P : Params) (hV : 0 < P.V) : Real.sqrt ((sig + 3) / P.V * P.V + 1) = sig := by
  have h : (sig + 3) / P.V * P.V + 1 = sig ^ 2 := by
    rw [sig_sq]; field_simp; ring
  rw [h, Real.sqrt_sq (by have := sig_gt; linarith)]

lemma T_ge_one (P : Params) (hS : P.Standing) (L : ℝ) (hL : P.mu - 1 / P.V ≤ L) :
    1 ≤ Real.sqrt (L * P.V + 1) := by
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)

end QSProp2Aux

open QSProp2Aux in
theorem solution (P : Params) (hS : P.Standing) :
    (∀ Lam : ℝ, 0 < Lam → IsOptPrice P Lam (priceStar P Lam)) ∧
    (∀ Lam price : ℝ, 0 < Lam → IsOptPrice P Lam price →
      price = priceStar P Lam) ∧
    (∃ Lp : ℝ, 0 < Lp ∧
      StrictMonoOn (priceStar P) (Set.Ioc (0 : ℝ) Lp) ∧
      StrictAntiOn (priceStar P) (Set.Ici Lp)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  -- common setup for each demand level
  have setup : ∀ Lam : ℝ, 0 < Lam →
      0 < cSOf P Lam ∧ Lam * cSOf P Lam < P.mu := by
    intro Lam hLam
    simp only [cSOf]
    split_ifs with h
    · have : 0 < 1 / P.V := by positivity
      constructor <;> linarith
    · have hLV : 0 < 1 + Lam * P.V := by positivity
      refine ⟨by positivity, ?_⟩
      rw [mul_div_assoc', div_lt_iff₀ hLV]; nlinarith
  -- the optimal revenue is g at ct*
  have optrev : ∀ Lam : ℝ, 0 < Lam →
      IsOptRevenue P Lam (g P.mu Lam (cSOf P Lam)
        ((P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam)) ∧
      (∃ price lam q, price = (P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam *
          ((Lam * cSOf P Lam / P.mu) ^ 2 / Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) ∧
        0 ≤ price ∧ IsCustEq P Lam price lam q (cSOf P Lam)
          ((P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam) ∧
        price * lam * q = g P.mu Lam (cSOf P Lam)
          ((P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam)) := by
    intro Lam hLam
    obtain ⟨hpp1, hpp2⟩ := pricing_problem P hS Lam hLam
    obtain ⟨hc0, hst⟩ := setup Lam hLam
    set c := cSOf P Lam
    set s := Real.sqrt (P.mu ^ 2 - Lam * c * P.mu) with hsdef
    have hin : 0 < P.mu ^ 2 - Lam * c * P.mu := by nlinarith
    have hs2 : s ^ 2 = P.mu ^ 2 - Lam * c * P.mu := Real.sq_sqrt hin.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hin
    have hsmu : s ≤ P.mu := by nlinarith [mul_pos (mul_pos hLam hc0) hmu]
    have hx0 : 0 ≤ (P.mu - s) / Lam := div_nonneg (by linarith) hLam.le
    have hxc : (P.mu - s) / Lam ≤ c := by
      rw [div_le_iff₀ hLam]
      have h1 : 0 ≤ P.mu - Lam * c := by linarith
      have h2 : (P.mu - Lam * c) ^ 2 ≤ P.mu ^ 2 - Lam * c * P.mu := by
        nlinarith [mul_pos (mul_pos hLam hc0) hmu]
      have h3 := Real.abs_le_sqrt h2
      rw [← hsdef, abs_of_nonneg h1] at h3
      linarith
    have hxe : P.mu - Lam * ((P.mu - s) / Lam) = s := by field_simp; ring
    have hgeq := (g_eq_iff P.mu Lam c s ((P.mu - s) / Lam) hmu hLam hc0 hs2
      (by rw [show Lam * ((P.mu - s) / Lam) = P.mu - s by field_simp]; linarith)).2 rfl
    obtain ⟨price, lam, q, hprice, hpnn, heq⟩ := hpp2 ((P.mu - s) / Lam) ⟨hx0, hxc⟩
    have hrev : price * lam * q = g P.mu Lam c ((P.mu - s) / Lam) := by
      rw [hpp1 _ _ _ _ _ hpnn heq]; rfl
    refine ⟨⟨⟨price, lam, q, c, (P.mu - s) / Lam, hpnn, heq, hrev⟩, ?_⟩,
      ⟨price, lam, q, ?_, hpnn, heq, hrev⟩⟩
    · intro price' lam' q' cS' ct' hp' he'
      have hcS : cS' = c := lemma_A_1 P hS Lam hLam price' lam' q' cS' ct' he'
      rw [hpp1 _ _ _ _ _ hp' he', hgeq, hcS]
      have hct : Lam * ct' < P.mu := by
        have := mul_le_mul_of_nonneg_left he'.ct_le_cS hLam.le
        rw [hcS] at this; linarith
      have := g_le P.mu Lam c s ct' hmu hLam hc0 hs2 hct
      simpa [g] using this
    · rw [hprice, D_eq P.mu Lam c _ hc0.ne', hxe]
  refine ⟨?_, ?_, ?_⟩
  · intro Lam hLam
    obtain ⟨hopt, price, lam, q, hprice, hpnn, heq, hrev⟩ := optrev Lam hLam
    obtain ⟨hc0, hst⟩ := setup Lam hLam
    have hin : 0 < P.mu ^ 2 - Lam * cSOf P Lam * P.mu := by nlinarith
    have hpe := price_eq P hS Lam hLam (cSOf P Lam) _ rfl rfl (Real.sqrt_pos.2 hin)
    refine ⟨lam, q, cSOf P Lam,
      (P.mu - Real.sqrt (P.mu ^ 2 - Lam * cSOf P Lam * P.mu)) / Lam, ?_, ?_, ?_⟩
    · rw [← hpe, ← hprice]; exact hpnn
    · rw [← hpe, ← hprice]; exact heq
    · rw [← hpe, ← hprice, hrev]; exact hopt
  · intro Lam price hLam ⟨lam, q, cS, ct, hp, he, hR⟩
    obtain ⟨hopt, -⟩ := optrev Lam hLam
    obtain ⟨hpp1, -⟩ := pricing_problem P hS Lam hLam
    obtain ⟨hc0, hst⟩ := setup Lam hLam
    have hcS : cS = cSOf P Lam := lemma_A_1 P hS Lam hLam price lam q cS ct he
    set c := cSOf P Lam
    set s := Real.sqrt (P.mu ^ 2 - Lam * c * P.mu) with hsdef
    have hin : 0 < P.mu ^ 2 - Lam * c * P.mu := by nlinarith
    have hs2 : s ^ 2 = P.mu ^ 2 - Lam * c * P.mu := Real.sq_sqrt hin.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hin
    -- revenues agree
    have hR1 : price * lam * q = g P.mu Lam c ((P.mu - s) / Lam) := by
      obtain ⟨⟨p1, l1, q1, c1, t1, hp1, he1, hr1⟩, hb1⟩ := hR
      obtain ⟨⟨p2, l2, q2, c2, t2, hp2, he2, hr2⟩, hb2⟩ := hopt
      have := hb1 p2 l2 q2 c2 t2 hp2 he2
      have := hb2 p1 l1 q1 c1 t1 hp1 he1
      linarith
    have hct : Lam * ct < P.mu := by
      have := mul_le_mul_of_nonneg_left he.ct_le_cS hLam.le
      rw [hcS] at this; linarith
    have hgeq := (g_eq_iff P.mu Lam c s ((P.mu - s) / Lam) hmu hLam hc0 hs2
      (by rw [show Lam * ((P.mu - s) / Lam) = P.mu - s by field_simp]; linarith)).2 rfl
    have hctx : ct = (P.mu - s) / Lam := by
      apply (g_eq_iff P.mu Lam c s ct hmu hLam hc0 hs2 hct).1
      rw [← hgeq, ← hR1, hpp1 _ _ _ _ _ hp he, hcS]; rfl
    have hxe : P.mu - Lam * ((P.mu - s) / Lam) = s := by field_simp; ring
    rw [← price_eq P hS Lam hLam c s rfl hsdef hs0, he.indiff, he.thru, he.rate, hcS, hctx]
    have := D_eq P.mu Lam c ((P.mu - s) / Lam) hc0.ne'
    unfold D at this
    rw [this, hxe]
  · -- unimodality
    set L0 := P.mu - 1 / P.V with hL0def
    set Ls := (sig + 3) / P.V with hLs
    have hLs0 : 0 < Ls := by have := sig_gt; positivity
    refine ⟨max L0 Ls, lt_of_lt_of_le hL0 (le_max_left _ _), ?_, ?_⟩
    · have hm2 : StrictMonoOn (priceStar P) (Set.Icc L0 (max L0 Ls)) := by
        intro a ha b hb hab
        rw [price_reg2 P hS a ha.1, price_reg2 P hS b hb.1]
        apply mul_lt_mul_of_pos_left _ hV0
        have hst : b ≤ Ls := by
          have : b ≤ max L0 Ls := hb.2
          rcases le_total L0 Ls with h | h
          · rwa [max_eq_right h] at this
          · rw [max_eq_left h] at this; linarith [ha.1]
        have hT := T_mono P.V hV0 (le_trans hL0.le ha.1) hab
        have hTb : Real.sqrt (b * P.V + 1) ≤ sig := by
          rw [← T_sig P hV0]
          exact Real.sqrt_le_sqrt (by nlinarith)
        exact psi_mono ⟨T_ge_one P hS a ha.1, by linarith⟩ ⟨T_ge_one P hS b hb.1, hTb⟩ hT
      intro a ha b hb hab
      by_cases hb0 : b ≤ L0
      · exact price_mono1 P hS ⟨ha.1, le_trans hab.le hb0⟩ ⟨lt_trans ha.1 hab, hb0⟩ hab
      · push Not at hb0
        by_cases ha0 : L0 ≤ a
        · exact hm2 ⟨ha0, le_trans hab.le hb.2⟩ ⟨le_trans ha0 hab.le, hb.2⟩ hab
        · push Not at ha0
          have h1 := price_mono1 P hS ⟨ha.1, ha0.le⟩ ⟨hL0, le_rfl⟩ ha0
          have h2 := hm2 ⟨le_rfl, le_max_left _ _⟩ ⟨hb0.le, hb.2⟩ hb0
          exact lt_trans h1 h2
    · intro a ha b hb hab
      have ha' : max L0 Ls ≤ a := ha
      have ha1 : L0 ≤ a := le_trans (le_max_left _ _) ha'
      have hb1 : L0 ≤ b := le_trans ha1 hab.le
      have ha2 : Ls ≤ a := le_trans (le_max_right _ _) ha'
      rw [price_reg2 P hS a ha1, price_reg2 P hS b hb1]
      apply mul_lt_mul_of_pos_left _ hV0
      have hT := T_mono P.V hV0 (le_trans hLs0.le ha2) hab
      have hTa : sig ≤ Real.sqrt (a * P.V + 1) := by
        rw [← T_sig P hV0]
        exact Real.sqrt_le_sqrt (by nlinarith)
      exact psi_anti (Set.mem_Ici.2 hTa) (Set.mem_Ici.2 (by linarith)) hT
