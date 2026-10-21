-- Prove2me | solution 1 for QueueScalp.Entry.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:23:01.420197+00:00
-- url     : https://prove2.me/submissions/2504f54e-1ff9-4584-ac5c-47d02084d6f9

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model
import Theorems.Thm_QueueScalp_Entry_optimal_revenue

open QueueScalp.Entry

namespace QSProp3Aux

lemma optRev_unique {P : Params} {Lam R R' : ℝ} (h : IsOptRevenue P Lam R)
    (h' : IsOptRevenue P Lam R') : R = R' := by
  obtain ⟨⟨p, l, q, c, t, hp, he, hR⟩, hb⟩ := h
  obtain ⟨⟨p', l', q', c', t', hp', he', hR'⟩, hb'⟩ := h'
  have h1 := hb p' l' q' c' t' hp' he'
  have h2 := hb' p l q c t hp he
  linarith

noncomputable def phi (t : ℝ) : ℝ := (t ^ 2 - 1) * (t - 1) ^ 2 / t ^ 6

noncomputable def tau : ℝ := (1 + Real.sqrt 13) / 2

lemma phi_deriv (t : ℝ) (ht : t ≠ 0) :
    deriv phi t = 2 * (t - 1) ^ 2 * (3 + t - t ^ 2) / t ^ 7 := by
  have h := ((((hasDerivAt_id t).pow 2).sub_const 1).mul
    (((hasDerivAt_id t).sub_const 1).pow 2)).div ((hasDerivAt_id t).pow 6) (pow_ne_zero 6 ht)
  have e : phi = ((fun x => (id ^ 2) x - 1) * (fun x => id x - 1) ^ 2 / id ^ 6) := by
    funext x; simp [phi]
  rw [e, h.deriv]
  simp
  field_simp
  ring

lemma tau_sq : tau ^ 2 = tau + 3 := by
  unfold tau
  have : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma tau_gt : 2 < tau := by
  unfold tau
  have : 3 < Real.sqrt 13 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma quad_pos (t : ℝ) (h0 : 0 < t) (h : t < tau) : 0 < 3 + t - t ^ 2 := by
  have := tau_sq; have := tau_gt
  nlinarith

lemma quad_neg (t : ℝ) (h : tau < t) : 3 + t - t ^ 2 < 0 := by
  have := tau_sq; have := tau_gt
  nlinarith

lemma phi_mono : StrictMonoOn phi (Set.Icc 1 tau) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro t ht
    have : t ≠ 0 := by linarith [ht.1]
    unfold phi
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero _ this))
  · intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [phi_deriv t ht0.ne']
    have h1 : 0 < (t - 1) ^ 2 := by have : 0 < t - 1 := by linarith [ht.1]
                                    positivity
    have := quad_pos t ht0 ht.2
    positivity

lemma phi_anti : StrictAntiOn phi (Set.Ici tau) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro t ht
    have : t ≠ 0 := by have := tau_gt; linarith [Set.mem_Ici.1 ht]
    unfold phi
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact pow_ne_zero _ this))
  · intro t ht
    rw [interior_Ici] at ht
    have hg := tau_gt
    have ht' : tau < t := ht
    have ht0 : 0 < t := by linarith
    rw [phi_deriv t ht0.ne']
    have h1 : 0 < (t - 1) ^ 2 := by have : 0 < t - 1 := by linarith
                                    positivity
    have := quad_neg t ht'
    have h7 : 0 < t ^ 7 := by positivity
    apply div_neg_of_neg_of_pos _ h7
    nlinarith

/-- regime-1 closed form -/
lemma Pi_reg1 (P : Params) (hS : P.Standing) (L : ℝ) (hL : 0 < L)
    (h : L ≤ P.mu - 1 / P.V) :
    PiStar P L = L ^ 3 / (P.mu * (P.mu + Real.sqrt (P.mu ^ 2 - L * 1 * P.mu)) ^ 2) := by
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hLm : L < P.mu := by have : 0 < 1 / P.V := by positivity
                            linarith
  simp only [PiStar, ctStar, cSOf, if_pos h]
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (P.mu ^ 2 - L * 1 * P.mu) := ⟨_, rfl⟩
  rw [← hr]
  have hin : 0 < P.mu ^ 2 - L * 1 * P.mu := by nlinarith
  have hr2 : r ^ 2 = P.mu ^ 2 - L * 1 * P.mu := by rw [hr]; exact Real.sq_sqrt hin.le
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hin
  have hL' : L = (P.mu ^ 2 - r ^ 2) / P.mu := by field_simp; linarith
  have hne : P.mu ^ 2 - r ^ 2 ≠ 0 := by rw [hr2]; nlinarith [mul_pos hL hmu]
  rw [hL']
  have : P.mu ≠ 0 := hmu.ne'
  have : P.mu + r ≠ 0 := by linarith
  have : r ≠ 0 := hr0.ne'
  have hrr : P.mu - r ≠ 0 := by
    intro h0; apply hne; have : P.mu = r := by linarith
    rw [this]; ring
  field_simp
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ this
  linear_combination (-2 * P.mu ^ 2 * r ^ 2 + P.mu ^ 4 + r ^ 4) * hri

lemma Pi_reg2 (P : Params) (hS : P.Standing) (L : ℝ) (hL : P.mu - 1 / P.V ≤ L) :
    PiStar P L = P.mu * P.V * phi (Real.sqrt (L * P.V + 1)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hmV : 1 < P.mu * P.V := by
    have := (div_lt_iff₀ hmu).1 hV; linarith
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  rcases eq_or_lt_of_le hL with h | h
  · -- boundary
    subst h
    rw [Pi_reg1 P hS _ hL0 le_rfl]
    set s := Real.sqrt (P.mu * P.V) with hs_def
    have hs2 : s ^ 2 = P.mu * P.V := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 < s := by nlinarith
    have hmu' : P.mu = s ^ 2 / P.V := by field_simp; linarith
    have e1 : Real.sqrt (P.mu ^ 2 - (P.mu - 1 / P.V) * 1 * P.mu) = s / P.V := by
      have : P.mu ^ 2 - (P.mu - 1 / P.V) * 1 * P.mu = (s / P.V) ^ 2 := by
        rw [div_pow, hs2]; field_simp; ring
      rw [this, Real.sqrt_sq (by positivity)]
    have e2 : Real.sqrt ((P.mu - 1 / P.V) * P.V + 1) = s := by
      rw [hs_def]; congr 1; field_simp; ring
    rw [e1, e2]
    unfold phi
    rw [hmu']
    have : s ≠ 0 := by linarith
    have : P.V ≠ 0 := hV0.ne'
    have : s + 1 ≠ 0 := by linarith
    field_simp
    ring
  · have hn : ¬ L ≤ P.mu - 1 / P.V := not_le.2 h
    simp only [PiStar, if_neg hn]
    set t := Real.sqrt (L * P.V + 1)
    have ht2 : t ^ 2 = L * P.V + 1 := Real.sq_sqrt (by positivity)
    have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
    have e : Real.sqrt (P.mu ^ 2 * (L * P.V + 1)) = P.mu * t := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hmu.le]
    have hLt : L = (t ^ 2 - 1) / P.V := by field_simp; linarith
    rw [e, show L * P.V + 1 = t ^ 2 from ht2.symm, hLt]
    unfold phi
    have : t ≠ 0 := ht0.ne'
    have : P.V ≠ 0 := hV0.ne'
    have : P.mu ≠ 0 := hmu.ne'
    field_simp
    ring

lemma Pi_mono1 (P : Params) (hS : P.Standing) :
    StrictMonoOn (PiStar P) (Set.Ioc 0 (P.mu - 1 / P.V)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  intro a ha b hb hab
  rw [Pi_reg1 P hS a ha.1 ha.2, Pi_reg1 P hS b hb.1 hb.2]
  have hbm : b < P.mu := by have : 0 < 1 / P.V := by positivity
                            linarith [hb.2]
  set ra := Real.sqrt (P.mu ^ 2 - a * 1 * P.mu)
  set rb := Real.sqrt (P.mu ^ 2 - b * 1 * P.mu)
  have hrb : rb ≤ ra := Real.sqrt_le_sqrt (by nlinarith)
  have hrb0 : 0 ≤ rb := Real.sqrt_nonneg _
  have hra0 : 0 ≤ ra := Real.sqrt_nonneg _
  have ha0 := ha.1
  have h3 : a ^ 3 < b ^ 3 := by
    exact pow_lt_pow_left₀ hab ha0.le (by norm_num)
  have hd : (P.mu + rb) ^ 2 ≤ (P.mu + ra) ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : 0 < P.mu * (P.mu + rb) ^ 2 := by positivity
  calc a ^ 3 * (P.mu * (P.mu + rb) ^ 2) < b ^ 3 * (P.mu * (P.mu + rb) ^ 2) :=
        mul_lt_mul_of_pos_right h3 this
    _ ≤ b ^ 3 * (P.mu * (P.mu + ra) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_trans ha0.le hab.le) 3)
        exact mul_le_mul_of_nonneg_left hd hmu.le

lemma T_mono (V : ℝ) (hV : 0 < V) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Real.sqrt (a * V + 1) < Real.sqrt (b * V + 1) :=
  Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

lemma T_tilde (P : Params) (hV : 0 < P.V) : Real.sqrt (LamTilde P * P.V + 1) = tau := by
  have h : LamTilde P * P.V + 1 = tau ^ 2 := by
    rw [tau_sq]; unfold LamTilde tau; field_simp; ring
  rw [h, Real.sqrt_sq (by have := tau_gt; linarith)]

lemma T_ge_one (P : Params) (hS : P.Standing) (L : ℝ) (hL : P.mu - 1 / P.V ≤ L) :
    1 ≤ Real.sqrt (L * P.V + 1) := by
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)

lemma Pi_mono2 (P : Params) (hS : P.Standing) :
    StrictMonoOn (PiStar P) (Set.Icc (P.mu - 1 / P.V) (LamStar P)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  intro a ha b hb hab
  rw [Pi_reg2 P hS a ha.1, Pi_reg2 P hS b hb.1]
  have hmV : 0 < P.mu * P.V := by positivity
  apply mul_lt_mul_of_pos_left _ hmV
  -- LamStar must be LamTilde here
  have hst : b ≤ LamTilde P := by
    have : b ≤ max (P.mu - 1 / P.V) (LamTilde P) := hb.2
    rcases le_total (P.mu - 1 / P.V) (LamTilde P) with h | h
    · rwa [max_eq_right h] at this
    · rw [max_eq_left h] at this; linarith [ha.1]
  have hT := T_mono P.V hV0 (le_trans hL0.le ha.1) hab
  have hTb : Real.sqrt (b * P.V + 1) ≤ tau := by
    rw [← T_tilde P hV0]
    exact Real.sqrt_le_sqrt (by nlinarith)
  apply phi_mono ⟨T_ge_one P hS a ha.1, by linarith⟩ ⟨T_ge_one P hS b hb.1, hTb⟩ hT

lemma Pi_anti (P : Params) (hS : P.Standing) :
    StrictAntiOn (PiStar P) (Set.Ioi (LamStar P)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  intro a ha b hb hab
  have ha1 : P.mu - 1 / P.V ≤ a := le_trans (le_max_left _ _) (le_of_lt ha)
  have hb1 : P.mu - 1 / P.V ≤ b := le_trans ha1 hab.le
  have ha2 : LamTilde P ≤ a := le_trans (le_max_right _ _) (le_of_lt ha)
  rw [Pi_reg2 P hS a ha1, Pi_reg2 P hS b hb1]
  have hmV : 0 < P.mu * P.V := by positivity
  apply mul_lt_mul_of_pos_left _ hmV
  have hLT : 0 < LamTilde P := by unfold LamTilde; positivity
  have hT := T_mono P.V hV0 (le_trans hLT.le ha2) hab
  have hTa : tau ≤ Real.sqrt (a * P.V + 1) := by
    rw [← T_tilde P hV0]
    exact Real.sqrt_le_sqrt (by nlinarith)
  exact phi_anti (Set.mem_Ici.2 hTa) (Set.mem_Ici.2 (by linarith)) hT

end QSProp3Aux

open QSProp3Aux in
theorem solution (P : Params) (hS : P.Standing) :
    (∃! LamS : ℝ,
      P.mu - 1 / P.V ≤ LamS ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, 0 < L₁ → L₁ < L₂ → L₂ ≤ LamS →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₁ < R₂) ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, LamS < L₁ → L₁ < L₂ →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₂ < R₁)) ∧
    (P.mu - 1 / P.V ≤ LamStar P ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, 0 < L₁ → L₁ < L₂ → L₂ ≤ LamStar P →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₁ < R₂) ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, LamStar P < L₁ → L₁ < L₂ →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₂ < R₁)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; have := (div_lt_iff₀ hmu).1 hV; linarith
  set L0 := P.mu - 1 / P.V with hL0def
  have hstar : L0 ≤ LamStar P := le_max_left _ _
  -- strict increase on (0, LamStar]
  have hinc : ∀ a b, 0 < a → a < b → b ≤ LamStar P → PiStar P a < PiStar P b := by
    intro a b ha hab hb
    by_cases hb0 : b ≤ L0
    · exact Pi_mono1 P hS ⟨ha, le_trans hab.le hb0⟩ ⟨lt_trans ha hab, hb0⟩ hab
    · push Not at hb0
      by_cases ha0 : L0 ≤ a
      · exact Pi_mono2 P hS ⟨ha0, le_trans hab.le hb⟩ ⟨le_trans ha0 hab.le, hb⟩ hab
      · push Not at ha0
        have h1 := Pi_mono1 P hS ⟨ha, ha0.le⟩ ⟨hL0, le_rfl⟩ ha0
        have h2 := Pi_mono2 P hS ⟨le_rfl, hstar⟩ ⟨hb0.le, hb⟩ hb0
        exact lt_trans h1 h2
  have hdec : ∀ a b, LamStar P < a → a < b → PiStar P b < PiStar P a := by
    intro a b ha hab
    exact Pi_anti P hS ha (lt_trans ha hab) hab
  have part2 : P.mu - 1 / P.V ≤ LamStar P ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, 0 < L₁ → L₁ < L₂ → L₂ ≤ LamStar P →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₁ < R₂) ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, LamStar P < L₁ → L₁ < L₂ →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₂ < R₁) := by
    refine ⟨hstar, ?_, ?_⟩
    · intro L₁ L₂ R₁ R₂ h1 h12 h2 hR1 hR2
      rw [optRev_unique hR1 (optimal_revenue P hS L₁ h1),
        optRev_unique hR2 (optimal_revenue P hS L₂ (lt_trans h1 h12))]
      exact hinc L₁ L₂ h1 h12 h2
    · intro L₁ L₂ R₁ R₂ h1 h12 hR1 hR2
      have hp1 : 0 < L₁ := lt_of_lt_of_le hL0 (le_trans hstar h1.le)
      rw [optRev_unique hR1 (optimal_revenue P hS L₁ hp1),
        optRev_unique hR2 (optimal_revenue P hS L₂ (lt_trans hp1 h12))]
      exact hdec L₁ L₂ h1 h12
  refine ⟨⟨LamStar P, part2, ?_⟩, part2⟩
  rintro y ⟨hy0, hyinc, hydec⟩
  obtain ⟨-, hsinc, hsdec⟩ := part2
  have hR : ∀ L, 0 < L → IsOptRevenue P L (PiStar P L) := fun L hL => optimal_revenue P hS L hL
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · -- y < LamStar
    have hy : 0 < y := lt_of_lt_of_le hL0 hy0
    set m := (y + LamStar P) / 2
    have hm1 : y < m := by simp only [m]; linarith
    have hm2 : m < LamStar P := by simp only [m]; linarith
    have hm0 : 0 < m := lt_trans hy hm1
    have a1 := hydec m (LamStar P) _ _ hm1 hm2 (hR m hm0) (hR _ (lt_trans hm0 hm2))
    have a2 := hsinc m (LamStar P) _ _ hm0 hm2 le_rfl (hR m hm0) (hR _ (lt_trans hm0 hm2))
    linarith
  · have hy : 0 < LamStar P := lt_of_lt_of_le hL0 hstar
    set m := (y + LamStar P) / 2
    have hm1 : LamStar P < m := by simp only [m]; linarith
    have hm2 : m < y := by simp only [m]; linarith
    have hm0 : 0 < m := lt_trans hy hm1
    have a1 := hsdec m y _ _ hm1 hm2 (hR m hm0) (hR _ (lt_trans hm0 hm2))
    have a2 := hyinc m y _ _ hm0 hm2 le_rfl (hR m hm0) (hR _ (lt_trans hm0 hm2))
    linarith
