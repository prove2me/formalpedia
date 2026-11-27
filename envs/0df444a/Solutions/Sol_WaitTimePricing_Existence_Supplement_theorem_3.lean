-- Prove2me | solution 1 for WaitTimePricing.Existence.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:21.446413+00:00
-- url     : https://prove2.me/submissions/ae7debc7-7622-44fd-ac2c-da4ea84ccd64

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Supplement_ServicePolicy

set_option autoImplicit false

open WaitTimePricing
open WaitTimePricing.Existence
open WaitTimePricing.Existence.Supplement

open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 21, Theorem 3, with (35)–(39), pp. 20–21.
Formalization Note: counterexample to the printed closed rejection interval, without changing
(35)–(39). Set U(t)=2t−t²/2, c(w)=w, C=1, λ=1/100, revenue. Then ŵ=1/2, wbar=3/2,
0<g<1, and r=3/2−g is strictly above ŵ. At r the acceptance expression is exactly zero,
so (37) admits service 1, while every w in (r,wbar] rejects. No W3 can give both the printed
fourth and fifth service clauses. `FiveSections` retains policy equality, all thresholds and
all ten printed clauses on the full intervals. No load or regularity premise has been added.
The first conjunct states the theorem's opening clause, P*(w) = p*_s(w) on [0,wbar], for every
model satisfying the standing assumptions and both concrete objectives: the counterexample refutes
only the threshold clause, so the policy-equality clause is kept at full strength.
The threshold clause is replaced by an explicit counterexample as required by the source-audit policy. -/
theorem solution :
    (∀ (M : Model) (obj : Objective), M.Standing →
      ∀ w ∈ Icc 0 (wbar M),
        PStar M obj w = feedback M (concreteReward M obj) (Vbar M obj) w) ∧
    let M := testModel (1 / 100)
    let g := gbar M .revenue
    let r := (3 : ℝ) / 2 - g
    M.Standing ∧ what M = 1 / 2 ∧ wbar M = 3 / 2 ∧
    0 < g ∧ g < 1 ∧ what M < r ∧ r < wbar M ∧
    (∀ w ∈ Icc 0 (what M), ∃ t : ℝ, serviceArgmax M .revenue w = {t}) ∧
    PStar M .revenue r = g ∧ TStar M .revenue r = 1 ∧
    (∀ w ∈ Ioc r (wbar M), TStar M .revenue w = 0) ∧
    ¬ FiveSections M .revenue := by
      open Filter in
        open scoped Topology in
            have P1 : ∀ (M : Model) (obj : Objective), M.Standing →
                ConcaveOn ℝ (Ici 0) (Vbar M obj) ∧ ContinuousOn (Vbar M obj) (Ici 0) ∧
                (∀ d e : ℝ, 0 ≤ d → 0 ≤ e → (∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ d * tOf M p + e) →
                  gbar M obj ≤ d + M.lam * e) ∧
                (∀ p ∈ Icc 0 (deriv M.U 0), M.lam * (v M obj p - gbar M obj * tOf M p) ≤ gbar M obj) := by
              as_aux_lemma =>
                intro M obj hM
                classical
                have hlam := hM.lam_pos
                have hC := hM.C_pos
                have hUdiff : Differentiable ℝ M.U := hM.U_contDiff.differentiable (by norm_num)
                have hDcont : Continuous (deriv M.U) := hM.U_contDiff.continuous_deriv (by norm_num)
                have hDdiff : Differentiable ℝ (deriv M.U) :=
                  (show ContDiff ℝ 2 M.U from hM.U_contDiff.of_le (by norm_num)).differentiable_deriv_two
                have hanti : StrictAntiOn (deriv M.U) (Icc 0 M.C) := by
                  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hDcont.continuousOn
                  intro x hx
                  exact hM.deriv2_U_neg x (interior_subset hx)
                have hD0 : 0 < deriv M.U 0 := by
                  have h := hanti (left_mem_Icc.mpr hM.C_pos.le)
                    (right_mem_Icc.mpr hM.C_pos.le) hM.C_pos
                  have hn := hM.deriv_U_nonneg M.C (right_mem_Icc.mpr hM.C_pos.le)
                  linarith only [h, hn]
                have htmem : ∀ p ∈ Icc 0 (deriv M.U 0),
                    tOf M p ∈ Icc 0 M.C ∧ p ≤ deriv M.U (tOf M p) := by
                  intro p hp
                  have hne : {t ∈ Icc 0 M.C | p ≤ deriv M.U t}.Nonempty :=
                    ⟨0, ⟨⟨le_rfl, hM.C_pos.le⟩, hp.2⟩⟩
                  have hb : BddAbove {t ∈ Icc 0 M.C | p ≤ deriv M.U t} :=
                    ⟨M.C, fun t ht => ht.1.2⟩
                  exact (isClosed_Icc.inter (isClosed_le continuous_const hDcont)).csSup_mem hne hb
                have ht_deriv : ∀ s ∈ Icc 0 M.C, tOf M (deriv M.U s) = s := by
                  intro s hs
                  apply le_antisymm
                  · change sSup {t ∈ Icc 0 M.C | deriv M.U s ≤ deriv M.U t} ≤ s
                    refine csSup_le (s := {t ∈ Icc 0 M.C | deriv M.U s ≤ deriv M.U t}) ⟨s, hs, le_rfl⟩ ?_
                    intro t ht
                    by_contra h
                    exact (not_lt_of_ge ht.2) (hanti hs ht.1 (lt_of_not_ge h))
                  · exact le_csSup ⟨M.C, fun t ht => ht.1.2⟩ ⟨hs, le_rfl⟩
                have ht_top : tOf M (deriv M.U 0) = 0 := ht_deriv 0 ⟨le_rfl, hM.C_pos.le⟩
                have ht_zero : tOf M 0 = M.C := by
                  apply le_antisymm (htmem 0 ⟨le_rfl, hD0.le⟩).1.2
                  exact le_csSup ⟨M.C, fun t ht => ht.1.2⟩
                    ⟨⟨hM.C_pos.le, le_rfl⟩, hM.deriv_U_nonneg M.C ⟨hM.C_pos.le, le_rfl⟩⟩
                have hjoin0 : ∀ p ∈ Icc 0 (deriv M.U 0),
                    0 ≤ M.U (tOf M p) - p * tOf M p - M.c 0 := by
                  intro p hp
                  obtain ⟨ht, hpt⟩ := htmem p hp
                  have hi := (convex_Icc 0 (tOf M p)).mul_sub_le_image_sub_of_le_deriv
                    hUdiff.continuous.continuousOn hUdiff.differentiableOn
                    (C := p) (by
                      intro x hx
                      have hx' : x ∈ Icc 0 (tOf M p) := interior_subset hx
                      exact hpt.trans (hanti.antitoneOn ⟨hx'.1, hx'.2.trans ht.2⟩ ht hx'.2))
                    0 ⟨le_rfl, ht.1⟩ (tOf M p) ⟨ht.1, le_rfl⟩ ht.1
                  simpa [hM.U_zero, hM.c_zero] using hi
                have hGamma0 : Gamma M 0 = deriv M.U 0 := by
                  have he : {p ∈ Icc 0 (deriv M.U 0) |
                      0 ≤ M.U (tOf M p) - p * tOf M p - M.c 0} = Icc 0 (deriv M.U 0) := by
                    ext p
                    exact ⟨fun h => h.1, fun h => ⟨h, hjoin0 p h⟩⟩
                  rw [Gamma, he, csSup_Icc hD0.le]
                have ht_anti : AntitoneOn (tOf M) (Icc 0 (deriv M.U 0)) := by
                  intro p hp q hq hpq
                  change sSup {t ∈ Icc 0 M.C | q ≤ deriv M.U t} ≤ tOf M p
                  refine csSup_le (s := {t ∈ Icc 0 M.C | q ≤ deriv M.U t}) ⟨0, ⟨le_rfl, hM.C_pos.le⟩, hq.2⟩ ?_
                  intro t ht
                  exact le_csSup ⟨M.C, fun s hs => hs.1.2⟩ ⟨ht.1, hpq.trans ht.2⟩
                have hUb : ∀ t ∈ Icc 0 M.C, M.U t ≤ deriv M.U 0 * t := by
                  intro t ht
                  have hi := (convex_Icc 0 t).image_sub_le_mul_sub_of_deriv_le
                    hUdiff.continuous.continuousOn hUdiff.differentiableOn
                    (C := deriv M.U 0) (by
                      intro x hx
                      have hx' : x ∈ Icc 0 t := interior_subset hx
                      exact hM.deriv_U_le x ⟨hx'.1, hx'.2.trans ht.2⟩)
                    0 ⟨le_rfl, ht.1⟩ t ⟨ht.1, le_rfl⟩ ht.1
                  simpa [hM.U_zero] using hi
                have hvb : ∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ deriv M.U 0 * tOf M p := by
                  intro p hp
                  cases obj with
                  | revenue => exact mul_le_mul_of_nonneg_right hp.2 (htmem p hp).1.1
                  | welfare => exact hUb _ (htmem p hp).1
                have hcmono : StrictMonoOn M.c (Ici 0) := by
                  apply strictMonoOn_of_deriv_pos (convex_Ici _) hM.c_contDiff.continuous.continuousOn
                  intro w hw
                  exact hM.deriv_c_pos w (interior_subset hw)
                have hc_nonneg : ∀ w, 0 ≤ w → 0 ≤ M.c w := by
                  intro w hw
                  simpa [hM.c_zero] using hcmono.monotoneOn (show (0 : ℝ) ∈ Ici 0 from by simp) hw hw
                have hGammaBounds : ∀ w, Gamma M w ∈ Icc 0 (deriv M.U 0) := by
                  intro w
                  let S := {p ∈ Icc 0 (deriv M.U 0) |
                      0 ≤ M.U (tOf M p) - p * tOf M p - M.c w}
                  by_cases he : S.Nonempty
                  · have hb : BddAbove S := ⟨deriv M.U 0, fun p hp => hp.1.2⟩
                    exact ⟨(he.choose_spec.1.1).trans (le_csSup hb he.choose_spec),
                      csSup_le he (fun p hp => hp.1.2)⟩
                  · have he' : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
                    change sSup S ∈ _
                    simp [he', hD0.le]
                have hDcd : ContDiff ℝ 2 (deriv M.U) := hM.U_contDiff.deriv'
                have hD2cont : Continuous (deriv (deriv M.U)) := hDcd.continuous_deriv (by norm_num)
                obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn
                  (show (Icc 0 M.C).Nonempty from ⟨0, le_rfl, hC.le⟩) hD2cont.continuousOn
                let a := -deriv (deriv M.U) z
                have ha : 0 < a := neg_pos.mpr (hM.deriv2_U_neg z hz)
                have haD : ∀ x ∈ Icc 0 M.C, deriv (deriv M.U) x ≤ -a := by
                  intro x hx
                  simpa [a] using hzmax hx
                have hstrong : ∀ x ∈ Icc 0 M.C, ∀ y ∈ Icc 0 M.C, x ≤ y →
                    deriv M.U y - deriv M.U x ≤ -a * (y - x) := by
                  exact (convex_Icc 0 M.C).image_sub_le_mul_sub_of_deriv_le
                    hDcont.continuousOn hDdiff.differentiableOn
                    (fun x hx => haD x (interior_subset hx))
                have ht_cases : ∀ p ∈ Icc 0 (deriv M.U 0),
                    tOf M p = M.C ∨ deriv M.U (tOf M p) = p := by
                  intro p hp
                  by_cases hpc : p ≤ deriv M.U M.C
                  · left
                    apply le_antisymm (htmem p hp).1.2
                    exact le_csSup ⟨M.C, fun t ht => ht.1.2⟩ ⟨⟨hC.le, le_rfl⟩, hpc⟩
                  · right
                    obtain ⟨t, ht, htp⟩ := intermediate_value_Icc' hC.le hDcont.continuousOn
                      (show p ∈ Icc (deriv M.U M.C) (deriv M.U 0) from ⟨(lt_of_not_ge hpc).le, hp.2⟩)
                    rw [← htp, ht_deriv t ht]
                have ht_slope : ∀ p ∈ Icc 0 (deriv M.U 0), ∀ q ∈ Icc 0 (deriv M.U 0), p ≤ q →
                    a * (tOf M p - tOf M q) ≤ q - p := by
                  intro p hp q hq hpq
                  have htqtp := ht_anti hp hq hpq
                  rcases ht_cases q hq with hqt | hqt
                  · have hpt : tOf M p = M.C := le_antisymm (htmem p hp).1.2 (hqt ▸ htqtp)
                    rw [hpt, hqt]
                    simp only [sub_self, mul_zero]
                    exact sub_nonneg.mpr hpq
                  · have hst := hstrong _ (htmem q hq).1 _ (htmem p hp).1 htqtp
                    have hpt := (htmem p hp).2
                    rw [hqt] at hst
                    linarith only [hst, hpt]
                have ht_lip : ∀ p ∈ Icc 0 (deriv M.U 0), ∀ q ∈ Icc 0 (deriv M.U 0),
                    |tOf M p - tOf M q| ≤ (1 / a) * |p - q| := by
                  intro p hp q hq
                  rcases le_total p q with hpq | hqp
                  · rw [abs_of_nonneg (sub_nonneg.mpr (ht_anti hp hq hpq)),
                      abs_of_nonpos (sub_nonpos.mpr hpq)]
                    have hi := ht_slope p hp q hq hpq
                    apply (mul_le_mul_iff_right₀ ha).mp
                    calc
                      a * (tOf M p - tOf M q) = a * (tOf M p - tOf M q) := by ring
                      _ ≤ q - p := hi
                      _ = a * (1 / a * -(p - q)) := by field_simp <;> ring
                  · rw [abs_of_nonpos (sub_nonpos.mpr (ht_anti hq hp hqp)),
                      abs_of_nonneg (sub_nonneg.mpr hqp)]
                    apply (mul_le_mul_iff_right₀ ha).mp
                    calc
                      a * -(tOf M p - tOf M q) = a * (tOf M q - tOf M p) := by ring
                      _ ≤ p - q := ht_slope q hq p hp hqp
                      _ = a * (1 / a * (p - q)) := by field_simp <;> ring
                have htcont : ContinuousOn (tOf M) (Icc 0 (deriv M.U 0)) := by
                  let K : NNReal := ⟨1 / a, by positivity⟩
                  have hK : LipschitzOnWith K (tOf M) (Icc 0 (deriv M.U 0)) := by
                    apply LipschitzOnWith.of_dist_le_mul
                    intro p hp q hq
                    change dist (tOf M p) (tOf M q) ≤ (1 / a) * dist p q
                    simpa [Real.dist_eq] using ht_lip p hp q hq
                  exact hK.continuousOn
                have hvcont : ContinuousOn (v M obj) (Icc 0 (deriv M.U 0)) := by
                  cases obj with
                  | revenue => exact continuousOn_id.mul htcont
                  | welfare => exact hM.U_contDiff.continuous.comp_continuousOn htcont
                have hUstrict : StrictMonoOn M.U (Icc 0 M.C) := by
                  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hUdiff.continuous.continuousOn
                  intro t ht
                  have ht' : t ∈ Ioo 0 M.C := by simpa [interior_Icc] using ht
                  have := hanti ⟨ht'.1.le, ht'.2.le⟩ ⟨hC.le, le_rfl⟩ ht'.2
                  have := hM.deriv_U_nonneg M.C ⟨hC.le, le_rfl⟩
                  linarith
                have hUC : 0 < M.U M.C := by
                  simpa [hM.U_zero] using hUstrict ⟨le_rfl, hC.le⟩ ⟨hC.le, le_rfl⟩ hC
                have hcdiff : Differentiable ℝ M.c := hM.c_contDiff.differentiable (by norm_num)
                have hcDcont : Continuous (deriv M.c) := hM.c_contDiff.continuous_deriv (by norm_num)
                have hcDdiff : Differentiable ℝ (deriv M.c) := hM.c_contDiff.differentiable_deriv_two
                have hcDmono : MonotoneOn (deriv M.c) (Ici 0) := by
                  apply monotoneOn_of_deriv_nonneg (convex_Ici _) hcDcont.continuousOn hcDdiff.differentiableOn
                  intro w hw
                  exact hM.deriv2_c_nonneg w (interior_subset hw)
                have hcD0 : 0 < deriv M.c 0 := hM.deriv_c_pos 0 le_rfl
                have hclower : ∀ w, 0 ≤ w → deriv M.c 0 * w ≤ M.c w := by
                  intro w hw
                  have hi := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
                    hcdiff.continuous.continuousOn hcdiff.differentiableOn
                    (C := deriv M.c 0) (by
                      intro x hx
                      exact hcDmono (by simp) (interior_subset hx) (interior_subset hx))
                    0 (by simp) w hw hw
                  simpa [hM.c_zero] using hi
                obtain ⟨wB, hwBpos, hwBeq⟩ : ∃ w > (0 : ℝ), M.U M.C = M.c w := by
                  let b := M.U M.C / deriv M.c 0 + 1
                  have hb : 0 < b := by dsimp [b]; positivity
                  have hbc : M.U M.C ≤ M.c b := by
                    have := hclower b hb.le
                    have he : deriv M.c 0 * b = M.U M.C + deriv M.c 0 := by
                      dsimp [b]
                      field_simp
                    linarith
                  obtain ⟨w, hw, he⟩ := intermediate_value_Icc hb.le hcdiff.continuous.continuousOn
                    (show M.U M.C ∈ Icc (M.c 0) (M.c b) from ⟨by simpa [hM.c_zero] using hUC.le, hbc⟩)
                  refine ⟨w, ?_, he.symm⟩
                  by_contra hn
                  have hw0 : w = 0 := le_antisymm (not_lt.mp hn) hw.1
                  subst w
                  rw [hM.c_zero] at he
                  linarith
                have hwbar_eq : wbar M = wB := by
                  have he : {w ∈ Ioi (0 : ℝ) | M.U M.C = M.c w} = {wB} := by
                    ext w
                    constructor
                    · intro hw
                      exact hcmono.injOn (show 0 ≤ w from hw.1.le) hwBpos.le (hw.2.symm.trans hwBeq)
                    · intro hw
                      rw [mem_singleton_iff] at hw
                      subst w
                      exact ⟨hwBpos, hwBeq⟩
                  change sSup {w ∈ Ioi (0 : ℝ) | M.U M.C = M.c w} = wB
                  rw [he, csSup_singleton]
                have hwbar : 0 < wbar M := by rw [hwbar_eq]; exact hwBpos
                have hwbar_c : M.c (wbar M) = M.U M.C := by rw [hwbar_eq]; exact hwBeq.symm
                have hGamma_ne : ∀ w ∈ Icc 0 (wbar M),
                    {p ∈ Icc 0 (deriv M.U 0) |
                      0 ≤ M.U (tOf M p) - p * tOf M p - M.c w}.Nonempty := by
                  intro w hw
                  refine ⟨0, ⟨le_rfl, hD0.le⟩, ?_⟩
                  have hi := hcmono.monotoneOn hw.1 hwbar.le hw.2
                  rw [hwbar_c] at hi
                  simpa [ht_zero] using sub_nonneg.mpr hi
                have hGamma_anti : AntitoneOn (Gamma M) (Icc 0 (wbar M)) := by
                  intro x hx y hy hxy
                  apply csSup_le_csSup ⟨deriv M.U 0, fun p hp => hp.1.2⟩ (hGamma_ne y hy)
                  intro p hp
                  refine ⟨hp.1, ?_⟩
                  have hi := hcmono.monotoneOn hx.1 hy.1 hxy
                  linarith [hp.2]
                have hconcinc : ∀ (f : ℝ → ℝ), ConcaveOn ℝ univ f →
                    ∀ x y t : ℝ, x ≤ y → 0 ≤ t → f (y + t) - f y ≤ f (x + t) - f x := by
                  intro f hf x y t hxy ht
                  rcases hxy.eq_or_lt with h | h
                  · rw [h]
                  rcases ht.eq_or_lt with h' | h'
                  · rw [← h']; simp only [add_zero, sub_self, le_refl]
                  obtain ⟨D, hDd⟩ : ∃ D, D = y - x + t := ⟨_, rfl⟩
                  have hd : 0 < D := by linarith only [h, h', hDd]
                  have hr : 0 ≤ (y - x) / D := div_nonneg (sub_nonneg.mpr hxy) hd.le
                  have hu : 0 ≤ t / D := div_nonneg ht hd.le
                  have hru : (y - x) / D + t / D = 1 := by rw [← add_div, ← hDd, div_self hd.ne']
                  obtain ⟨r, hrr⟩ : ∃ r, r = (y - x) / D := ⟨_, rfl⟩
                  obtain ⟨u, huu⟩ : ∃ u, u = t / D := ⟨_, rfl⟩
                  rw [← hrr] at hr hru
                  rw [← huu] at hu hru
                  have hrD : r * D = y - x := by rw [hrr, div_mul_cancel₀ _ hd.ne']
                  have huD : u * D = t := by rw [huu, div_mul_cancel₀ _ hd.ne']
                  have hyt : y + t = x + D := by linarith only [hDd]
                  have he1 : r * x + u * (x + D) = x + t := by
                    calc _ = (r + u) * x + u * D := by ring
                      _ = _ := by rw [hru, huD, one_mul]
                  have he2 : u * x + r * (x + D) = y := by
                    calc _ = (r + u) * x + r * D := by ring
                      _ = _ := by rw [hru, hrD, one_mul]; ring
                  have h1 := hf.2 (mem_univ x) (mem_univ (x + D)) hr hu hru
                  have h2 := hf.2 (mem_univ x) (mem_univ (x + D)) hu hr (by rw [add_comm]; exact hru)
                  simp only [smul_eq_mul, he1, he2] at h1 h2
                  rw [hyt]
                  have he : r * f x + u * f (x + D) + (u * f x + r * f (x + D)) = f x + f (x + D) := by
                    calc
                      _ = (r + u) * (f x + f (x + D)) := by ring
                      _ = _ := by rw [hru, one_mul]
                  linarith only [h1, h2, he]
                have hsplice : ∀ (f : ℝ → ℝ) (b l u s : ℝ), l ≤ s → s ≤ u →
                    (∀ x y, b ≤ x → x ≤ y → l * (y - x) ≤ f y - f x ∧ f y - f x ≤ u * (y - x)) →
                    ∀ x y, x ≤ y →
                      l * (y - x) ≤ (if y < b then f b + s * (y - b) else f y) -
                        (if x < b then f b + s * (x - b) else f x) ∧
                      (if y < b then f b + s * (y - b) else f y) -
                        (if x < b then f b + s * (x - b) else f x) ≤ u * (y - x) := by
                  intro f b l u s hls hsu hf x y hxy
                  split_ifs with hy hx hx
                  · constructor <;> nlinarith only [hls, hsu, hxy]
                  · exfalso; linarith only [hy, hx, hxy]
                  · obtain ⟨hlo, hhi⟩ := hf b y le_rfl (not_lt.mp hy)
                    constructor <;> nlinarith only [hlo, hhi, hls, hsu, hx, hy]
                  · exact hf x y (not_lt.mp hx) hxy
                have halpha : 0 ≤ alpha obj := by cases obj <;> norm_num [alpha]
                have hInnerCont : ∀ (f : ℝ → ℝ), Continuous f → ∀ w,
                    ContinuousOn (fun p => v M obj p - alpha obj * M.c w + f (w + tOf M p) - f w)
                      (Icc 0 (Gamma M w)) := by
                  intro f hf w
                  have hs : Icc 0 (Gamma M w) ⊆ Icc 0 (deriv M.U 0) :=
                    fun p hp => ⟨hp.1, hp.2.trans (hGammaBounds w).2⟩
                  exact (((hvcont.mono hs).sub continuousOn_const).add
                    (hf.comp_continuousOn (continuousOn_const.add (htcont.mono hs)))).sub continuousOn_const
                have hInnerBdd : ∀ (f : ℝ → ℝ), Continuous f → ∀ w,
                    BddAbove ((fun p => v M obj p - alpha obj * M.c w + f (w + tOf M p) - f w) ''
                      Icc 0 (Gamma M w)) := by
                  intro f hf w
                  exact isCompact_Icc.bddAbove_image (hInnerCont f hf w)
                have hAdj_nonneg : ∀ (f : ℝ → ℝ) w, 0 ≤ slopeAdj M obj f w := by
                  intro f w
                  exact mul_nonneg hM.lam_pos.le (le_max_right _ _)
                have hAdj_mono : ∀ (f g : ℝ → ℝ), Continuous f → Continuous g → ∀ w,
                    (∀ p ∈ Icc 0 (Gamma M w), f (w + tOf M p) - f w ≤ g (w + tOf M p) - g w) →
                    slopeAdj M obj f w ≤ slopeAdj M obj g w := by
                  intro f g hf hg w hfg
                  apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
                  apply max_le_max_right
                  apply csSup_le (show ((fun p => v M obj p - alpha obj * M.c w + f (w + tOf M p) - f w) ''
                      Icc 0 (Gamma M w)).Nonempty from ⟨_, ⟨0, ⟨le_rfl, (hGammaBounds w).1⟩, rfl⟩⟩)
                  rintro _ ⟨p, hp, rfl⟩
                  apply le_trans _ (le_csSup (hInnerBdd g hg w) (mem_image_of_mem _ hp))
                  linarith [hfg p hp]
                have hAdj_eq : ∀ (f g : ℝ → ℝ) b,
                    (∀ w, b ≤ w → f w = g w) → slopeAdj M obj f b = slopeAdj M obj g b := by
                  intro f g b hfg
                  have he : (fun p => v M obj p - alpha obj * M.c b + f (b + tOf M p) - f b) '' Icc 0 (Gamma M b) =
                      (fun p => v M obj p - alpha obj * M.c b + g (b + tOf M p) - g b) '' Icc 0 (Gamma M b) := by
                    apply Set.image_congr
                    intro p hp
                    have ht0 := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩).1.1
                    rw [hfg b le_rfl, hfg (b + tOf M p) (by linarith)]
                  simp only [slopeAdj, innerMax, he]
                have hAdj_anti : ∀ (f : ℝ → ℝ), Continuous f → ConcaveOn ℝ univ f →
                    AntitoneOn (slopeAdj M obj f) (Icc 0 (wbar M)) := by
                  intro f hf hfc x hx y hy hxy
                  apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
                  apply max_le_max_right
                  apply csSup_le (show ((fun p => v M obj p - alpha obj * M.c y + f (y + tOf M p) - f y) ''
                      Icc 0 (Gamma M y)).Nonempty from ⟨_, ⟨0, ⟨le_rfl, (hGammaBounds y).1⟩, rfl⟩⟩)
                  rintro _ ⟨p, hp, rfl⟩
                  have hpx : p ∈ Icc 0 (Gamma M x) := ⟨hp.1, hp.2.trans (hGamma_anti hx hy hxy)⟩
                  apply le_trans _ (le_csSup (hInnerBdd f hf x) (mem_image_of_mem _ hpx))
                  have hc := mul_le_mul_of_nonneg_left (hcmono.monotoneOn hx.1 hy.1 hxy) halpha
                  have ht := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds y).2⟩).1.1
                  linarith [hconcinc f hfc x y (tOf M p) hxy ht]
                have hAffine : ∀ c d : ℝ, ConcaveOn ℝ univ (fun w : ℝ => c + d * w) := by
                  intro c d
                  refine ⟨convex_univ, ?_⟩
                  intro x hx y hy r u hr hu hru
                  simp only [smul_eq_mul]
                  have he : c + d * (r * x + u * y) = r * (c + d * x) + u * (c + d * y) := by
                    calc
                      _ = (r + u) * c + d * (r * x + u * y) := by rw [hru]; ring
                      _ = _ := by ring
                  exact he.ge
                let W : ℝ → ℕ → ℕ → ℝ → ℝ := fun g N =>
                  Nat.rec (fun w => -(w - wbar M) * g)
                    (fun k f w => if w < grid M N (N - k) then
                      f (grid M N (N - k)) +
                        (-g + slopeAdj M obj f (grid M N (N - k))) * (w - grid M N (N - k))
                      else f w)
                have hW0 : ∀ g N w, W g N 0 w = -(w - wbar M) * g := by intros; rfl
                have hWs : ∀ g N k w, W g N (k + 1) w =
                    if w < grid M N (N - k) then W g N k (grid M N (N - k)) +
                      (-g + slopeAdj M obj (W g N k) (grid M N (N - k))) * (w - grid M N (N - k))
                    else W g N k w := by intros; rfl
                have hgrid : ∀ N : ℕ, 0 < N → grid M N N = wbar M := by
                  intro N hN
                  dsimp [grid]
                  field_simp
                have hgrid_nonneg : ∀ N i : ℕ, 0 ≤ grid M N i := fun N i =>
                  mul_nonneg (Nat.cast_nonneg _) (div_nonneg hwbar.le (Nat.cast_nonneg _))
                have hgrid_mono : ∀ N : ℕ, Monotone (grid M N) := fun N i j hij =>
                  mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (div_nonneg hwbar.le (Nat.cast_nonneg _))
                have hW_inv : ∀ g : ℝ, ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                    ConcaveOn ℝ univ (W g N k) ∧ Continuous (W g N k) ∧
                    Monotone (fun w => W g N k w + g * w) ∧
                    (∀ w, wbar M ≤ w → W g N k w = -(w - wbar M) * g) ∧
                    ∃ s : ℝ,
                      (∀ w, w ≤ grid M N (N - k) →
                        W g N k w = W g N k (grid M N (N - k)) + s * (w - grid M N (N - k))) ∧
                      (∀ x y : ℝ, x ≤ y → W g N k y - W g N k x ≤ s * (y - x)) ∧
                      s ≤ -g + slopeAdj M obj (W g N k) (grid M N (N - k)) := by
                  intro g N hN k
                  induction k with
                  | zero =>
                    intro hk
                    refine ⟨?_, ?_, ?_, ?_, -g, ?_, ?_, ?_⟩
                    · have he : W g N 0 = (fun w => wbar M * g + -g * w) := by
                        ext w
                        rw [hW0]
                        ring
                      rw [he]
                      exact hAffine _ _
                    · change Continuous (fun w : ℝ => -(w - wbar M) * g)
                      fun_prop
                    · intro x y hxy
                      simp only [hW0]
                      ring_nf
                      exact le_rfl
                    · intro w hw; rfl
                    · intro w hw
                      simp only [hW0]
                      ring
                    · intro x y hxy
                      simp only [hW0]
                      nlinarith only []
                    · linarith [hAdj_nonneg (W g N 0) (grid M N (N - 0))]
                  | succ k ih =>
                    intro hk
                    obtain ⟨hfc, hfcont, hflow, hftail, s, hflin, hfup, hs⟩ := ih (by omega)
                    let b := grid M N (N - k)
                    let s' := -g + slopeAdj M obj (W g N k) b
                    have hss : s ≤ s' := hs
                    have hemin : W g N (k + 1) = (W g N k) ⊓ (fun w => W g N k b + s' * (w - b)) := by
                      ext w
                      rw [hWs]
                      change (if w < b then _ else _) = min _ _
                      split_ifs with hw
                      · rw [min_eq_right]
                        rw [hflin w hw.le]
                        nlinarith only [hss, hw]
                      · rw [min_eq_left]
                        have hi := hfup b w (not_lt.mp hw)
                        nlinarith only [hi, hss, hw]
                    have hnewc : ConcaveOn ℝ univ (W g N (k + 1)) := by
                      rw [hemin]
                      apply hfc.inf
                      have he : (fun w => W g N k b + s' * (w - b)) =
                          (fun w => (W g N k b - s' * b) + s' * w) := by ext w; ring
                      rw [he]
                      exact hAffine _ _
                    have hnewcont : Continuous (W g N (k + 1)) := by
                      exact (continuousOn_univ.mp (hnewc.continuousOn isOpen_univ))
                    have hnewlow : Monotone (fun w => W g N (k + 1) w + g * w) := by
                      intro x y hxy
                      have hi := (hsplice (W g N k) b (-g) s' s' (by dsimp [s']; linarith [hAdj_nonneg (W g N k) b])
                        le_rfl (by
                          intro x y hbx hxy
                          refine ⟨?_, (hfup x y hxy).trans ?_⟩
                          · have hi := hflow hxy; linarith only [hi]
                          · exact mul_le_mul_of_nonneg_right hss (sub_nonneg.mpr hxy))) x y hxy
                      have hlo := hi.1
                      change -g * (y - x) ≤ W g N (k + 1) y - W g N (k + 1) x at hlo
                      linarith only [hlo]
                    have hnewtail : ∀ w, wbar M ≤ w → W g N (k + 1) w = -(w - wbar M) * g := by
                      intro w hw
                      have hb : b ≤ wbar M := (hgrid_mono N (Nat.sub_le N k)).trans_eq (hgrid N hN)
                      rw [hWs, if_neg (by change ¬ w < b; linarith)]
                      exact hftail w hw
                    have hba : grid M N (N - (k + 1)) ≤ b := hgrid_mono N (by omega)
                    have hlinear : ∀ w, w ≤ b → W g N (k + 1) w = W g N k b + s' * (w - b) := by
                      intro w hw
                      rw [hWs]
                      change (if w < b then _ else _) = _
                      split_ifs with hw'
                      · rfl
                      · have he : w = b := by linarith
                        subst w; ring
                    have hnewup : ∀ x y, x ≤ y → W g N (k + 1) y - W g N (k + 1) x ≤ s' * (y - x) := by
                      intro x y hxy
                      have hi := (hsplice (W g N k) b (-g) s' s' (by dsimp [s']; linarith [hAdj_nonneg (W g N k) b])
                        le_rfl (by
                          intro x y hbx hxy
                          refine ⟨?_, (hfup x y hxy).trans ?_⟩
                          · have hi := hflow hxy; linarith only [hi]
                          · exact mul_le_mul_of_nonneg_right hss (sub_nonneg.mpr hxy))) x y hxy
                      exact hi.2
                    refine ⟨hnewc, hnewcont, hnewlow, hnewtail, s', ?_, hnewup, ?_⟩
                    · intro w hw
                      rw [hlinear w (hw.trans hba), hlinear _ hba]
                      ring
                    · have hAb : slopeAdj M obj (W g N (k + 1)) b = slopeAdj M obj (W g N k) b := by
                        apply hAdj_eq
                        intro w hw
                        rw [hWs, if_neg (show ¬ w < grid M N (N - k) from not_lt.mpr hw)]
                      have hb0 : 0 ≤ b := hgrid_nonneg _ _
                      have hbW : b ≤ wbar M := (hgrid_mono N (Nat.sub_le N k)).trans_eq (hgrid N hN)
                      have ha0 := hgrid_nonneg N (N - (k + 1))
                      have hantiA := hAdj_anti _ hnewcont hnewc ⟨ha0, hba.trans hbW⟩ ⟨hb0, hbW⟩ hba
                      rw [hAb] at hantiA
                      dsimp [s']
                      linarith only [hantiA]
                have hWmatch : ∀ g : ℝ, ∀ N k : ℕ, k ≤ N → ∀ w,
                    grid M N (N - k) ≤ w → W g N k w = VStep M obj g N k w := by
                  intro g N k
                  induction k with
                  | zero => intro hk w hw; rfl
                  | succ k ih =>
                    intro hk w hw
                    have hprev := ih (by omega)
                    have hAd : slopeAdj M obj (W g N k) (grid M N (N - k)) =
                        slopeAdj M obj (VStep M obj g N k) (grid M N (N - k)) :=
                      hAdj_eq _ _ _ hprev
                    rw [hWs, VStep]
                    dsimp only
                    by_cases hwb : w < grid M N (N - k)
                    · rw [if_pos hwb, if_pos ⟨hw, hwb⟩, hprev _ le_rfl, hAd]
                    · rw [if_neg hwb, if_neg (by tauto)]
                      exact hprev _ (not_lt.mp hwb)
                have hVW : ∀ g : ℝ, ∀ N : ℕ, ∀ w, 0 ≤ w → VgN M obj g N w = W g N N w := by
                  intro g N w hw
                  exact (hWmatch g N N le_rfl w (by simpa [grid] using hw)).symm
                have hKW : ∀ g : ℝ, ∀ N : ℕ, KgN M obj g N 0 = slopeAdj M obj (W g N N) 0 := by
                  intro g N
                  rw [KgN, if_pos rfl]
                  exact hAdj_eq _ _ _ (hVW g N)
                have hWsup : ∀ d e G : ℝ, 0 ≤ e → G = d + M.lam * e →
                    (∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ d * tOf M p + e) → ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                    ∀ x y, x ≤ y → W G N k y - W G N k x ≤ -d * (y - x) := by
                  intro d e G he0 hGdef hvde N hN k
                  have hGd : d ≤ G := by rw [hGdef]; linarith only [mul_nonneg hlam.le he0]
                  induction k with
                  | zero =>
                    intro hk x y hxy
                    simp only [hW0]
                    have hi := mul_le_mul_of_nonneg_right hGd (sub_nonneg.mpr hxy)
                    nlinarith only [hi]
                  | succ k ih =>
                    intro hk x y hxy
                    have hprev := ih (by omega)
                    let b := grid M N (N - k)
                    have hb0 : 0 ≤ b := hgrid_nonneg _ _
                    have hκ : slopeAdj M obj (W G N k) b ≤ M.lam * e := by
                      have hinner : innerMax M obj (W G N k) b ≤ e := by
                        apply csSup_le (show ((fun p => v M obj p - alpha obj * M.c b + W G N k (b + tOf M p) - W G N k b) ''
                          Icc 0 (Gamma M b)).Nonempty from ⟨_, ⟨0, ⟨le_rfl, (hGammaBounds b).1⟩, rfl⟩⟩)
                        rintro _ ⟨p, hp, rfl⟩
                        have hpt : p ∈ Icc 0 (deriv M.U 0) := ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩
                        have ht0 := (htmem p hpt).1.1
                        have hcost := mul_nonneg halpha (hc_nonneg b hb0)
                        have hdiff := hprev b (b + tOf M p) (by linarith)
                        linarith only [hvde p hpt, hcost, hdiff]
                      exact mul_le_mul_of_nonneg_left (max_le hinner he0) hM.lam_pos.le
                    have hlo := (hW_inv G N hN k (by omega)).2.2.1
                    have hi := hsplice (W G N k) b (-G) (-d) (-G + slopeAdj M obj (W G N k) b)
                      (by linarith only [hAdj_nonneg (W G N k) b])
                      (by linarith only [hκ, hGdef])
                      (by intro x y hbx hxy; exact ⟨by have := hlo hxy; linarith, hprev x y hxy⟩) x y hxy
                    exact hi.2
                have hGfeas' : ∀ d e G : ℝ, 0 ≤ d → 0 ≤ e → G = d + M.lam * e →
                    (∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ d * tOf M p + e) →
                    ∀ N : ℕ, 0 < N → 0 ≤ G ∧ KgN M obj G N 0 ≤ G := by
                  intro d e G hd he0 hGdef hvde N hN
                  refine ⟨by rw [hGdef]; linarith only [hd, mul_nonneg hlam.le he0], ?_⟩
                  rw [hKW]
                  have hinner : innerMax M obj (W G N N) 0 ≤ e := by
                    apply csSup_le (show ((fun p => v M obj p - alpha obj * M.c 0 + W G N N (0 + tOf M p) - W G N N 0) ''
                      Icc 0 (Gamma M 0)).Nonempty from ⟨_, ⟨0, ⟨le_rfl, (hGammaBounds 0).1⟩, rfl⟩⟩)
                    rintro _ ⟨p, hp, rfl⟩
                    have hpt : p ∈ Icc 0 (deriv M.U 0) := by simpa [hGamma0] using hp
                    have hi := hWsup d e G he0 hGdef hvde N hN N le_rfl 0 (0 + tOf M p) (by simpa using (htmem p hpt).1.1)
                    have hc := hM.c_zero
                    rw [hc] ; simp only [mul_zero, sub_zero]
                    linarith only [hvde p hpt, hi]
                  have hκ := mul_le_mul_of_nonneg_left (max_le hinner he0) hM.lam_pos.le
                  change M.lam * max (innerMax M obj (W G N N) 0) 0 ≤ G
                  exact hκ.trans (by linarith only [hd, hGdef])
                obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = deriv M.U 0 + M.lam * 0 := ⟨_, rfl⟩
                have hGfeas : ∀ N : ℕ, 0 < N → 0 ≤ G ∧ KgN M obj G N 0 ≤ G :=
                  hGfeas' (deriv M.U 0) 0 G hD0.le le_rfl hGdef (by intro p hp; simpa using hvb p hp)
                have hdiffsplice : ∀ (f₁ f₂ : ℝ → ℝ) (b s₁ s₂ : ℝ), s₁ ≤ s₂ →
                    Antitone (fun w => f₁ w - f₂ w) →
                    Antitone (fun w => (if w < b then f₁ b + s₁ * (w - b) else f₁ w) -
                      (if w < b then f₂ b + s₂ * (w - b) else f₂ w)) := by
                  intro f₁ f₂ b s₁ s₂ hs hf x y hxy
                  dsimp only
                  split_ifs with hy hx hx
                  · nlinarith only [hs, hxy]
                  · exfalso; linarith only [hy, hx, hxy]
                  · have hi := hf (not_lt.mp hy : b ≤ y)
                    dsimp at hi
                    nlinarith only [hi, hs, hx]
                  · exact hf hxy
                have hgrid_double : ∀ N k : ℕ, k ≤ N →
                    grid M (2 * N) (2 * N - 2 * k) = grid M N (N - k) := by
                  intro N k hk
                  rw [← Nat.mul_sub]
                  unfold grid
                  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, mul_comm (2:ℝ) ((N - k : ℕ) : ℝ), mul_assoc,
                    mul_div_assoc', mul_div_mul_left _ _ (two_ne_zero' ℝ)]
                have hW_refine : ∀ g : ℝ, ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                    Antitone (fun w => W g N k w - W g (2 * N) (2 * k) w) := by
                  intro g N hN k
                  induction k with
                  | zero =>
                    intro hk x y hxy
                    simp [hW0]
                  | succ k ih =>
                    intro hk
                    have hkN : k ≤ N := by omega
                    have hold := ih hkN
                    let b := grid M N (N - k)
                    let m := grid M (2 * N) (2 * N - (2 * k + 1))
                    have hb : grid M (2 * N) (2 * N - 2 * k) = b := hgrid_double N k hkN
                    have hmb : m ≤ b := by
                      rw [← hb]
                      exact hgrid_mono (2 * N) (by omega)
                    have hm0 : 0 ≤ m := hgrid_nonneg _ _
                    have hbW : b ≤ wbar M := (hgrid_mono N (Nat.sub_le _ _)).trans_eq (hgrid N hN)
                    have hb0 : 0 ≤ b := hgrid_nonneg _ _
                    have hco := hW_inv g N hN k hkN
                    have hfi := hW_inv g (2 * N) (by omega) (2 * k) (by omega)
                    have hfm := hW_inv g (2 * N) (by omega) (2 * k + 1) (by omega)
                    have hA₁ : slopeAdj M obj (W g N k) b ≤ slopeAdj M obj (W g (2 * N) (2 * k)) b := by
                      apply hAdj_mono _ _ hco.2.1 hfi.2.1
                      intro p hp
                      have ht0 := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩).1.1
                      have hi := hold (show b ≤ b + tOf M p by linarith)
                      dsimp at hi
                      linarith only [hi]
                    have hA₂ : slopeAdj M obj (W g (2 * N) (2 * k)) b ≤
                        slopeAdj M obj (W g (2 * N) (2 * k + 1)) m := by
                      have he : slopeAdj M obj (W g (2 * N) (2 * k + 1)) b =
                          slopeAdj M obj (W g (2 * N) (2 * k)) b := by
                        apply hAdj_eq
                        intro w hw
                        rw [hWs, hb, if_neg (not_lt.mpr hw)]
                      rw [← he]
                      exact hAdj_anti _ hfm.2.1 hfm.1 ⟨hm0, hmb.trans hbW⟩ ⟨hb0, hbW⟩ hmb
                    let s₁ := -g + slopeAdj M obj (W g N k) b
                    let s₂ := -g + slopeAdj M obj (W g (2 * N) (2 * k)) b
                    let s₃ := -g + slopeAdj M obj (W g (2 * N) (2 * k + 1)) m
                    have hD₁ : Antitone (fun w => W g N (k + 1) w - W g (2 * N) (2 * k + 1) w) := by
                      have hi := hdiffsplice (W g N k) (W g (2 * N) (2 * k)) b s₁ s₂
                        (by dsimp [s₁, s₂]; linarith only [hA₁]) hold
                      simpa only [hWs, hb] using hi
                    have hcoext : ∀ w,
                        (if w < m then W g N (k + 1) m + s₁ * (w - m) else W g N (k + 1) w) =
                          W g N (k + 1) w := by
                      intro w
                      split_ifs with hw
                      · have hmexpr : W g N (k + 1) m = W g N k b + s₁ * (m - b) := by
                          rw [hWs]
                          change (if m < b then _ else _) = _
                          split_ifs with hmlt
                          · rfl
                          · have he : m = b := by linarith only [hmb, hmlt]
                            rw [he]; ring
                        have hwexpr : W g N (k + 1) w = W g N k b + s₁ * (w - b) := by
                          rw [hWs, if_pos (show w < grid M N (N - k) from hw.trans_le hmb)]
                        rw [hmexpr, hwexpr]
                        ring
                      · rfl
                    have hD₂ := hdiffsplice (W g N (k + 1)) (W g (2 * N) (2 * k + 1)) m s₁ s₃
                      (by dsimp [s₁, s₃]; linarith only [hA₁, hA₂]) hD₁
                    have heN : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
                    rw [heN]
                    change Antitone (fun w => W g N (k + 1) w -
                      (if w < m then W g (2 * N) (2 * k + 1) m + s₃ * (w - m)
                        else W g (2 * N) (2 * k + 1) w))
                    simpa only [hcoext] using hD₂
                have hK_refine : ∀ g : ℝ, ∀ N : ℕ, 0 < N → KgN M obj g N 0 ≤ KgN M obj g (2 * N) 0 := by
                  intro g N hN
                  rw [hKW, hKW]
                  apply hAdj_mono _ _ (hW_inv g N hN N le_rfl).2.1
                    (hW_inv g (2 * N) (by omega) (2 * N) le_rfl).2.1
                  intro p hp
                  have ht0 := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds 0).2⟩).1.1
                  have hi := hW_refine g N hN N le_rfl (show (0 : ℝ) ≤ 0 + tOf M p by linarith)
                  dsimp at hi
                  linarith only [hi]
                have hg_bounds : ∀ N : ℕ, 0 < N → 0 ≤ gN M obj N ∧ gN M obj N ≤ G := by
                  intro N hN
                  have hne : {g : ℝ | 0 ≤ g ∧ KgN M obj g N 0 ≤ g}.Nonempty := ⟨G, hGfeas N hN⟩
                  exact ⟨le_csInf hne (fun g hg => hg.1), csInf_le ⟨0, fun g hg => hg.1⟩ (hGfeas N hN)⟩
                have hg_mono : ∀ N : ℕ, 0 < N → gN M obj N ≤ gN M obj (2 * N) := by
                  intro N hN
                  apply csInf_le_csInf ⟨0, fun g hg => hg.1⟩ ⟨G, hGfeas (2 * N) (by omega)⟩
                  intro g hg
                  exact ⟨hg.1, (hK_refine g N hN).trans hg.2⟩
                have hseqg : Monotone (fun j : ℕ => gN M obj (2 ^ j)) := by
                  apply monotone_nat_of_le_succ
                  intro j
                  simpa [pow_succ, Nat.mul_comm] using hg_mono (2 ^ j) (by positivity)
                have hglim : Tendsto (fun j : ℕ => gN M obj (2 ^ j)) atTop (𝓝 (gbar M obj)) := by
                  exact tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciSup hseqg
                    ⟨G, by rintro _ ⟨j, rfl⟩; exact (hg_bounds _ (by positivity)).2⟩⟩
                have hgb0 : 0 ≤ gbar M obj := ge_of_tendsto hglim (Eventually.of_forall fun j : ℕ => (hg_bounds (2 ^ j) (by positivity)).1)
                have hgbG : gbar M obj ≤ G := le_of_tendsto hglim (Eventually.of_forall fun j : ℕ => (hg_bounds (2 ^ j) (by positivity)).2)
                have hWmin : ∀ g : ℝ, ∀ N : ℕ, 0 < N → ∀ k : ℕ, k < N →
                    W g N (k + 1) = (W g N k) ⊓ (fun w => W g N k (grid M N (N - k)) +
                      (-g + slopeAdj M obj (W g N k) (grid M N (N - k))) * (w - grid M N (N - k))) := by
                  intro g N hN k hk
                  obtain ⟨hfc, hfcont, hflow, hftail, s, hlin, hup, hs⟩ := hW_inv g N hN k hk.le
                  ext w
                  rw [hWs]
                  change (if w < grid M N (N - k) then _ else _) = min _ _
                  split_ifs with hw
                  · rw [min_eq_right]
                    rw [hlin w hw.le]
                    nlinarith only [hs, hw]
                  · rw [min_eq_left]
                    have hi := hup (grid M N (N - k)) w (not_lt.mp hw)
                    nlinarith only [hi, hs, hw]
                have hAg_cont : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ b : ℝ,
                    Continuous (fun g => slopeAdj M obj (F g) b) := by
                  intro F hF b
                  let K := Icc 0 (Gamma M b)
                  have htK : Continuous (fun p : K => tOf M p) :=
                    (htcont.mono (fun p hp => ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩)).restrict
                  have hvK : Continuous (fun p : K => v M obj p) :=
                    (hvcont.mono (fun p hp => ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩)).restrict
                  let f : ℝ → K → ℝ := fun g p => v M obj p - alpha obj * M.c b + F g (b + tOf M p) - F g b
                  have hfc : Continuous (Function.uncurry f) := by
                    exact (((hvK.comp continuous_snd).sub continuous_const).add
                      (hF.comp (continuous_fst.prodMk (continuous_const.add (htK.comp continuous_snd))))).sub
                        (hF.comp (continuous_fst.prodMk continuous_const))
                  have hsc := (isCompact_univ : IsCompact (univ : Set K)).continuous_sSup (f := f) hfc
                  have he : ∀ g, f g '' univ =
                      (fun p => v M obj p - alpha obj * M.c b + F g (b + tOf M p) - F g b) '' Icc 0 (Gamma M b) := by
                    intro g
                    ext r
                    constructor
                    · rintro ⟨p, hp, rfl⟩
                      exact ⟨p, p.property, rfl⟩
                    · rintro ⟨p, hp, rfl⟩
                      exact ⟨⟨p, hp⟩, mem_univ _, rfl⟩
                  have hic : Continuous (fun g => innerMax M obj (F g) b) := by
                    simpa only [he, innerMax] using hsc
                  exact continuous_const.mul (hic.max continuous_const)
                have hW_joint : ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                    Continuous (fun z : ℝ × ℝ => W z.1 N k z.2) := by
                  intro N hN k
                  induction k with
                  | zero =>
                    intro hk
                    change Continuous (fun z : ℝ × ℝ => -(z.2 - wbar M) * z.1)
                    fun_prop
                  | succ k ih =>
                    intro hk
                    have hprev := ih (by omega)
                    have hAc := hAg_cont (fun g => W g N k) hprev (grid M N (N - k))
                    have hline : Continuous (fun z : ℝ × ℝ => W z.1 N k (grid M N (N - k)) +
                        (-z.1 + slopeAdj M obj (W z.1 N k) (grid M N (N - k))) * (z.2 - grid M N (N - k))) := by
                      exact (hprev.comp (continuous_fst.prodMk continuous_const)).add
                        ((continuous_fst.neg.add (hAc.comp continuous_fst)).mul (continuous_snd.sub continuous_const))
                    have he : (fun z : ℝ × ℝ => W z.1 N (k + 1) z.2) =
                        (fun z => min (W z.1 N k z.2) (W z.1 N k (grid M N (N - k)) +
                          (-z.1 + slopeAdj M obj (W z.1 N k) (grid M N (N - k))) * (z.2 - grid M N (N - k)))) := by
                      ext z
                      rw [hWmin z.1 N hN k (by omega)]
                      rfl
                    rw [he]
                    exact hprev.min hline
                have hKg_cont : ∀ N : ℕ, 0 < N → Continuous (fun g => KgN M obj g N 0) := by
                  intro N hN
                  simpa only [hKW] using hAg_cont (fun g => W g N N) (hW_joint N hN N le_rfl) 0
                have hg_root : ∀ N : ℕ, 0 < N → KgN M obj (gN M obj N) N 0 ≤ gN M obj N := by
                  intro N hN
                  have hc : IsClosed {g : ℝ | 0 ≤ g ∧ KgN M obj g N 0 ≤ g} :=
                    isClosed_Ici.inter (isClosed_le (hKg_cont N hN) continuous_id)
                  exact (hc.csInf_mem ⟨G, hGfeas N hN⟩ ⟨0, fun g hg => hg.1⟩).2
                have hW_gmono : ∀ g₁ g₂ : ℝ, g₁ ≤ g₂ → ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                    Antitone (fun w => W g₂ N k w - W g₁ N k w) := by
                  intro g₁ g₂ hgg N hN k
                  induction k with
                  | zero =>
                    intro hk x y hxy
                    simp only [hW0]
                    nlinarith only [hgg, hxy]
                  | succ k ih =>
                    intro hk
                    have hprev := ih (by omega)
                    let b := grid M N (N - k)
                    have hA : slopeAdj M obj (W g₂ N k) b ≤ slopeAdj M obj (W g₁ N k) b := by
                      apply hAdj_mono _ _ (hW_inv g₂ N hN k (by omega)).2.1 (hW_inv g₁ N hN k (by omega)).2.1
                      intro p hp
                      have ht0 := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds b).2⟩).1.1
                      have hi := hprev (show b ≤ b + tOf M p by linarith)
                      dsimp at hi
                      linarith only [hi]
                    have hi := hdiffsplice (W g₂ N k) (W g₁ N k) b
                      (-g₂ + slopeAdj M obj (W g₂ N k) b) (-g₁ + slopeAdj M obj (W g₁ N k) b)
                      (by linarith only [hgg, hA]) hprev
                    exact hi
                have hK_gmono : ∀ g₁ g₂ : ℝ, g₁ ≤ g₂ → ∀ N : ℕ, 0 < N →
                    KgN M obj g₂ N 0 ≤ KgN M obj g₁ N 0 := by
                  intro g₁ g₂ hgg N hN
                  rw [hKW, hKW]
                  apply hAdj_mono _ _ (hW_inv g₂ N hN N le_rfl).2.1 (hW_inv g₁ N hN N le_rfl).2.1
                  intro p hp
                  have ht0 := (htmem p ⟨hp.1, hp.2.trans (hGammaBounds 0).2⟩).1.1
                  have hi := hW_gmono g₁ g₂ hgg N hN N le_rfl (show (0 : ℝ) ≤ 0 + tOf M p by linarith)
                  dsimp at hi
                  linarith only [hi]
                have hgjbar : ∀ j : ℕ, gN M obj (2 ^ j) ≤ gbar M obj := by
                  intro j
                  exact ge_of_tendsto hglim (eventually_atTop.mpr ⟨j, fun k hjk => hseqg hjk⟩)
                have hWgb_anti : ∀ j : ℕ, Antitone (W (gbar M obj) (2 ^ j) (2 ^ j)) := by
                  intro j
                  obtain ⟨hfc, hcont, hlo, htail, s, hlin, hup, hs⟩ :=
                    hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl
                  have hκ : slopeAdj M obj (W (gbar M obj) (2 ^ j) (2 ^ j)) 0 ≤ gbar M obj := by
                    rw [← hKW]
                    exact ((hK_gmono _ _ (hgjbar j) _ (by positivity)).trans (hg_root _ (by positivity))).trans (hgjbar j)
                  have hs0 : s ≤ 0 := by
                    simp only [Nat.sub_self, grid, Nat.cast_zero, zero_mul] at hs
                    linarith only [hs, hκ]
                  intro x y hxy
                  have hi := hup x y hxy
                  have hi' := mul_nonpos_of_nonpos_of_nonneg hs0 (sub_nonneg.mpr hxy)
                  linarith only [hi, hi']
                have hWgb_lip : ∀ j : ℕ, ∀ x y : ℝ,
                    |W (gbar M obj) (2 ^ j) (2 ^ j) x - W (gbar M obj) (2 ^ j) (2 ^ j) y| ≤
                      gbar M obj * |x - y| := by
                  intro j x y
                  have hlo := (hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl).2.2.1
                  rcases le_total x y with hxy | hyx
                  · rw [abs_of_nonneg (sub_nonneg.mpr (hWgb_anti j hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
                    have hi := hlo hxy
                    dsimp at hi
                    linarith only [hi]
                  · rw [abs_of_nonpos (sub_nonpos.mpr (hWgb_anti j hyx)), abs_of_nonneg (sub_nonneg.mpr hyx)]
                    have hi := hlo hyx
                    dsimp at hi
                    linarith only [hi]
                have hVseq_anti : ∀ w, 0 ≤ w → Antitone (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) := by
                  intro w hw
                  apply antitone_nat_of_succ_le
                  intro j
                  rw [hVW _ _ _ hw, hVW _ _ _ hw]
                  have hdiff := hW_refine (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl
                  by_cases hww : w ≤ wbar M
                  · have hi := hdiff hww
                    have ht₁ := (hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl).2.2.2.1 (wbar M) le_rfl
                    have ht₂ := (hW_inv (gbar M obj) (2 * 2 ^ j) (by positivity) (2 * 2 ^ j) le_rfl).2.2.2.1 (wbar M) le_rfl
                    dsimp at hi
                    rw [ht₁, ht₂] at hi
                    simpa [pow_succ, Nat.mul_comm] using sub_nonneg.mp (show 0 ≤ W (gbar M obj) (2 ^ j) (2 ^ j) w -
                      W (gbar M obj) (2 * 2 ^ j) (2 * 2 ^ j) w by linarith only [hi])
                  · have ht₁ := (hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl).2.2.2.1 w (not_le.mp hww).le
                    have ht₂ := (hW_inv (gbar M obj) (2 ^ (j + 1)) (by positivity) (2 ^ (j + 1)) le_rfl).2.2.2.1 w (not_le.mp hww).le
                    rw [ht₁, ht₂]
                have hVlim : ∀ w, 0 ≤ w → Tendsto (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) atTop (𝓝 (Vbar M obj w)) := by
                  intro w hw
                  have hb : BddBelow (range (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w)) := by
                    refine ⟨-gbar M obj * |w - wbar M|, ?_⟩
                    rintro _ ⟨j, rfl⟩
                    dsimp only
                    rw [hVW _ _ _ hw]
                    have hi := hWgb_lip j w (wbar M)
                    have ht := (hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl).2.2.2.1 (wbar M) le_rfl
                    rw [ht] at hi
                    have hlo := (abs_le.mp hi).1
                    simpa only [sub_self, neg_zero, zero_mul, sub_zero, neg_mul] using hlo
                  exact tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciInf (hVseq_anti w hw) hb⟩
                have hVlip : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
                    |Vbar M obj x - Vbar M obj y| ≤ gbar M obj * |x - y| := by
                  intro x y hx hy
                  apply le_of_tendsto (((hVlim x hx).sub (hVlim y hy)).abs)
                  apply Eventually.of_forall
                  intro j
                  rw [hVW _ _ _ hx, hVW _ _ _ hy]
                  exact hWgb_lip j x y
                have hVcc : ConcaveOn ℝ (Ici 0) (Vbar M obj) := by
                  refine ⟨convex_Ici 0, ?_⟩
                  intro x hx y hy r u hr hu hru
                  have hz : (0:ℝ) ≤ r • x + u • y := by
                    simp only [smul_eq_mul]
                    exact add_nonneg (mul_nonneg hr hx) (mul_nonneg hu hy)
                  refine le_of_tendsto_of_tendsto (((hVlim x hx).const_smul r).add ((hVlim y hy).const_smul u)) (hVlim _ hz) ?_
                  apply Eventually.of_forall
                  intro j
                  dsimp only
                  rw [hVW _ _ _ hx, hVW _ _ _ hy, hVW _ _ _ hz]
                  exact (hW_inv (gbar M obj) (2 ^ j) (by positivity) (2 ^ j) le_rfl).1.2 (mem_univ x) (mem_univ y) hr hu hru
                have hVcont : ContinuousOn (Vbar M obj) (Ici 0) := by
                  have hl : LipschitzOnWith (⟨gbar M obj, hgb0⟩ : NNReal) (Vbar M obj) (Ici 0) := by
                    apply LipschitzOnWith.of_dist_le_mul
                    intro x hx y hy
                    change dist (Vbar M obj x) (Vbar M obj y) ≤ gbar M obj * dist x y
                    simpa only [Real.dist_eq] using hVlip x y hx hy
                  exact hl.continuousOn
                refine ⟨hVcc, hVcont, ?_, ?_⟩
                · intro d e hd he hvde
                  apply le_of_tendsto hglim
                  apply Eventually.of_forall
                  intro j
                  exact csInf_le ⟨0, fun g hg => hg.1⟩ (hGfeas' d e _ hd he rfl hvde (2 ^ j) (by positivity))
                · intro p hp
                  have hfe : ∀ N : ℕ, 0 < N → ∀ g : ℝ, KgN M obj g N 0 ≤ g → M.lam * (v M obj p - g * tOf M p) ≤ g := by
                    intro N hN g hg
                    refine le_trans ?_ hg
                    rw [hKW]
                    have hinv := hW_inv g N hN N le_rfl
                    apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
                    apply le_trans _ (le_max_left _ _)
                    apply le_trans _ (le_csSup (hInnerBdd _ hinv.2.1 0) (mem_image_of_mem _ (show p ∈ Icc 0 (Gamma M 0) by rw [hGamma0]; exact hp)))
                    have hi := hinv.2.2.1 (show (0:ℝ) ≤ 0 + tOf M p by simpa using (htmem p hp).1.1)
                    dsimp only at hi
                    rw [hM.c_zero]
                    linarith only [hi]
                  have hN : ∀ j : ℕ, M.lam * (v M obj p - gN M obj (2 ^ j) * tOf M p) ≤ gN M obj (2 ^ j) :=
                    fun j => hfe _ (by positivity) _ (hg_root _ (by positivity))
                  exact le_of_tendsto_of_tendsto
                    (((tendsto_const_nhds.sub (hglim.mul_const _)).const_mul _)) hglim (Eventually.of_forall hN)
            have P2 : ∀ (M : Model) (obj : Objective), M.Standing →
                ConcaveOn ℝ (Ici 0) (Vbar M obj) → ContinuousOn (Vbar M obj) (Ici 0) →
                ∀ w, 0 ≤ w → w ≤ what M → (∃ t : ℝ, serviceArgmax M obj w = {t}) ∧
                  (w ≤ wbar M → PStar M obj w = feedback M (concreteReward M obj) (Vbar M obj) w) := by
              as_aux_lemma =>
                intro M obj hM hVcc hVc w hw0 hww
                have hC := hM.C_pos
                have hUd : Differentiable ℝ M.U := hM.U_contDiff.differentiable (by norm_num)
                have hDcont : Continuous (deriv M.U) := hM.U_contDiff.continuous_deriv (by norm_num)
                have hDdiff : Differentiable ℝ (deriv M.U) :=
                  (show ContDiff ℝ 2 M.U from hM.U_contDiff.of_le (by norm_num)).differentiable_deriv_two
                have hanti : StrictAntiOn (deriv M.U) (Icc 0 M.C) := by
                  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hDcont.continuousOn
                  intro x hx
                  exact hM.deriv2_U_neg x (interior_subset hx)
                have hD0 : 0 < deriv M.U 0 := by
                  have h := hanti (left_mem_Icc.mpr hC.le) (right_mem_Icc.mpr hC.le) hC
                  have hn := hM.deriv_U_nonneg M.C (right_mem_Icc.mpr hC.le)
                  linarith only [h, hn]
                have htmem : ∀ p ∈ Icc 0 (deriv M.U 0),
                    tOf M p ∈ Icc 0 M.C ∧ p ≤ deriv M.U (tOf M p) := by
                  intro p hp
                  have hne : {t ∈ Icc 0 M.C | p ≤ deriv M.U t}.Nonempty :=
                    ⟨0, ⟨⟨le_rfl, hC.le⟩, hp.2⟩⟩
                  have hb : BddAbove {t ∈ Icc 0 M.C | p ≤ deriv M.U t} :=
                    ⟨M.C, fun t ht => ht.1.2⟩
                  exact (isClosed_Icc.inter (isClosed_le continuous_const hDcont)).csSup_mem hne hb
                have ht_deriv : ∀ s ∈ Icc 0 M.C, tOf M (deriv M.U s) = s := by
                  intro s hs
                  apply le_antisymm
                  · change sSup {t ∈ Icc 0 M.C | deriv M.U s ≤ deriv M.U t} ≤ s
                    refine csSup_le (s := {t ∈ Icc 0 M.C | deriv M.U s ≤ deriv M.U t}) ⟨s, hs, le_rfl⟩ ?_
                    intro t ht
                    by_contra h
                    exact (not_lt_of_ge ht.2) (hanti hs ht.1 (lt_of_not_ge h))
                  · exact le_csSup ⟨M.C, fun t ht => ht.1.2⟩ ⟨hs, le_rfl⟩
                have htC : ∀ p, 0 ≤ p → p ≤ deriv M.U M.C → tOf M p = M.C := by
                  intro p hp0 hp
                  have hp1 : p ∈ Icc 0 (deriv M.U 0) := ⟨hp0, hp.trans (hM.deriv_U_le _ ⟨hC.le, le_rfl⟩)⟩
                  exact le_antisymm (htmem p hp1).1.2 (le_csSup ⟨M.C, fun t ht => ht.1.2⟩ ⟨⟨hC.le, le_rfl⟩, hp⟩)
                have ht_inv : ∀ p, deriv M.U M.C ≤ p → p ≤ deriv M.U 0 → deriv M.U (tOf M p) = p := by
                  intro p hp1 hp2
                  obtain ⟨t, ht, htp⟩ := intermediate_value_Icc' hC.le hDcont.continuousOn
                    (show p ∈ Icc (deriv M.U M.C) (deriv M.U 0) from ⟨hp1, hp2⟩)
                  rw [← htp, ht_deriv t ht]
                have hcmono : StrictMonoOn M.c (Ici 0) := by
                  apply strictMonoOn_of_deriv_pos (convex_Ici _) hM.c_contDiff.continuous.continuousOn
                  intro x hx
                  exact hM.deriv_c_pos x (interior_subset hx)
                -- h t = U t - U' t * t
                have hhder : ∀ t, HasDerivAt (fun t => M.U t - deriv M.U t * t) (-(deriv (deriv M.U) t) * t) t := by
                  intro t
                  exact ((hUd t).hasDerivAt.sub ((hDdiff t).hasDerivAt.mul (hasDerivAt_id t))).congr_deriv (by simp)
                have hhcont : Continuous (fun t => M.U t - deriv M.U t * t) :=
                  continuous_iff_continuousAt.mpr fun t => (hhder t).continuousAt
                have hhmono : StrictMonoOn (fun t => M.U t - deriv M.U t * t) (Icc 0 M.C) := by
                  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hhcont.continuousOn
                  intro t ht
                  rw [(hhder t).deriv]
                  have h1 := hM.deriv2_U_neg t (interior_subset ht)
                  rw [interior_Icc] at ht
                  exact mul_pos (neg_pos.mpr h1) ht.1
                have hK0 : 0 < M.U M.C - deriv M.U M.C * M.C := by
                  have := hhmono ⟨le_rfl, hC.le⟩ ⟨hC.le, le_rfl⟩ hC
                  simpa [hM.U_zero] using this
                have hcw : M.c w ≤ M.U M.C - deriv M.U M.C * M.C := by
                  by_cases hne : ({x ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c x = 0}).Nonempty
                  · obtain ⟨x, hx0, hx⟩ := hne
                    have hset : {x ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c x = 0} = {x} := by
                      ext y; simp only [mem_ofPred_eq, mem_singleton_iff, mem_Ioi]
                      constructor
                      · rintro ⟨hy0, hy⟩
                        exact hcmono.injOn (le_of_lt hy0) (le_of_lt (show (0:ℝ) < x from hx0)) (by linarith)
                      · rintro rfl; exact ⟨hx0, hx⟩
                    have he : what M = x := by unfold what; rw [hset, csSup_singleton]
                    rw [he] at hww
                    have := hcmono.monotoneOn hw0 (le_of_lt (show (0:ℝ) < x from hx0)) hww
                    linarith
                  · rw [not_nonempty_iff_eq_empty] at hne
                    have hwh : what M = 0 := by unfold what; rw [hne, Real.sSup_empty]
                    have : w = 0 := by rw [hwh] at hww; linarith
                    rw [this, hM.c_zero]; exact hK0.le
                -- L
                have hLmem : Lw M w ∈ {t ∈ Icc 0 M.C | 0 ≤ M.U t - deriv M.U t * t - M.c w} := by
                  apply IsClosed.csInf_mem
                  · exact isClosed_Icc.inter (isClosed_le continuous_const (hhcont.sub continuous_const))
                  · exact ⟨M.C, ⟨hC.le, le_rfl⟩, by linarith⟩
                  · exact ⟨0, fun t ht => ht.1.1⟩
                obtain ⟨L, hLdef⟩ : ∃ L, L = Lw M w := ⟨_, rfl⟩
                rw [← hLdef] at hLmem
                obtain ⟨⟨hL0, hLC⟩, hLh⟩ := hLmem
                have hLmin : ∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w → L ≤ t := by
                  intro t ht h
                  rw [hLdef]
                  exact csInf_le ⟨0, fun t ht => ht.1.1⟩ ⟨ht, h⟩
                have hDL0 : 0 ≤ deriv M.U L := hM.deriv_U_nonneg L ⟨hL0, hLC⟩
                have hDLC : deriv M.U M.C ≤ deriv M.U L := hanti.antitoneOn ⟨hL0, hLC⟩ ⟨hC.le, le_rfl⟩ hLC
                have hDC0 : 0 ≤ deriv M.U M.C := hM.deriv_U_nonneg M.C ⟨hC.le, le_rfl⟩
                have hGam : Gamma M w = deriv M.U L := by
                  unfold Gamma
                  have : {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w} = Icc 0 (deriv M.U L) := by
                    ext p; simp only [mem_ofPred_eq, mem_Icc]
                    constructor
                    · rintro ⟨⟨hp0, hp1⟩, hp⟩
                      refine ⟨hp0, ?_⟩
                      by_contra hlt
                      push Not at hlt
                      have hinv := ht_inv p (by linarith) hp1
                      have htm := (htmem p ⟨hp0, hp1⟩).1
                      have := hLmin _ htm (by rw [hinv]; exact hp)
                      have := hanti.antitoneOn ⟨hL0, hLC⟩ htm this
                      linarith
                    · rintro ⟨hp0, hpL⟩
                      have hp1 : p ≤ deriv M.U 0 := hpL.trans (hM.deriv_U_le L ⟨hL0, hLC⟩)
                      refine ⟨⟨hp0, hp1⟩, ?_⟩
                      rcases le_total p (deriv M.U M.C) with h | h
                      · rw [htC p hp0 h]
                        have := mul_le_mul_of_nonneg_right h hC.le
                        linarith
                      · have hinv := ht_inv p h hp1
                        have htm := (htmem p ⟨hp0, hp1⟩).1
                        have hLt : L ≤ tOf M p := by
                          by_contra hlt
                          push Not at hlt
                          have := hanti htm ⟨hL0, hLC⟩ hlt
                          linarith
                        have := hhmono.monotoneOn ⟨hL0, hLC⟩ htm hLt
                        simp only [hinv] at this
                        linarith
                  rw [this, csSup_Icc hDL0]
                -- strict concavity
                have hvstrict : StrictConcaveOn ℝ (Icc 0 M.C) (fun t => v M obj (deriv M.U t)) := by
                  cases obj with
                  | revenue =>
                    have hr : StrictConcaveOn ℝ (Icc 0 M.C) (fun t => deriv M.U t * t) := by
                      apply strictConcaveOn_of_deriv2_neg' (convex_Icc _ _)
                      · exact (hDcont.mul continuous_id).continuousOn
                      · intro t ht
                        exact hM.deriv2_revenue_neg t ht
                    refine hr.congr ?_
                    intro t ht
                    simp only [v]
                    rw [ht_deriv t ht]
                  | welfare =>
                    have hr : StrictConcaveOn ℝ (Icc 0 M.C) M.U := by
                      apply strictConcaveOn_of_deriv2_neg' (convex_Icc _ _)
                      · exact hUd.continuous.continuousOn
                      · intro t ht
                        exact hM.deriv2_U_neg t ht
                    refine hr.congr ?_
                    intro t ht
                    simp only [v]
                    rw [ht_deriv t ht]
                have hvcont : ContinuousOn (fun t => v M obj (deriv M.U t)) (Icc 0 M.C) := by
                  cases obj with
                  | revenue =>
                    refine ((hDcont.mul continuous_id).continuousOn (s := Icc 0 M.C)).congr ?_
                    intro t ht
                    simp only [v]
                    rw [ht_deriv t ht]; rfl
                  | welfare =>
                    refine (hUd.continuous.continuousOn (s := Icc 0 M.C)).congr ?_
                    intro t ht
                    simp only [v]
                    rw [ht_deriv t ht]
                have hVwcc : ConcaveOn ℝ (Icc 0 M.C) (fun t => Vbar M obj (w + t)) := by
                  refine ⟨convex_Icc _ _, ?_⟩
                  intro x hx y hy r u hr hu hru
                  have := hVcc.2 (show (w + x) ∈ Ici (0:ℝ) from add_nonneg hw0 hx.1)
                    (show (w + y) ∈ Ici (0:ℝ) from add_nonneg hw0 hy.1) hr hu hru
                  have he : r • (w + x) + u • (w + y) = w + (r • x + u • y) := by
                    simp only [smul_eq_mul]
                    calc _ = (r + u) * w + (r * x + u * y) := by ring
                      _ = _ := by rw [hru, one_mul]
                  rw [he] at this
                  exact this
                have hVwc : ContinuousOn (fun t => Vbar M obj (w + t)) (Icc 0 M.C) := by
                  apply hVc.comp (continuous_const.add continuous_id).continuousOn
                  intro t ht
                  exact add_nonneg hw0 ht.1
                have hxc : ContinuousOn (fun t => xiHat M obj t w) (Icc 0 M.C) := by
                  unfold xiHat f
                  exact ((hvcont.sub continuousOn_const).add hVwc).sub continuousOn_const
                have hxs : StrictConcaveOn ℝ (Icc 0 M.C) (fun t => xiHat M obj t w) := by
                  have h := (hvstrict.add_concaveOn hVwcc).add_const (-(alpha obj * M.c w) - Vbar M obj w)
                  refine h.congr ?_
                  intro t ht
                  simp only [xiHat, f, Pi.add_apply]
                  ring
                have hsub : Icc L M.C ⊆ Icc 0 M.C := Icc_subset_Icc_left hL0
                obtain ⟨T, hT, hTmax⟩ := isCompact_Icc.exists_isMaxOn
                  (show (Icc L M.C).Nonempty from ⟨L, le_rfl, hLC⟩) (hxc.mono hsub)
                have hxs' : StrictConcaveOn ℝ (Icc L M.C) (fun t => xiHat M obj t w) :=
                  hxs.subset hsub (convex_Icc _ _)
                have hset : serviceArgmax M obj w = {T} := by
                  ext t
                  simp only [serviceArgmax, ← hLdef, mem_ofPred_eq, mem_singleton_iff]
                  constructor
                  · rintro ⟨ht, htm⟩
                    exact hxs'.eq_of_isMaxOn (fun u hu => htm u hu) hTmax ht hT
                  · rintro rfl
                    exact ⟨hT, fun u hu => hTmax hu⟩
                refine ⟨⟨T, hset⟩, ?_⟩
                intro hwb
                have htS : tStar M obj w = T := by unfold tStar; rw [hset, csSup_singleton]
                have hxieq : ∀ t ∈ Icc 0 M.C, xi M (concreteReward M obj) (Vbar M obj) (deriv M.U t) w = xiHat M obj t w := by
                  intro t ht
                  simp only [xi, concreteReward, xiHat, f, ht_deriv t ht]
                have hT0 := hsub hT
                have hTD : deriv M.U T ∈ Icc 0 (deriv M.U L) :=
                  ⟨hM.deriv_U_nonneg T hT0, hanti.antitoneOn ⟨hL0, hLC⟩ hT0 hT.1⟩
                -- every feasible price p: xi p ≤ xiHat T
                have hup : ∀ p ∈ Icc 0 (deriv M.U L), tOf M p ∈ Icc L M.C ∧
                    xi M (concreteReward M obj) (Vbar M obj) p w ≤ xiHat M obj (tOf M p) w := by
                  intro p hp
                  have hp1 : p ≤ deriv M.U 0 := hp.2.trans (hM.deriv_U_le L ⟨hL0, hLC⟩)
                  rcases le_total p (deriv M.U M.C) with h | h
                  · rw [htC p hp.1 h]
                    refine ⟨⟨hLC, le_rfl⟩, ?_⟩
                    simp only [xi, concreteReward, xiHat, f, htC p hp.1 h]
                    have : v M obj p ≤ v M obj (deriv M.U M.C) := by
                      cases obj <;> simp only [v, htC p hp.1 h, htC _ hDC0 le_rfl]
                      · exact mul_le_mul_of_nonneg_right h hC.le
                      · exact le_rfl
                    linarith
                  · have hinv := ht_inv p h hp1
                    have htm := (htmem p ⟨hp.1, hp1⟩).1
                    refine ⟨⟨?_, htm.2⟩, ?_⟩
                    · by_contra hlt
                      push Not at hlt
                      have := hanti htm ⟨hL0, hLC⟩ hlt
                      linarith [hp.2]
                    · rw [← hxieq _ htm, hinv]
                have hpb : pbar M (concreteReward M obj) (Vbar M obj) w = deriv M.U T := by
                  unfold pbar
                  apply IsGreatest.csSup_eq
                  unfold priceArgmax
                  rw [hGam]
                  refine ⟨⟨hTD, ?_⟩, ?_⟩
                  · intro q hq
                    rw [hxieq T hT0]
                    exact (hup q hq).2.trans (hTmax (hup q hq).1)
                  · rintro p ⟨hp, hpm⟩
                    have h1 := hpm _ hTD
                    rw [hxieq T hT0] at h1
                    obtain ⟨h2, h3⟩ := hup p hp
                    have h4 : tOf M p = T := by
                      refine hxs'.eq_of_isMaxOn (fun u hu => ?_) hTmax h2 hT
                      exact (hTmax hu).trans (h1.trans h3)
                    rw [← h4]
                    exact (htmem p ⟨hp.1, hp.2.trans (hM.deriv_U_le L ⟨hL0, hLC⟩)⟩).2
                unfold PStar feedback
                have hmem : w ∈ Icc 0 (wbar M) := ⟨hw0, hwb⟩
                rw [if_pos hmem, if_pos hmem, if_pos hww, hpb, hxieq T hT0, htS]
                split_ifs <;> rfl
            refine ⟨?_, ?_⟩
            ·
              intro M obj hM w hw
              by_cases hww : w ≤ what M
              · exact (P2 M obj hM (P1 M obj hM).1 (P1 M obj hM).2.1 w hw.1 hww).2 hw.2
              · have hC := hM.C_pos
                have hU3 : ContDiff ℝ (2 + 1) M.U := hM.U_contDiff
                have hUd : Differentiable ℝ M.U := (contDiff_succ_iff_deriv.mp hU3).1
                have hU'd : Differentiable ℝ (deriv M.U) :=
                  (contDiff_succ_iff_deriv.mp hU3).2.2.differentiable (by norm_num)
                have hc2 : ContDiff ℝ (1 + 1) M.c := hM.c_contDiff
                have hcd : Differentiable ℝ M.c := (contDiff_succ_iff_deriv.mp hc2).1
                have hc'd : Differentiable ℝ (deriv M.c) :=
                  (contDiff_succ_iff_deriv.mp hc2).2.2.differentiable (by norm_num)
                have hanti : AntitoneOn (deriv M.U) (Icc 0 M.C) := by
                  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 M.C) hU'd.continuous.continuousOn
                    hU'd.differentiableOn
                  intro x hx; rw [interior_Icc] at hx
                  exact (hM.deriv2_U_neg x (Ioo_subset_Icc_self hx)).le
                have hcmono : StrictMonoOn M.c (Ici 0) := by
                  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcd.continuous.continuousOn
                  intro x hx; rw [interior_Ici] at hx
                  exact hM.deriv_c_pos x (le_of_lt hx)
                have hc'mono : MonotoneOn (deriv M.c) (Ici 0) := by
                  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc'd.continuous.continuousOn
                    hc'd.differentiableOn
                  intro x hx; rw [interior_Ici] at hx
                  exact hM.deriv2_c_nonneg x (le_of_lt hx)
                have hclin : ∀ x, 0 ≤ x → deriv M.c 0 * x ≤ M.c x := by
                  have hmo : MonotoneOn (fun x => M.c x - deriv M.c 0 * x) (Ici 0) := by
                    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
                    · exact (hcd.continuous.sub (continuous_const.mul continuous_id)).continuousOn
                    · exact (hcd.sub (differentiable_const _ |>.mul differentiable_id)).differentiableOn
                    · intro x hx; rw [interior_Ici] at hx
                      have h1 : HasDerivAt (fun x => M.c x - deriv M.c 0 * x) (deriv M.c x - deriv M.c 0 * 1) x :=
                        (hcd x).hasDerivAt.sub ((hasDerivAt_id x).const_mul _)
                      rw [h1.deriv]
                      have := hc'mono (mem_Ici.mpr le_rfl) (show (0:ℝ) ≤ x from le_of_lt hx) (show (0:ℝ) ≤ x from le_of_lt hx)
                      linarith
                  intro x hx
                  have := hmo (mem_Ici.mpr le_rfl) hx hx
                  simp only [hM.c_zero, mul_zero, sub_zero] at this
                  linarith
                have hc0 := hM.deriv_c_pos 0 le_rfl
                obtain ⟨hw0, hwb⟩ := hw
                -- (ii) c w ≤ U C
                have hii : M.c w ≤ M.U M.C := by
                  by_cases hne : ({x ∈ Ioi (0:ℝ) | M.U M.C = M.c x}).Nonempty
                  · obtain ⟨x, hx0, hx⟩ := hne
                    have hset : {x ∈ Ioi (0:ℝ) | M.U M.C = M.c x} = {x} := by
                      ext y; simp only [mem_setOf_eq, mem_singleton_iff, mem_Ioi]
                      constructor
                      · rintro ⟨hy0, hy⟩
                        exact hcmono.injOn (le_of_lt hy0) (le_of_lt (show (0:ℝ) < x from hx0)) (hy.symm.trans hx)
                      · rintro rfl; exact ⟨hx0, hx⟩
                    have : wbar M = x := by unfold wbar; rw [hset, csSup_singleton]
                    rw [this] at hwb
                    rw [hx]; exact hcmono.monotoneOn hw0 (le_of_lt (show (0:ℝ) < x from hx0)) hwb
                  · rw [not_nonempty_iff_eq_empty] at hne
                    have : wbar M = 0 := by unfold wbar; rw [hne, Real.sSup_empty]
                    have hw00 : w = 0 := le_antisymm (this ▸ hwb) hw0
                    rw [hw00, hM.c_zero]; exact hM.U_nonneg _ ⟨hC.le, le_rfl⟩
                -- (i) h C < c w
                have hi : M.U M.C - deriv M.U M.C * M.C < M.c w := by
                  set K := M.U M.C - deriv M.U M.C * M.C with hK
                  by_cases hne : ({x ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c x = 0}).Nonempty
                  · obtain ⟨x, hx0, hx⟩ := hne
                    have hset : {x ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c x = 0} = {x} := by
                      ext y; simp only [mem_setOf_eq, mem_singleton_iff, mem_Ioi]
                      constructor
                      · rintro ⟨hy0, hy⟩
                        exact hcmono.injOn (le_of_lt hy0) (le_of_lt (show (0:ℝ) < x from hx0)) (by linarith)
                      · rintro rfl; exact ⟨hx0, hx⟩
                    have : what M = x := by unfold what; rw [hset, csSup_singleton]
                    rw [this, not_le] at hww
                    have := hcmono (le_of_lt (show (0:ℝ) < x from hx0)) hw0 hww
                    linarith
                  · rw [not_nonempty_iff_eq_empty] at hne
                    have hwh : what M = 0 := by unfold what; rw [hne, Real.sSup_empty]
                    have hwpos : 0 < w := by rw [hwh] at hww; linarith
                    by_contra hcon
                    push Not at hcon
                    set W := max w (K / deriv M.c 0) with hW
                    have hwW : w ≤ W := le_max_left _ _
                    have hcW : K ≤ M.c W := by
                      have := hclin W (le_trans hw0 hwW)
                      have h2 : K / deriv M.c 0 ≤ W := le_max_right _ _
                      have h3 : K ≤ deriv M.c 0 * W := by
                        rw [div_le_iff₀ hc0] at h2; linarith
                      linarith
                    obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ := intermediate_value_Icc hwW hcd.continuous.continuousOn ⟨hcon, hcW⟩
                    have : y ∈ ({x ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c x = 0}) :=
                      ⟨lt_of_lt_of_le hwpos hy1, by linarith [hy]⟩
                    rw [hne] at this; exact this
                set q := qPrice M w with hqdef
                have hqC : q * M.C = M.U M.C - M.c w := by
                  rw [hqdef]; unfold qPrice; field_simp
                have hq0 : 0 ≤ q := by
                  rw [hqdef]; unfold qPrice; exact div_nonneg (by linarith) hC.le
                have hqU : q < deriv M.U M.C := by
                  by_contra h; push Not at h
                  have := mul_le_mul_of_nonneg_right h hC.le
                  linarith
                have hUC0 : deriv M.U M.C ≤ deriv M.U 0 := hM.deriv_U_le _ ⟨hC.le, le_rfl⟩
                have F4 : ∀ p, p ≤ deriv M.U M.C → tOf M p = M.C := by
                  intro p hp
                  unfold tOf
                  have : {t ∈ Icc 0 M.C | p ≤ deriv M.U t} = Icc 0 M.C := by
                    ext t; simp only [mem_ofPred_eq, and_iff_left_iff_imp]
                    intro ht; exact le_trans hp (hanti ht ⟨hC.le, le_rfl⟩ ht.2)
                  rw [this, csSup_Icc hC.le]
                have F4' : ∀ p, p ≤ deriv M.U 0 → tOf M p ∈ Icc 0 M.C := by
                  intro p hp
                  unfold tOf
                  have hne : ({t ∈ Icc 0 M.C | p ≤ deriv M.U t}).Nonempty := ⟨0, ⟨le_rfl, hC.le⟩, hp⟩
                  have hbdd : BddAbove {t ∈ Icc 0 M.C | p ≤ deriv M.U t} := ⟨M.C, fun t ht => ht.1.2⟩
                  exact ⟨le_csSup_of_le hbdd ⟨⟨le_rfl, hC.le⟩, hp⟩ le_rfl, csSup_le hne fun t ht => ht.1.2⟩
                have hGmono : MonotoneOn (fun s => M.U s - deriv M.U M.C * s) (Icc 0 M.C) := by
                  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 M.C)
                  · exact (hUd.continuous.sub (continuous_const.mul continuous_id)).continuousOn
                  · exact (hUd.sub (differentiable_const _ |>.mul differentiable_id)).differentiableOn
                  · intro x hx; rw [interior_Icc] at hx
                    have h1 : HasDerivAt (fun s => M.U s - deriv M.U M.C * s) (deriv M.U x - deriv M.U M.C * 1) x :=
                      (hUd x).hasDerivAt.sub ((hasDerivAt_id x).const_mul _)
                    rw [h1.deriv]
                    have := hanti (Ioo_subset_Icc_self hx) ⟨hC.le, le_rfl⟩ hx.2.le
                    linarith
                have F5 : Gamma M w = q := by
                  unfold Gamma
                  have : {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w} = Icc 0 q := by
                    ext p; simp only [mem_ofPred_eq, mem_Icc]
                    constructor
                    · rintro ⟨⟨hp0, hp1⟩, hp⟩
                      refine ⟨hp0, ?_⟩
                      by_cases hpc : p ≤ deriv M.U M.C
                      · rw [F4 p hpc] at hp
                        by_contra hlt; push Not at hlt
                        have := mul_lt_mul_of_pos_right hlt hC
                        linarith
                      · push Not at hpc
                        exfalso
                        have ht := F4' p hp1
                        have h1 := hGmono ht ⟨hC.le, le_rfl⟩ ht.2
                        have h2 : deriv M.U M.C * tOf M p ≤ p * tOf M p := mul_le_mul_of_nonneg_right hpc.le ht.1
                        simp only at h1
                        linarith
                    · rintro ⟨hp0, hpq⟩
                      refine ⟨⟨hp0, by linarith⟩, ?_⟩
                      rw [F4 p (by linarith)]
                      have := mul_le_mul_of_nonneg_right hpq hC.le
                      linarith
                  rw [this, csSup_Icc hq0]
                have F6 : pbar M (concreteReward M obj) (Vbar M obj) w = q := by
                  unfold pbar
                  apply IsGreatest.csSup_eq
                  unfold priceArgmax
                  rw [F5]
                  refine ⟨⟨⟨hq0, le_rfl⟩, ?_⟩, fun p hp => hp.1.2⟩
                  intro p hp
                  have hpC := F4 p (by linarith [hp.2])
                  have hqC' := F4 q hqU.le
                  have hpq := mul_le_mul_of_nonneg_right hp.2 hC.le
                  cases obj <;> simp only [xi, concreteReward, v, alpha, hpC, hqC']
                  · linarith only [hpq]
                  · exact le_rfl
                unfold PStar feedback
                have hmem : w ∈ Icc 0 (wbar M) := ⟨hw0, hwb⟩
                rw [if_pos hmem, if_pos hmem, if_neg hww, F6]
                have hqC' := F4 q hqU.le
                simp only [xi, concreteReward, hqC']
                rfl
            intro M g r
            have hMdef : M = testModel (1/100) := rfl
            have hgdef : g = gbar M .revenue := rfl
            have hrdef : r = 3/2 - g := rfl
            clear_value r g M
            have hU : ∀ t, deriv M.U t = 2 - t := by
              intro t
              rw [hMdef]; show deriv (fun t : ℝ => 2 * t - t ^ 2 / 2) t = 2 - t
              have : HasDerivAt (fun t : ℝ => 2 * t - t ^ 2 / 2) (2 * 1 - (2 * t ^ 1 * 1) / 2) t := by
                exact ((hasDerivAt_id t).const_mul 2).sub ((hasDerivAt_pow 2 t).div_const 2) |>.congr_deriv (by simp)
              rw [this.deriv]; ring
            have hUfun : deriv M.U = fun t => 2 - t := funext hU
            have hwhat : what M = 1 / 2 := by
              unfold what
              have : {w ∈ Ioi (0:ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c w = 0} = {1/2} := by
                ext w; simp only [hU, mem_setOf_eq, mem_Ioi, mem_singleton_iff]
                simp only [hMdef, testModel, id]
                constructor
                · rintro ⟨-, h⟩; linarith
                · rintro rfl; norm_num
              rw [this, csSup_singleton]
            have hwbar : wbar M = 3 / 2 := by
              unfold wbar
              have : {w ∈ Ioi (0:ℝ) | M.U M.C = M.c w} = {3/2} := by
                ext w; simp only [mem_setOf_eq, mem_Ioi, mem_singleton_iff]
                simp only [hMdef, testModel, id]
                constructor
                · rintro ⟨-, h⟩; linarith
                · rintro rfl; norm_num
              rw [this, csSup_singleton]
            have hst : M.Standing := by
              have hc : ∀ w, deriv M.c w = 1 := by
                intro w; rw [hMdef]; show deriv id w = 1; simp
              have hrev : deriv (fun s => deriv M.U s * s) = fun s => 2 - 2 * s := by
                rw [hUfun]; funext s
                have : HasDerivAt (fun s : ℝ => (2 - s) * s) ((0 - 1) * s + (2 - s) * 1) s :=
                  ((hasDerivAt_const s (2:ℝ)).sub (hasDerivAt_id s)).mul (hasDerivAt_id s)
                rw [this.deriv]; ring
              refine ⟨by norm_num [hMdef, testModel], by norm_num [hMdef, testModel], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hMdef]; show ContDiff ℝ 3 (fun t : ℝ => 2 * t - t ^ 2 / 2); fun_prop
              · rw [hMdef]; show ContDiff ℝ 2 (id : ℝ → ℝ); exact contDiff_id
              · intro t ht; simp only [hMdef, testModel, mem_Icc] at ht ⊢; nlinarith [ht.1, ht.2]
              · simp [hMdef, testModel]
              · intro t ht; simp only [hMdef, testModel, mem_Icc] at ht; rw [hU]; linarith
              · intro t ht; simp only [hMdef, testModel, mem_Icc] at ht; rw [hU, hU]; linarith
              · intro t _; rw [hUfun]
                have : deriv (fun t : ℝ => 2 - t) t = -1 := by
                  have h : HasDerivAt (fun t : ℝ => 2 - t) (0 - 1) t := ((hasDerivAt_const t (2:ℝ)).sub (hasDerivAt_id t))
                  rw [h.deriv]; ring
                rw [this]; norm_num
              · intro t _; rw [hrev]
                have h : HasDerivAt (fun s : ℝ => 2 - 2 * s) (0 - 2 * 1) t := ((hasDerivAt_const t (2:ℝ)).sub ((hasDerivAt_id t).const_mul 2))
                rw [h.deriv]; norm_num
              · simp [hMdef, testModel]
              · intro w _; rw [hc]; norm_num
              · intro w _
                have : deriv M.c = fun _ => 1 := funext hc
                rw [this]; simp

            have htOf : ∀ p : ℝ, p ≤ 2 → tOf M p = min 1 (2 - p) := by
              intro p hp
              unfold tOf
              have : {t ∈ Icc 0 M.C | p ≤ deriv M.U t} = Icc 0 (min 1 (2 - p)) := by
                ext t; simp only [hU, mem_Icc, mem_ofPred_eq, le_min_iff]
                simp only [hMdef, testModel]
                constructor
                · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
                · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
              rw [this, csSup_Icc (by simp only [le_min_iff]; constructor <;> linarith)]
            have hGamma : ∀ x : ℝ, 1/2 < x → Gamma M x ≤ max (3/2 - x) 0 := by
              intro x hx
              unfold Gamma
              apply Real.sSup_le _ (le_max_right _ _)
              rintro p ⟨⟨hp0, hp2⟩, hp⟩
              rw [hU] at hp2
              rw [htOf p (by linarith only [hp2])] at hp
              simp only [hMdef, testModel, id] at hp
              rcases le_total p 1 with h | h
              · rw [min_eq_left (by linarith only [h])] at hp
                exact le_max_of_le_left (by linarith only [hp])
              · rw [min_eq_right (by linarith only [h])] at hp
                exfalso
                have h1 := mul_nonneg (sub_nonneg.mpr h) (show (0:ℝ) ≤ 3 - p by linarith only [hp2])
                linarith only [h1, hp, hx]
            have hVstep : ∀ (G : ℝ), 0 < G → G < 1 → ∀ (N k : ℕ), ∀ w, 3/2 - G ≤ w →
                VStep M .revenue G N k w = (3/2 - w) * G := by
              intro G hG0 hG1 N k
              induction k with
              | zero => intro w _; simp only [VStep, hwbar]; ring
              | succ k ih =>
                intro w hw
                obtain ⟨x, hx⟩ : ∃ x, x = grid M N (N - k) := ⟨_, rfl⟩
                simp only [VStep, ← hx]
                by_cases hc : grid M N (N - (k + 1)) ≤ w ∧ w < x
                · rw [if_pos hc]
                  have hxG : 3/2 - G ≤ x := by linarith only [hc.2, hw]
                  have hsl : slopeAdj M .revenue (VStep M .revenue G N k) x = 0 := by
                    unfold slopeAdj innerMax
                    have hs : sSup ((fun p => v M .revenue p - alpha .revenue * M.c x +
                        VStep M .revenue G N k (x + tOf M p) - VStep M .revenue G N k x) '' Icc 0 (Gamma M x)) ≤ 0 := by
                      apply Real.sSup_le _ le_rfl
                      rintro _ ⟨p, ⟨hp0, hp⟩, rfl⟩
                      have hgam := hGamma x (by linarith only [hxG, hG1])
                      have hpg : p ≤ G := le_trans hp (le_trans hgam (max_le (by linarith only [hxG]) hG0.le))
                      have ht := htOf p (by linarith only [hpg, hG1])
                      rw [min_eq_left (by linarith only [hpg, hG1])] at ht
                      simp only [v, alpha, ht]
                      rw [ih _ (by linarith only [hxG]), ih _ hxG]
                      linarith only [hpg]
                    rw [max_eq_right hs, mul_zero]
                  rw [hsl, ih _ hxG]; ring
                · rw [if_neg hc]; exact ih w hw
            have hVbar : 0 < g → g < 1 → ∀ w, r ≤ w → Vbar M .revenue w = (3/2 - w) * g := by
              intro h0 h1 w hw
              unfold Vbar
              rw [← hgdef]
              have : (fun j : ℕ => VgN M .revenue g (2^j) w) = fun _ => (3/2 - w) * g :=
                funext fun j => hVstep g h0 h1 _ _ w (by rw [hrdef] at hw; exact hw)
              rw [this]; exact tendsto_const_nhds.limUnder_eq
            obtain ⟨Q1, Q2, Q3, Q4⟩ := P1 M .revenue hst
            have hlamv : M.lam = 1 / 100 := by rw [hMdef]; rfl
            rw [← hgdef] at Q3 Q4
            have hg0 : 0 < g := by
              have h := Q4 1 (by rw [hU]; constructor <;> norm_num)
              have ht1 : tOf M 1 = 1 := by rw [htOf 1 (by norm_num)]; norm_num
              simp only [v, ht1, hlamv] at h
              linarith
            have hg1 : g < 1 := by
              have h := Q3 0 1 le_rfl zero_le_one (by
                intro p hp
                rw [hU] at hp
                have hp2 := hp.2
                simp only [v]
                rw [htOf p (by linarith only [hp2]), zero_mul, zero_add]
                rcases le_total p 1 with h | h
                · rw [min_eq_left (by linarith only [h])]; linarith only [h]
                · rw [min_eq_right (by linarith only [h])]; linarith only [sq_nonneg (p - 1)])
              rw [hlamv] at h
              linarith only [h]
            have hrI : r ∈ Icc 0 (wbar M) := by
              rw [hwbar]; exact ⟨by linarith only [hrdef, hg1], by linarith only [hrdef, hg0]⟩
            have hrh : ¬ r ≤ what M := by rw [hwhat]; linarith only [hrdef, hg1]
            have hC : M.C = 1 := by rw [hMdef]; rfl
            have hUv : ∀ t, M.U t = 2 * t - t ^ 2 / 2 := by intro t; rw [hMdef]; rfl
            have hcv : ∀ w, M.c w = w := by intro w; rw [hMdef]; rfl
            have htOf1 : ∀ p, p ≤ 1 → tOf M p = 1 := by
              intro p hp
              rw [htOf p (by linarith only [hp]), min_eq_left (by linarith only [hp])]
            have htOf2 : tOf M 2 = 0 := by rw [htOf 2 le_rfl]; norm_num
            have hqP : ∀ w, qPrice M w = 3/2 - w := by
              intro w; unfold qPrice; rw [hC, hUv, hcv]; ring
            have hVr : Vbar M .revenue r = g * g := by
              rw [hVbar hg0 hg1 _ le_rfl, show (3:ℝ)/2 - r = g by linarith only [hrdef]]
            have hPr : PStar M .revenue r = g := by
              have hq : qPrice M r = g := by rw [hqP]; linarith only [hrdef]
              unfold PStar
              simp only [if_pos hrI, if_neg hrh, hq]
              rw [if_pos]
              rw [hC, hVbar hg0 hg1 _ (by linarith only), hVr, show (3:ℝ)/2 - (r+1) = g - 1 by linarith only [hrdef]]
              simp only [v, alpha]
              rw [htOf1 g hg1.le]
              apply le_of_eq; ring
            have hTr : TStar M .revenue r = 1 := by
              unfold TStar
              simp only [if_pos hrI, if_neg hrh, hPr]
              unfold tJoin
              rw [htOf1 g hg1.le, if_pos (by rw [hUv, hcv]; linarith only [hrdef])]
            have hTw : ∀ w ∈ Ioc r (wbar M), TStar M .revenue w = 0 := by
              rintro w ⟨hw1, hw2⟩
              have hwI : w ∈ Icc 0 (wbar M) := ⟨hrI.1.trans hw1.le, hw2⟩
              have hwh : ¬ w ≤ what M := fun h => hrh (hw1.le.trans h)
              have hP : PStar M .revenue w = deriv M.U 0 := by
                unfold PStar
                simp only [if_pos hwI, if_neg hwh]
                rw [if_neg]
                rw [hqP, hC, hVbar hg0 hg1 _ (by linarith only [hw1]), hVbar hg0 hg1 _ hw1.le]
                simp only [v, alpha]
                rw [htOf1 _ (by linarith only [hw1, hrdef, hg1])]
                intro h; linarith only [h, hw1, hrdef]
              unfold TStar
              simp only [if_pos hwI, if_neg hwh, hP, hU]
              unfold tJoin
              simp only [sub_zero, htOf2, ite_self]
            refine ⟨hst, hwhat, hwbar, hg0, hg1, not_le.mp hrh, by rw [hwbar]; linarith only [hrdef, hg0],
              ?_, hPr, hTr, hTw, ?_⟩
            · intro w hw
              exact (P2 M .revenue hst Q1 Q2 w hw.1 hw.2).1
            · rintro ⟨-, W1, W2, W3, -, -, -, -, h3b, -, -, -, -, hCw, hz, -⟩
              rcases le_or_gt W3 r with h | h
              · have h1 := hz r ⟨h, hrI.2⟩
                rw [hTr] at h1
                exact one_ne_zero h1
              · have h1 := hCw ((r + W3)/2) ⟨by linarith only [not_le.mp hrh, h], by linarith only [h]⟩
                have h2 := hTw ((r + W3)/2) ⟨by linarith only [h], by linarith only [h, h3b]⟩
                rw [h1, hC] at h2
                exact one_ne_zero h2
