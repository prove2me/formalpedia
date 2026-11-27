-- Prove2me | solution 1 for WaitTimePricing.Existence.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:05.658054+00:00
-- url     : https://prove2.me/submissions/afbb2b72-e50e-4240-9333-743cfffe69e0

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Definitions.Def_WaitTimePricing_Existence_Supplement_Rewards

set_option autoImplicit false

open WaitTimePricing
open WaitTimePricing.Existence
open WaitTimePricing.Existence.Supplement

open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 18, Lemma 4.
Formalization Note: for each concrete objective the constructed base Vbar is used, with the
greatest-price maximizer and the admission-on-equality convention of (25),(26). Standing is the
immutable base predicate (global C³/C² extensions and positive λ,C). The abstract reward extension
on p. 11 is refuted in theorem_2; it is not silently covered by Objective's two constructors. -/
theorem solution (M : Model) (obj : Objective) (hM : M.Standing) :
    0 < tJoin M (feedback M (concreteReward M obj) (Vbar M obj) 0) 0 := by
      open Filter in
        open scoped Topology in
          set_option maxHeartbeats 0 in
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
            have ht_pos : ∀ p ∈ Ico 0 (deriv M.U 0), 0 < tOf M p := by
              intro p hp
              have he : ∀ᶠ t in 𝓝 (0 : ℝ), p < deriv M.U t :=
                hDcont.continuousAt.eventually (lt_mem_nhds hp.2)
              obtain ⟨ε, hε, heε⟩ := Metric.eventually_nhds_iff.mp he
              let s := min ε M.C / 2
              have hs : 0 < s := by dsimp [s]; positivity
              have hsε : s < ε := by dsimp [s]; have := min_le_left ε M.C; linarith
              have hsC : s ≤ M.C := by dsimp [s]; have := min_le_right ε M.C; linarith
              have hsp : p < deriv M.U s := heε (by simpa [Real.dist_eq, abs_of_pos hs] using hsε)
              have hm : s ≤ tOf M p := le_csSup ⟨M.C, fun t ht => ht.1.2⟩
                ⟨⟨hs.le, hsC⟩, hsp.le⟩
              exact hs.trans_le hm
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
            have hvtop : v M obj (deriv M.U 0) = 0 := by
              cases obj <;> simp [v, ht_top, hM.U_zero]
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
            have hquad : ∀ t ∈ Icc 0 M.C,
                M.U t ≤ deriv M.U 0 * t - a / 2 * t ^ 2 := by
              let f : ℝ → ℝ := fun t => M.U t - deriv M.U 0 * t + a / 2 * t ^ 2
              have hfder : ∀ t, HasDerivAt f (deriv M.U t - deriv M.U 0 + a * t) t := by
                intro t
                have hi := (((hUdiff t).hasDerivAt.sub ((hasDerivAt_id t).const_mul (deriv M.U 0))).add
                  ((hasDerivAt_pow 2 t).const_mul (a / 2)))
                exact hi.congr_deriv (by ring)
              have hfanti : AntitoneOn f (Icc 0 M.C) := by
                apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
                  (by
                    exact ((hUdiff.continuous.sub (continuous_const.mul continuous_id)).add
                      (continuous_const.mul (continuous_id.pow 2))).continuousOn)
                  (fun t ht => (hfder t).differentiableAt.differentiableWithinAt)
                intro t ht
                rw [(hfder t).deriv]
                have hi := hstrong 0 ⟨le_rfl, hC.le⟩ t (interior_subset ht) (interior_subset ht).1
                nlinarith only [hi]
              intro t ht
              have hi := hfanti ⟨le_rfl, hC.le⟩ ht ht.1
              dsimp [f] at hi
              rw [hM.U_zero] at hi
              nlinarith only [hi]
            have hvquad : ∀ p ∈ Icc 0 (deriv M.U 0),
                v M obj p ≤ deriv M.U 0 * tOf M p - a / 2 * (tOf M p) ^ 2 := by
              intro p hp
              cases obj with
              | welfare => exact hquad _ (htmem p hp).1
              | revenue =>
                have hi := hstrong 0 ⟨le_rfl, hC.le⟩ _ (htmem p hp).1 (htmem p hp).1.1
                have hi' := mul_le_mul_of_nonneg_right (htmem p hp).2 (htmem p hp).1.1
                have hi'' := mul_le_mul_of_nonneg_right hi (htmem p hp).1.1
                change p * tOf M p ≤ _
                have hn := mul_nonneg ha.le (sq_nonneg (tOf M p))
                nlinarith only [hi', hi'', hn]
            have hconcinc : ∀ (f : ℝ → ℝ), ConcaveOn ℝ univ f →
                ∀ x y t : ℝ, x ≤ y → 0 ≤ t → f (y + t) - f y ≤ f (x + t) - f x := by
              intro f hf x y t hxy ht
              by_cases hzero : y - x + t = 0
              · have hye : y = x := by linarith
                have hte : t = 0 := by linarith
                simp [hye, hte]
              have hd : 0 < y - x + t := lt_of_le_of_ne (by linarith) (Ne.symm hzero)
              let r := (y - x) / (y - x + t)
              let u := t / (y - x + t)
              have hr : 0 ≤ r := by dsimp [r]; positivity
              have hu : 0 ≤ u := by dsimp [u]; positivity
              have hru : r + u = 1 := by dsimp [r, u]; field_simp <;> ring
              have he1 : r * x + u * (y + t) = x + t := by dsimp [r, u]; field_simp <;> ring
              have he2 : u * x + r * (y + t) = y := by dsimp [r, u]; field_simp <;> ring
              have h1 := hf.2 (mem_univ x) (mem_univ (y + t)) hr hu hru
              have h2 := hf.2 (mem_univ x) (mem_univ (y + t)) hu hr (by linarith : u + r = 1)
              simp only [smul_eq_mul, he1, he2] at h1 h2
              have he : r * f x + u * f (y + t) + (u * f x + r * f (y + t)) = f x + f (y + t) := by
                calc
                  _ = (r + u) * (f x + f (y + t)) := by ring
                  _ = _ := by rw [hru]; ring
              linarith
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
            have hgrid_nonneg : ∀ N i : ℕ, 0 ≤ grid M N i := by
              intro N i
              dsimp [grid]
              positivity
            have hgrid_mono : ∀ N : ℕ, Monotone (grid M N) := by
              intro N i j hij
              dsimp [grid]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
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
            let δ := min (deriv M.U 0 / 2) (a / (M.lam + 1))
            have hδ : 0 < δ := by dsimp [δ]; positivity
            have hδU : δ ≤ deriv M.U 0 / 2 := min_le_left _ _
            have hδa : δ * (M.lam + 1) ≤ a := by
              apply (le_div_iff₀ (by linarith [hM.lam_pos] : 0 < M.lam + 1)).mp
              exact min_le_right _ _
            have hdeltaLam : M.lam * δ < 2 * a := by nlinarith only [hδa, hδ, ha]
            let e := δ ^ 2 / (2 * a)
            let d := deriv M.U 0 - δ
            let G := d + M.lam * e
            have he0 : 0 ≤ e := by dsimp [e]; positivity
            have heq : 2 * a * e = δ ^ 2 := by dsimp [e]; field_simp
            have hLame : M.lam * e < δ := by
              have hi := mul_pos hδ (sub_pos.mpr hdeltaLam)
              apply (mul_lt_mul_iff_right₀ (show 0 < 2 * a by positivity)).mp
              calc
                2 * a * (M.lam * e) = M.lam * (2 * a * e) := by ring
                _ = M.lam * δ ^ 2 := by rw [heq]
                _ < 2 * a * δ := by nlinarith only [hi]
            have hd : 0 < d := by dsimp [d]; linarith only [hδU, hD0]
            have hG : 0 < G := by dsimp [G]; positivity
            have hGU : G < deriv M.U 0 := by dsimp [G, d]; linarith only [hLame]
            have hGd : d ≤ G := by dsimp [G]; linarith only [mul_nonneg hlam.le he0]
            have hvde : ∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ d * tOf M p + e := by
              intro p hp
              have hi := mul_le_mul_of_nonneg_left (hvquad p hp) (show 0 ≤ 2 * a by positivity)
              have hs := sq_nonneg (a * tOf M p - δ)
              apply (mul_le_mul_iff_right₀ (show 0 < 2 * a by positivity)).mp
              dsimp [d]
              nlinarith only [hi, hs, heq]
            have hWsup : ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
                ∀ x y, x ≤ y → W G N k y - W G N k x ≤ -d * (y - x) := by
              intro N hN k
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
                  (by dsimp [G]; linarith only [hκ])
                  (by intro x y hbx hxy; exact ⟨by have := hlo hxy; linarith, hprev x y hxy⟩) x y hxy
                exact hi.2
            have hGfeas : ∀ N : ℕ, 0 < N → 0 ≤ G ∧ KgN M obj G N 0 ≤ G := by
              intro N hN
              refine ⟨hG.le, ?_⟩
              rw [hKW]
              have hinner : innerMax M obj (W G N N) 0 ≤ e := by
                apply csSup_le (show ((fun p => v M obj p - alpha obj * M.c 0 + W G N N (0 + tOf M p) - W G N N 0) ''
                  Icc 0 (Gamma M 0)).Nonempty from ⟨_, ⟨0, ⟨le_rfl, (hGammaBounds 0).1⟩, rfl⟩⟩)
                rintro _ ⟨p, hp, rfl⟩
                have hpt : p ∈ Icc 0 (deriv M.U 0) := by simpa [hGamma0] using hp
                have hi := hWsup N hN N le_rfl 0 (0 + tOf M p) (by simpa using (htmem p hpt).1.1)
                have hc := hM.c_zero
                rw [hc] ; simp only [mul_zero, sub_zero]
                linarith only [hvde p hpt, hi]
              have hκ := mul_le_mul_of_nonneg_left (max_le hinner he0) hM.lam_pos.le
              change M.lam * max (innerMax M obj (W G N N) 0) 0 ≤ G
              exact hκ.trans (by dsimp [G]; linarith only [hd])
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
              rw [show 2 * N - 2 * k = 2 * (N - k) by omega]
              dsimp [grid]
              push_cast
              by_cases hN : N = 0
              · simp [hN]
              · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
                field_simp <;> ring
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
            have hgbU : gbar M obj < deriv M.U 0 := hgbG.trans_lt hGU
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
            have hVcont : ContinuousOn (Vbar M obj) (Icc 0 M.C) := by
              have hl : LipschitzOnWith (⟨gbar M obj, hgb0⟩ : NNReal) (Vbar M obj) (Icc 0 M.C) := by
                apply LipschitzOnWith.of_dist_le_mul
                intro x hx y hy
                change dist (Vbar M obj x) (Vbar M obj y) ≤ gbar M obj * dist x y
                simpa only [Real.dist_eq] using hVlip x y hx.1 hy.1
              exact hl.continuousOn
            have hVneeded :
                ContinuousOn (Vbar M obj) (Icc 0 M.C) ∧
                ∃ p ∈ Icc 0 (deriv M.U 0), 0 < xi M (concreteReward M obj) (Vbar M obj) p 0 := by
              refine ⟨hVcont, ?_⟩
              have he : ∀ᶠ t in 𝓝 (0 : ℝ), gbar M obj < deriv M.U t :=
                hDcont.continuousAt.eventually (lt_mem_nhds hgbU)
              obtain ⟨ε, hε, heε⟩ := Metric.eventually_nhds_iff.mp he
              let t := min ε M.C / 2
              have ht : 0 < t := by dsimp [t]; positivity
              have htε : t < ε := by dsimp [t]; have := min_le_left ε M.C; linarith
              have htC : t ≤ M.C := by dsimp [t]; have := min_le_right ε M.C; linarith
              have hgt : gbar M obj < deriv M.U t := heε (by simpa [Real.dist_eq, abs_of_pos ht] using htε)
              have hpt : deriv M.U t ∈ Icc 0 (deriv M.U 0) :=
                ⟨hM.deriv_U_nonneg t ⟨ht.le, htC⟩, hM.deriv_U_le t ⟨ht.le, htC⟩⟩
              refine ⟨deriv M.U t, hpt, ?_⟩
              have htval : tOf M (deriv M.U t) = t := ht_deriv t ⟨ht.le, htC⟩
              have hvlo : deriv M.U t * t ≤ v M obj (deriv M.U t) := by
                cases obj with
                | revenue => simp [v, htval]
                | welfare =>
                  have hi := hjoin0 (deriv M.U t) hpt
                  simpa [htval, hM.c_zero, v] using (show deriv M.U t * t ≤ M.U t from by
                    rw [htval, hM.c_zero] at hi; linarith only [hi])
              have hVl := (abs_le.mp (hVlip t 0 ht.le le_rfl)).1
              simp only [sub_zero, abs_of_pos ht] at hVl
              have hpos := mul_pos (sub_pos.mpr hgt) ht
              dsimp [xi, concreteReward]
              rw [htval, hM.c_zero]
              simp only [mul_zero, sub_zero, zero_add]
              linarith only [hvlo, hVl, hpos]
            have hxi_cont : ContinuousOn (fun p => xi M (concreteReward M obj) (Vbar M obj) p 0)
                (Icc 0 (deriv M.U 0)) := by
              have htV := hVneeded.1.comp htcont (fun p hp => (htmem p hp).1)
              convert (hvcont.add htV).sub (continuousOn_const (c := Vbar M obj 0)) using 1
              ext p
              simp [xi, concreteReward, hM.c_zero]
            obtain ⟨q, hq, hqmax⟩ := isCompact_Icc.exists_isMaxOn
              (show (Icc 0 (deriv M.U 0)).Nonempty from ⟨0, le_rfl, hD0.le⟩) hxi_cont
            have harg_ne : (priceArgmax M (concreteReward M obj) (Vbar M obj) 0).Nonempty := by
              refine ⟨q, ?_⟩
              change q ∈ Icc 0 (Gamma M 0) ∧ _
              refine ⟨by simpa [hGamma0] using hq, ?_⟩
              intro r hr
              exact hqmax (by simpa [hGamma0] using hr)
            have harg_bdd : BddAbove (priceArgmax M (concreteReward M obj) (Vbar M obj) 0) :=
              ⟨deriv M.U 0, fun p hp => by simpa [hGamma0] using hp.1.2⟩
            have harg_closed : IsClosed (priceArgmax M (concreteReward M obj) (Vbar M obj) 0) := by
              have he : priceArgmax M (concreteReward M obj) (Vbar M obj) 0 =
                  {p ∈ Icc 0 (deriv M.U 0) |
                    xi M (concreteReward M obj) (Vbar M obj) q 0 ≤
                      xi M (concreteReward M obj) (Vbar M obj) p 0} := by
                ext p
                simp only [priceArgmax, mem_setOf_eq, hGamma0]
                constructor
                · intro hp
                  exact ⟨hp.1, hp.2 q hq⟩
                · intro hp
                  exact ⟨hp.1, fun r hr => (hqmax hr).trans hp.2⟩
              rw [he]
              exact isClosed_Icc.isClosed_le continuousOn_const hxi_cont
            have hpb : pbar M (concreteReward M obj) (Vbar M obj) 0 ∈
                priceArgmax M (concreteReward M obj) (Vbar M obj) 0 :=
              harg_closed.csSup_mem harg_ne harg_bdd
            obtain ⟨p, hp, hpxi⟩ := hVneeded.2
            have hpbpos : 0 < xi M (concreteReward M obj) (Vbar M obj)
                (pbar M (concreteReward M obj) (Vbar M obj) 0) 0 :=
              hpxi.trans_le (hpb.2 p (by simpa [hGamma0] using hp))
            have hpbtop : pbar M (concreteReward M obj) (Vbar M obj) 0 < deriv M.U 0 := by
              have hle : pbar M (concreteReward M obj) (Vbar M obj) 0 ≤ deriv M.U 0 := by
                simpa [hGamma0] using hpb.1.2
              apply lt_of_le_of_ne hle
              intro he
              rw [he] at hpbpos
              simpa [xi, concreteReward, hvtop, ht_top, hM.c_zero] using hpbpos
            have hfb : feedback M (concreteReward M obj) (Vbar M obj) 0 =
                pbar M (concreteReward M obj) (Vbar M obj) 0 := by
              simp [feedback, hwbar.le, hpbpos.le]
            rw [hfb, tJoin, if_pos (hjoin0 _ (by simpa [hGamma0] using hpb.1))]
            exact ht_pos _ ⟨hpb.1.1, hpbtop⟩
