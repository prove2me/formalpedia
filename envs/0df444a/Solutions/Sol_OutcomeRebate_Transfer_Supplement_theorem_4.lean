-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:34.621784+00:00
-- url     : https://prove2.me/submissions/a7270a42-28f1-4979-93ec-93ad7a9ecf15

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
import Definitions.Def_OutcomeRebate_Transfer_Supplement_UniformPrices

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (hA : Assumption1 P) (k : ℝ) (hk : 0 < k) :
    (thresholdA P ≤ k + 1 → IsEqPriceKU P k (pStar P) ∧ coversKU P k (pStar P) ∧
      ∀ p, IsEqPriceKU P k p → p = pStar P) ∧
    (thresholdB P ≤ k + 1 → k + 1 < thresholdA P →
      IsEqPriceKU P k (pHat1 P k) ∧ coversKU P k (pHat1 P k) ∧
      (P.c < pHat1 P k → ∀ p, IsEqPriceKU P k p → p = pHat1 P k)) ∧
    (k + 1 < thresholdB P → P.c ≤ P.vbar / P.z →
      IsEqPriceKU P k (pBarStar P) ∧ ¬coversKU P k (pBarStar P) ∧
      (P.c < P.vbar / P.z → ∀ p, IsEqPriceKU P k p → p = pBarStar P)) ∧
    (k + 1 < thresholdB P → P.vbar / P.z < P.c →
      (∀ p, 0 ≤ p → realizedProfitKU P k p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitKU P k p = 0) ∧
      (∀ p, P.c ≤ p → p < P.vbar / (P.β * P.z) → ¬coversKU P k p)) := by
        set_option maxHeartbeats 600000 in
        set_option maxRecDepth 4000 in
          classical
          rcases hS with ⟨hn, hv, hc, hβ, hβh, hq, hq1, hα, hα1, hlam, hvp⟩
          have hbase : 0 < P.lam * (1 - P.q) / P.q :=
            div_pos (mul_pos (by linarith) (by linarith)) hq
          have hz1 : 1 < P.z := by
            dsimp [Params.z, zOf]
            linarith [Real.rpow_pos_of_pos hbase (1 / P.α)]
          have hz : 0 < P.z := by linarith
          have hβ1 : P.β < 1 := by linarith
          have hcut : ∀ (bb p v : ℝ), 0 ≤ bb → 0 ≤ p → 0 ≤ v →
              (0 ≤ welfareU P bb p v ↔ bb * p * P.z ≤ v) := by
            intro bb p v hbb hp hv0
            have ht : 0 ≤ bb * p := mul_nonneg hbb hp
            have hr : ((P.z - 1) : ℝ) ^ P.α = P.lam * (1 - P.q) / P.q := by
              have he : P.z - 1 = (P.lam * (1 - P.q) / P.q) ^ (P.α)⁻¹ := by
                simp [Params.z, zOf, one_div]
              rw [he, Real.rpow_inv_rpow hbase.le (ne_of_gt hα)]
            have hz0 : 0 ≤ P.z - 1 := by linarith
            have hrmul : (bb * p * (P.z - 1)) ^ P.α =
                (bb * p) ^ P.α * (P.lam * (1 - P.q) / P.q) := by
              rw [Real.mul_rpow ht hz0, hr]
            have hneg : u P.α P.lam (-(bb * p)) = -(P.lam * (bb * p) ^ P.α) := by
              by_cases ht0 : bb * p = 0
              · simp [ht0, u, Real.zero_rpow (ne_of_gt hα)]
              · rw [u, if_neg (by intro h; apply ht0; linarith), neg_neg]
            by_cases hvt : bb * p ≤ v
            · have hw : welfareU P bb p v = P.q * (v - bb * p) ^ P.α -
                  (1 - P.q) * P.lam * (bb * p) ^ P.α := by
                rw [welfareU, hneg, u, if_pos (sub_nonneg.mpr hvt)]
                ring
              rw [hw]
              have he : (1 - P.q) * P.lam * (bb * p) ^ P.α =
                  P.q * (bb * p * (P.z - 1)) ^ P.α := by
                rw [hrmul]
                field_simp
              rw [he]
              have hm := Real.rpow_le_rpow_iff (mul_nonneg ht hz0) (sub_nonneg.mpr hvt) hα
              constructor
              · intro h
                have hh : (bb * p * (P.z - 1)) ^ P.α ≤ (v - bb * p) ^ P.α := by
                  nlinarith only [h, hq]
                have := hm.mp hh
                nlinarith only [this]
              · intro h
                have hh : bb * p * (P.z - 1) ≤ v - bb * p := by nlinarith only [h]
                have := hm.mpr hh
                nlinarith only [this, hq]
            · have hvt' : v - bb * p < 0 := by linarith
              have hw : welfareU P bb p v < 0 := by
                rw [welfareU, hneg, u, if_neg (not_le.mpr hvt')]
                have hpow := Real.rpow_pos_of_pos (neg_pos.mpr hvt') P.α
                have hp0 := Real.rpow_nonneg ht P.α
                have : 0 < P.lam := by linarith
                nlinarith only [mul_pos hq (mul_pos this hpow), mul_nonneg (by linarith only [hq1] : 0 ≤ 1-P.q) (mul_nonneg this.le hp0)]
              constructor
              · intro h; linarith
              · intro h
                have : bb * p ≤ bb * p * P.z := by nlinarith only [mul_nonneg ht (show 0 ≤ P.z-1 by linarith only [hz1])]
                linarith
          have hforms : ∀ (bb p : ℝ), 0 ≤ bb → 0 ≤ p →
              demandU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 ∧
              payerObjKU P k bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 *
                (P.q * (k + 1) / 2 * (P.vbar + bb * p * P.z) - p) := by
            intro bb p hbb hp
            have ht : 0 ≤ bb * p * P.z := mul_nonneg (mul_nonneg hbb hp) hz.le
            have hb : buyersU P bb p = Set.Icc (bb * p * P.z) P.vbar := by
              ext v
              simp only [buyersU, Set.mem_ofPred_eq, Set.mem_Icc]
              constructor
              · rintro ⟨⟨hv0, hvV⟩, hw⟩
                exact ⟨(hcut bb p v hbb hp hv0).mp hw, hvV⟩
              · rintro ⟨hv0, hvV⟩
                exact ⟨⟨ht.trans hv0, hvV⟩, (hcut bb p v hbb hp (ht.trans hv0)).mpr hv0⟩
            by_cases hle : bb * p * P.z ≤ P.vbar
            · have hint : ∀ (A B : ℝ),
                  (∫ v in Set.Icc (bb * p * P.z) P.vbar, (A * v + B)) =
                  (P.vbar - bb * p * P.z) * (A / 2 * (P.vbar + bb * p * P.z) + B) := by
                intro A B
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
                rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
                  integral_id, intervalIntegral.integral_const]
                · simp only [smul_eq_mul]
                  ring
                · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
                · exact continuous_const.intervalIntegrable _ _
              have hi1 : (fun v : ℝ => P.q * (k * v - (1 - bb) * p) -
                  (1 - P.q) * (1 - bb) * p) = (fun v => (P.q * k) * v + (-(1-bb)*p)) := by
                funext v; ring
              have hi2 : (fun v : ℝ => P.q * (v - bb*p) - (1-P.q)*(bb*p)) =
                  (fun v => P.q*v + (-(bb*p))) := by funext v; ring
              constructor
              · simp [demandU, hb, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hle), max_eq_left (sub_nonneg.mpr hle)]
              · simp only [payerObjKU, payerPayoffKU, patientPayoffU, hb, hi1, hi2,
                  hint, max_eq_left (sub_nonneg.mpr hle)]
                ring
            · have hem : Set.Icc (bb * p * P.z) P.vbar = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hle)
              simp [demandU, payerObjKU, payerPayoffKU, patientPayoffU, hb, hem,
                max_eq_right (by linarith : P.vbar - bb*p*P.z ≤ 0)]
          let V := P.vbar
          let c := P.c
          let a := P.β * P.z
          let b := P.z
          let N := P.n / P.vbar
          let r := P.q * (k + 1) / 2
          let f := fun t p : ℝ => (p - c) * max (V - t * p) 0
          have hV : 0 < V := hv
          have hc0 : 0 < c := hc
          have ha : 0 < a := mul_pos hβ hz
          have hb : 0 < b := hz
          have hab : a < b := by dsimp [a, b]; nlinarith only [mul_pos (sub_pos.mpr hβ1) hz]
          have hab2 : 2 * a ≤ b := by dsimp [a, b]; nlinarith only [mul_nonneg (show 0 ≤ 1/2-P.β by linarith only [hβh]) hz.le]
          have hN : 0 < N := div_pos hn hv
          have hr : 0 < r := by dsimp [r]; positivity
          have hcA : a * c < V := by
            have hh := (lt_min_iff.mp hA).2
            have hh' := (div_lt_iff₀ hv).mp hh
            have hh'' := (lt_div_iff₀ hz).mp (show P.β * P.c < P.vbar / P.z by simpa [div_eq_mul_inv, mul_comm] using hh')
            dsimp [a, c, V]
            nlinarith only [hh'']
          have hpr : ∀ p, 0 ≤ p → realizedProfitKU P k p =
              N * (if coversKU P k p then f a p else f b p) := by
            intro p hp
            by_cases hh : coversKU P k p
            · rw [realizedProfitKU, shareKU, if_pos hh, firmProfitU, (hforms P.β p hβ.le hp).1]
              simp only [if_pos hh]
              dsimp [N, f, a, c, V]
              rw [show P.β*p*P.z = P.β*P.z*p by ring]
              ring
            · rw [realizedProfitKU, shareKU, if_neg hh, firmProfitU, (hforms 1 p (by norm_num) hp).1]
              simp only [if_neg hh]
              dsimp [N, f, b, c, V]
              simp only [one_mul]
              ring
          have hcov : ∀ p, 0 ≤ p → (coversKU P k p ↔
              max (V - b*p) 0 * (r*(V+b*p)-p) ≤ max (V-a*p) 0 * (r*(V+a*p)-p)) := by
            intro p hp
            rw [coversKU, (hforms 1 p (by norm_num) hp).2, (hforms P.β p hβ.le hp).2]
            have he : ∀ bb : ℝ, bb*p*P.z = (bb*P.z)*p := by intro bb; ring
            simp only [one_mul, he, mul_comm p P.z]
            change N * max (V-b*p) 0 * (r*(V+b*p)-p) ≤
              N * max (V-a*p) 0 * (r*(V+a*p)-p) ↔ _
            rw [mul_assoc, mul_assoc, mul_le_mul_iff_right₀ hN]
          have hcovhi : ∀ p, 0 ≤ p → V ≤ b*p → a*p < V →
              (coversKU P k p ↔ p ≤ r*(V+a*p)) := by
            intro p hp hpB hpA
            rw [hcov p hp, max_eq_right (by linarith : V-b*p ≤ 0),
              max_eq_left (by linarith : 0 ≤ V-a*p)]
            simp only [zero_mul]
            exact (mul_nonneg_iff_of_pos_left (by linarith : 0 < V-a*p)).trans (sub_nonneg)
          have hcovlo : ∀ p, 0 < p → b*p ≤ V → r*(a+b) < 1 → ¬coversKU P k p := by
            intro p hp hpB hrr hh
            have hpA : a*p ≤ V := by nlinarith only [hpB, mul_nonneg (sub_nonneg.mpr hab.le) hp.le]
            have hh' := (hcov p hp.le).mp hh
            rw [max_eq_left (by linarith : 0 ≤ V-b*p), max_eq_left (by linarith : 0 ≤ V-a*p)] at hh'
            have hpos : 0 < (b-a)*p^2 := mul_pos (by linarith) (sq_pos_of_pos hp)
            have hneg := mul_neg_of_pos_of_neg hpos (by linarith : r*(a+b)-1 < 0)
            nlinarith only [hh', hneg]
          have hfle : ∀ p, c ≤ p → f b p ≤ f a p := by
            intro p hp
            apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hp)
            apply max_le_max_right
            nlinarith only [mul_nonneg (sub_nonneg.mpr hab.le) (hc0.le.trans hp)]
          have hnonpos : ∀ t p, p ≤ c → f t p ≤ 0 := by
            intro t p hp
            exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (le_max_right _ _)
          have hzero : ∀ t p, V ≤ t*p → f t p = 0 := by
            intro t p hp
            simp only [f, max_eq_right (by linarith : V-t*p ≤ 0), mul_zero]
          have hpositive : ∀ t s, c < s → t*s < V → 0 < f t s := by
            intro t s hs hsV
            dsimp [f]
            rw [max_eq_left (by linarith : 0 ≤ V-t*s)]
            exact mul_pos (by linarith) (by linarith)
          have hquad : ∀ t s, 0 < t → c ≤ s → t*s ≤ V →
              2*t*s = t*c+V →
              (∀ p, f t p ≤ f t s) ∧
              (c < s → ∀ p, f t p = f t s → p = s) := by
            intro t s ht hs hsV he
            have hfs : 0 ≤ f t s := by
              exact mul_nonneg (sub_nonneg.mpr hs) (le_max_right _ _)
            have hmain : ∀ p, t*p ≤ V → f t p ≤ f t s := by
              intro p hp
              dsimp [f]
              rw [max_eq_left (by linarith : 0 ≤ V-t*p), max_eq_left (by linarith : 0 ≤ V-t*s)]
              have hid : (s-c)*(V-t*s) - (p-c)*(V-t*p) = t*(p-s)^2 := by
                linear_combination (p-s)*he
              nlinarith only [hid, mul_nonneg ht.le (sq_nonneg (p-s))]
            constructor
            · intro p
              by_cases hp : t*p ≤ V
              · exact hmain p hp
              · rw [hzero t p (by linarith)]
                exact hfs
            · intro hcs p heq
              have hsV' : t*s < V := by nlinarith only [he, mul_pos ht (sub_pos.mpr hcs)]
              have hfs' := hpositive t s hcs hsV'
              by_cases hp : t*p ≤ V
              · have hid : f t s - f t p = t*(p-s)^2 := by
                  dsimp [f]
                  rw [max_eq_left (by linarith : 0 ≤ V-t*p), max_eq_left (by linarith : 0 ≤ V-t*s)]
                  linear_combination (p-s)*he
                have hsq : t*(p-s)^2 = 0 := by linarith only [hid, heq]
                have hsq' : (p-s)^2 = 0 := (mul_eq_zero.mp hsq).resolve_left (ne_of_gt ht)
                exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq')
              · rw [hzero t p (by linarith)] at heq
                linarith
          have hcap : ∀ s H, 2*a*s = a*c+V → c ≤ H → H ≤ s →
              (∀ p, c ≤ p → p ≤ H → f a p ≤ f a H) ∧
              (c < H → ∀ p, c ≤ p → p ≤ H → f a p = f a H → p = H) := by
            intro s H he hcH hHs
            have hHV : a*H ≤ V := by nlinarith only [he, mul_nonneg ha.le (sub_nonneg.mpr hcH), mul_nonneg ha.le (sub_nonneg.mpr hHs)]
            have hmain : ∀ p, c ≤ p → p ≤ H →
                f a H - f a p = (H-p)*(V+a*c-a*(H+p)) := by
              intro p hcp hpH
              have hpV : a*p ≤ V := by nlinarith only [hHV, mul_nonneg ha.le (sub_nonneg.mpr hpH)]
              dsimp [f]
              rw [max_eq_left (by linarith : 0 ≤ V-a*p), max_eq_left (by linarith : 0 ≤ V-a*H)]
              ring
            constructor
            · intro p hcp hpH
              have hh : 0 ≤ V+a*c-a*(H+p) := by nlinarith only [he, mul_nonneg ha.le (sub_nonneg.mpr hHs), mul_nonneg ha.le (sub_nonneg.mpr hpH)]
              have := mul_nonneg (sub_nonneg.mpr hpH) hh
              rw [← hmain p hcp hpH] at this
              linarith
            · intro hcH' p hcp hpH heq
              by_contra hne
              have hpH' : p < H := lt_of_le_of_ne hpH hne
              have hh : 0 < V+a*c-a*(H+p) := by nlinarith only [he, mul_nonneg ha.le (sub_nonneg.mpr hHs), mul_pos ha (sub_pos.mpr hpH')]
              have := mul_pos (sub_pos.mpr hpH') hh
              rw [← hmain p hcp hpH] at this
              linarith
          let s := pStar P
          let u := pBarStar P
          let L := V / b
          let m := max c L
          have hL : 0 < L := div_pos hV hb
          have hbL : b*L = V := by dsimp [L]; field_simp
          have hm : 0 < m := lt_of_lt_of_le hc0 (le_max_left _ _)
          have hcm : c ≤ m := le_max_left _ _
          have hLm : L ≤ m := le_max_right _ _
          have hs : 2*a*s = a*c+V := by
            dsimp [s, a, c, V, pStar]
            field_simp
            <;> ring
          have hu : 2*b*u = b*c+V := by
            dsimp [u, b, c, V, pBarStar]
            field_simp
            <;> ring
          have hcs : c < s := by nlinarith only [hs, ha, hcA]
          have hs0 : 0 < s := hc0.trans hcs
          have has : a*s < V := by nlinarith only [hs, ha, hcA]
          have hbs : V < b*s := by nlinarith only [hs, hab2, hs0, mul_pos ha hc0]
          have hAeq : thresholdA P = 2*(V+c*a)/(P.q*a*(3*V+c*a)) := by
            dsimp [thresholdA, V, c, a]
            field_simp
            <;> ring
          have hAd : 0 < P.q*a*(3*V+c*a) := by positivity
          have hAid : (k+1)*(P.q*a*(3*V+c*a))-2*(V+c*a) =
              4*a*(r*(V+a*s)-s) := by
            have he : V = 2*a*s-a*c := by linarith only [hs]
            rw [he]
            dsimp [r]
            ring
          have hAchar : thresholdA P ≤ k+1 ↔ s ≤ r*(V+a*s) := by
            rw [hAeq, div_le_iff₀ hAd]
            constructor <;> intro hh
            · nlinarith only [hh, hAid, ha]
            · nlinarith only [hh, hAid, ha]
          have hAchar' : k+1 < thresholdA P ↔ r*(V+a*s) < s := by
            exact lt_iff_lt_of_le_iff_le hAchar
          have hBeq : thresholdB P = 2*m/(P.q*(a*m+V)) := by
            have hm0 : m ≠ 0 := ne_of_gt hm
            dsimp [thresholdB]
            change 2 / (P.q*(a+V/m)) = _
            field_simp
            <;> ring
          have hBd : 0 < P.q*(a*m+V) := by positivity
          have hBid : (k+1)*(P.q*(a*m+V))-2*m = 2*(r*(V+a*m)-m) := by
            dsimp [r]; ring
          have hBchar : thresholdB P ≤ k+1 ↔ m ≤ r*(V+a*m) := by
            rw [hBeq, div_le_iff₀ hBd]
            constructor <;> intro hh <;> nlinarith only [hh, hBid]
          have hBchar' : k+1 < thresholdB P ↔ r*(V+a*m) < m := by
            exact lt_iff_lt_of_le_iff_le hBchar
          have hsmall : r*(V+a*m) < m →
              (∀ p, c ≤ p → a*p < V → ¬coversKU P k p) ∧
              (c ≤ L → ∀ p, 0 < p → b*p ≤ V → ¬coversKU P k p) := by
            intro hlow
            have hra : r*a < 1 := by nlinarith only [hlow, mul_pos hr hV, hm]
            have hsmallhi : ∀ p, m ≤ p → a*p < V → ¬coversKU P k p := by
              intro p hmp hpA hh
              have hp0 : 0 ≤ p := le_trans hc0.le (hcm.trans hmp)
              have hpB : V ≤ b*p := by nlinarith only [hbL, hb, hLm, hmp]
              have hh' := (hcovhi p hp0 hpB hpA).mp hh
              nlinarith only [hlow, hh', hmp, hra]
            constructor
            · intro p hcp hpA
              by_cases hpB : b*p ≤ V
              · have hpL : p ≤ L := by nlinarith only [hpB, hbL, hb]
                have hcL : c ≤ L := hcp.trans hpL
                have hmL : m = L := max_eq_right hcL
                have hrr : r*(a+b) < 1 := by
                  rw [hmL] at hlow
                  have he : r*(V+a*L)-L = L*(r*(a+b)-1) := by rw [← hbL]; ring
                  nlinarith only [hlow, he, hL]
                exact hcovlo p (hc0.trans_le hcp) hpB hrr
              · have hmp : m ≤ p := max_le hcp (by nlinarith only [hpB, hbL, hb])
                exact hsmallhi p hmp hpA
            · intro hcL p hp hpB
              have hmL : m = L := max_eq_right hcL
              have hrr : r*(a+b) < 1 := by
                rw [hmL] at hlow
                have he : r*(V+a*L)-L = L*(r*(a+b)-1) := by rw [← hbL]; ring
                nlinarith only [hlow, he, hL]
              exact hcovlo p hp hpB hrr
          have hreal_nonpos : ∀ p, 0 ≤ p → p ≤ c → realizedProfitKU P k p ≤ 0 := by
            intro p hp hpc
            rw [hpr p hp]
            split_ifs <;> exact mul_nonpos_of_nonneg_of_nonpos hN.le (hnonpos _ _ hpc)
          have hreal_zero : ∀ p, 0 ≤ p → V ≤ a*p → realizedProfitKU P k p = 0 := by
            intro p hp hpA
            have hpB : V ≤ b*p := by nlinarith only [hpA, hab, hp]
            rw [hpr p hp]
            split_ifs <;> simp [hzero _ _ hpA, hzero _ _ hpB]
          have hreal_bound : ∀ p, 0 ≤ p → c ≤ p → realizedProfitKU P k p ≤ N*f a p := by
            intro p hp hcp
            rw [hpr p hp]
            split_ifs
            · exact le_rfl
            · exact mul_le_mul_of_nonneg_left (hfle p hcp) hN.le
          have hcovered : ∀ p, 0 ≤ p → coversKU P k p → realizedProfitKU P k p = N*f a p := by
            intro p hp hh; rw [hpr p hp, if_pos hh]
          have huncovered : ∀ p, 0 ≤ p → ¬coversKU P k p → realizedProfitKU P k p = N*f b p := by
            intro p hp hh; rw [hpr p hp, if_neg hh]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hhigh
            have hcovs : coversKU P k s :=
              (hcovhi s hs0.le hbs.le has).mpr (hAchar.mp hhigh)
            have heq : realizedProfitKU P k s = N*f a s := hcovered s hs0.le hcovs
            have hfs : 0 < f a s := hpositive a s hcs has
            have hquadS := hquad a s ha hcs.le has.le hs
            have hmax : ∀ p, 0 ≤ p → realizedProfitKU P k p ≤ realizedProfitKU P k s := by
              intro p hp
              rw [heq]
              by_cases hpc : p ≤ c
              · exact (hreal_nonpos p hp hpc).trans (mul_nonneg hN.le hfs.le)
              · exact (hreal_bound p hp (le_of_not_ge hpc)).trans
                  (mul_le_mul_of_nonneg_left (hquadS.1 p) hN.le)
            refine ⟨⟨hs0.le, hmax⟩, hcovs, ?_⟩
            intro p hp
            have hh := hp.2 s hs0.le
            rw [heq] at hh
            have hpc : c ≤ p := by
              by_contra hn
              have := hreal_nonpos p hp.1 (le_of_not_ge hn)
              have := mul_pos hN hfs
              linarith
            have hh' := hreal_bound p hp.1 hpc
            have hf : f a p = f a s := by
              have := hquadS.1 p
              nlinarith only [hh, hh', this, hN]
            exact hquadS.2 hcs p hf
          · intro hhigh hlow
            have hlow' := hAchar'.mp hlow
            have hra : 0 < 1-r*a := by
              nlinarith only [hlow', mul_pos hr hV, hs0]
            let H := pHat1 P k
            have hH : (1-r*a)*H = r*V := by
              have hd : 2-P.β*P.z*P.q*(k+1) ≠ 0 := by
                have he : 2-P.β*P.z*P.q*(k+1) = 2*(1-r*a) := by dsimp [r, a]; ring
                rw [he]; positivity
              have hprice : H * (2-P.β*P.z*P.q*(k+1)) = P.vbar*P.q*(k+1) :=
                div_mul_cancel₀ _ hd
              dsimp only [r, a, V]
              nlinarith only [hprice]
            have hmH : m ≤ H := by nlinarith only [hBchar.mp hhigh, hH, hra]
            have hHs : H < s := by nlinarith only [hlow', hH, hra]
            have hcH : c ≤ H := hcm.trans hmH
            have hH0 : 0 < H := hc0.trans_le hcH
            have hHV : a*H < V := by nlinarith only [hHs, has, ha]
            have hHB : V ≤ b*H := by nlinarith only [hbL, hLm, hmH, hb]
            have hcovH : coversKU P k H := by
              apply (hcovhi H hH0.le hHB hHV).mpr
              nlinarith only [hH]
            have heq : realizedProfitKU P k H = N*f a H := hcovered H hH0.le hcovH
            have hfH : 0 ≤ f a H := mul_nonneg (sub_nonneg.mpr hcH) (le_max_right _ _)
            have hcapH := hcap s H hs hcH hHs.le
            have hbound : ∀ p, 0 ≤ p → c ≤ p → a*p < V →
                0 < realizedProfitKU P k p → p ≤ H := by
              intro p hp hcp hpA hprofit
              by_cases hh : coversKU P k p
              · by_cases hpB : V ≤ b*p
                · have hh' := (hcovhi p hp hpB hpA).mp hh
                  nlinarith only [hh', hH, hra]
                · nlinarith only [hpB, hHB, hb]
              · have hpB : b*p < V := by
                  by_contra hn
                  rw [huncovered p hp hh, hzero b p (le_of_not_gt hn), mul_zero] at hprofit
                  linarith
                nlinarith only [hpB, hHB, hb]
            have hmax : ∀ p, 0 ≤ p → realizedProfitKU P k p ≤ realizedProfitKU P k H := by
              intro p hp
              rw [heq]
              by_cases hprof : realizedProfitKU P k p ≤ 0
              · exact hprof.trans (mul_nonneg hN.le hfH)
              · have hprof' := lt_of_not_ge hprof
                have hcp : c ≤ p := by
                  by_contra hn
                  exact hprof (hreal_nonpos p hp (le_of_not_ge hn))
                have hpA : a*p < V := by
                  by_contra hn
                  rw [hreal_zero p hp (le_of_not_gt hn)] at hprof'
                  linarith
                have hpH := hbound p hp hcp hpA hprof'
                exact (hreal_bound p hp hcp).trans
                  (mul_le_mul_of_nonneg_left (hcapH.1 p hcp hpH) hN.le)
            refine ⟨⟨hH0.le, hmax⟩, hcovH, ?_⟩
            intro hcH' p hp
            have hfH' : 0 < f a H := hpositive a H hcH' hHV
            have hh := hp.2 H hH0.le
            rw [heq] at hh
            have hprof : 0 < realizedProfitKU P k p := lt_of_lt_of_le (mul_pos hN hfH') hh
            have hcp : c ≤ p := by
              by_contra hn
              have := hreal_nonpos p hp.1 (le_of_not_ge hn)
              linarith
            have hpA : a*p < V := by
              by_contra hn
              rw [hreal_zero p hp.1 (le_of_not_gt hn)] at hprof
              linarith
            have hpH := hbound p hp.1 hcp hpA hprof
            have hfa : f a p = f a H := by
              have h1 := hreal_bound p hp.1 hcp
              have h2 := hcapH.1 p hcp hpH
              nlinarith only [hh, h1, h2, hN]
            exact hcapH.2 hcH' p hcp hpH hfa
          · intro hlow hcL
            have hcL' : c ≤ L := hcL
            have hlow' := hBchar'.mp hlow
            have hncover := hsmall hlow'
            have hcu : c ≤ u := by nlinarith only [hu, hcL', hbL, hb]
            have hu0 : 0 < u := hc0.trans_le hcu
            have huV : b*u ≤ V := by nlinarith only [hu, hcL', hbL, hb]
            have hcovu : ¬coversKU P k u := hncover.2 hcL' u hu0 huV
            have heq : realizedProfitKU P k u = N*f b u := huncovered u hu0.le hcovu
            have hfu : 0 ≤ f b u := mul_nonneg (sub_nonneg.mpr hcu) (le_max_right _ _)
            have hqu := hquad b u hb hcu huV hu
            have hmax : ∀ p, 0 ≤ p → realizedProfitKU P k p ≤ realizedProfitKU P k u := by
              intro p hp
              rw [heq]
              by_cases hpc : p ≤ c
              · exact (hreal_nonpos p hp hpc).trans (mul_nonneg hN.le hfu)
              · have hcp := le_of_not_ge hpc
                by_cases hpA : a*p < V
                · rw [huncovered p hp (hncover.1 p hcp hpA)]
                  exact mul_le_mul_of_nonneg_left (hqu.1 p) hN.le
                · rw [hreal_zero p hp (le_of_not_gt hpA)]
                  exact mul_nonneg hN.le hfu
            refine ⟨⟨hu0.le, hmax⟩, hcovu, ?_⟩
            intro hcL'' p hp
            have hcu' : c < u := by
              have hcL''' : c < L := hcL''
              nlinarith only [hu, hcL''', hbL, hb]
            have huV' : b*u < V := by nlinarith only [hu, hcu', hb]
            have hfu' := hpositive b u hcu' huV'
            have hh := hp.2 u hu0.le
            rw [heq] at hh
            have hprof : 0 < realizedProfitKU P k p := lt_of_lt_of_le (mul_pos hN hfu') hh
            have hcp : c ≤ p := by
              by_contra hn
              have := hreal_nonpos p hp.1 (le_of_not_ge hn)
              linarith
            have hpA : a*p < V := by
              by_contra hn
              rw [hreal_zero p hp.1 (le_of_not_gt hn)] at hprof
              linarith
            rw [huncovered p hp.1 (hncover.1 p hcp hpA)] at hh
            have hfb : f b p = f b u := by
              have hh' := hqu.1 p
              nlinarith only [hh, hh', hN]
            exact hqu.2 hcu' p hfb
          · intro hlow hLc
            have hLc' : L < c := hLc
            have hlow' := hBchar'.mp hlow
            have hncover := (hsmall hlow').1
            have hnon : ∀ p, 0 ≤ p → realizedProfitKU P k p ≤ 0 := by
              intro p hp
              by_cases hpc : p ≤ c
              · exact hreal_nonpos p hp hpc
              · have hcp := le_of_not_ge hpc
                by_cases hpA : a*p < V
                · rw [huncovered p hp (hncover p hcp hpA), hzero b p (by nlinarith only [hbL, hLc', hcp, hb]), mul_zero]
                · rw [hreal_zero p hp (le_of_not_gt hpA)]
            refine ⟨hnon, ?_, ?_⟩
            · refine ⟨V/a, (div_pos hV ha).le, ?_⟩
              apply hreal_zero _ (div_pos hV ha).le
              rw [mul_div_cancel₀ _ (ne_of_gt ha)]
            · intro p hcp hpA
              apply hncover p hcp
              simpa [mul_comm] using (lt_div_iff₀ ha).mp hpA
