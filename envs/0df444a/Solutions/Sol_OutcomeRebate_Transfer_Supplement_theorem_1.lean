-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:07.437128+00:00
-- url     : https://prove2.me/submissions/d851cc18-9848-4614-9f0e-b0a5a3606285

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_UniformPrices

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

/-- All five price regions; the printed exhaustiveness assertion is corrected only on its
missing boundary. Implicit price roots are required only in the applicable branches. -/
theorem solution (P : Params) (hS : P.Standing) (hA : Assumption1 P) (q1 q2 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β)
    (hq2 : 0 < q2 ∧ q2 < 1 ∧ zOf P.α P.lam q2 * q2 = 2 / (1 + P.β)) :
    let rootQ := fun qb : ℝ => 0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb * qb = 1 / P.β
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc P.c (pBarStar P) ∧
      firmProfitU P 1 (pBarStar P) = firmProfitU P P.β p3
    let a := 1 / P.q - P.z * P.β / 2
    let b := 1 / P.q - P.z * (1 + P.β) / 2
    let p1 := P.q * (P.vp + P.vbar / 2) / (1 - P.q * P.z * P.β / 2)
    let p2 := P.q * P.vp / (1 - P.q * P.z * (1 + P.β) / 2)
    let C1 := fun qb => P.q ≤ qb ∨ (qb < P.q ∧ pStar P * a - P.vbar / 2 ≤ P.vp)
    let C2 := fun qb => qb < P.q ∧ max P.c (P.vbar / P.z) * a - P.vbar / 2 < P.vp ∧
      P.vp < pStar P * a - P.vbar / 2
    let C3 := fun p3 => q2 < P.q ∧ P.c ≤ P.vbar / P.z ∧ p3 * b ≤ P.vp ∧ P.vp ≤ P.vbar / P.z * b
    let C4 := fun p3 => q2 < P.q ∧ P.c ≤ P.vbar / P.z ∧ P.vp < p3 * b
    let C5 := fun qb => qb < P.q ∧ P.vbar / P.z < P.c ∧ P.vp ≤ P.c / P.q * (1 - P.q * P.z * P.β / 2) - P.vbar / 2
    (∃! qb, rootQ qb) ∧
    (P.c ≤ P.vbar / P.z → ∃! p3, rootP p3) ∧
    (∀ qb, rootQ qb → (q1 < qb ∧ qb < q2) ∧
      (C1 qb → IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧
        ∀ p, IsEqPriceU P p → p = pStar P) ∧
      (C2 qb → IsEqPriceU P p1 ∧ coversU P p1 ∧ ∀ p, IsEqPriceU P p → p = p1) ∧
      (∀ p3, rootP p3 →
        (C3 p3 → IsEqPriceU P p2 ∧ coversU P p2 ∧
          (p3 * b < P.vp → ∀ p, IsEqPriceU P p → p = p2)) ∧
        (C4 p3 → IsEqPriceU P (pBarStar P) ∧ ¬coversU P (pBarStar P) ∧
          (P.c < P.vbar / P.z → ∀ p, IsEqPriceU P p → p = pBarStar P))) ∧
      (C5 qb → (∀ p, 0 ≤ p → realizedProfitU P p ≤ 0) ∧
        (∃ p, 0 ≤ p ∧ realizedProfitU P p = 0) ∧
        (∀ p, P.c < p → p < P.vbar / (P.β * P.z) → ¬coversU P p) ∧
        (P.vp < P.c / P.q * (1 - P.q * P.z * P.β / 2) - P.vbar / 2 → ¬coversU P P.c)) ∧
      (¬(P.q = q2 ∧ P.vp = 0 ∧ P.c ≤ P.vbar / P.z) →
        C1 qb ∨ C2 qb ∨ (∃ p3, rootP p3 ∧ C3 p3) ∨ (∃ p3, rootP p3 ∧ C4 p3) ∨ C5 qb)) := by
          set_option maxHeartbeats 1000000 in
            classical
            rcases hS with ⟨hn,hv,hc,hβ,hβh,hq,hqone,hα,hα1,hl,hvp⟩
            have hcompare : ∀ x y : ℝ, 0 < x → x < y → y < 1 →
                1 < zOf P.α P.lam y * y →
                zOf P.α P.lam y * y < zOf P.α P.lam x * x := by
              clear hA q1 q2 hq1 hq2 hn hv hc hβ hβh hq hqone hvp
              have hr : 0 < 1 / P.α - 1 := by
                have : 1 < 1 / P.α := (lt_div_iff₀ hα).2 (by linarith only [hα1])
                linarith only [this]
              intro x y hx hxy hy hfy
              have hy0 : 0 < y := lt_trans hx hxy
              have hx1 : x < 1 := lt_trans hxy hy
              let tx := (1-x)/x
              let ty := (1-y)/y
              have htx : 0 < tx := div_pos (by linarith only [hx1]) hx
              have hty : 0 < ty := div_pos (by linarith only [hy]) hy0
              have ht : ty < tx := by
                dsimp [tx, ty]
                apply (div_lt_div_iff₀ hy0 hx).2
                nlinarith only [hxy]
              have hl0 : 0 < P.lam := by linarith only [hl]
              have hlt : P.lam * ty < P.lam * tx := mul_lt_mul_of_pos_left ht hl0
              have hpow := Real.rpow_lt_rpow (le_of_lt (mul_pos hl0 hty)) hlt hr
              have hpx : (P.lam * tx) ^ (1/P.α) =
                  (P.lam * tx) ^ (1/P.α-1) * (P.lam * tx) := by
                convert Real.rpow_add (mul_pos hl0 htx) (1/P.α-1) 1 using 1 <;> simp
              have hpy : (P.lam * ty) ^ (1/P.α) =
                  (P.lam * ty) ^ (1/P.α-1) * (P.lam * ty) := by
                convert Real.rpow_add (mul_pos hl0 hty) (1/P.α-1) 1 using 1 <;> simp
              let gx := (P.lam * tx) ^ (1/P.α)
              let gy := (P.lam * ty) ^ (1/P.α)
              have hcross : gy * tx < gx * ty := by
                dsimp [gx,gy]
                rw [hpx,hpy]
                have hh := mul_lt_mul_of_pos_right hpow (mul_pos hl0 (mul_pos htx hty))
                nlinarith only [hh]
              have hzx : zOf P.α P.lam x * x = (1+gx)*x := by
                dsimp [zOf, gx, tx]
                congr 2
                rw [mul_div_assoc]
              have hzy : zOf P.α P.lam y * y = (1+gy)*y := by
                dsimp [zOf, gy, ty]
                congr 2
                rw [mul_div_assoc]
              have htxe : (1+tx)*x = 1 := by dsimp [tx]; field_simp; ring
              have htye : (1+ty)*y = 1 := by dsimp [ty]; field_simp; ring
              have hgy : ty < gy := by
                rw [hzy] at hfy
                have hh : (1+ty)*y < (1+gy)*y := by linarith only [hfy,htye]
                have hh' := (mul_lt_mul_iff_left₀ hy0).1 hh
                linarith only [hh']
              have hdiff : tx - ty < gx - gy := by
                have hh := mul_pos (sub_pos.2 ht) (sub_pos.2 hgy)
                have hm : 0 < ty*(gx-gy-(tx-ty)) := by nlinarith only [hcross,hh]
                have hh' := (mul_pos_iff_of_pos_left hty).1 hm
                linarith only [hh']
              have hratio : (1+gy)*(1+tx) < (1+gx)*(1+ty) := by nlinarith only [hcross,hdiff]
              rw [hzx,hzy]
              have hid : (1+gx)*x-(1+gy)*y =
                  x*y*((1+gx)*(1+ty)-(1+gy)*(1+tx)) := by
                linear_combination -(1+gx)*x*htye+(1+gy)*y*htxe
              have hh := mul_pos (mul_pos hx hy0) (sub_pos.2 hratio)
              nlinarith only [hid,hh]
            have hk : 1 < 1 / P.β := (lt_div_iff₀ hβ).2 (by linarith only [hβh])
            have hk1 : 1 / P.β < 2 / P.β := (div_lt_div_iff_of_pos_right hβ).2 (by norm_num)
            have hk2 : 2 / (1+P.β) < 1 / P.β := by
              apply (div_lt_div_iff₀ (by linarith only [hβ] : 0 < 1+P.β) hβ).2
              linarith only [hβh]
            have h12 : q1 < q2 := by
              by_contra hh
              rcases lt_or_eq_of_le (le_of_not_gt hh) with hh | hh
              · have hh' := hcompare q2 q1 hq2.1 hh hq1.2.1 (by rw [hq1.2.2]; linarith only [hk,hk1])
                rw [hq1.2.2, hq2.2.2] at hh'
                linarith only [hh',hk1,hk2]
              · have hh' := hq1.2.2
                rw [← hh, hq2.2.2] at hh'
                linarith only [hh',hk1,hk2]
            have hcont : ContinuousOn (fun x => zOf P.α P.lam x * x) (Set.Icc q1 q2) := by
              unfold zOf
              apply ContinuousOn.mul _ continuousOn_id
              apply continuousOn_const.add
              apply ContinuousOn.rpow_const
              · apply ContinuousOn.div
                · fun_prop
                · fun_prop
                · intro x hx
                  exact ne_of_gt (lt_of_lt_of_le hq1.1 hx.1)
              · intro x hx
                exact Or.inr (by positivity)
            have hex : ∃ qb ∈ Set.Icc q1 q2, zOf P.α P.lam qb * qb = 1/P.β := by
              have hi := intermediate_value_Icc (le_of_lt h12) hcont
              have hm : 1/P.β ∈ Set.Icc (zOf P.α P.lam q2*q2) (zOf P.α P.lam q1*q1) := by
                rw [hq1.2.2, hq2.2.2]
                exact ⟨le_of_lt hk2, le_of_lt hk1⟩
              exact intermediate_value_Icc' (le_of_lt h12) hcont hm
            have horder : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb * qb = 1/P.β) →
                q1 < qb ∧ qb < q2 := by
              intro qb hb
              constructor
              · by_contra hh
                rcases lt_or_eq_of_le (le_of_not_gt hh) with hh | hh
                · have hh' := hcompare qb q1 hb.1 hh hq1.2.1 (by rw [hq1.2.2]; linarith only [hk,hk1])
                  rw [hq1.2.2, hb.2.2] at hh'
                  linarith only [hh',hk1,hk2]
                · have hh' := hb.2.2
                  rw [hh, hq1.2.2] at hh'
                  linarith only [hh',hk1,hk2]
              · by_contra hh
                rcases lt_or_eq_of_le (le_of_not_gt hh) with hh | hh
                · have hh' := hcompare q2 qb hq2.1 hh hb.2.1 (by rw [hb.2.2]; exact hk)
                  rw [hq2.2.2, hb.2.2] at hh'
                  linarith only [hh',hk1,hk2]
                · have hh' := hb.2.2
                  rw [← hh, hq2.2.2] at hh'
                  linarith only [hh',hk1,hk2]
            have hroots : ∃! qb, 0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb * qb = 1/P.β := by
              obtain ⟨qb, hb, hbe⟩ := hex
              have hb0 : 0 < qb := lt_of_lt_of_le hq1.1 hb.1
              have hb1 : qb < 1 := lt_of_le_of_lt hb.2 hq2.2.1
              refine ⟨qb, ⟨hb0,hb1,hbe⟩, ?_⟩
              intro y hy
              rcases lt_trichotomy y qb with hh | hh | hh
              · have hh' := hcompare y qb hy.1 hh hb1 (by rw [hbe]; exact hk)
                rw [hy.2.2,hbe] at hh'
                exact False.elim (lt_irrefl _ hh')
              · exact hh
              · have hh' := hcompare qb y hb0 hh hy.2.1 (by rw [hy.2.2]; exact hk)
                rw [hy.2.2,hbe] at hh'
                exact False.elim (lt_irrefl _ hh')
            have hzbase : 0 < P.lam * (1-P.q) / P.q := by positivity
            have hzt : 0 < (P.lam * (1-P.q) / P.q) ^ (1/P.α) := Real.rpow_pos_of_pos hzbase _
            have hz : 1 < P.z := by
              dsimp [Params.z,zOf]
              linarith only [hzt]
            have hztpow : ((P.lam*(1-P.q)/P.q)^(1/P.α))^P.α = P.lam*(1-P.q)/P.q := by
              rw [← Real.rpow_mul (le_of_lt hzbase)]
              simp [ne_of_gt hα]
            have hwelfare : ∀ d v : ℝ, 0 ≤ d → 0 ≤ v →
                (0 ≤ P.q*u P.α P.lam (v-d)+(1-P.q)*u P.α P.lam (-d) ↔ d*P.z ≤ v) := by
              intro d v hd hv0
              have hud : u P.α P.lam (-d) = -(P.lam*d^P.α) := by
                rcases eq_or_lt_of_le hd with hh | hh
                · subst d
                  simp [u, Real.zero_rpow (ne_of_gt hα)]
                · rw [u, if_neg (by linarith only [hh]), neg_neg]
              rw [hud]
              by_cases hdv : d ≤ v
              · rw [u, if_pos (by linarith only [hdv] : 0 ≤ v-d)]
                have hpow : (d*((P.lam*(1-P.q)/P.q)^(1/P.α)))^P.α =
                    d^P.α*(P.lam*(1-P.q)/P.q) := by
                  rw [Real.mul_rpow hd (le_of_lt hzt),hztpow]
                have hpowe := Real.rpow_le_rpow_iff (mul_nonneg hd (le_of_lt hzt))
                  (sub_nonneg.2 hdv) hα
                rw [hpow] at hpowe
                have hze : d*P.z ≤ v ↔ d*((P.lam*(1-P.q)/P.q)^(1/P.α)) ≤ v-d := by
                  dsimp [Params.z,zOf]
                  constructor <;> intro h <;> nlinarith only [h]
                rw [hze, ← hpowe]
                have heq : d^P.α*(P.lam*(1-P.q)/P.q)*P.q = (1-P.q)*(P.lam*d^P.α) := by
                  field_simp
                  <;> ring
                constructor <;> intro h
                · apply (mul_le_mul_iff_left₀ hq).mp
                  rw [heq]
                  nlinarith only [h]
                · have hh := (mul_le_mul_iff_left₀ hq).mpr h
                  rw [heq] at hh
                  nlinarith only [hh]
              · have hdv' : v < d := lt_of_not_ge hdv
                have hneg : 0 < (-(v-d))^P.α := Real.rpow_pos_of_pos (by linarith only [hdv']) _
                rw [u, if_neg (by linarith only [hdv'])]
                have hdpow : 0 ≤ d^P.α := Real.rpow_nonneg hd _
                constructor
                · intro h
                  nlinarith only [h,mul_pos hq (mul_pos (by linarith only [hl] : 0 < P.lam) hneg),
                    mul_nonneg (by linarith only [hqone] : 0 ≤ 1-P.q) (mul_nonneg (by linarith only [hl] : 0 ≤ P.lam) hdpow)]
                · intro h
                  have : d ≤ d*P.z := le_mul_of_one_le_right hd (le_of_lt hz)
                  linarith only [this,h,hdv']
            have hbuyers : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p →
                buyersU P bb p = Set.Icc (bb*p*P.z) P.vbar := by
              intro bb p hbb hp
              have hd : 0 ≤ bb*p := mul_nonneg hbb hp
              have hdz : 0 ≤ bb*p*P.z := mul_nonneg hd (by linarith only [hz])
              ext v
              simp only [buyersU,Set.mem_setOf_eq,Set.mem_Icc,welfareU]
              constructor
              · rintro ⟨⟨hv0,hvv⟩,hw⟩
                exact ⟨(hwelfare _ _ hd hv0).1 hw,hvv⟩
              · rintro ⟨hvl,hvu⟩
                have hv0 := le_trans hdz hvl
                exact ⟨⟨hv0,hvu⟩,(hwelfare _ _ hd hv0).2 hvl⟩
            have hdemand : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p →
                demandU P bb p = P.n/P.vbar * max (P.vbar-bb*p*P.z) 0 := by
              intro bb p hbb hp
              simp only [demandU,hbuyers bb p hbb hp,Real.volume_Icc,ENNReal.toReal_ofReal']
            have hpatient : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p →
                patientPayoffU P bb p = P.n/P.vbar * max (P.vbar-bb*p*P.z) 0 *
                  (P.q/2*(P.vbar+bb*p*P.z)-bb*p) := by
              intro bb p hbb hp
              rw [patientPayoffU,hbuyers bb p hbb hp]
              by_cases hh : bb*p*P.z ≤ P.vbar
              · rw [max_eq_left (sub_nonneg.2 hh),MeasureTheory.integral_Icc_eq_integral_Ioc,
                  ← intervalIntegral.integral_of_le hh]
                have hf : (fun v : ℝ => P.q*(v-bb*p)-(1-P.q)*(bb*p)) =
                    (fun v : ℝ => P.q*v-bb*p) := by funext v; ring
                rw [hf,intervalIntegral.integral_sub]
                · rw [intervalIntegral.integral_const_mul,integral_id,intervalIntegral.integral_const]
                  simp only [smul_eq_mul]
                  ring
                · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
                · exact continuous_const.intervalIntegrable _ _
              · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hh),MeasureTheory.setIntegral_empty,
                  max_eq_right (by linarith only [hh] : P.vbar-bb*p*P.z ≤ 0)]
                ring
            have hobj : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p →
                payerObjU P bb p = P.n/P.vbar * max (P.vbar-bb*p*P.z) 0 *
                  (P.q*P.vp-p+P.q/2*(P.vbar+bb*p*P.z)) := by
              intro bb p hbb hp
              rw [payerObjU,payerPayoffU,hdemand bb p hbb hp,hpatient bb p hbb hp]
              ring
            have hprofit : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p →
                firmProfitU P bb p = P.n/P.vbar * (p-P.c)*max (P.vbar-bb*p*P.z) 0 := by
              intro bb p hbb hp
              rw [firmProfitU,hdemand bb p hbb hp]
              ring
            let V : ℝ := P.vbar / P.z
            let R : ℝ := P.vbar / (P.β*P.z)
            let a : ℝ := 1/P.q-P.z*P.β/2
            let b : ℝ := 1/P.q-P.z*(1+P.β)/2
            have hz0 : 0 < P.z := by linarith only [hz]
            have hV0 : 0 < V := div_pos hv hz0
            have hR0 : 0 < R := div_pos hv (mul_pos hβ hz0)
            have hVz : V*P.z = P.vbar := div_mul_cancel₀ _ (ne_of_gt hz0)
            have hRz : R*(P.β*P.z) = P.vbar := div_mul_cancel₀ _ (ne_of_gt (mul_pos hβ hz0))
            have hβone : 0 < 1-P.β := by linarith only [hβh]
            have hRβ : R*P.β = V := by
              dsimp [R,V]
              field_simp
              <;> ring
            have hVR : V < R := by
              nlinarith only [hRβ,mul_pos hR0 hβone]
            have hcR : P.c < R := by
              have ha := (lt_min_iff.mp hA).2
              have hh := (div_lt_div_iff₀ hv hz0).1 ha
              apply (lt_div_iff₀ (mul_pos hβ hz0)).2
              nlinarith only [hh]
            have haq : a*P.q = 1-P.z*P.β*P.q/2 := by dsimp [a]; field_simp <;> ring
            have hbq : b*P.q = 1-P.z*(1+P.β)*P.q/2 := by dsimp [b]; field_simp <;> ring
            have hVab : V*a-P.vbar/2 = V*b := by
              dsimp [a,b]
              nlinarith only [hVz]
            have hcoverlow : ∀ p : ℝ, 0 ≤ p → p ≤ V → (coversU P p ↔ p*b ≤ P.vp) := by
              intro p hp hpV
              have hd1 : 0 ≤ P.vbar-1*p*P.z := by
                have := (mul_le_mul_iff_left₀ hz0).2 hpV
                rw [hVz] at this
                nlinarith only [this]
              have hdβ : 0 ≤ P.vbar-P.β*p*P.z := by
                nlinarith only [hd1,hβh,mul_nonneg hp (le_of_lt hz0)]
              unfold coversU
              rw [hobj 1 p (by norm_num) hp,hobj P.β p (le_of_lt hβ) hp,
                max_eq_left hd1,max_eq_left hdβ]
              have hdif : P.n/P.vbar*(P.vbar-P.β*p*P.z)*(P.q*P.vp-p+P.q/2*(P.vbar+P.β*p*P.z))-
                  P.n/P.vbar*(P.vbar-1*p*P.z)*(P.q*P.vp-p+P.q/2*(P.vbar+1*p*P.z)) =
                  (P.n/P.vbar*(1-P.β)*p*P.z*P.q)*(P.vp-p*b) := by
                dsimp [b]
                field_simp
                <;> ring
              rcases eq_or_lt_of_le hp with hh | hh
              · subst p
                simp only [zero_mul,mul_zero,sub_zero,add_zero,le_refl,true_iff]
                exact hvp
              · have hpos : 0 < P.n/P.vbar*(1-P.β)*p*P.z*P.q := by positivity
                constructor
                · intro h
                  have : 0 ≤ (P.n/P.vbar*(1-P.β)*p*P.z*P.q)*(P.vp-p*b) := by
                    rw [← hdif]
                    linarith only [h]
                  have := (mul_nonneg_iff_of_pos_left hpos).1 this
                  linarith only [this]
                · intro h
                  have hh := mul_nonneg (le_of_lt hpos) (sub_nonneg.2 h)
                  rw [← hdif] at hh
                  linarith only [hh]
            have hcoverhigh : ∀ p : ℝ, V ≤ p → p < R →
                (coversU P p ↔ p*a-P.vbar/2 ≤ P.vp) := by
              intro p hpV hpR
              have hp : 0 ≤ p := le_trans (le_of_lt hV0) hpV
              have hd1 : P.vbar-1*p*P.z ≤ 0 := by
                have := (mul_le_mul_iff_left₀ hz0).2 hpV
                rw [hVz] at this
                nlinarith only [this]
              have hdβ : 0 < P.vbar-P.β*p*P.z := by
                have := (mul_lt_mul_iff_left₀ (mul_pos hβ hz0)).2 hpR
                rw [hRz] at this
                nlinarith only [this]
              unfold coversU
              rw [hobj 1 p (by norm_num) hp,hobj P.β p (le_of_lt hβ) hp,
                max_eq_right hd1,max_eq_left (le_of_lt hdβ)]
              have hbr : P.q*P.vp-p+P.q/2*(P.vbar+P.β*p*P.z) =
                  P.q*(P.vp-(p*a-P.vbar/2)) := by linear_combination p*haq
              rw [hbr]
              have hpos : 0 < P.n/P.vbar*(P.vbar-P.β*p*P.z)*P.q := by positivity
              simp only [mul_zero,zero_mul]
              rw [← mul_assoc,mul_nonneg_iff_of_pos_left hpos]
              exact sub_nonneg
            let s : ℝ := pStar P
            let t : ℝ := pBarStar P
            let K : ℝ := P.n/P.vbar
            have hK : 0 < K := div_pos hn hv
            have hs : 2*s = P.c+R := by dsimp [s,pStar,R]; field_simp <;> ring
            have ht : 2*t = P.c+V := by dsimp [t,pBarStar,V]; ring
            have hsc : P.c < s := by linarith only [hs,hcR]
            have hsR : s < R := by linarith only [hs,hcR]
            have hs0 : 0 < s := lt_trans hc hsc
            have ht0 : 0 < t := by linarith only [ht,hc,hV0]
            have hts : t < s := by linarith only [hs,ht,hVR]
            have hprofitβ : ∀ p : ℝ, 0 ≤ p → p ≤ R →
                firmProfitU P P.β p = K*(P.β*P.z)*(p-P.c)*(R-p) := by
              intro p hp hpR
              have hh : 0 ≤ P.vbar-P.β*p*P.z := by
                have hh := (mul_le_mul_iff_left₀ (mul_pos hβ hz0)).2 hpR
                rw [hRz] at hh
                nlinarith only [hh]
              rw [hprofit _ _ (le_of_lt hβ) hp,max_eq_left hh]
              change K*(p-P.c)*(P.vbar-P.β*p*P.z) = _
              rw [← hRz]
              ring
            have hprofit1 : ∀ p : ℝ, 0 ≤ p → p ≤ V →
                firmProfitU P 1 p = K*P.z*(p-P.c)*(V-p) := by
              intro p hp hpV
              have hh : 0 ≤ P.vbar-1*p*P.z := by
                have hh := (mul_le_mul_iff_left₀ hz0).2 hpV
                rw [hVz] at hh
                nlinarith only [hh]
              rw [hprofit _ _ (by norm_num) hp,max_eq_left hh]
              change K*(p-P.c)*(P.vbar-1*p*P.z) = _
              rw [← hVz]
              ring
            have hzeroβ : ∀ p : ℝ, R ≤ p → firmProfitU P P.β p = 0 := by
              intro p hpR
              have hp := le_trans (le_of_lt hR0) hpR
              have hh : P.vbar-P.β*p*P.z ≤ 0 := by
                have hh := (mul_le_mul_iff_left₀ (mul_pos hβ hz0)).2 hpR
                rw [hRz] at hh
                nlinarith only [hh]
              rw [hprofit _ _ (le_of_lt hβ) hp,max_eq_right hh]
              ring
            have hzero1 : ∀ p : ℝ, V ≤ p → firmProfitU P 1 p = 0 := by
              intro p hpV
              have hp := le_trans (le_of_lt hV0) hpV
              have hh : P.vbar-1*p*P.z ≤ 0 := by
                have hh := (mul_le_mul_iff_left₀ hz0).2 hpV
                rw [hVz] at hh
                nlinarith only [hh]
              rw [hprofit _ _ (by norm_num) hp,max_eq_right hh]
              ring
            have hcovered : ∀ p, coversU P p → realizedProfitU P p = firmProfitU P P.β p := by
              intro p hp
              simp only [realizedProfitU,shareU,if_pos hp]
            have huncovered : ∀ p, ¬ coversU P p → realizedProfitU P p = firmProfitU P 1 p := by
              intro p hp
              simp only [realizedProfitU,shareU,if_neg hp]
            have hnonpos : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p → p ≤ P.c → firmProfitU P bb p ≤ 0 := by
              intro bb p hbb hp hpc
              rw [hprofit _ _ hbb hp]
              exact mul_nonpos_of_nonpos_of_nonneg
                (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hK) (sub_nonpos.2 hpc)) (le_max_right _ _)
            have hrealnonpos : ∀ p : ℝ, 0 ≤ p → p ≤ P.c → realizedProfitU P p ≤ 0 := by
              intro p hp hpc
              by_cases hh : coversU P p
              · rw [hcovered p hh]
                exact hnonpos _ _ (le_of_lt hβ) hp hpc
              · rw [huncovered p hh]
                exact hnonpos _ _ (by norm_num) hp hpc
            have hdom : ∀ p : ℝ, P.c ≤ p → realizedProfitU P p ≤ firmProfitU P P.β p := by
              intro p hpc
              have hp : 0 ≤ p := le_trans (le_of_lt hc) hpc
              by_cases hh : coversU P p
              · rw [hcovered p hh]
              · rw [huncovered p hh,hprofit _ _ (by norm_num) hp,hprofit _ _ (le_of_lt hβ) hp]
                apply mul_le_mul_of_nonneg_left
                · apply max_le_max_right
                  nlinarith only [hβh,mul_nonneg hp (le_of_lt hz0)]
                · exact mul_nonneg (le_of_lt hK) (sub_nonneg.2 hpc)
            have hpeakpos : 0 < firmProfitU P P.β s := by
              rw [hprofitβ s (le_of_lt hs0) (le_of_lt hsR)]
              exact mul_pos (mul_pos (mul_pos hK (mul_pos hβ hz0)) (sub_pos.2 hsc)) (sub_pos.2 hsR)
            have hpeak : ∀ p : ℝ, 0 ≤ p → firmProfitU P P.β p ≤ firmProfitU P P.β s ∧
                (firmProfitU P P.β p = firmProfitU P P.β s → p=s) := by
              intro p hp
              by_cases hpR : p ≤ R
              · have hid : firmProfitU P P.β s-firmProfitU P P.β p = K*(P.β*P.z)*(p-s)^2 := by
                  rw [hprofitβ s (le_of_lt hs0) (le_of_lt hsR),hprofitβ p hp hpR]
                  linear_combination -K*(P.β*P.z)*(s-p)*hs
                have hcoef : 0 < K*(P.β*P.z) := mul_pos hK (mul_pos hβ hz0)
                constructor
                · nlinarith only [hid,mul_nonneg (le_of_lt hcoef) (sq_nonneg (p-s))]
                · intro heq
                  have hzsq : (p-s)^2=0 := by nlinarith only [hid,heq,hcoef,sq_nonneg (p-s)]
                  nlinarith only [hzsq]
              · rw [hzeroβ p (le_of_lt (lt_of_not_ge hpR))]
                exact ⟨le_of_lt hpeakpos,fun h => False.elim ((ne_of_gt hpeakpos) h.symm)⟩
            have hinc : ∀ x y : ℝ, P.c ≤ x → x < y → y ≤ s →
                firmProfitU P P.β x < firmProfitU P P.β y := by
              intro x y hcx hxy hys
              have hx0 : 0 ≤ x := le_trans (le_of_lt hc) hcx
              have hy0 : 0 ≤ y := le_trans hx0 (le_of_lt hxy)
              have hxR : x ≤ R := by linarith only [hxy,hys,hsR]
              have hyR : y ≤ R := le_trans hys (le_of_lt hsR)
              have hid : firmProfitU P P.β y-firmProfitU P P.β x = K*(P.β*P.z)*(y-x)*(2*s-x-y) := by
                rw [hprofitβ y hy0 hyR,hprofitβ x hx0 hxR]
                linear_combination -K*(P.β*P.z)*(y-x)*hs
              have hh : 0 < K*(P.β*P.z)*(y-x)*(2*s-x-y) := by
                apply mul_pos
                · exact mul_pos (mul_pos hK (mul_pos hβ hz0)) (sub_pos.2 hxy)
                · linarith only [hxy,hys]
              linarith only [hid,hh]
            have hprofdom : ∀ p : ℝ, P.c ≤ p → firmProfitU P 1 p ≤ firmProfitU P P.β p := by
              intro p hpc
              have hp : 0 ≤ p := le_trans (le_of_lt hc) hpc
              rw [hprofit _ _ (by norm_num) hp,hprofit _ _ (le_of_lt hβ) hp]
              apply mul_le_mul_of_nonneg_left
              · apply max_le_max_right
                nlinarith only [hβh,mul_nonneg hp (le_of_lt hz0)]
              · exact mul_nonneg (le_of_lt hK) (sub_nonneg.2 hpc)
            have hpriceRoots : P.c ≤ V → ∃! p3, p3 ∈ Set.Icc P.c t ∧
                firmProfitU P 1 t = firmProfitU P P.β p3 := by
              intro hcV
              have hct : P.c ≤ t := by linarith only [ht,hcV]
              have htV : t ≤ V := by linarith only [ht,hcV]
              have hft : 0 ≤ firmProfitU P 1 t := by
                rw [hprofit1 t (le_of_lt ht0) htV]
                exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt hz0))
                  (sub_nonneg.2 hct)) (sub_nonneg.2 htV)
              let f : ℝ → ℝ := fun p => K*(P.β*P.z)*(p-P.c)*(R-p)
              have hfc : f P.c = 0 := by dsimp [f]; ring
              have hft' : firmProfitU P 1 t ≤ f t := by
                change firmProfitU P 1 t ≤ K*(P.β*P.z)*(t-P.c)*(R-t)
                rw [← hprofitβ t (le_of_lt ht0) (le_of_lt (lt_trans hts hsR))]
                exact hprofdom t hct
              have hfe : ∃ p3 ∈ Set.Icc P.c t, f p3 = firmProfitU P 1 t := by
                apply intermediate_value_Icc hct (by fun_prop : ContinuousOn f (Set.Icc P.c t))
                rw [hfc]
                exact ⟨hft,hft'⟩
              obtain ⟨p3,hp3,heq⟩ := hfe
              have hp30 : 0 ≤ p3 := le_trans (le_of_lt hc) hp3.1
              have hp3R : p3 ≤ R := le_trans hp3.2 (le_of_lt (lt_trans hts hsR))
              have heq' : firmProfitU P 1 t = firmProfitU P P.β p3 := by
                rw [hprofitβ p3 hp30 hp3R]
                exact heq.symm
              refine ⟨p3,⟨hp3,heq'⟩,?_⟩
              intro y hy
              rcases lt_trichotomy y p3 with hh | hh | hh
              · have hf := hinc y p3 hy.1.1 hh (le_trans hp3.2 (le_of_lt hts))
                rw [← heq',← hy.2] at hf
                exact False.elim (lt_irrefl _ hf)
              · exact hh
              · have hf := hinc p3 y hp3.1 hh (le_trans hy.1.2 (le_of_lt hts))
                rw [← heq',← hy.2] at hf
                exact False.elim (lt_irrefl _ hf)
            have hunpeak : P.c ≤ V → ∀ p : ℝ, 0 ≤ p →
                firmProfitU P 1 p ≤ firmProfitU P 1 t ∧
                (P.c < V → firmProfitU P 1 p = firmProfitU P 1 t → p=t) := by
              intro hcV p hp
              have hct : P.c ≤ t := by linarith only [ht,hcV]
              have htV : t ≤ V := by linarith only [ht,hcV]
              have hft : 0 ≤ firmProfitU P 1 t := by
                rw [hprofit1 t (le_of_lt ht0) htV]
                exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt hz0))
                  (sub_nonneg.2 hct)) (sub_nonneg.2 htV)
              by_cases hpV : p ≤ V
              · have hid : firmProfitU P 1 t-firmProfitU P 1 p = K*P.z*(p-t)^2 := by
                  rw [hprofit1 t (le_of_lt ht0) htV,hprofit1 p hp hpV]
                  linear_combination -K*P.z*(t-p)*ht
                have hcoef : 0 < K*P.z := mul_pos hK hz0
                constructor
                · nlinarith only [hid,mul_nonneg (le_of_lt hcoef) (sq_nonneg (p-t))]
                · intro hcV' heq
                  have hzsq : (p-t)^2=0 := by nlinarith only [hid,heq,hcoef,sq_nonneg (p-t)]
                  nlinarith only [hzsq]
              · rw [hzero1 p (le_of_lt (lt_of_not_ge hpV))]
                refine ⟨hft,?_⟩
                intro hcV' heq
                have hct' : P.c < t := by linarith only [ht,hcV']
                have htV' : t < V := by linarith only [ht,hcV']
                have hfpos : 0 < firmProfitU P 1 t := by
                  rw [hprofit1 t (le_of_lt ht0) htV]
                  exact mul_pos (mul_pos (mul_pos hK hz0) (sub_pos.2 hct')) (sub_pos.2 htV')
                exact False.elim ((ne_of_gt hfpos) heq.symm)
            have hrealpeak : ∀ p : ℝ, 0 ≤ p → realizedProfitU P p ≤ firmProfitU P P.β s ∧
                (realizedProfitU P p = firmProfitU P P.β s → p=s) := by
              intro p hp
              by_cases hpc : p ≤ P.c
              · have hh := hrealnonpos p hp hpc
                exact ⟨le_trans hh (le_of_lt hpeakpos),fun he => False.elim (by linarith only [hh,he,hpeakpos])⟩
              · have hd := hdom p (le_of_lt (lt_of_not_ge hpc))
                have hm := hpeak p hp
                refine ⟨le_trans hd hm.1,?_⟩
                intro he
                apply hm.2
                exact le_antisymm hm.1 (by rw [← he]; exact hd)
            have hmaxs : coversU P s → IsEqPriceU P s ∧ coversU P s ∧
                ∀ p, IsEqPriceU P p → p=s := by
              intro hcov
              have he := hcovered s hcov
              refine ⟨⟨le_of_lt hs0,?_⟩,hcov,?_⟩
              · intro p hp
                rw [he]
                exact (hrealpeak p hp).1
              · intro p hp
                apply (hrealpeak p hp.1).2
                exact le_antisymm (hrealpeak p hp.1).1 (by rw [← he]; exact hp.2 s (le_of_lt hs0))
            have hVs : V < s := by
              have hh : 2*V ≤ R := by
                have hh := mul_le_mul_of_nonneg_left hβh (le_of_lt hR0)
                nlinarith only [hRβ,hh]
              linarith only [hs,hh,hc]
            have hrootless : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                qb < P.q → P.z*P.q < 1/P.β := by
              intro qb hb hqbq
              by_cases hf : 1 < P.z*P.q
              · have hh := hcompare qb P.q hb.1 hqbq hqone hf
                rw [hb.2.2] at hh
                exact hh
              · linarith only [hf,hk]
            have hrootmore : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                P.q ≤ qb → 1/P.β ≤ P.z*P.q := by
              intro qb hb hqqb
              rcases lt_or_eq_of_le hqqb with hh | hh
              · have hf := hcompare P.q qb hq hh hb.2.1 (by rw [hb.2.2]; exact hk)
                rw [hb.2.2] at hf
                exact le_of_lt hf
              · simpa only [hh,Params.z] using le_of_eq hb.2.2.symm
            have hregion1 : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                (P.q ≤ qb ∨ (qb < P.q ∧ s*a-P.vbar/2 ≤ P.vp)) →
                IsEqPriceU P s ∧ coversU P s ∧ ∀ p, IsEqPriceU P p → p=s := by
              intro qb hb hreg
              apply hmaxs
              apply (hcoverhigh s (le_of_lt hVs) hsR).2
              rcases hreg with hh | ⟨hh,hvp'⟩
              · have hf := hrootmore qb hb hh
                have hf' := (div_le_iff₀ hβ).1 hf
                have ha : a ≤ P.z*P.β/2 := by
                  apply (mul_le_mul_iff_left₀ hq).1
                  nlinarith only [haq,hf']
                have ha' := mul_le_mul_of_nonneg_left ha (le_of_lt hs0)
                have hs' := (mul_lt_mul_iff_left₀ (mul_pos hβ hz0)).2 hsR
                rw [hRz] at hs'
                nlinarith only [ha',hs',hvp]
              · exact hvp'
            have hprofpos : ∀ l : ℝ, P.c < l → l < R → 0 < firmProfitU P P.β l := by
              intro l hcl hlR
              have hl0 := lt_trans hc hcl
              rw [hprofitβ l (le_of_lt hl0) (le_of_lt hlR)]
              exact mul_pos (mul_pos (mul_pos hK (mul_pos hβ hz0)) (sub_pos.2 hcl)) (sub_pos.2 hlR)
            have hincle : ∀ x y : ℝ, P.c ≤ x → x ≤ y → y ≤ s →
                firmProfitU P P.β x ≤ firmProfitU P P.β y := by
              intro x y hcx hxy hys
              rcases lt_or_eq_of_le hxy with hh | hh
              · exact le_of_lt (hinc x y hcx hh hys)
              · rw [hh]
            have hcapbound : ∀ l : ℝ, P.c ≤ l → l ≤ s →
                (∀ p, P.c < p → p < R → coversU P p → p ≤ l) →
                ∀ p, 0 ≤ p → coversU P p →
                  firmProfitU P P.β p ≤ firmProfitU P P.β l ∧
                  (P.c < l → firmProfitU P P.β p = firmProfitU P P.β l → p=l) := by
              intro l hcl hls hcap p hp hcov
              have hl0 : 0 ≤ l := le_trans (le_of_lt hc) hcl
              have hlR : l < R := lt_of_le_of_lt hls hsR
              have hfl : 0 ≤ firmProfitU P P.β l := by
                rw [hprofitβ l hl0 (le_of_lt hlR)]
                exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt (mul_pos hβ hz0)))
                  (sub_nonneg.2 hcl)) (le_of_lt (sub_pos.2 hlR))
              by_cases hpc : p ≤ P.c
              · have hh := hnonpos P.β p (le_of_lt hβ) hp hpc
                refine ⟨le_trans hh hfl,?_⟩
                intro hcl' heq
                have hh' := hprofpos l hcl' hlR
                exact False.elim (by linarith only [hh,hh',heq])
              · by_cases hpR : p < R
                · have hpl := hcap p (lt_of_not_ge hpc) hpR hcov
                  refine ⟨hincle p l (le_of_lt (lt_of_not_ge hpc)) hpl hls,?_⟩
                  intro hcl' heq
                  rcases lt_or_eq_of_le hpl with hh | hh
                  · have hh' := hinc p l (le_of_lt (lt_of_not_ge hpc)) hh hls
                    exact False.elim (by linarith only [hh',heq])
                  · exact hh
                · rw [hzeroβ p (le_of_not_gt hpR)]
                  refine ⟨hfl,?_⟩
                  intro hcl' heq
                  exact False.elim ((ne_of_gt (hprofpos l hcl' hlR)) heq.symm)
            have hcapEq : ∀ l : ℝ, P.c ≤ l → l ≤ s → coversU P l →
                (∀ p, P.c < p → p < R → coversU P p → p ≤ l) →
                (∀ p, 0 ≤ p → firmProfitU P 1 p ≤ firmProfitU P P.β l) →
                IsEqPriceU P l := by
              intro l hcl hls hcov hcap hun
              refine ⟨le_trans (le_of_lt hc) hcl,?_⟩
              intro p hp
              rw [hcovered l hcov]
              by_cases hh : coversU P p
              · rw [hcovered p hh]
                exact (hcapbound l hcl hls hcap p hp hh).1
              · rw [huncovered p hh]
                exact hun p hp
            have hcapUnique : ∀ l : ℝ, P.c < l → l ≤ s → coversU P l →
                (∀ p, P.c < p → p < R → coversU P p → p ≤ l) →
                (∀ p, 0 ≤ p → firmProfitU P 1 p < firmProfitU P P.β l) →
                ∀ p, IsEqPriceU P p → p=l := by
              intro l hcl hls hcov hcap hun p hp
              have hm := hp.2 l (le_of_lt (lt_trans hc hcl))
              rw [hcovered l hcov] at hm
              by_cases hh : coversU P p
              · rw [hcovered p hh] at hm
                have hbnd := hcapbound l (le_of_lt hcl) hls hcap p hp.1 hh
                exact hbnd.2 hcl (le_antisymm hbnd.1 hm)
              · rw [huncovered p hh] at hm
                exact False.elim (not_lt_of_ge hm (hun p hp.1))
            have hregion2 : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                (qb < P.q ∧ max P.c V*a-P.vbar/2 < P.vp ∧ P.vp < s*a-P.vbar/2) →
                IsEqPriceU P (P.q*(P.vp+P.vbar/2)/(1-P.q*P.z*P.β/2)) ∧
                  coversU P (P.q*(P.vp+P.vbar/2)/(1-P.q*P.z*P.β/2)) ∧
                  ∀ p, IsEqPriceU P p → p=P.q*(P.vp+P.vbar/2)/(1-P.q*P.z*P.β/2) := by
              intro qb hb hreg
              have hf := hrootless qb hb hreg.1
              have hf' := (lt_div_iff₀ hβ).1 hf
              have ha : 0 < a := by
                have : 0 < a*P.q := by nlinarith only [haq,hf']
                exact (mul_pos_iff_of_pos_right hq).1 this
              let l := P.q*(P.vp+P.vbar/2)/(1-P.q*P.z*P.β/2)
              have hden : 0 < 1-P.q*P.z*P.β/2 := by nlinarith only [hf']
              have hla : l*a = P.vp+P.vbar/2 := by
                dsimp only [l]
                rw [show 1-P.q*P.z*P.β/2=a*P.q by nlinarith only [haq]]
                field_simp [ne_of_gt ha,ne_of_gt hq]
                <;> ring
              have hml : max P.c V < l := by
                apply (mul_lt_mul_iff_left₀ ha).1
                linarith only [hreg.2.1,hla]
              have hcl : P.c < l := lt_of_le_of_lt (le_max_left _ _) hml
              have hVl : V < l := lt_of_le_of_lt (le_max_right _ _) hml
              have hls : l < s := by
                apply (mul_lt_mul_iff_left₀ ha).1
                linarith only [hreg.2.2,hla]
              have hlR := lt_trans hls hsR
              have hcov : coversU P l := (hcoverhigh l (le_of_lt hVl) hlR).2 (by linarith only [hla])
              have hcap : ∀ p, P.c < p → p < R → coversU P p → p ≤ l := by
                intro p hpc hpR hcp
                by_cases hpV : p ≤ V
                · exact le_trans hpV (le_of_lt hVl)
                · have hpv := (hcoverhigh p (le_of_lt (lt_of_not_ge hpV)) hpR).1 hcp
                  apply (mul_le_mul_iff_left₀ ha).1
                  linarith only [hpv,hla]
              have hun : ∀ p, 0 ≤ p → firmProfitU P 1 p < firmProfitU P P.β l := by
                intro p hp
                by_cases hpc : p ≤ P.c
                · exact lt_of_le_of_lt (hnonpos 1 p (by norm_num) hp hpc) (hprofpos l hcl hlR)
                · by_cases hpV : p ≤ V
                  · exact lt_of_le_of_lt (hprofdom p (le_of_lt (lt_of_not_ge hpc)))
                      (hinc p l (le_of_lt (lt_of_not_ge hpc)) (lt_of_le_of_lt hpV hVl) (le_of_lt hls))
                  · rw [hzero1 p (le_of_lt (lt_of_not_ge hpV))]
                    exact hprofpos l hcl hlR
              exact ⟨hcapEq l (le_of_lt hcl) (le_of_lt hls) hcov hcap (fun p hp => le_of_lt (hun p hp)),
                hcov,hcapUnique l hcl (le_of_lt hls) hcov hcap hun⟩
            have hab : a=b+P.z/2 := by dsimp [a,b]; ring
            have hbpos : q2 < P.q → 0 < b := by
              intro hqq
              have hk2one : 1 < 2/(1+P.β) := (lt_div_iff₀ (by linarith only [hβ] : 0 < 1+P.β)).2 (by linarith only [hβh])
              have hf : P.z*P.q < 2/(1+P.β) := by
                by_cases hh : 1 < P.z*P.q
                · have hh' := hcompare q2 P.q hq2.1 hqq hqone hh
                  rw [hq2.2.2] at hh'
                  exact hh'
                · linarith only [hh,hk2one]
              have hf' := (lt_div_iff₀ (by linarith only [hβ] : 0 < 1+P.β)).1 hf
              apply (mul_pos_iff_of_pos_right hq).1
              nlinarith only [hbq,hf']
            have hcaplow : ∀ l : ℝ, 0 < b → l*b=P.vp → l ≤ V →
                ∀ p, P.c < p → p < R → coversU P p → p ≤ l := by
              intro l hb hl hlV p hpc hpR hcov
              have hp0 := le_of_lt (lt_trans hc hpc)
              by_cases hpV : p ≤ V
              · have hh := (hcoverlow p hp0 hpV).1 hcov
                apply (mul_le_mul_iff_left₀ hb).1
                linarith only [hh,hl]
              · have hh := (hcoverhigh p (le_of_lt (lt_of_not_ge hpV)) hpR).1 hcov
                have ha : 0 < a := by linarith only [hab,hb,hz0]
                have hpa := mul_lt_mul_of_pos_right (lt_of_not_ge hpV) ha
                have hlb := mul_le_mul_of_nonneg_right hlV (le_of_lt hb)
                exact False.elim (by linarith only [hh,hpa,hVab,hlb,hl])
            have hregion34 : ∀ p3, (p3 ∈ Set.Icc P.c t ∧ firmProfitU P 1 t=firmProfitU P P.β p3) →
                (q2<P.q ∧ P.c≤V ∧ p3*b≤P.vp ∧ P.vp≤V*b →
                  IsEqPriceU P (P.q*P.vp/(1-P.q*P.z*(1+P.β)/2)) ∧
                    coversU P (P.q*P.vp/(1-P.q*P.z*(1+P.β)/2)) ∧
                    (p3*b<P.vp → ∀ p, IsEqPriceU P p → p=P.q*P.vp/(1-P.q*P.z*(1+P.β)/2))) ∧
                (q2<P.q ∧ P.c≤V ∧ P.vp<p3*b →
                  IsEqPriceU P t ∧ ¬ coversU P t ∧
                    (P.c<V → ∀ p, IsEqPriceU P p → p=t)) := by
              intro p3 hp3
              have hp30 : 0 ≤ p3 := le_trans (le_of_lt hc) hp3.1.1
              have hp3s : p3 ≤ s := le_trans hp3.1.2 (le_of_lt hts)
              constructor
              · intro hreg
                have hb := hbpos hreg.1
                let l := P.q*P.vp/(1-P.q*P.z*(1+P.β)/2)
                have hden : 0 < 1-P.q*P.z*(1+P.β)/2 := by nlinarith only [hbq,mul_pos hb hq]
                have hlb : l*b=P.vp := by
                  dsimp only [l]
                  rw [show 1-P.q*P.z*(1+P.β)/2=b*P.q by nlinarith only [hbq]]
                  field_simp [ne_of_gt hb,ne_of_gt hq]
                  <;> ring
                have hp3l : p3 ≤ l := by
                  apply (mul_le_mul_iff_left₀ hb).1
                  linarith only [hlb,hreg.2.2.1]
                have hlV : l ≤ V := by
                  apply (mul_le_mul_iff_left₀ hb).1
                  linarith only [hlb,hreg.2.2.2]
                have hcl := le_trans hp3.1.1 hp3l
                have hl0 := le_trans (le_of_lt hc) hcl
                have hls := le_trans hlV (le_of_lt hVs)
                have hcov : coversU P l := (hcoverlow l hl0 hlV).2 (le_of_eq hlb)
                have hcap := hcaplow l hb hlb hlV
                have hun : ∀ p, 0 ≤ p → firmProfitU P 1 p ≤ firmProfitU P P.β l := by
                  intro p hp
                  have hh := (hunpeak hreg.2.1 p hp).1
                  rw [hp3.2] at hh
                  exact le_trans hh (hincle p3 l hp3.1.1 hp3l hls)
                refine ⟨hcapEq l hcl hls hcov hcap hun,hcov,?_⟩
                intro hstrict
                have hp3l' : p3 < l := by
                  apply (mul_lt_mul_iff_left₀ hb).1
                  linarith only [hlb,hstrict]
                have hcl' := lt_of_le_of_lt hp3.1.1 hp3l'
                apply hcapUnique l hcl' hls hcov hcap
                intro p hp
                have hh := (hunpeak hreg.2.1 p hp).1
                rw [hp3.2] at hh
                exact lt_of_le_of_lt hh (hinc p3 l hp3.1.1 hp3l' hls)
              · intro hreg
                have hb := hbpos hreg.1
                have htV : t ≤ V := by linarith only [ht,hreg.2.1]
                have hncov : ¬ coversU P t := by
                  intro hh
                  have hh' := (hcoverlow t (le_of_lt ht0) htV).1 hh
                  have hh'' := mul_le_mul_of_nonneg_right hp3.1.2 (le_of_lt hb)
                  linarith only [hh',hh'',hreg.2.2]
                have hft : 0 ≤ firmProfitU P 1 t := by
                  have hh := (hunpeak hreg.2.1 P.c (le_of_lt hc)).1
                  have hfc : firmProfitU P 1 P.c=0 := by simp only [firmProfitU,sub_self,zero_mul]
                  rw [hfc] at hh
                  exact hh
                have hbound : ∀ p, 0 ≤ p → coversU P p → firmProfitU P P.β p ≤ firmProfitU P 1 t := by
                  intro p hp hcov
                  by_cases hpc : p ≤ P.c
                  · exact le_trans (hnonpos P.β p (le_of_lt hβ) hp hpc) hft
                  · by_cases hpR : p < R
                    · have hpV : p ≤ V := by
                        by_contra hh
                        have hc := (hcoverhigh p (le_of_lt (lt_of_not_ge hh)) hpR).1 hcov
                        have ha : 0<a := by linarith only [hab,hb,hz0]
                        have hh' := mul_lt_mul_of_pos_right (lt_of_not_ge hh) ha
                        have h3 := mul_le_mul_of_nonneg_right (le_trans hp3.1.2 htV) (le_of_lt hb)
                        linarith only [hc,hh',h3,hVab,hreg.2.2]
                      have hh := (hcoverlow p hp hpV).1 hcov
                      have hpp3 : p < p3 := by
                        apply (mul_lt_mul_iff_left₀ hb).1
                        linarith only [hh,hreg.2.2]
                      rw [hp3.2]
                      exact le_of_lt (hinc p p3 (le_of_lt (lt_of_not_ge hpc)) hpp3 hp3s)
                    · rw [hzeroβ p (le_of_not_gt hpR)]
                      exact hft
                have heq : IsEqPriceU P t := by
                  refine ⟨le_of_lt ht0,?_⟩
                  intro p hp
                  rw [huncovered t hncov]
                  by_cases hh : coversU P p
                  · rw [hcovered p hh]
                    exact hbound p hp hh
                  · rw [huncovered p hh]
                    exact (hunpeak hreg.2.1 p hp).1
                refine ⟨heq,hncov,?_⟩
                intro hcV p hp
                have hm := hp.2 t (le_of_lt ht0)
                rw [huncovered t hncov] at hm
                by_cases hh : coversU P p
                · rw [hcovered p hh] at hm
                  have hfpos : 0 < firmProfitU P 1 t := by
                    rw [hprofit1 t (le_of_lt ht0) htV]
                    have hct : P.c<t := by linarith only [ht,hcV]
                    have htV' : t<V := by linarith only [ht,hcV]
                    exact mul_pos (mul_pos (mul_pos hK hz0) (sub_pos.2 hct)) (sub_pos.2 htV')
                  by_cases hpc : p ≤ P.c
                  · have hh' := hnonpos P.β p (le_of_lt hβ) hp.1 hpc
                    exact False.elim (by linarith only [hh',hm,hfpos])
                  · by_cases hpR : p < R
                    · have hpV : p ≤ V := by
                        by_contra hh'
                        have hc := (hcoverhigh p (le_of_lt (lt_of_not_ge hh')) hpR).1 hh
                        have ha : 0<a := by linarith only [hab,hb,hz0]
                        have hh'' := mul_lt_mul_of_pos_right (lt_of_not_ge hh') ha
                        have h3 := mul_le_mul_of_nonneg_right (le_trans hp3.1.2 htV) (le_of_lt hb)
                        linarith only [hc,hh'',h3,hVab,hreg.2.2]
                      have hh' := (hcoverlow p hp.1 hpV).1 hh
                      have hpp3 : p<p3 := by
                        apply (mul_lt_mul_iff_left₀ hb).1
                        linarith only [hh',hreg.2.2]
                      have hi := hinc p p3 (le_of_lt (lt_of_not_ge hpc)) hpp3 hp3s
                      rw [← hp3.2] at hi
                      exact False.elim (not_lt_of_ge hm hi)
                    · rw [hzeroβ p (le_of_not_gt hpR)] at hm
                      exact False.elim (by linarith only [hm,hfpos])
                · rw [huncovered p hh] at hm
                  exact (hunpeak hreg.2.1 p hp.1).2 hcV
                    (le_antisymm (hunpeak hreg.2.1 p hp.1).1 hm)
            have hcostthreshold : P.c/P.q*(1-P.q*P.z*P.β/2)-P.vbar/2 = P.c*a-P.vbar/2 := by
              dsimp [a]
              field_simp
              <;> ring
            have hregion5 : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                (qb<P.q ∧ V<P.c ∧ P.vp≤P.c/P.q*(1-P.q*P.z*P.β/2)-P.vbar/2) →
                (∀ p, 0≤p → realizedProfitU P p≤0) ∧
                (∃ p, 0≤p ∧ realizedProfitU P p=0) ∧
                (∀ p, P.c<p → p<R → ¬ coversU P p) ∧
                (P.vp<P.c/P.q*(1-P.q*P.z*P.β/2)-P.vbar/2 → ¬ coversU P P.c) := by
              intro qb hb hreg
              have hf := hrootless qb hb hreg.1
              have hf' := (lt_div_iff₀ hβ).1 hf
              have ha : 0<a := by
                apply (mul_pos_iff_of_pos_right hq).1
                nlinarith only [haq,hf']
              have hvp' : P.vp≤P.c*a-P.vbar/2 := by rw [← hcostthreshold]; exact hreg.2.2
              have hncov : ∀ p, P.c<p → p<R → ¬coversU P p := by
                intro p hpc hpR hcov
                have hpV : V≤p := le_of_lt (lt_trans hreg.2.1 hpc)
                have hh := (hcoverhigh p hpV hpR).1 hcov
                have hh' := mul_lt_mul_of_pos_right hpc ha
                linarith only [hh,hh',hvp']
              refine ⟨?_,?_,hncov,?_⟩
              · intro p hp
                by_cases hpc : p≤P.c
                · exact hrealnonpos p hp hpc
                · by_cases hpR : p<R
                  · rw [huncovered p (hncov p (lt_of_not_ge hpc) hpR),
                      hzero1 p (le_of_lt (lt_trans hreg.2.1 (lt_of_not_ge hpc))) ]
                  · by_cases hh : coversU P p
                    · rw [hcovered p hh,hzeroβ p (le_of_not_gt hpR)]
                    · rw [huncovered p hh,hzero1 p (le_trans (le_of_lt hVR) (le_of_not_gt hpR))]
              · refine ⟨P.c,le_of_lt hc,?_⟩
                simp only [realizedProfitU,firmProfitU,sub_self,zero_mul]
              · intro hstrict hcov
                have hh := (hcoverhigh P.c (le_of_lt hreg.2.1) hcR).1 hcov
                rw [hcostthreshold] at hstrict
                linarith only [hh,hstrict]
            have hexhaust : ∀ qb, (0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb*qb=1/P.β) →
                ¬(P.q=q2 ∧ P.vp=0 ∧ P.c≤V) →
                (P.q≤qb ∨ (qb<P.q ∧ s*a-P.vbar/2≤P.vp)) ∨
                (qb<P.q ∧ max P.c V*a-P.vbar/2<P.vp ∧ P.vp<s*a-P.vbar/2) ∨
                (∃ p3, (p3∈Set.Icc P.c t ∧ firmProfitU P 1 t=firmProfitU P P.β p3) ∧
                  q2<P.q ∧ P.c≤V ∧ p3*b≤P.vp ∧ P.vp≤V*b) ∨
                (∃ p3, (p3∈Set.Icc P.c t ∧ firmProfitU P 1 t=firmProfitU P P.β p3) ∧
                  q2<P.q ∧ P.c≤V ∧ P.vp<p3*b) ∨
                (qb<P.q ∧ V<P.c ∧ P.vp≤P.c/P.q*(1-P.q*P.z*P.β/2)-P.vbar/2) := by
              intro qb hb hboundary
              by_cases hqqb : P.q≤qb
              · exact Or.inl (Or.inl hqqb)
              have hqbq := lt_of_not_ge hqqb
              by_cases hstar : s*a-P.vbar/2≤P.vp
              · exact Or.inl (Or.inr ⟨hqbq,hstar⟩)
              have hvpstar := lt_of_not_ge hstar
              by_cases hmax : max P.c V*a-P.vbar/2<P.vp
              · exact Or.inr (Or.inl ⟨hqbq,hmax,hvpstar⟩)
              have hvpmax := le_of_not_gt hmax
              by_cases hcV : P.c≤V
              · have hvpV : P.vp≤V*b := by
                  rw [max_eq_right hcV,hVab] at hvpmax
                  exact hvpmax
                have hbnonneg : 0≤b := by
                  by_contra hh
                  have hh' := mul_neg_of_pos_of_neg hV0 (lt_of_not_ge hh)
                  linarith only [hh',hvpV,hvp]
                have hq2q : q2<P.q := by
                  by_contra hh
                  have hqq2 := le_of_not_gt hh
                  rcases lt_or_eq_of_le hqq2 with hqq2 | hqq2
                  · have hk2one : 1<2/(1+P.β) := (lt_div_iff₀ (by linarith only [hβ] : 0<1+P.β)).2 (by linarith only [hβh])
                    have hf := hcompare P.q q2 hq hqq2 hq2.2.1 (by rw [hq2.2.2]; exact hk2one)
                    rw [hq2.2.2] at hf
                    change 2/(1+P.β)<P.z*P.q at hf
                    have hf' := (div_lt_iff₀ (by linarith only [hβ] : 0<1+P.β)).1 hf
                    have hbqnonneg := mul_nonneg hbnonneg (le_of_lt hq)
                    nlinarith only [hbq,hf',hbqnonneg]
                  · apply hboundary
                    refine ⟨hqq2,?_,hcV⟩
                    have hqroot : P.z*P.q=2/(1+P.β) := by
                      change zOf P.α P.lam P.q*P.q=_
                      rw [hqq2,hq2.2.2]
                    have hqroot' := (eq_div_iff (by linarith only [hβ] : 1+P.β≠0)).1 hqroot
                    have hbzero : b=0 := by
                      have hh : b*P.q=0 := by nlinarith only [hbq,hqroot']
                      exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hq)
                    rw [hbzero,mul_zero] at hvpV
                    exact le_antisymm hvpV hvp
                obtain ⟨p3,hp3,huniq⟩ := hpriceRoots hcV
                by_cases hh : p3*b≤P.vp
                · exact Or.inr (Or.inr (Or.inl ⟨p3,hp3,hq2q,hcV,hh,hvpV⟩))
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p3,hp3,hq2q,hcV,lt_of_not_ge hh⟩)))
              · have hVc := lt_of_not_ge hcV
                rw [max_eq_left (le_of_lt hVc)] at hvpmax
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hqbq,hVc,by rw [hcostthreshold]; exact hvpmax⟩)))
            dsimp only
            refine ⟨hroots, ?_, ?_⟩
            · exact hpriceRoots
            · intro qb hb
              refine ⟨horder qb hb, ?_, ?_, ?_, ?_, ?_⟩
              · exact hregion1 qb hb
              · exact hregion2 qb hb
              · exact hregion34
              · exact hregion5 qb hb
              · exact hexhaust qb hb
