-- Prove2me | solution 1 for StrategicRFx.Benefit.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:35.956886+00:00
-- url     : https://prove2.me/submissions/115f79fd-8f88-4097-99d6-cbcc009d2ceb

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous

open StrategicRFx
open StrategicRFx.Benefit
open StrategicRFx.Benefit.Supplement

theorem solution (M : Technology) (b : FirstBest) (h : TechnologyAssumptions M b)
    (x : ContractOutcome) (hx : IsParetoSimultaneous M x) :
    IsCoordinated M b x.order := by
      have H1 : ∀ θ S u v : ℝ, 0 < θ → θ < 1 → 0 ≤ u → 0 ≤ v → u + v ≤ S →
          nashProduct θ u v ≤ nashProduct θ (θ*S) ((1-θ)*S) := by
        intro θ S u v h0 h1 hu hv hs
        have hS : 0 ≤ S := by linarith
        have h1' : 0 < 1 - θ := by linarith
        have amgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := θ) (w₂ := 1-θ) (p₁ := u/θ) (p₂ := v/(1-θ))
          h0.le h1'.le (div_nonneg hu h0.le) (div_nonneg hv h1'.le) (by ring)
        rw [Real.div_rpow hu h0.le, Real.div_rpow hv h1'.le] at amgm
        have e1 : θ * (u/θ) + (1-θ) * (v/(1-θ)) = u + v := by field_simp
        rw [e1] at amgm
        have hc0 : 0 < θ ^ θ := Real.rpow_pos_of_pos h0 _
        have hc1 : 0 < (1-θ) ^ (1-θ) := Real.rpow_pos_of_pos h1' _
        have key : u ^ θ * v ^ (1-θ) ≤ θ ^ θ * (1-θ) ^ (1-θ) * (u+v) := by
          rw [div_mul_div_comm, div_le_iff₀ (mul_pos hc0 hc1)] at amgm
          linarith
        unfold nashProduct
        rw [Real.mul_rpow h0.le hS, Real.mul_rpow h1'.le hS]
        have : S ^ θ * S ^ (1-θ) = S := by
          rw [← Real.rpow_add' hS (by norm_num)]; simp
        calc u ^ θ * v ^ (1-θ) ≤ θ ^ θ * (1-θ) ^ (1-θ) * (u+v) := key
          _ ≤ θ ^ θ * (1-θ) ^ (1-θ) * S := by gcongr
          _ = θ ^ θ * S ^ θ * ((1 - θ) ^ (1 - θ) * S ^ (1 - θ)) := by
            linear_combination (-(θ ^ θ * (1 - θ) ^ (1 - θ))) * this
      have H2 : ∀ θ T a : ℝ, 0 < θ → θ < 1 → 0 ≤ a → a ≤ T →
          nashProduct θ (θ*T) ((1-θ)*T) ≤ nashProduct θ a (T - a) → a = θ * T := by
        intro θ T a h0 h1 ha haT hle
        have h1' : 0 < 1 - θ := by linarith
        by_contra hne
        have hz : a/θ ≠ (T-a)/(1-θ) := by
          intro he
          apply hne
          field_simp at he
          linarith
        have strict := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
          ![θ, 1-θ] ![a/θ, (T-a)/(1-θ)] (by intro i _; fin_cases i <;> simp [h0, h1'])
          (by simp [Fin.sum_univ_two]) (by intro i _; fin_cases i <;> simp <;> apply div_nonneg <;> linarith)).2
          ⟨0, by simp, 1, by simp, by simpa using hz⟩
        simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at strict
        rw [Real.div_rpow ha h0.le, Real.div_rpow (by linarith) h1'.le] at strict
        have e1 : θ * (a/θ) + (1-θ) * ((T-a)/(1-θ)) = T := by field_simp; ring
        rw [e1] at strict
        have hc0 : 0 < θ ^ θ := Real.rpow_pos_of_pos h0 _
        have hc1 : 0 < (1-θ) ^ (1-θ) := Real.rpow_pos_of_pos h1' _
        have key : a ^ θ * (T-a) ^ (1-θ) < θ ^ θ * (1-θ) ^ (1-θ) * T := by
          rw [div_mul_div_comm, div_lt_iff₀ (mul_pos hc0 hc1)] at strict
          linarith
        have hT : 0 ≤ T := by linarith
        unfold nashProduct at hle
        rw [Real.mul_rpow h0.le hT, Real.mul_rpow h1'.le hT] at hle
        have : T ^ θ * T ^ (1-θ) = T := by
          rw [← Real.rpow_add' hT (by norm_num)]; simp
        have : θ ^ θ * T ^ θ * ((1 - θ) ^ (1 - θ) * T ^ (1 - θ)) = θ ^ θ * (1-θ) ^ (1-θ) * T := by
          linear_combination (θ ^ θ * (1 - θ) ^ (1 - θ)) * this
        linarith
      obtain ⟨hR0, hc0, hpow, hd1, hd2, hmax, huniq, hexcl, -, -, -⟩ := h
      obtain ⟨hsim, hnot⟩ := hx
      have hsim' := hsim
      obtain ⟨⟨hbo, hexo⟩, hbarg⟩ := hsim'
      have hexcl0 : ∀ i, exclusiveProfit M i 0 = 0 := by
        intro i; fin_cases i <;> simp [exclusiveProfit, exclusiveQuantity, chainProfit, hR0, hc0]
      have hEx : ∀ i q, M.revenue (exclusiveQuantity i q) - M.cost i q = exclusiveProfit M i q := by
        intro i q; fin_cases i <;> simp [exclusiveProfit, chainProfit, exclusiveQuantity, hc0]
      set PI := chainProfit M b.dual with hPI
      set B : Fin 2 → ℝ := fun i => (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).buyer with hB
      set P : Fin 2 → ℝ := fun i => exclusiveProfit M i (b.exclusive i) with hP
      have hP0 : ∀ i, 0 ≤ P i := by
        intro i; have := (hexcl i).2 0 le_rfl; rw [hexcl0] at this; exact this
      have hB0 : ∀ i, 0 ≤ B i := by
        intro i
        have := (hexo i).1.2.2 .none (Or.inl rfl) trivial
        simpa [outcomePayoff, B, exclusivePayoff] using this
      have hBP : ∀ i, B i ≤ P i := by
        intro i
        obtain ⟨⟨hs, hav, -⟩, hsup⟩ := hexo i
        rcases hs with hs | ⟨q, hs⟩
        · simp [B, hs, exclusivePayoff, outcomePayoff]; exact hP0 i
        · simp only [hs, Available] at hav
          have h1 := (hexcl i).2 q hav.1.le
          simp only [B, hs, exclusivePayoff, outcomePayoff, if_true] at hsup ⊢
          have := hEx i q
          simp only [P]; linarith
      set π := (x.payoff M).supplier with hπ
      set W := (x.payoff M).buyer + π 0 + π 1 with hW
      have hK : W = chainProfit M (sourcingQuantity x.order) ∧ sourcingQuantity x.order ∈ quadrant ∧
          (∀ i, 0 ≤ π i) ∧ ∀ i, π i = M.power i * (W - π (other i) - B (other i)) := by
        have hpx : x.payoff M = outcomePayoff M x.contracts x.order := rfl
        have hexeq : ∀ (p p' : Payment) i s, p'.exclusive = p.exclusive → (s = .none ∨ ∃ q, s = .single i q) →
            exclusivePayoff M (some p') i s = exclusivePayoff M (some p) i s := by
          rintro p p' i s he (rfl | ⟨q, rfl⟩) <;> simp [exclusivePayoff, outcomePayoff, exclusiveTransfer, he]
        have hexo' : ∀ (p p' : Payment) i s, p'.exclusive = p.exclusive → IsExclusiveOrder M (some p) i s →
            IsExclusiveOrder M (some p') i s := by
          rintro p p' i s he ⟨hs, hav, hopt⟩
          refine ⟨hs, ?_, fun r hr hav' => ?_⟩
          · rcases hs with rfl | ⟨q, rfl⟩
            · trivial
            · simpa [Available] using hav
          · have e1 := hexeq p p' i r he hr
            have e2 := hexeq p p' i s he hs
            unfold exclusivePayoff at e1 e2
            rw [e1, e2]
            apply hopt r hr
            rcases hr with rfl | ⟨q, rfl⟩
            · trivial
            · simpa [Available] using hav'
        rcases hord : x.order with _ | q | ⟨k, q⟩
        · have hBz : ∀ i, B i = 0 := by
            intro i
            refine le_antisymm ?_ (hB0 i)
            obtain ⟨⟨hs, hav, -⟩, -⟩ := hexo i
            have := hbo.2 (x.exclusiveOrder i)
            rcases hs with hs | ⟨q', hs⟩
            · simp [B, hs, exclusivePayoff, outcomePayoff]
            · rw [hs] at hav this; simp only [Available, if_true] at hav
              have := this ⟨hav.1, hav.2⟩
              rw [hord] at this
              simpa [B, hs, exclusivePayoff, outcomePayoff] using this
          have hπz : ∀ i, π i = 0 := by intro i; simp [hπ, hpx, hord, outcomePayoff]
          have hWz : W = 0 := by simp [hW, hπz, hpx, hord, outcomePayoff]
          refine ⟨by rw [hWz]; simp [sourcingQuantity, chainProfit, hR0, hc0], by simp [sourcingQuantity, quadrant],
            fun i => by rw [hπz], fun i => by rw [hπz, hπz, hBz, hWz]; ring⟩
        · have hav := hbo.1
          rw [hord] at hav
          obtain ⟨hq1, hq2, hs0, hs1⟩ := hav
          have hxfun : ∀ i, (fun k => if k = i then x.contracts i else x.contracts (other i)) = x.contracts := by
            intro i; funext k; fin_cases i <;> fin_cases k <;> simp [other]
          have hbuy : (x.payoff M).buyer = (outcomePayoff M x.contracts (.dual q)).buyer := by rw [hpx, hord]
          have hπd : ∀ i, π i = (outcomePayoff M x.contracts (.dual q)).supplier i := by
            intro i; rw [hπ, hpx, hord]
          have hWq : W = chainProfit M q := by
            rw [hW, hbuy, hπd, hπd]; simp [outcomePayoff, chainProfit]; ring
          have hb : ∀ i, IsDualBargain M i (x.contracts (other i)) (x.contracts i) q (B (other i)) := by
            intro i; have := hbarg i; rw [hord] at this; exact this
          have hnn : ∀ i, 0 ≤ π i := by
            intro i; have := (hb i).1.2.2.1; rw [hxfun i] at this; rw [hπd]; exact this
          refine ⟨hWq, ⟨hq1.le, hq2.le⟩, hnn, fun i => ?_⟩
          have hsome : (x.contracts i).isSome := by fin_cases i <;> assumption
          obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsome
          set T := π i + (x.payoff M).buyer - B (other i) with hT
          set α := M.power i * T - π i with hα
          let d' : Contract := some ⟨fun r => p.normal r + α, p.exclusive⟩
          have hshift : ∀ r : ℝ × ℝ,
              (outcomePayoff M (fun k => if k = i then d' else x.contracts (other i)) (.dual r)).buyer =
                (outcomePayoff M x.contracts (.dual r)).buyer - α ∧
              (outcomePayoff M (fun k => if k = i then d' else x.contracts (other i)) (.dual r)).supplier i =
                (outcomePayoff M x.contracts (.dual r)).supplier i + α := by
            intro r
            fin_cases i <;> simp [outcomePayoff, normalTransfer, other, d', hp] at hp ⊢ <;> ring_nf <;> simp
          have hcand := (hb i).1
          unfold DualCandidate at hcand
          rw [hxfun i] at hcand
          obtain ⟨⟨s, hsx, hss⟩, ⟨-, hopt⟩, hsup, hbD⟩ := hcand
          have hsx' := hsx
          rw [hp] at hsx'
          have hT0 : 0 ≤ T := by
            have : π i = (outcomePayoff M x.contracts (.dual q)).supplier i := hπd i
            rw [hT, hbuy]; linarith
          have hc : DualCandidate M i (x.contracts (other i)) d' q (B (other i)) := by
            refine ⟨⟨s, hexo' p _ i s rfl hsx', ?_⟩, ⟨?_, fun r hr => ?_⟩, ?_, ?_⟩
            · show 0 ≤ (exclusivePayoff M (some ⟨fun r => p.normal r + α, p.exclusive⟩) i s).supplier i
              have e := hexeq p ⟨fun r => p.normal r + α, p.exclusive⟩ i s rfl hsx'.1
              rw [hp] at hss; rw [e]; exact hss
            · refine ⟨hq1, hq2, ?_, ?_⟩ <;> fin_cases i <;> simp [d', other, hs0, hs1]
            · rw [(hshift r).1, (hshift q).1]
              have hr' : Available x.contracts (.dual r) := ⟨hr.1, hr.2.1, hs0, hs1⟩
              linarith [hopt r hr']
            · rw [(hshift q).2, ← hπd, hα]
              have := (hpow i).1; nlinarith
            · rw [(hshift q).1, ← hbuy, hα]
              have h1 : M.power i * T ≤ T := by nlinarith [(hpow i).2]
              rw [hT] at h1 ⊢; linarith
          have hle := (hb i).2 d' q hc
          rw [(hshift q).1, (hshift q).2, hxfun i, ← hπd, ← hbuy] at hle
          have hfin := H2 (M.power i) T (π i) (hpow i).1 (hpow i).2 (hnn i) (by rw [hT]; linarith) (by
            convert hle using 2 <;> first | ring | (rw [hα]; ring))
          rw [hfin, hT, hW]; ring_nf
          fin_cases i <;> simp [other] <;> ring
        · have hav := hbo.1
          rw [hord] at hav
          obtain ⟨hq, hsk⟩ := hav
          obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsk
          have hb : IsSingleBargain M k (x.contracts k) (.single k q) (B (other k)) := by
            have := hbarg k; rw [hord] at this; simpa using this
          have hbuy : (x.payoff M).buyer = M.revenue (exclusiveQuantity k q) - p.exclusive q := by
            rw [hpx, hord]; simp [outcomePayoff, hp, exclusiveTransfer]
          have hπk : π k = p.exclusive q - M.cost k q := by
            rw [hπ, hpx, hord]; simp [outcomePayoff, hp, exclusiveTransfer]
          have hπo : ∀ j, j ≠ k → π j = 0 := by
            intro j hj; rw [hπ, hpx, hord]; simp [outcomePayoff, hj]
          have hok : other k ≠ k := (by decide : ∀ k : Fin 2, other k ≠ k) k
          have hoo : ∀ j, j ≠ k → other j = k := fun j hj => (by decide : ∀ j k : Fin 2, j ≠ k → other j = k) j k hj
          have hsum2 : ∀ (k : Fin 2) (f : Fin 2 → ℝ), (∀ j, j ≠ k → f j = 0) → f 0 + f 1 = f k := by
            intro k f hf; fin_cases k
            · simp [hf 1 (by decide)]
            · simp [hf 0 (by decide)]
          have hWk : W = π k + (x.payoff M).buyer := by
            rw [hW, add_assoc, hsum2 k π hπo]; ring
          have hWq : W = exclusiveProfit M k q := by
            rw [hWk, hπk, hbuy, ← hEx]; ring
          obtain ⟨⟨hadm, ⟨hs1, hs2, hsopt⟩, hsup, hD⟩, hopt⟩ := hb
          have hbuyx : (x.payoff M).buyer = (exclusivePayoff M (x.contracts k) k (.single k q)).buyer := by
            rw [hbuy]; simp [exclusivePayoff, outcomePayoff, hp, exclusiveTransfer]
          have hBk : B k = (x.payoff M).buyer := by
            apply le_antisymm
            · rw [hbuyx]; exact hsopt _ (hexo k).1.1 (hexo k).1.2.1
            · rw [hbuyx]; exact (hexo k).1.2.2 _ (Or.inr ⟨q, rfl⟩) hs2
          have hπkn : 0 ≤ π k := by
            rw [hπk]; simpa [exclusivePayoff, outcomePayoff, hp, exclusiveTransfer] using hsup
          refine ⟨by rw [hWq]; rfl, ?_, ?_, ?_⟩
          · have hq2 : ∀ (k : Fin 2) (q : ℝ), 0 ≤ q → exclusiveQuantity k q ∈ quadrant := by
              intro k q hq; fin_cases k <;> simp [exclusiveQuantity, quadrant, hq]
            exact hq2 k q hq.le
          · intro j; by_cases hj : j = k
            · rw [hj]; exact hπkn
            · rw [hπo j hj]
          · intro j
            by_cases hj : j = k
            swap
            · rw [hπo j hj, hoo j hj, hBk, hWk]; ring
            subst hj
            rw [hπo (other j) hok]
            set T := π j + (x.payoff M).buyer - B (other j) with hT
            set α := M.power j * T - π j with hα
            let d' : Contract := some ⟨p.normal, fun r => p.exclusive r + α⟩
            have hpay' : ∀ r, (exclusivePayoff M d' j (.single j r)).buyer =
                (exclusivePayoff M (x.contracts j) j (.single j r)).buyer - α ∧
                (exclusivePayoff M d' j (.single j r)).supplier j =
                (exclusivePayoff M (x.contracts j) j (.single j r)).supplier j + α := by
              intro r; simp [exclusivePayoff, outcomePayoff, hp, exclusiveTransfer, d']; constructor <;> ring
            have hbD : B (other j) ≤ (x.payoff M).buyer := by rw [hbuyx]; exact hD
            have hT0 : 0 ≤ T := by rw [hT]; linarith
            have hαle : α ≤ (x.payoff M).buyer - B (other j) := by
              have := mul_le_of_le_one_left hT0 (hpow j).2.le
              rw [hα]; rw [hT] at this ⊢; linarith
            have hex' : IsExclusiveOrder M d' j (.single j q) := by
              refine ⟨Or.inr ⟨q, rfl⟩, ⟨hq, by simp [d']⟩, ?_⟩
              rintro r (rfl | ⟨r', rfl⟩) hr
              · show (exclusivePayoff M d' j .none).buyer ≤ (exclusivePayoff M d' j (.single j q)).buyer
                rw [(hpay' q).1, ← hbuyx]
                simp only [exclusivePayoff, outcomePayoff]; linarith [hB0 (other j)]
              · show (exclusivePayoff M d' j (.single j r')).buyer ≤ (exclusivePayoff M d' j (.single j q)).buyer
                rw [(hpay' q).1, (hpay' r').1]
                have : Available (fun i => if i = j then x.contracts j else none) (.single j r') := by
                  simp only [Available] at hr ⊢; refine ⟨hr.1, ?_⟩; simp [hp]
                have h' : (exclusivePayoff M (x.contracts j) j (.single j r')).buyer ≤
                    (exclusivePayoff M (x.contracts j) j (.single j q)).buyer := hsopt _ (Or.inr ⟨r', rfl⟩) this
                linarith
            have hsup' : 0 ≤ (exclusivePayoff M d' j (.single j q)).supplier j := by
              rw [(hpay' q).2]
              have e : (exclusivePayoff M (x.contracts j) j (.single j q)).supplier j = π j := by
                rw [hπk]; simp [exclusivePayoff, outcomePayoff, hp, exclusiveTransfer]
              rw [e, hα]; have := mul_nonneg (hpow j).1.le hT0; linarith
            have hc : SingleCandidate M j d' (.single j q) (B (other j)) :=
              ⟨⟨_, hex', hsup'⟩, hex', hsup', by rw [(hpay' q).1, ← hbuyx]; linarith⟩
            have hle := hopt d' (.single j q) hc
            have e : (exclusivePayoff M (x.contracts j) j (.single j q)).supplier j = π j := by
              rw [hπk]; simp [exclusivePayoff, outcomePayoff, hp, exclusiveTransfer]
            rw [(hpay' q).1, (hpay' q).2, e, ← hbuyx] at hle
            have hfin := H2 (M.power j) T (π j) (hpow j).1 (hpow j).2 hπkn (by rw [hT]; linarith) (by
              convert hle using 2 <;> first | ring | (rw [hα]; ring))
            rw [hfin, hT, hWk]; ring
      by_contra hnc
      have hWlt : W < PI := by
        have h1 := hmax _ hK.2.1
        rw [← hK.1] at h1
        rcases h1.lt_or_eq with h1 | h1
        · exact h1
        · exact (hnc (by unfold IsCoordinated; rw [← hK.1]; exact h1)).elim
      obtain ⟨-, -, hπ0, hπ⟩ := hK
      have t0 := hpow 0
      have t1 := hpow 1
      have hden : 0 < 1 - M.power 0 * M.power 1 := by nlinarith
      set a : Fin 2 → ℝ := ![M.power 0 * ((1 - M.power 1) * PI - B 1 + M.power 1 * B 0) / (1 - M.power 0 * M.power 1),
        M.power 1 * ((1 - M.power 0) * PI - B 0 + M.power 0 * B 1) / (1 - M.power 0 * M.power 1)] with ha
      have e0 : a 0 * (1 - M.power 0 * M.power 1) = M.power 0 * ((1 - M.power 1) * PI - B 1 + M.power 1 * B 0) := by
        simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one]; exact div_mul_cancel₀ _ hden.ne'
      have e1 : a 1 * (1 - M.power 0 * M.power 1) = M.power 1 * ((1 - M.power 0) * PI - B 0 + M.power 0 * B 1) := by
        simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one]; exact div_mul_cancel₀ _ hden.ne'
      have ha0 : a 0 = M.power 0 * (PI - a 1 - B 1) := by
        apply mul_right_cancel₀ hden.ne'; linear_combination e0 + M.power 0 * e1
      have ha1 : a 1 = M.power 1 * (PI - a 0 - B 0) := by
        apply mul_right_cancel₀ hden.ne'; linear_combination e1 + M.power 1 * e0
      have hx0 : π 0 = M.power 0 * (W - π 1 - B 1) := hπ 0
      have hx1 : π 1 = M.power 1 * (W - π 0 - B 0) := hπ 1
      have hd0 : (a 0 - π 0) * (1 - M.power 0 * M.power 1) = M.power 0 * (1 - M.power 1) * (PI - W) := by
        linear_combination ha0 - hx0 - M.power 0 * (ha1 - hx1)
      have hd1' : (a 1 - π 1) * (1 - M.power 0 * M.power 1) = M.power 1 * (1 - M.power 0) * (PI - W) := by
        linear_combination ha1 - hx1 - M.power 1 * (ha0 - hx0)
      have hdB : ((PI - a 0 - a 1) - (W - π 0 - π 1)) * (1 - M.power 0 * M.power 1) =
          (1 - M.power 0) * (1 - M.power 1) * (PI - W) := by
        linear_combination (-1 : ℝ) * hd0 - hd1'
      have hΔ : 0 < PI - W := by linarith
      have hlt0 : π 0 < a 0 := by
        have : 0 < (a 0 - π 0) * (1 - M.power 0 * M.power 1) := by
          rw [hd0]; apply mul_pos (mul_pos t0.1 (by linarith)) hΔ
        have := (pos_iff_pos_of_mul_pos this).2 hden
        linarith
      have hlt1 : π 1 < a 1 := by
        have : 0 < (a 1 - π 1) * (1 - M.power 0 * M.power 1) := by
          rw [hd1']; apply mul_pos (mul_pos t1.1 (by linarith)) hΔ
        have := (pos_iff_pos_of_mul_pos this).2 hden
        linarith
      have hltB : W - π 0 - π 1 < PI - a 0 - a 1 := by
        have : 0 < ((PI - a 0 - a 1) - (W - π 0 - π 1)) * (1 - M.power 0 * M.power 1) := by
          rw [hdB]; apply mul_pos (mul_pos (by linarith) (by linarith)) hΔ
        have := (pos_iff_pos_of_mul_pos this).2 hden
        linarith
      have hapos : ∀ i, 0 < a i := by
        intro i; fin_cases i
        · exact lt_of_le_of_lt (hπ0 0) hlt0
        · exact lt_of_le_of_lt (hπ0 1) hlt1
      have hS0 : a 0 = M.power 0 * (PI - a 1 - B 1) := ha0
      have hYB : ∀ i, B i ≤ PI - a 0 - a 1 := by
        intro i; fin_cases i
        · show B 0 ≤ _
          have hS1 : 0 < PI - a 0 - B 0 :=
            (pos_iff_pos_of_mul_pos (ha1 ▸ hapos 1 : 0 < M.power 1 * (PI - a 0 - B 0))).1 t1.1
          have := mul_pos (sub_pos.2 t1.2) hS1
          linear_combination (exp := 1) this + ha1
        · show B 1 ≤ _
          have hS0 : 0 < PI - a 1 - B 1 :=
            (pos_iff_pos_of_mul_pos (ha0 ▸ hapos 0 : 0 < M.power 0 * (PI - a 1 - B 1))).1 t0.1
          have := mul_pos (sub_pos.2 t0.2) hS0
          linear_combination (exp := 1) this + ha0
      let e : Fin 2 → ℝ := fun i => P i - B i
      have he0 : ∀ i, 0 ≤ e i := fun i => by simp only [e]; linarith [hBP i]
      let yc : Contracts := fun i => some ⟨fun r => M.cost i r + a i, fun r => M.cost i r + e i⟩
      let ys : Fin 2 → Sourcing := fun i => if 0 < b.exclusive i then .single i (b.exclusive i) else .none
      have hyex : ∀ i, IsExclusiveOrder M (yc i) i (ys i) ∧
          (exclusivePayoff M (yc i) i (ys i)).buyer = B i ∧
          (exclusivePayoff M (yc i) i (ys i)).supplier i = e i := by
        intro i
        by_cases hpos : 0 < b.exclusive i
        · have hys : ys i = .single i (b.exclusive i) := by simp [ys, hpos]
          rw [hys]
          have hval : (exclusivePayoff M (yc i) i (.single i (b.exclusive i))).buyer = B i := by
            simp only [exclusivePayoff, outcomePayoff, if_true, yc, exclusiveTransfer]
            have := hEx i (b.exclusive i); simp only [e, P] at this ⊢; linarith
          refine ⟨⟨Or.inr ⟨_, rfl⟩, ⟨hpos, by simp [yc]⟩, ?_⟩, hval, ?_⟩
          · rintro r (rfl | ⟨q, rfl⟩) hr
            · rw [show (exclusivePayoff M (yc i) i (.single i (b.exclusive i))).buyer =
                (outcomePayoff M (fun j => if j = i then yc i else none) (.single i (b.exclusive i))).buyer from rfl] at hval
              rw [hval]; simpa [outcomePayoff] using hB0 i
            · simp only [Available] at hr
              have h1 := (hexcl i).2 q hr.1.le
              have h2 := hEx i q
              change _ ≤ (exclusivePayoff M (yc i) i (.single i (b.exclusive i))).buyer
              rw [hval]
              simp only [outcomePayoff, if_true, yc, exclusiveTransfer]
              simp only [e, P] at h1 ⊢; linarith
          · simp [exclusivePayoff, outcomePayoff, yc, exclusiveTransfer]
        · have hb0 : b.exclusive i = 0 := le_antisymm (not_lt.1 hpos) (hexcl i).1
          have hP0' : P i = 0 := by simp only [P, hb0, hexcl0]
          have hBi : B i = 0 := le_antisymm (hP0' ▸ hBP i) (hB0 i)
          have hys : ys i = .none := by simp [ys, hpos]
          rw [hys]
          refine ⟨⟨Or.inl rfl, trivial, ?_⟩, ?_, ?_⟩
          · rintro r (rfl | ⟨q, rfl⟩) hr
            · exact le_rfl
            · simp only [Available] at hr
              have h1 := (hexcl i).2 q hr.1.le
              have h2 := hEx i q
              simp only [outcomePayoff, if_true, yc, exclusiveTransfer]
              simp only [e, P] at h1 hP0' ⊢; rw [hBi]; linarith
          · simp [exclusivePayoff, outcomePayoff, hBi]
          · simp [exclusivePayoff, outcomePayoff, e, hP0', hBi]
      have hyself : ∀ i, (fun k => if k = i then yc i else yc (other i)) = yc := by
        intro i; funext k; fin_cases i <;> fin_cases k <;> simp [other]
      have hsum : ∀ i (d : Contract) (q : ℝ × ℝ),
          (outcomePayoff M (fun k => if k = i then d else yc (other i)) (.dual q)).buyer +
          (outcomePayoff M (fun k => if k = i then d else yc (other i)) (.dual q)).supplier i =
            chainProfit M q - a (other i) := by
        intro i d q; fin_cases i <;> simp [outcomePayoff, other, yc, normalTransfer, chainProfit] <;> ring
      have hypay : (outcomePayoff M yc (.dual b.dual)).buyer = PI - a 0 - a 1 ∧
          ∀ i, (outcomePayoff M yc (.dual b.dual)).supplier i = a i := by
        refine ⟨?_, ?_⟩
        · simp [outcomePayoff, yc, normalTransfer, PI, chainProfit]; ring
        · intro i; fin_cases i <;> simp [outcomePayoff, yc, normalTransfer]
      have hyorder : IsBuyerOrder M yc (.dual b.dual) := by
        refine ⟨⟨hd1, hd2, by simp [yc], by simp [yc]⟩, ?_⟩
        rw [hypay.1]
        rintro (_ | r | ⟨i, q⟩) hr
        · simpa [outcomePayoff] using (hB0 0).trans (hYB 0)
        · simp only [Available] at hr
          have := hmax r ⟨hr.1.le, hr.2.1.le⟩
          simp only [outcomePayoff, yc, normalTransfer]
          simp only [chainProfit] at this; linarith
        · simp only [Available] at hr
          have h1 := (hexcl i).2 q hr.1.le
          have h2 := hEx i q
          simp only [outcomePayoff, yc, exclusiveTransfer]
          have := hYB i
          simp only [e, P] at h1 ⊢; linarith
      apply hnot
      refine ⟨⟨yc, .dual b.dual, ys⟩, ⟨⟨hyorder, fun i => ⟨(hyex i).1, (hyex i).2.2 ▸ he0 i⟩⟩, ?_⟩, ?_⟩
      · intro i
        show IsDualBargain M i (yc (other i)) (yc i) b.dual
          (exclusivePayoff M (yc (other i)) (other i) (ys (other i))).buyer
        rw [(hyex (other i)).2.1]
        unfold IsDualBargain DualCandidate
        rw [hyself i]
        have hSi : a i = M.power i * (PI - a (other i) - B (other i)) ∧
            PI - a 0 - a 1 - B (other i) = (1 - M.power i) * (PI - a (other i) - B (other i)) := by
          fin_cases i
          · exact ⟨ha0, by simp [other]; linear_combination (-1:ℝ) * ha0⟩
          · exact ⟨ha1, by simp [other]; linear_combination (-1:ℝ) * ha1⟩
        refine ⟨⟨⟨ys i, (hyex i).1, (hyex i).2.2 ▸ he0 i⟩, ⟨hyorder.1, fun r hr => hyorder.2 _ hr⟩,
          by rw [hypay.2]; exact (hapos i).le, by rw [hypay.1]; exact hYB _⟩, ?_⟩
        intro d' q' hc
        rw [hypay.1, hypay.2, hSi.1, hSi.2]
        obtain ⟨-, ⟨⟨hq1, hq2, -, -⟩, -⟩, hu, hv⟩ := hc
        have := hsum i d' q'
        have hm := hmax q' ⟨hq1.le, hq2.le⟩
        apply H1 _ _ _ _ (hpow i).1 (hpow i).2 hu (by linarith)
        linarith
      · have hpy : ContractOutcome.payoff M ⟨yc, .dual b.dual, ys⟩ = outcomePayoff M yc (.dual b.dual) := rfl
        rw [hpy]
        have hxb : (ContractOutcome.payoff M x).buyer = W - π 0 - π 1 := by simp only [hW]; ring
        refine ⟨⟨by rw [hypay.1, hxb]; exact hltB.le, fun i => ?_⟩, Or.inl (by rw [hypay.1, hxb]; exact hltB)⟩
        rw [hypay.2]
        change π i ≤ a i
        fin_cases i
        · exact hlt0.le
        · exact hlt1.le
