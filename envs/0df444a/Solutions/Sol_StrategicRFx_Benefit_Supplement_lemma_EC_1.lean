-- Prove2me | solution 1 for StrategicRFx.Benefit.Supplement.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:16.475556+00:00
-- url     : https://prove2.me/submissions/ae8f3d49-d1c5-42bd-b732-0fc0ca825c60

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous

open StrategicRFx
open StrategicRFx.Benefit
open StrategicRFx.Benefit.Supplement

theorem solution (M : Technology) (b : FirstBest) (h : TechnologyAssumptions M b) :
    (∀ x, IsSimultaneous M x → (∃ i q, x.order = .single i q) →
      ∃ y, IsSimultaneous M y ∧ (∃ q, y.order = .dual q) ∧
        StrictlyImproves (y.payoff M) (x.payoff M)) ∧
    (∀ x, IsSimultaneous M x → (∃ q, x.order = .dual q) →
      ∃ y, IsSimultaneous M y ∧ IsCoordinated M b y.order ∧
        (∀ i, IsCostPlus M i (y.contracts i)) ∧ WeaklyImproves (y.payoff M) (x.payoff M)) := by
          have nash_eq : ∀ θ s u : ℝ, 0 < θ → θ < 1 → 0 ≤ s → 0 ≤ u →
              nashProduct θ s u = (θ ^ θ * (1 - θ) ^ (1 - θ)) * ((s / θ) ^ θ * (u / (1 - θ)) ^ (1 - θ)) := by
            intro θ s u h0 h1 hs hu
            have h1' : 0 < 1 - θ := by linarith
            unfold nashProduct
            have e1 : s = θ * (s / θ) := by field_simp
            have e2 : u = (1 - θ) * (u / (1 - θ)) := by field_simp
            conv_lhs => rw [e1, e2]
            rw [Real.mul_rpow h0.le (div_nonneg hs h0.le), Real.mul_rpow h1'.le (div_nonneg hu h1'.le)]
            ring
          have nash_opt : ∀ θ T : ℝ, 0 < θ → θ < 1 → 0 ≤ T →
              nashProduct θ (θ * T) ((1 - θ) * T) = (θ ^ θ * (1 - θ) ^ (1 - θ)) * T := by
            intro θ T h0 h1 hT
            have h1' : 0 < 1 - θ := by linarith
            rw [nash_eq θ _ _ h0 h1 (by positivity) (by nlinarith)]
            congr 1
            rw [show θ * T / θ = T by field_simp, show (1 - θ) * T / (1 - θ) = T by field_simp]
            rw [← Real.rpow_add' hT (by norm_num)]
            simp
          have amgm_le : ∀ θ s u T : ℝ, 0 < θ → θ < 1 → 0 ≤ s → 0 ≤ u → s + u ≤ T →
              nashProduct θ s u ≤ nashProduct θ (θ * T) ((1 - θ) * T) := by
            intro θ s u T h0 h1 hs hu hT
            have h1' : 0 < 1 - θ := by linarith
            rw [nash_eq θ s u h0 h1 hs hu, nash_opt θ T h0 h1 (by linarith)]
            have hK : 0 ≤ θ ^ θ * (1 - θ) ^ (1 - θ) := by positivity
            apply mul_le_mul_of_nonneg_left _ hK
            have := Real.geom_mean_le_arith_mean2_weighted h0.le h1'.le (div_nonneg hs h0.le)
              (div_nonneg hu h1'.le) (by ring)
            have e : θ * (s / θ) + (1 - θ) * (u / (1 - θ)) = s + u := by field_simp
            linarith
          have amgm_lt : ∀ θ s u : ℝ, 0 < θ → θ < 1 → 0 ≤ s → 0 ≤ u → s ≠ θ * (s + u) →
              nashProduct θ s u < nashProduct θ (θ * (s + u)) ((1 - θ) * (s + u)) := by
            intro θ s u h0 h1 hs hu hne
            have h1' : 0 < 1 - θ := by linarith
            rw [nash_eq θ s u h0 h1 hs hu, nash_opt θ (s + u) h0 h1 (by linarith)]
            have hK : 0 < θ ^ θ * (1 - θ) ^ (1 - θ) := by positivity
            apply mul_lt_mul_of_pos_left _ hK
            have := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
              ![θ, 1 - θ] ![s / θ, u / (1 - θ)] (by intro i _; fin_cases i <;> simp [h0, h1'])
              (by simp [Fin.sum_univ_two])
              (by intro i _; fin_cases i <;> simp [div_nonneg hs h0.le, div_nonneg hu h1'.le])).2 (by
                refine ⟨0, by simp, 1, by simp, ?_⟩
                simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
                intro heq
                apply hne
                field_simp at heq
                linarith)
            simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons] at this
            have e : θ * (s / θ) + (1 - θ) * (u / (1 - θ)) = s + u := by field_simp
            linarith
          obtain ⟨hR0, hC0, hθ, hb1, hb2, hmax, huniq, hex, -, -, -⟩ := h
          have hoth : ∀ i : Fin 2, other (other i) = i := by intro i; fin_cases i <;> rfl
          have hne2 : ∀ k i : Fin 2, k ≠ i → k = other i := by decide
          have hexq0 : ∀ k : Fin 2, exclusiveProfit M k 0 = 0 := by
            intro k; fin_cases k <;> simp [exclusiveProfit, exclusiveQuantity, chainProfit, hR0, hC0]
          have hP0 : ∀ k, 0 ≤ exclusiveProfit M k (b.exclusive k) := by
            intro k; have := (hex k).2 0 le_rfl; rw [hexq0] at this; exact this
          have hexcl : ∀ (k : Fin 2) q, exclusiveProfit M k q =
              M.revenue (exclusiveQuantity k q) - M.cost k q := by
            intro k q; fin_cases k <;> simp [exclusiveProfit, exclusiveQuantity, chainProfit, hC0]
          have hquad : ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 → chainProfit M q ≤ chainProfit M b.dual := by
            intro q h1 h2; exact hmax q ⟨h1.le, h2.le⟩
          have hPlt : ∀ k, exclusiveProfit M k (b.exclusive k) < chainProfit M b.dual := by
            intro k
            have hq : exclusiveQuantity k (b.exclusive k) ∈ quadrant := by
              fin_cases k <;> simp [exclusiveQuantity, quadrant, (hex _).1]
            have hle := hmax _ hq
            rcases hle.lt_or_eq with hlt | heq
            · exact hlt
            · exfalso
              have := huniq _ hq heq
              fin_cases k <;> simp [exclusiveQuantity] at this
              · have := congrArg Prod.snd this; simp at this; linarith
              · have := congrArg Prod.fst this; simp at this; linarith
          -- payoff of an exclusive outcome
          have hexpay_single : ∀ (c : Contract) (k : Fin 2) q,
              (exclusivePayoff M c k (.single k q)).buyer = M.revenue (exclusiveQuantity k q) - exclusiveTransfer c q ∧
              (exclusivePayoff M c k (.single k q)).supplier k = exclusiveTransfer c q - M.cost k q := by
            intro c k q; simp [exclusivePayoff, outcomePayoff]
          have hexpay_none : ∀ (c : Contract) (k : Fin 2),
              (exclusivePayoff M c k .none).buyer = 0 ∧ (exclusivePayoff M c k .none).supplier k = 0 := by
            intro c k; simp [exclusivePayoff, outcomePayoff]
          -- bounds on an exclusive buyer payoff
          have hEbd : ∀ (c : Contract) k s, IsExclusiveOrder M c k s →
              0 ≤ (exclusivePayoff M c k s).supplier k →
              0 ≤ (exclusivePayoff M c k s).buyer ∧
                (exclusivePayoff M c k s).buyer ≤ exclusiveProfit M k (b.exclusive k) := by
            intro c k s hs hsup
            refine ⟨?_, ?_⟩
            · have := hs.2.2 .none (Or.inl rfl) trivial
              simpa [exclusivePayoff, outcomePayoff] using this
            · rcases hs.1 with rfl | ⟨q, rfl⟩
              · rw [(hexpay_none c k).1]; exact hP0 k
              · have hav := hs.2.1
                simp [Available] at hav
                obtain ⟨h1, h2⟩ := hexpay_single c k q
                rw [h2] at hsup; rw [h1]
                have := (hex k).2 q hav.1.le
                rw [hexcl] at this
                linarith
          have verify : ∀ (a E : Fin 2 → ℝ), (∀ i, 0 ≤ a i) →
              (∀ k, 0 ≤ E k ∧ E k ≤ exclusiveProfit M k (b.exclusive k)) →
              (∀ i, a i * (1 - M.power i) =
                M.power i * (chainProfit M b.dual - a 0 - a 1 - E (other i))) →
              ∃ y : ContractOutcome, IsSimultaneous M y ∧ y.order = .dual b.dual ∧
                (∀ i, IsCostPlus M i (y.contracts i)) ∧
                (y.payoff M).buyer = chainProfit M b.dual - a 0 - a 1 ∧
                ∀ i, (y.payoff M).supplier i = a i := by
            intro a E ha hE hrel
            set Pi := chainProfit M b.dual with hPi
            let ct : Contracts := fun i => some ⟨fun s => M.cost i s + a i,
              fun s => M.cost i s + (exclusiveProfit M i (b.exclusive i) - E i)⟩
            let eo : Fin 2 → Sourcing := fun k =>
              if 0 < b.exclusive k then .single k (b.exclusive k) else .none
            have hEle : ∀ k, E k ≤ Pi - a 0 - a 1 := by
              intro k
              have h1 := hrel (other k)
              rw [hoth] at h1
              have := hθ (other k)
              nlinarith [ha (other k)]
            -- exclusive facts
            have hexo : ∀ k, IsExclusiveOrder M (ct k) k (eo k) ∧
                (exclusivePayoff M (ct k) k (eo k)).buyer = E k ∧
                0 ≤ (exclusivePayoff M (ct k) k (eo k)).supplier k := by
              intro k
              have hbuy : ∀ q, (exclusivePayoff M (ct k) k (.single k q)).buyer =
                  exclusiveProfit M k q - (exclusiveProfit M k (b.exclusive k) - E k) := by
                intro q; rw [(hexpay_single _ k q).1, hexcl]; simp [ct, exclusiveTransfer]; ring
              have hsup : ∀ q, (exclusivePayoff M (ct k) k (.single k q)).supplier k =
                  exclusiveProfit M k (b.exclusive k) - E k := by
                intro q; rw [(hexpay_single _ k q).2]; simp [ct, exclusiveTransfer]
              by_cases hpos : 0 < b.exclusive k
              · have heo : eo k = .single k (b.exclusive k) := by simp [eo, hpos]
                rw [heo]
                refine ⟨⟨Or.inr ⟨_, rfl⟩, ?_, ?_⟩, ?_, ?_⟩
                · simp [Available, hpos, ct]
                · intro r hr _
                  rcases hr with rfl | ⟨q, rfl⟩
                  · rw [show (outcomePayoff M (fun j => if j = k then ct k else none) .none).buyer = 0 by
                      simp [outcomePayoff]]
                    have := hbuy (b.exclusive k)
                    simp only [exclusivePayoff] at this
                    rw [this]; linarith [hE k]
                  · rename_i hav
                    simp [Available] at hav
                    have h1 := hbuy q; have h2 := hbuy (b.exclusive k)
                    simp only [exclusivePayoff] at h1 h2
                    rw [h1, h2]
                    linarith [(hex k).2 q hav.1.le]
                · rw [hbuy]; ring
                · rw [hsup]; linarith [hE k]
              · have heo : eo k = .none := by simp [eo, hpos]
                have hb0 : b.exclusive k = 0 := le_antisymm (not_lt.1 hpos) (hex k).1
                have hPk : exclusiveProfit M k (b.exclusive k) = 0 := by rw [hb0, hexq0]
                have hEk : E k = 0 := le_antisymm (by linarith [hE k]) (hE k).1
                rw [heo]
                refine ⟨⟨Or.inl rfl, trivial, ?_⟩, ?_, ?_⟩
                · intro r hr hav
                  rcases hr with rfl | ⟨q, rfl⟩
                  · exact le_rfl
                  · simp [Available] at hav
                    have h1 := hbuy q
                    simp only [exclusivePayoff] at h1
                    rw [h1, show (outcomePayoff M (fun j => if j = k then ct k else none) .none).buyer = 0 by
                      simp [outcomePayoff]]
                    have := (hex k).2 q hav.1.le
                    rw [hPk] at this ⊢; rw [hEk]; linarith
                · rw [(hexpay_none _ k).1, hEk]
                · rw [(hexpay_none _ k).2]
            have hfun : ∀ i : Fin 2, (fun k => if k = i then ct i else ct (other i)) = ct := by
              intro i; funext k; fin_cases i <;> fin_cases k <;> simp [other]
            have hpay_b : (outcomePayoff M ct (.dual b.dual)).buyer = Pi - a 0 - a 1 := by
              simp [outcomePayoff, ct, normalTransfer, hPi, chainProfit]; ring
            have hpay_s : ∀ i, (outcomePayoff M ct (.dual b.dual)).supplier i = a i := by
              intro i; fin_cases i <;> simp [outcomePayoff, ct, normalTransfer]
            have hBO : IsBuyerOrder M ct (.dual b.dual) := by
              refine ⟨⟨hb1, hb2, by simp [ct], by simp [ct]⟩, ?_⟩
              intro r hr
              rw [hpay_b]
              cases r with
              | none =>
                simp [outcomePayoff]
                linarith [hEle 0, (hE 0).1]
              | dual q =>
                obtain ⟨h1, h2, -, -⟩ := hr
                have := hquad q h1 h2
                simp [outcomePayoff, ct, normalTransfer, chainProfit] at this ⊢
                linarith
              | single k q =>
                have hav : 0 < q := hr.1
                have := (hex k).2 q hav.le
                rw [hexcl] at this
                have hk := hEle k
                fin_cases k <;> simp [outcomePayoff, ct, exclusiveTransfer] at this hk ⊢ <;> linarith
            refine ⟨⟨ct, .dual b.dual, eo⟩, ⟨⟨hBO, fun i => ⟨(hexo i).1, (hexo i).2.2⟩⟩, fun i => ?_⟩,
              rfl, fun i => ⟨_, a i, _, rfl, fun q _ => rfl, fun q _ => rfl⟩, hpay_b, hpay_s⟩
            show IsDualBargain M i (ct (other i)) (ct i) b.dual
              (exclusivePayoff M (ct (other i)) (other i) (eo (other i))).buyer
            rw [(hexo (other i)).2.1]
            have hθi := hθ i
            have hreli := hrel i
            -- the sum identity for any candidate
            have hsum : ∀ (d : Contract) (q : ℝ × ℝ),
                (outcomePayoff M (fun k => if k = i then d else ct (other i)) (.dual q)).buyer +
                (outcomePayoff M (fun k => if k = i then d else ct (other i)) (.dual q)).supplier i =
                chainProfit M q - a (other i) := by
              intro d q
              fin_cases i <;> simp [outcomePayoff, ct, normalTransfer, other, chainProfit] <;> ring
            have hcand : DualCandidate M i (ct (other i)) (ct i) b.dual (E (other i)) := by
              rw [DualCandidate, hfun i]
              refine ⟨⟨eo i, (hexo i).1, (hexo i).2.2⟩, ⟨hBO.1, fun r hr => hBO.2 _ hr⟩, ?_, ?_⟩
              · rw [hpay_s]; exact ha i
              · rw [hpay_b]; exact hEle _
            refine ⟨hcand, fun d' q' hc' => ?_⟩
            rw [hfun i, hpay_s, hpay_b]
            obtain ⟨-, ⟨⟨hq1, hq2, -, -⟩, -⟩, hs', hb'⟩ := hc'
            have hs := hsum d' q'
            have hq := hquad q' hq1 hq2
            have key := amgm_le (M.power i) _ _ (Pi - a (other i) - E (other i)) hθi.1 hθi.2 hs'
              (sub_nonneg.2 hb') (by linarith)
            have e1 : M.power i * (Pi - a (other i) - E (other i)) = a i := by
              fin_cases i <;> simp [other] at hreli ⊢ <;> linarith
            have e2 : (1 - M.power i) * (Pi - a (other i) - E (other i)) = Pi - a 0 - a 1 - E (other i) := by
              fin_cases i <;> simp [other] at hreli ⊢ <;> linarith
            rw [e1, e2] at key
            exact key
          have combine : ∀ (B : ℝ) (S E : Fin 2 → ℝ), (∀ i, 0 ≤ S i) →
              (∀ k, 0 ≤ E k ∧ E k ≤ exclusiveProfit M k (b.exclusive k)) →
              (∀ i, S i * (1 - M.power i) = M.power i * (B - E (other i))) →
              B + S 0 + S 1 ≤ chainProfit M b.dual →
              ∃ y : ContractOutcome, IsSimultaneous M y ∧ y.order = .dual b.dual ∧
                (∀ i, IsCostPlus M i (y.contracts i)) ∧ B ≤ (y.payoff M).buyer ∧
                (∀ i, S i ≤ (y.payoff M).supplier i) ∧
                (B + S 0 + S 1 < chainProfit M b.dual → B < (y.payoff M).buyer) := by
            intro B S E hS hE hrel hsum
            set Pi := chainProfit M b.dual with hPi
            let r : Fin 2 → ℝ := fun i => M.power i / (1 - M.power i)
            have hr : ∀ i, 0 ≤ r i ∧ r i * (1 - M.power i) = M.power i := by
              intro i
              have := hθ i
              have h1 : (1 - M.power i) ≠ 0 := by linarith
              refine ⟨div_nonneg this.1.le (by linarith), ?_⟩
              simp only [r]; field_simp
            have hden : 0 < 1 + r 0 + r 1 := by linarith [(hr 0).1, (hr 1).1]
            set β := (Pi - B - S 0 - S 1) / (1 + r 0 + r 1) with hβ
            have hβ' : β * (1 + r 0 + r 1) = Pi - B - S 0 - S 1 := by
              rw [hβ]; field_simp
            have hβ0 : 0 ≤ β := div_nonneg (by linarith) hden.le
            let a : Fin 2 → ℝ := fun i => S i + r i * β
            have hPa : Pi - a 0 - a 1 = B + β := by simp only [a]; nlinarith
            obtain ⟨y, hy, hyo, hyc, hyb, hys⟩ := verify a E
              (fun i => add_nonneg (hS i) (mul_nonneg (hr i).1 hβ0)) hE (by
                intro i
                rw [hPa]
                have := hrel i
                have h2 := (hr i).2
                simp only [a]
                linear_combination this + β * h2)
            refine ⟨y, hy, hyo, hyc, ?_, ?_, ?_⟩
            · rw [hyb, hPa]; linarith
            · intro i; rw [hys]; simp only [a]; nlinarith [(hr i).1]
            · intro hlt
              rw [hyb, hPa]
              have : 0 < β := div_pos (by linarith) hden
              linarith
          have hfunc : ∀ (c : Contracts) (i : Fin 2), (fun k => if k = i then c i else c (other i)) = c := by
            intro c i; funext k; fin_cases i <;> fin_cases k <;> simp [other]
          have split_eq : ∀ (θ S u : ℝ), 0 < θ → θ < 1 → 0 ≤ S → 0 ≤ u →
              nashProduct θ (θ * (S + u)) ((1 - θ) * (S + u)) ≤ nashProduct θ S u →
              S * (1 - θ) = θ * u := by
            intro θ S u h0 h1 hS hu hle
            by_contra hne
            have : S ≠ θ * (S + u) := by intro h; apply hne; linarith
            have := amgm_lt θ S u h0 h1 hS hu this
            linarith
          have dualNash : ∀ (c : Contracts) (q : ℝ × ℝ) (i : Fin 2) (D : ℝ), IsDualOrder M c q →
              IsDualBargain M i (c (other i)) (c i) q D →
              (outcomePayoff M c (.dual q)).supplier i * (1 - M.power i) =
                M.power i * ((outcomePayoff M c (.dual q)).buyer - D) ∧
              0 ≤ (outcomePayoff M c (.dual q)).supplier i := by
            intro c q i D hDO ⟨hcand, hmx⟩
            rw [DualCandidate, hfunc] at hcand
            obtain ⟨hadm, -, hS, hD⟩ := hcand
            set S := (outcomePayoff M c (.dual q)).supplier i
            set B := (outcomePayoff M c (.dual q)).buyer
            have hsome : (c i).isSome := by
              have := hDO.1; fin_cases i
              · exact this.2.2.1
              · exact this.2.2.2
            obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hsome
            have hθi := hθ i
            set κ := M.power i * (S + (B - D)) - S with hκ
            let d' : Contract := some ⟨fun s => t.normal s + κ, t.exclusive⟩
            have hshift : ∀ r, (outcomePayoff M (fun k => if k = i then d' else c (other i)) (.dual r)).buyer =
                (outcomePayoff M c (.dual r)).buyer - κ ∧
                (outcomePayoff M (fun k => if k = i then d' else c (other i)) (.dual r)).supplier i =
                (outcomePayoff M c (.dual r)).supplier i + κ := by
              intro r
              obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
              all_goals simp [outcomePayoff, normalTransfer, ht, other, d']; constructor <;> ring
            have havail : ∀ r, Available (fun k => if k = i then d' else c (other i)) (.dual r) ↔
                Available c (.dual r) := by
              intro r
              obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
              all_goals simp [Available, ht, other, d']
            have hexsame : ∀ r, (r = .none ∨ ∃ q, r = .single i q) →
                outcomePayoff M (fun j => if j = i then d' else none) r =
                  outcomePayoff M (fun j => if j = i then c i else none) r ∧
                (Available (fun j => if j = i then d' else none) r ↔
                  Available (fun j => if j = i then c i else none) r) := by
              intro r hr
              rcases hr with rfl | ⟨q, rfl⟩
              · simp [outcomePayoff, Available]
              · simp [outcomePayoff, Available, exclusiveTransfer, ht, d']
            have hadm' : Admissible M d' i := by
              obtain ⟨s, ⟨hs1, hs2, hs3⟩, hsup⟩ := hadm
              refine ⟨s, ⟨hs1, (hexsame s hs1).2.2 hs2, fun r hr hav => ?_⟩, ?_⟩
              · rw [(hexsame r hr).1, (hexsame s hs1).1]
                exact hs3 r hr ((hexsame r hr).2.1 hav)
              · simp only [exclusivePayoff] at hsup ⊢
                rw [(hexsame s hs1).1]; exact hsup
            have hle := hmx d' q ⟨hadm', ⟨(havail q).2 hDO.1, fun r hr => by
                rw [(hshift r).1, (hshift q).1]
                linarith [hDO.2 r ((havail r).1 hr)]⟩, by
                rw [(hshift q).2]; nlinarith, by rw [(hshift q).1]; nlinarith⟩
            rw [hfunc, (hshift q).1, (hshift q).2] at hle
            have e1 : S + κ = M.power i * (S + (B - D)) := by rw [hκ]; ring
            have e2 : B - κ - D = (1 - M.power i) * (S + (B - D)) := by rw [hκ]; ring
            rw [e1, e2] at hle
            exact ⟨split_eq _ S (B - D) hθi.1 hθi.2 hS (by linarith) hle, hS⟩
          have singleNash : ∀ (c : Contract) (i : Fin 2) (q D : ℝ), 0 ≤ D →
              IsSingleBargain M i c (.single i q) D →
              (exclusivePayoff M c i (.single i q)).supplier i * (1 - M.power i) =
                M.power i * ((exclusivePayoff M c i (.single i q)).buyer - D) ∧
              0 ≤ (exclusivePayoff M c i (.single i q)).supplier i := by
            intro c i q D hD0 ⟨⟨hadm, hEO, hS, hD⟩, hmx⟩
            set S := (exclusivePayoff M c i (.single i q)).supplier i
            set B := (exclusivePayoff M c i (.single i q)).buyer
            have hav := hEO.2.1
            simp [Available] at hav
            obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hav.2
            subst ht
            have hθi := hθ i
            set κ := M.power i * (S + (B - D)) - S with hκ
            let d' : Contract := some ⟨t.normal, fun s => t.exclusive s + κ⟩
            have hsh : ∀ r, (exclusivePayoff M d' i (.single i r)).buyer =
                  (exclusivePayoff M (some t) i (.single i r)).buyer - κ ∧
                (exclusivePayoff M d' i (.single i r)).supplier i =
                  (exclusivePayoff M (some t) i (.single i r)).supplier i + κ := by
              intro r
              rw [(hexpay_single _ i r).1, (hexpay_single _ i r).2, (hexpay_single _ i r).1,
                (hexpay_single _ i r).2]
              simp [exclusiveTransfer, d']; constructor <;> ring
            have hEO' : IsExclusiveOrder M d' i (.single i q) := by
              refine ⟨Or.inr ⟨q, rfl⟩, by simp [Available, hav.1, d'], fun r hr hr' => ?_⟩
              have hq := (hsh q).1
              simp only [exclusivePayoff] at hq
              rw [hq]
              rcases hr with rfl | ⟨q', rfl⟩
              · simp [outcomePayoff]
                have : B - κ - D = (1 - M.power i) * (S + (B - D)) := by rw [hκ]; ring
                have hBdef : B = M.revenue (exclusiveQuantity i q) - exclusiveTransfer (some t) q :=
                  (hexpay_single (some t) i q).1
                have hT : 0 ≤ (1 - M.power i) * (S + (B - D)) := mul_nonneg (by linarith) (by linarith)
                linarith
              · have h1 := (hsh q').1
                simp only [exclusivePayoff] at h1
                rw [h1]
                have := hEO.2.2 (.single i q') (Or.inr ⟨q', rfl⟩) (by simp [Available] at hr' ⊢; exact hr'.1)
                linarith
            have hS' : 0 ≤ (exclusivePayoff M d' i (.single i q)).supplier i := by
              rw [(hsh q).2]; nlinarith
            have hle := hmx d' (.single i q) ⟨⟨_, hEO', hS'⟩, hEO', hS', by rw [(hsh q).1]; nlinarith⟩
            rw [(hsh q).1, (hsh q).2] at hle
            have e1 : S + κ = M.power i * (S + (B - D)) := by rw [hκ]; ring
            have e2 : B - κ - D = (1 - M.power i) * (S + (B - D)) := by rw [hκ]; ring
            rw [e1, e2] at hle
            exact ⟨split_eq _ S (B - D) hθi.1 hθi.2 hS (by linarith) hle, hS⟩
          refine ⟨?_, ?_⟩
          · intro x hx ⟨i, q, hq⟩
            obtain ⟨⟨hBO, hVO⟩, hbar⟩ := hx
            let E : Fin 2 → ℝ := fun k => (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer
            have hEb : ∀ k, 0 ≤ E k ∧ E k ≤ exclusiveProfit M k (b.exclusive k) :=
              fun k => hEbd _ k _ (hVO k).1 (hVO k).2
            have hbi : IsSingleBargain M i (x.contracts i) (.single i q) (E (other i)) := by
              have := hbar i; rw [hq] at this; simpa using this
            have hn := singleNash _ i q _ (hEb (other i)).1 hbi
            set Sx := exclusivePayoff M (x.contracts i) i (.single i q) with hSx
            have hpayB : (x.payoff M).buyer = Sx.buyer := by
              simp [ContractOutcome.payoff, hq, hSx, exclusivePayoff, outcomePayoff]
            have hpayS : ∀ k, (x.payoff M).supplier k = if k = i then Sx.supplier i else 0 := by
              intro k
              simp [ContractOutcome.payoff, hq, hSx, exclusivePayoff, outcomePayoff]
            have hEi : E i = Sx.buyer := by
              apply le_antisymm
              · exact hbi.1.2.1.2.2 (x.exclusiveOrder i) (hVO i).1.1 (hVO i).1.2.1
              · exact (hVO i).1.2.2 (.single i q) (Or.inr ⟨q, rfl⟩) hbi.1.2.1.2.1
            have hqpos : 0 < q := by
              have := hbi.1.2.1.2.1; simp [Available] at this; exact this.1
            have hS01 : (x.payoff M).supplier 0 + (x.payoff M).supplier 1 = Sx.supplier i := by
              rw [hpayS, hpayS]; fin_cases i <;> simp
            have hsum : (x.payoff M).buyer + (x.payoff M).supplier 0 + (x.payoff M).supplier 1 <
                chainProfit M b.dual := by
              rw [add_assoc, hS01, hpayB, hSx, (hexpay_single _ i q).1, (hexpay_single _ i q).2]
              have := (hex i).2 q hqpos.le
              rw [hexcl] at this
              linarith [hPlt i]
            obtain ⟨y, hy, hyo, -, hyB, hyS, hyst⟩ := combine (x.payoff M).buyer (x.payoff M).supplier E
              (by
                intro k; rw [hpayS]; split_ifs
                · exact hn.2
                · exact le_rfl)
              hEb
              (by
                intro k
                by_cases hk : k = i
                · subst hk; rw [hpayS, if_pos rfl, hpayB]; exact hn.1
                · have hk' : k = other i := hne2 k i hk
                  rw [hpayS, if_neg hk, hpayB, hk', hoth, hEi]; ring)
              hsum.le
            exact ⟨y, hy, ⟨_, hyo⟩, ⟨hyB, hyS⟩, Or.inl (hyst hsum)⟩
          · intro x hx ⟨q, hq⟩
            obtain ⟨⟨hBO, hVO⟩, hbar⟩ := hx
            let E : Fin 2 → ℝ := fun k => (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer
            have hEb : ∀ k, 0 ≤ E k ∧ E k ≤ exclusiveProfit M k (b.exclusive k) :=
              fun k => hEbd _ k _ (hVO k).1 (hVO k).2
            rw [hq] at hBO
            have hDO : IsDualOrder M x.contracts q := ⟨hBO.1, fun r hr => hBO.2 _ hr⟩
            have hb : ∀ i, IsDualBargain M i (x.contracts (other i)) (x.contracts i) q (E (other i)) := by
              intro i; have := hbar i; rw [hq] at this; exact this
            have hpay : x.payoff M = outcomePayoff M x.contracts (.dual q) := by
              simp [ContractOutcome.payoff, hq]
            have hn := fun i => dualNash x.contracts q i _ hDO (hb i)
            have hsum : (outcomePayoff M x.contracts (.dual q)).buyer +
                (outcomePayoff M x.contracts (.dual q)).supplier 0 +
                (outcomePayoff M x.contracts (.dual q)).supplier 1 ≤ chainProfit M b.dual := by
              have := hquad q hBO.1.1 hBO.1.2.1
              simp [outcomePayoff, chainProfit] at this ⊢
              linarith
            obtain ⟨y, hy, hyo, hyc, hyB, hyS, -⟩ := combine _ _ E (fun i => (hn i).2) hEb
              (fun i => (hn i).1) hsum
            refine ⟨y, hy, by rw [hyo]; simp [IsCoordinated, sourcingQuantity], hyc, ?_⟩
            rw [hpay]; exact ⟨hyB, hyS⟩
