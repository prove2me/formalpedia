-- Prove2me | solution 1 for StrategicRFx.Benefit.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:24.975807+00:00
-- url     : https://prove2.me/submissions/059f456e-1747-4c8a-9026-923621cbc279

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_RFContract

open StrategicRFx
open StrategicRFx.Benefit
open StrategicRFx.Benefit.Supplement

/-- Theorem 3, p. 11; proof ec4–ec5. The replacement is computed, including
both exclusive markups, and works in every source bargaining setting. -/
theorem solution (M : Technology) (b : FirstBest) (hM : TechnologyAssumptions M b)
    (setting : ContractSetting) (x : ContractOutcome)
    (hx : IsContractEquilibrium M b setting x) (hc : IsCoordinated M b x.order) :
    IsContractEquilibrium M b setting (costPlusOutcome M b x) ∧
    (costPlusOutcome M b x).payoff M = x.payoff M ∧
    (∀ i, (exclusivePayoff M ((costPlusOutcome M b x).contracts i) i
        ((costPlusOutcome M b x).exclusiveOrder i)).buyer =
      (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).buyer) ∧
    (∀ i, IsCostPlus M i ((costPlusOutcome M b x).contracts i)) := by
      set_option maxHeartbeats 2000000 in
        obtain ⟨hR0, hC0, hpow, hb1, hb2, hmax, huniq, hex, hdiff, hdiff2, hcross⟩ := hM
        have hvalid : ValidOutcome M x := by
          cases setting with
          | simultaneous => exact hx.1
          | sequential i =>
            obtain ⟨F, hF, z, -, hFx, -⟩ := hx
            exact (hF.1 _ _ hFx).1
          | rfx t i => exact hx.1
        have hav : Available x.contracts x.order := hvalid.1.1
        have hord : x.order = .dual b.dual := by
          unfold IsCoordinated at hc
          cases h : x.order with
          | none =>
            rw [h] at hc
            exfalso
            have := huniq (0, 0) ⟨le_refl _, le_refl _⟩ (by simpa [sourcingQuantity] using hc)
            have h2 : (0:ℝ) = b.dual.1 := congrArg Prod.fst this
            linarith
          | dual q =>
            rw [h] at hc hav
            obtain ⟨h1, h2, -, -⟩ := hav
            have := huniq q ⟨h1.le, h2.le⟩ (by simpa [sourcingQuantity] using hc)
            rw [this]
          | single i q =>
            rw [h] at hc hav
            obtain ⟨h1, -⟩ := hav
            exfalso
            have hq : exclusiveQuantity i q ∈ quadrant := by
              unfold exclusiveQuantity quadrant; split_ifs <;> simp [h1.le]
            have := huniq _ hq (by simpa [sourcingQuantity] using hc)
            unfold exclusiveQuantity at this
            split_ifs at this
            · have h2 : (0:ℝ) = b.dual.2 := congrArg Prod.snd this
              linarith
            · have h2 : (0:ℝ) = b.dual.1 := congrArg Prod.fst this
              linarith
        have hpay : (costPlusOutcome M b x).payoff M = x.payoff M := by
          simp only [costPlusOutcome, ContractOutcome.payoff, hord, outcomePayoff, replacement,
            normalTransfer]
          congr 1
          · simp
          · funext i
            fin_cases i <;> simp <;> ring
        have hexb : ∀ i, (exclusivePayoff M ((costPlusOutcome M b x).contracts i) i
              ((costPlusOutcome M b x).exclusiveOrder i)).buyer =
            (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).buyer := by
          intro i
          simp only [costPlusOutcome, exclusivePayoff, outcomePayoff, replacement, exclusiveTransfer]
          unfold exclusiveProfit chainProfit exclusiveQuantity
          fin_cases i <;> simp [hC0] <;> ring
        have hcp : ∀ i, IsCostPlus M i ((costPlusOutcome M b x).contracts i) := by
          intro i
          exact ⟨_, _, exclusiveProfit M i (b.exclusive i) -
            (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).buyer, rfl, fun q _ => rfl,
            fun q _ => by simp only [costPlusOutcome, replacement]; ring⟩
        have hBle : ∀ k, (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer ≤
            (x.payoff M).buyer := by
          intro k
          obtain ⟨⟨hform, havk, -⟩, -⟩ := hvalid.2 k
          rcases hform with h | ⟨q, h⟩
          · rw [h]
            have := hvalid.1.2 .none trivial
            simpa [exclusivePayoff, outcomePayoff, ContractOutcome.payoff] using this
          · rw [h] at havk ⊢
            have hav' : Available x.contracts (.single k q) := by
              simpa [Available] using havk
            have := hvalid.1.2 _ hav'
            simpa [exclusivePayoff, outcomePayoff, ContractOutcome.payoff] using this
        have hxbuyer : (x.payoff M).buyer = chainProfit M b.dual - (x.payoff M).supplier 0 -
            (x.payoff M).supplier 1 := by
          simp only [ContractOutcome.payoff, hord, outcomePayoff, chainProfit]
          simp
          ring
        have hBPi : ∀ k, (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer ≤
            exclusiveProfit M k (b.exclusive k) := by
          intro k
          obtain ⟨⟨hform, havk, -⟩, hS⟩ := hvalid.2 k
          have hex0 : exclusiveProfit M k 0 = 0 := by
            unfold exclusiveProfit chainProfit exclusiveQuantity
            split_ifs <;> simp [hR0, hC0]
          rcases hform with h | ⟨q, h⟩
          · rw [h]
            have := (hex k).2 0 le_rfl
            simp [exclusivePayoff, outcomePayoff]
            linarith
          · rw [h] at havk hS ⊢
            have hq : 0 < q := by simp [Available] at havk; exact havk.1
            have := (hex k).2 q hq.le
            simp [exclusivePayoff, outcomePayoff] at hS ⊢
            unfold exclusiveProfit chainProfit exclusiveQuantity at this ⊢
            fin_cases k <;> simp [hC0] at this hS ⊢ <;> linarith
        have haeanti : ∀ (f f' : ℝ → ℝ) (a c : ℝ), a ≤ c →
            ContinuousOn f (Set.Icc a c) →
            (∀ t ∈ Set.Ioo a c, HasDerivWithinAt f (f' t) (Set.Ioi t) t) →
            (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a c)), f' t ≤ 0) →
            f c ≤ f a := by
          intro f f' a c hac hfc hfd hfa
          let g := fun t => max (f' t) 0
          have hg : g =ᵐ[MeasureTheory.volume.restrict (Set.Icc a c)] (fun _ => 0) := by
            filter_upwards [hfa] with t ht
            exact max_eq_right ht
          have hgi : MeasureTheory.IntegrableOn g (Set.Icc a c) :=
            (MeasureTheory.integrable_zero _ _ _).congr hg.symm
          have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hac hfc hfd hgi
            (fun t ht => le_max_left (f' t) 0)
          have hgz : (∫ t in a..c, g t) = 0 := by
            rw [intervalIntegral.integral_of_le hac]
            apply MeasureTheory.integral_eq_zero_of_ae
            exact MeasureTheory.ae_mono
              (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl) hg
          rw [hgz] at hh
          linarith
        have hsub : chainProfit M b.dual + chainProfit M (0, 0) ≤
            chainProfit M (b.dual.1, 0) + chainProfit M (0, b.dual.2) := by
          let F := fderivWithin ℝ (chainProfit M) quadrant
          let H := fderivWithin ℝ F quadrant
          let μ := MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
          have hμ : μ.prod μ = MeasureTheory.volume.restrict quadrant := by
            rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
            rfl
          have hcr : ∀ᵐ p ∂μ.prod μ, (H p (1, 0)) (0, 1) < 0 := by
            rw [hμ]; exact hcross
          have hswap : ∀ᵐ p ∂μ.prod μ, (H p.swap (1, 0)) (0, 1) < 0 := by
            apply MeasureTheory.ae_of_ae_map (μ := μ.prod μ) (f := Prod.swap)
              (p := fun p => (H p (1, 0)) (0, 1) < 0) measurable_swap.aemeasurable
            rw [MeasureTheory.Measure.prod_swap]
            exact hcr
          have hslice := MeasureTheory.Measure.ae_ae_of_ae_prod hswap
          have hpartial : ∀ᵐ y ∂μ, (F (b.dual.1, y)) (0, 1) ≤ (F (0, y)) (0, 1) := by
            filter_upwards [hslice, MeasureTheory.ae_restrict_mem measurableSet_Ici] with y hy hy0
            have hline : ∀ t ∈ Set.Ici (0 : ℝ),
                HasDerivWithinAt (fun u => F (u, y)) (H (t, y) (1, 0)) (Set.Ici 0) t := by
              intro t ht
              exact (hdiff2 (t, y) ⟨ht, hy0⟩).hasFDerivWithinAt.comp_hasDerivWithinAt (f := fun u : ℝ => (u, y)) t
                ((hasDerivAt_id t).prodMk (hasDerivAt_const t y)).hasDerivWithinAt
                (fun u hu => ⟨hu, hy0⟩)
            have hscalar : ∀ t ∈ Set.Ici (0 : ℝ),
                HasDerivWithinAt (fun u => (F (u, y)) (0, 1))
                  ((H (t, y) (1, 0)) (0, 1)) (Set.Ici 0) t := by
              intro t ht
              simpa using (hline t ht).clm_apply (hasDerivWithinAt_const t (Set.Ici 0) (0, 1))
            apply haeanti (fun u => (F (u, y)) (0, 1))
              (fun u => (H (u, y) (1, 0)) (0, 1)) 0 b.dual.1 hb1.le
            · intro t ht
              exact (hscalar t ht.1).continuousWithinAt.mono (fun u hu => hu.1)
            · intro t ht
              exact (hscalar t ht.1.le).mono (fun u hu => le_trans ht.1.le hu.le)
            · exact MeasureTheory.ae_mono
                (MeasureTheory.Measure.restrict_mono (fun t ht => ht.1) le_rfl) (hy.mono (fun t ht => ht.le))
          have hvline : ∀ a, 0 ≤ a → ∀ t ∈ Set.Ici (0 : ℝ),
              HasDerivWithinAt (fun u => chainProfit M (a, u)) ((F (a, t)) (0, 1)) (Set.Ici 0) t := by
            intro a ha t ht
            exact (hdiff (a, t) ⟨ha, ht⟩).hasFDerivWithinAt.comp_hasDerivWithinAt (f := fun u : ℝ => (a, u)) t
              ((hasDerivAt_const t a).prodMk (hasDerivAt_id t)).hasDerivWithinAt
              (fun u hu => ⟨ha, hu⟩)
          have hfinal : chainProfit M (b.dual.1, b.dual.2) - chainProfit M (0, b.dual.2) ≤
              chainProfit M (b.dual.1, 0) - chainProfit M (0, 0) := by
            apply haeanti (fun t => chainProfit M (b.dual.1, t) - chainProfit M (0, t))
              (fun t => (F (b.dual.1, t)) (0, 1) - (F (0, t)) (0, 1))
                0 b.dual.2 hb2.le
            · intro t ht
              exact ((hvline _ hb1.le t ht.1).sub (hvline _ le_rfl t ht.1)).continuousWithinAt.mono
                (fun u hu => hu.1)
            · intro t ht
              exact ((hvline _ hb1.le t ht.1.le).sub (hvline _ le_rfl t ht.1.le)).mono
                (fun u hu => le_trans ht.1.le hu.le)
            · exact MeasureTheory.ae_mono
                (MeasureTheory.Measure.restrict_mono (fun t ht => ht.1) le_rfl)
                (hpartial.mono (fun t ht => sub_nonpos.mpr ht))
          have hb : (b.dual.1, b.dual.2) = b.dual := Prod.eta _
          rw [hb] at hfinal
          linarith
        have hpos : ∀ k, 0 < b.exclusive k := by
          intro k
          rcases (hex k).1.lt_or_eq with h | h
          · exact h
          exfalso
          have h00 : chainProfit M (0, 0) = 0 := by simp [chainProfit, hR0, hC0]
          have hle := (hex k).2
          rw [← h] at hle
          fin_cases k
          · have h1 := hle b.dual.1 hb1.le
            simp only [exclusiveProfit, exclusiveQuantity] at h1
            simp at h1
            rw [h00] at h1
            have hne : (0, b.dual.2) ≠ b.dual := by
              intro e; have := congrArg Prod.fst e; simp at this; linarith
            have hlt : chainProfit M (0, b.dual.2) < chainProfit M b.dual :=
              lt_of_le_of_ne (hmax _ ⟨le_rfl, hb2.le⟩) (fun e => hne (huniq _ ⟨le_rfl, hb2.le⟩ e))
            linarith
          · have h1 := hle b.dual.2 hb2.le
            simp only [exclusiveProfit, exclusiveQuantity] at h1
            simp at h1
            rw [h00] at h1
            have hne : (b.dual.1, 0) ≠ b.dual := by
              intro e; have := congrArg Prod.snd e; simp at this; linarith
            have hlt : chainProfit M (b.dual.1, 0) < chainProfit M b.dual :=
              lt_of_le_of_ne (hmax _ ⟨hb1.le, le_rfl⟩) (fun e => hne (huniq _ ⟨hb1.le, le_rfl⟩ e))
            linarith
        have hB0 : ∀ k, 0 ≤ (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer := by
          intro k
          have := (hvalid.2 k).1.2.2 .none (Or.inl rfl) trivial
          simpa [exclusivePayoff, outcomePayoff] using this
        have hnewsingle : ∀ (c : Contracts) k, c k = (costPlusOutcome M b x).contracts k →
            ∀ q, (outcomePayoff M c (.single k q)).buyer =
            exclusiveProfit M k q - exclusiveProfit M k (b.exclusive k) +
              (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer := by
          intro c k hc q
          simp only [outcomePayoff, hc, costPlusOutcome, replacement, exclusiveTransfer]
          unfold exclusiveProfit chainProfit exclusiveQuantity
          fin_cases k <;> simp [hC0] <;> ring
        have hnewdual : ∀ r : ℝ × ℝ, (outcomePayoff M (costPlusOutcome M b x).contracts (.dual r)).buyer =
            chainProfit M r - (x.payoff M).supplier 0 - (x.payoff M).supplier 1 := by
          intro r
          simp only [outcomePayoff, costPlusOutcome, replacement, normalTransfer, chainProfit]
          ring
        have hnewvalid : ValidOutcome M (costPlusOutcome M b x) := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · simp [Available, costPlusOutcome, replacement, hb1, hb2]
          · intro r hr
            have e1 : outcomePayoff M (costPlusOutcome M b x).contracts (costPlusOutcome M b x).order =
                (costPlusOutcome M b x).payoff M := rfl
            rw [e1, hpay]
            cases r with
            | none =>
              have := hvalid.1.2 .none trivial
              simpa [outcomePayoff, ContractOutcome.payoff] using this
            | dual r =>
              rw [hnewdual, hxbuyer]
              have := hmax r ⟨hr.1.le, hr.2.1.le⟩
              linarith
            | single k q =>
              rw [hnewsingle _ _ rfl]
              have := (hex k).2 q (hr.1.le)
              have := hBle k
              linarith
          · intro k
            refine ⟨⟨Or.inr ⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
            · simp [Available, costPlusOutcome, replacement, hpos k]
            · intro r hrf hra
              have hck : (fun j => if j = k then (costPlusOutcome M b x).contracts k else none) k =
                  (costPlusOutcome M b x).contracts k := by simp
              show _ ≤ (outcomePayoff M _ (.single k (b.exclusive k))).buyer
              rw [hnewsingle _ _ hck]
              rcases hrf with rfl | ⟨q, rfl⟩
              · simp only [outcomePayoff]
                linarith [hB0 k]
              · rw [hnewsingle _ _ hck]
                have := (hex k).2 q (by simp [Available] at hra; exact hra.1.le)
                linarith
            · have := hBPi k
              simp only [costPlusOutcome, replacement]
              generalize (exclusivePayoff M (x.contracts k) k (x.exclusiveOrder k)).buyer = B at this ⊢
              simp [exclusivePayoff, outcomePayoff, exclusiveTransfer]
              linarith
        have hbar : ∀ i D, IsDualBargain M i (x.contracts (other i)) (x.contracts i) b.dual D →
            IsDualBargain M i ((costPlusOutcome M b x).contracts (other i))
              ((costPlusOutcome M b x).contracts i) b.dual D := by
          intro i D ⟨⟨hadm, hdo, hS, hD⟩, hopt⟩
          have hfo : (fun k => if k = i then x.contracts i else x.contracts (other i)) = x.contracts := by
            funext k; fin_cases i <;> fin_cases k <;> rfl
          have hfn : (fun k => if k = i then (costPlusOutcome M b x).contracts i
              else (costPlusOutcome M b x).contracts (other i)) = (costPlusOutcome M b x).contracts := by
            funext k; fin_cases i <;> fin_cases k <;> rfl
          rw [hfo] at hdo hS hD
          have hxp : outcomePayoff M x.contracts (.dual b.dual) = x.payoff M := by
            simp [ContractOutcome.payoff, hord]
          have hnp : outcomePayoff M (costPlusOutcome M b x).contracts (.dual b.dual) =
              x.payoff M := hpay
          rw [hxp] at hS hD
          have hcand : DualCandidate M i ((costPlusOutcome M b x).contracts (other i))
              ((costPlusOutcome M b x).contracts i) b.dual D := by
            refine ⟨⟨_, hnewvalid.2 i⟩, ?_, ?_, ?_⟩
            · rw [hfn]; exact ⟨hnewvalid.1.1, fun r hr => hnewvalid.1.2 _ hr⟩
            · rw [hfn, hnp]; exact hS
            · rw [hfn, hnp]; exact hD
          refine ⟨hcand, ?_⟩
          intro d' q' hc'
          rw [hfn, hnp]
          rw [hfo, hxp] at hopt
          obtain ⟨hadm', hdo', hS', hD'⟩ := hc'
          have hθ := hpow i
          obtain ⟨t, ht⟩ : ∃ t, x.contracts i = some t := by
            have h2 := hav; rw [hord] at h2
            obtain ⟨-, -, h0, h1⟩ := h2
            fin_cases i
            · exact Option.isSome_iff_exists.mp h0
            · exact Option.isSome_iff_exists.mp h1
          have hsum : (outcomePayoff M (fun k => if k = i then d' else
                (costPlusOutcome M b x).contracts (other i)) (.dual q')).supplier i +
              (outcomePayoff M (fun k => if k = i then d' else
                (costPlusOutcome M b x).contracts (other i)) (.dual q')).buyer =
              chainProfit M q' - (x.payoff M).supplier (other i) := by
            simp only [outcomePayoff, chainProfit]
            fin_cases i <;> simp [other, costPlusOutcome, replacement, normalTransfer] <;> ring
          have hq' : q' ∈ quadrant := ⟨hdo'.1.1.le, hdo'.1.2.1.le⟩
          have hmq := hmax q' hq'
          generalize (outcomePayoff M (fun k => if k = i then d' else
                (costPlusOutcome M b x).contracts (other i)) (.dual q')).supplier i = S' at hsum hS' ⊢
          generalize (outcomePayoff M (fun k => if k = i then d' else
                (costPlusOutcome M b x).contracts (other i)) (.dual q')).buyer = B' at hsum hD' ⊢
          have hxb2 : (x.payoff M).buyer = chainProfit M b.dual - (x.payoff M).supplier i -
              (x.payoff M).supplier (other i) := by
            fin_cases i <;> simp [other] <;> linarith [hxbuyer]
          set δ := S' - (x.payoff M).supplier i with hδ
          let d'' : Contract := some ⟨fun q => t.normal q + δ, t.exclusive⟩
          have hpd : ∀ r : ℝ × ℝ,
              (outcomePayoff M (fun k => if k = i then d'' else x.contracts (other i)) (.dual r)).buyer =
                (outcomePayoff M x.contracts (.dual r)).buyer - δ ∧
              (outcomePayoff M (fun k => if k = i then d'' else x.contracts (other i)) (.dual r)).supplier i =
                (outcomePayoff M x.contracts (.dual r)).supplier i + δ := by
            intro r
            have hxo : x.contracts (other i) = x.contracts (other i) := rfl
            fin_cases i <;> simp [outcomePayoff, normalTransfer, d'', other, ht] at ht ⊢ <;>
              constructor <;> ring
          have hadm'' : Admissible M d'' i := by
            obtain ⟨hEO, hEN⟩ := hvalid.2 i
            have hfe : ∀ s, (s = .none ∨ ∃ q, s = .single i q) →
                exclusivePayoff M d'' i s = exclusivePayoff M (x.contracts i) i s := by
              intro s hs
              rcases hs with rfl | ⟨q, rfl⟩
              · rfl
              · simp [exclusivePayoff, outcomePayoff, exclusiveTransfer, d'', ht]
            have hav2 : ∀ s, Available (fun j => if j = i then d'' else none) s ↔
                Available (fun j => if j = i then x.contracts i else none) s := by
              intro s
              cases s with
              | none => simp [Available]
              | dual r => simp [Available, d'', ht]
              | single k q => simp [Available, d'', ht]
            refine ⟨x.exclusiveOrder i, ⟨hEO.1, (hav2 _).2 hEO.2.1, fun r hr hra => ?_⟩, ?_⟩
            · have := hEO.2.2 r hr ((hav2 _).1 hra)
              have e1 := hfe r hr
              have e2 := hfe (x.exclusiveOrder i) hEO.1
              simp only [exclusivePayoff] at e1 e2
              rw [e1, e2]; exact this
            · rw [hfe _ hEO.1]; exact hEN
          have hcand'' : DualCandidate M i (x.contracts (other i)) d'' b.dual D := by
            refine ⟨hadm'', ⟨?_, ?_⟩, ?_, ?_⟩
            · have h2 := hav; rw [hord] at h2
              obtain ⟨h1, h2, -, -⟩ := h2
              have h3 := hav; rw [hord] at h3
              obtain ⟨-, -, h30, h31⟩ := h3
              fin_cases i <;> simp [Available, d'', h1, h2, other] at h30 h31 ⊢ <;> assumption
            · intro r hr
              rw [(hpd r).1, (hpd _).1]
              have hr' : Available x.contracts (.dual r) := by
                have h3 := hav; rw [hord] at h3
                obtain ⟨-, -, h30, h31⟩ := h3
                exact ⟨hr.1, hr.2.1, h30, h31⟩
              have := hvalid.1.2 _ hr'
              simp only [ContractOutcome.payoff, hord] at this
              linarith
            · rw [(hpd _).2, hxp]; linarith
            · rw [(hpd _).1, hxp]; linarith
          have key := hopt d'' b.dual hcand''
          rw [(hpd _).1, (hpd _).2, hxp] at key
          unfold nashProduct at key ⊢
          calc S' ^ M.power i * (B' - D) ^ (1 - M.power i)
              ≤ S' ^ M.power i * ((x.payoff M).buyer - δ - D) ^ (1 - M.power i) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
                  (Real.rpow_nonneg hS' _)
            _ ≤ _ := by
                convert key using 3
                ring
        refine ⟨?_, hpay, hexb, hcp⟩
        cases setting with
        | simultaneous =>
          refine ⟨hnewvalid, fun i => ?_⟩
          show IsDualBargain M i ((costPlusOutcome M b x).contracts (other i))
            ((costPlusOutcome M b x).contracts i) b.dual
            (exclusivePayoff M ((costPlusOutcome M b x).contracts (other i)) (other i)
              ((costPlusOutcome M b x).exclusiveOrder (other i))).buyer
          rw [hexb]
          apply hbar
          have := hx.2 i
          simp only [hord] at this
          exact this
        | sequential i =>
          classical
          obtain ⟨F, hF, z, hFz, hFx, hlead⟩ := hx
          have hoo : other (other i) = i := by fin_cases i <;> rfl
          have hcont : FollowerContinuation M i ((costPlusOutcome M b x).contracts i)
              (costPlusOutcome M b x) := by
            refine ⟨hnewvalid, rfl, ?_⟩
            have h1 := (hF.1 _ _ hFx).2.2
            unfold SupplierBargainAt at h1 ⊢
            simp only [hord] at h1
            show IsDualBargain M (other i) ((costPlusOutcome M b x).contracts (other (other i)))
              ((costPlusOutcome M b x).contracts (other i)) b.dual _
            rw [hexb]
            rw [hoo] at h1 ⊢
            have := hbar (other i) _ (by rw [hoo]; exact h1)
            rw [hoo] at this
            exact this
          let F' : Contract → ContractOutcome → Prop := fun d y =>
            if d = (costPlusOutcome M b x).contracts i then y = costPlusOutcome M b x else F d y
          have hne : (none : Contract) ≠ (costPlusOutcome M b x).contracts i := by
            simp [costPlusOutcome, replacement]
          refine ⟨F', ⟨?_, ?_, ?_⟩, z, ?_, ?_, ?_⟩
          · intro d y hdy
            by_cases hd : d = (costPlusOutcome M b x).contracts i
            · simp only [F', hd, if_true] at hdy
              subst hdy; rw [hd]; exact hcont
            · simp only [F', hd, if_false] at hdy
              exact hF.1 _ _ hdy
          · intro d hd
            by_cases hd' : d = (costPlusOutcome M b x).contracts i
            · exact ⟨costPlusOutcome M b x, by simp [F', hd']⟩
            · obtain ⟨y, hy⟩ := hF.2.1 d hd
              exact ⟨y, by simp only [F', hd', if_false]; exact hy⟩
          · intro d y y' hy hy'
            by_cases hd' : d = (costPlusOutcome M b x).contracts i
            · simp only [F', hd', if_true] at hy hy'
              rw [hy, hy']
            · simp only [F', hd', if_false] at hy hy'
              exact hF.2.2 _ _ _ hy hy'
          · simp only [F', hne, if_false]; exact hFz
          · simp [F']
          · dsimp only at hlead ⊢
            rcases hlead with ⟨dual, hcand, hopt⟩ | ⟨-, hord', -⟩
            · refine Or.inl ⟨dual, ⟨by simp [F'], ?_, ?_, ?_⟩, ?_⟩
              · have hcand2 := hcand.2.1
                cases dual
                · simp only [Bool.false_eq_true, if_false] at hcand2
                  obtain ⟨q, hq⟩ := hcand2
                  rw [hord] at hq; cases hq
                · simp only [if_true]
                  exact ⟨_, rfl⟩
              · rw [hpay]; exact hcand.2.2.1
              · rw [hpay]; exact hcand.2.2.2
              · intro y hy
                rw [hpay]
                by_cases hd : y.contracts i = (costPlusOutcome M b x).contracts i
                · have hyF := hy.1
                  simp only [F', hd, if_true] at hyF
                  rw [hyF, hpay]
                · apply hopt
                  exact ⟨by have hyF := hy.1; simpa [F', hd] using hyF, hy.2⟩
            · exfalso
              rcases hord' with h | ⟨q, h⟩ <;> rw [hord] at h <;> cases h
        | rfx t i =>
          classical
          refine ⟨hnewvalid, ?_⟩
          have hnash_strict : ∀ (a c d e : ℝ) k, 0 ≤ a → 0 ≤ c → a < d → c < e →
              nashProduct (M.power k) a c < nashProduct (M.power k) d e := by
            intro a c d e k ha hc had hce
            unfold nashProduct
            have hp := hpow k
            have h1 := Real.rpow_lt_rpow ha had hp.1
            have h2 := Real.rpow_lt_rpow hc hce (by linarith : 0 < 1 - M.power k)
            exact mul_lt_mul_of_nonneg h1 h2 (Real.rpow_nonneg ha _) (Real.rpow_nonneg hc _)
          have hsome : ∀ k, ∃ p : Payment, x.contracts k = some p := by
            have hh := hav
            rw [hord] at hh
            intro k
            fin_cases k
            · exact Option.isSome_iff_exists.mp hh.2.2.1
            · exact Option.isSome_iff_exists.mp hh.2.2.2
          have htradAv : ∀ c s, tradeAvailable (ordinaryRights c) s ↔ Available c s := by
            intro c s
            cases s with
            | none => simp [tradeAvailable, Sourcing.positive, ordinaryRights, ProcurementRight.permits,
                quantityFrom, sourcingQuantity, Available]
            | dual q =>
              simp only [tradeAvailable, Sourcing.positive, ordinaryRights, ProcurementRight.permits,
                quantityFrom, sourcingQuantity, Available]
              constructor
              · intro hh
                exact ⟨hh.1.1, hh.1.2, hh.2 0 (by simpa using hh.1.1),
                  hh.2 1 (by simpa using hh.1.2)⟩
              · intro hh
                refine ⟨⟨hh.1, hh.2.1⟩, ?_⟩
                intro k hk
                fin_cases k
                · exact hh.2.2.1
                · exact hh.2.2.2
            | single k q =>
              fin_cases k <;>
                simp [tradeAvailable, Sourcing.positive, ordinaryRights, ProcurementRight.permits,
                  quantityFrom, sourcingQuantity, exclusiveQuantity, Available, Fin.forall_fin_two] <;> tauto
          have htradPay : ∀ c s, tradePayoff M (ordinaryRights c) s = outcomePayoff M c s := by
            intro c s
            cases s with
            | none =>
              simp [tradePayoff, ordinaryRights, ProcurementRight.transfer, quantityFrom,
                sourcingQuantity, outcomePayoff, hR0, hC0]
            | dual q =>
              simp [tradePayoff, ordinaryRights, ProcurementRight.transfer, quantityFrom,
                sourcingQuantity, outcomePayoff]
            | single k q =>
              fin_cases k <;>
                simp [tradePayoff, ordinaryRights, ProcurementRight.transfer, quantityFrom,
                  sourcingQuantity, outcomePayoff, exclusiveQuantity, hC0]
              all_goals
                congr 1
                funext j
                fin_cases j <;> simp [hC0]
          have htp : x.trade.payoff M = x.payoff M := by
            exact htradPay _ _
          have hntp : (costPlusOutcome M b x).trade.payoff M = x.payoff M := by
            rw [TradeOutcome.payoff, ContractOutcome.trade, htradPay]
            exact hpay
          have hnewTrade : ValidTrade M (costPlusOutcome M b x).trade := by
            refine ⟨⟨(htradAv _ _).2 hnewvalid.1.1, ?_⟩, ?_⟩
            · intro r hr
              change (tradePayoff M (ordinaryRights (costPlusOutcome M b x).contracts) r).buyer ≤ _
              rw [htradPay]
              change _ ≤ (tradePayoff M (ordinaryRights (costPlusOutcome M b x).contracts)
                (costPlusOutcome M b x).order).buyer
              rw [htradPay]
              exact hnewvalid.1.2 r ((htradAv _ _).1 hr)
            · intro k c hc
              have he : (costPlusOutcome M b x).contracts k = c := by
                exact ProcurementRight.contract.inj hc
              rw [← he]
              exact ⟨_, hnewvalid.2 k⟩
          have hadm_ex : ∀ k (p q : Payment), p.exclusive = q.exclusive →
              Admissible M (some p) k → Admissible M (some q) k := by
            intro i p q he ⟨s, hs, hsp⟩
            have hpayex : ∀ r, (r = .none ∨ ∃ z, r = .single i z) →
                exclusivePayoff M (some p) i r = exclusivePayoff M (some q) i r := by
              intro r hr
              rcases hr with rfl | ⟨z, rfl⟩
              · rfl
              · simp [exclusivePayoff, outcomePayoff, exclusiveTransfer, he]
            have havex : ∀ r, Available (fun j => if j = i then some p else none) r ↔
                Available (fun j => if j = i then some q else none) r := by
              intro r
              cases r <;> simp [Available]
            refine ⟨s, ⟨hs.1, (havex s).1 hs.2.1, ?_⟩, ?_⟩
            · intro r hr hra
              have hh := hs.2.2 r hr ((havex r).2 hra)
              change (exclusivePayoff M (some q) i r).buyer ≤ (exclusivePayoff M (some q) i s).buyer
              rw [← hpayex r hr, ← hpayex s hs.1]
              exact hh
            · rw [← hpayex s hs.1]; exact hsp
          have hmkStage : ∀ k (fixed : Contract) (c : Contracts) q (D : Payoff),
              (∃ p : Payment, c k = some p ∧ Admissible M (some p) k) →
              c (other k) = fixed → IsDualOrder M c q →
              D.supplier k ≤ (outcomePayoff M c (.dual q)).supplier k →
              D.buyer ≤ (outcomePayoff M c (.dual q)).buyer →
              RFStageCandidate M k (.contract fixed) D true ⟨ordinaryRights c, .dual q⟩ := by
            intro k fixed c q D ⟨p, hp, had⟩ hf ho hs hb
            refine ⟨⟨p, ?_, had⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
            · exact congrArg ProcurementRight.contract hp
            · exact congrArg ProcurementRight.contract hf
            · exact ⟨q, rfl⟩
            · exact (htradAv _ _).2 ho.1
            · intro r hr hra
              cases r with
              | none => cases hr
              | single j z => cases hr
              | dual z =>
                rw [htradPay, htradPay]
                exact ho.2 z ((htradAv _ _).1 hra)
            · change D.supplier k ≤ (tradePayoff M (ordinaryRights c) (.dual q)).supplier k
              rw [htradPay]; exact hs
            · change D.buyer ≤ (tradePayoff M (ordinaryRights c) (.dual q)).buyer
              rw [htradPay]; exact hb
          have hshift : ∀ k (c : Contracts) (p : Payment) (δ : ℝ), c k = some p →
              ∃ c' : Contracts, c' (other k) = c (other k) ∧
                (∃ p' : Payment, c' k = some p' ∧ p'.exclusive = p.exclusive) ∧
                (∀ q, (outcomePayoff M c' (.dual q)).buyer =
                  (outcomePayoff M c (.dual q)).buyer - δ ∧
                  (outcomePayoff M c' (.dual q)).supplier k =
                  (outcomePayoff M c (.dual q)).supplier k + δ) ∧
                (∀ q, IsDualOrder M c q → IsDualOrder M c' q) := by
            intro k c p δ hp
            let p' : Payment := ⟨fun q => p.normal q + δ, p.exclusive⟩
            let c' : Contracts := fun j => if j = k then some p' else c j
            have hf : c' (other k) = c (other k) := by fin_cases k <;> rfl
            have hav' : ∀ q, Available c' (.dual q) ↔ Available c (.dual q) := by
              intro q
              fin_cases k <;> simp at hp <;> simp [Available, c', hp]
            have hpd : ∀ q, (outcomePayoff M c' (.dual q)).buyer =
                (outcomePayoff M c (.dual q)).buyer - δ ∧
                (outcomePayoff M c' (.dual q)).supplier k =
                (outcomePayoff M c (.dual q)).supplier k + δ := by
              intro q
              fin_cases k <;> simp at hp <;> simp [outcomePayoff, c', p', normalTransfer, hp] <;>
                constructor <;> ring
            refine ⟨c', hf, ⟨p', by simp [c'], rfl⟩, hpd, ?_⟩
            intro q hq
            refine ⟨(hav' q).2 hq.1, ?_⟩
            intro r hr
            rw [(hpd r).1, (hpd q).1]
            exact sub_le_sub_right (hq.2 r ((hav' r).1 hr)) δ
          have hfront : ∀ k (D : Payoff),
              RFStageCandidate M k (.contract (x.contracts (other k))) D true x.trade →
              (∀ y, RFStageCandidate M k (.contract (x.contracts (other k))) D true y →
                rfStageProduct M k D y ≤ rfStageProduct M k D x.trade) →
              ∀ (c : Contracts) q (p : Payment), c k = some p → Admissible M (some p) k →
                c (other k) = x.contracts (other k) → IsDualOrder M c q →
                (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer ≤
                  (x.payoff M).supplier k + (x.payoff M).buyer := by
            intro k D hcand hopt c q p hp had hf ho
            by_contra hle
            have hgap : 0 < (outcomePayoff M c (.dual q)).supplier k +
                (outcomePayoff M c (.dual q)).buyer -
                ((x.payoff M).supplier k + (x.payoff M).buyer) := by linarith
            let ε := ((outcomePayoff M c (.dual q)).supplier k +
                (outcomePayoff M c (.dual q)).buyer -
                ((x.payoff M).supplier k + (x.payoff M).buyer)) / 2
            have he : 0 < ε := by dsimp [ε]; linarith
            let δ := (x.payoff M).supplier k + ε - (outcomePayoff M c (.dual q)).supplier k
            obtain ⟨c', hfixed, ⟨p', hp', hex'⟩, hpd, horder⟩ := hshift k c p δ hp
            have hs := hcand.2.2.2.2.1
            have hb := hcand.2.2.2.2.2
            rw [htp] at hs hb
            have hsp : (outcomePayoff M c' (.dual q)).supplier k = (x.payoff M).supplier k + ε := by
              rw [(hpd q).2]; dsimp [δ]; ring
            have hbp : (outcomePayoff M c' (.dual q)).buyer = (x.payoff M).buyer + ε := by
              rw [(hpd q).1]; dsimp [δ, ε]; ring
            have hc' := hmkStage k (x.contracts (other k)) c' q D
              ⟨p', hp', hadm_ex k p p' hex'.symm had⟩ (hfixed.trans hf) (horder q ho)
              (by rw [hsp]; linarith) (by rw [hbp]; linarith)
            have hbound := hopt _ hc'
            unfold rfStageProduct at hbound
            change nashProduct _ ((tradePayoff M (ordinaryRights c') (.dual q)).supplier k - _)
              ((tradePayoff M (ordinaryRights c') (.dual q)).buyer - _) ≤ _ at hbound
            rw [htradPay, htp, hsp, hbp] at hbound
            have hlt := hnash_strict ((x.payoff M).supplier k - D.supplier k)
              ((x.payoff M).buyer - D.buyer)
              ((x.payoff M).supplier k + ε - D.supplier k)
              ((x.payoff M).buyer + ε - D.buyer) k (by linarith) (by linarith)
              (by linarith) (by linarith)
            exact (not_lt_of_ge hbound) hlt
          have hdecode : ∀ k (fixed : Contract) D y,
              RFStageCandidate M k (.contract fixed) D true y →
              ∃ (p : Payment) (q : ℝ × ℝ) (c : Contracts),
                y.rights = ordinaryRights c ∧ y.order = .dual q ∧
                c k = some p ∧ Admissible M (some p) k ∧ c (other k) = fixed ∧
                IsDualOrder M c q ∧
                D.supplier k ≤ (outcomePayoff M c (.dual q)).supplier k ∧
                D.buyer ≤ (outcomePayoff M c (.dual q)).buyer := by
            intro k fixed D y ⟨⟨p, hp, had⟩, hf, hbranch, ho, hs, hb⟩
            obtain ⟨q, hq⟩ := hbranch
            let c : Contracts := fun j => if j = k then some p else fixed
            have heq : y.rights = ordinaryRights c := by
              funext j
              fin_cases k <;> fin_cases j <;> simp at hp hf <;> simpa [ordinaryRights, c, other] using
                (by assumption : _)
            refine ⟨p, q, c, heq, hq, by simp [c], had, ?_, ?_, ?_, ?_⟩
            · fin_cases k <;> rfl
            · rw [heq, hq] at ho
              refine ⟨(htradAv _ _).1 ho.1, ?_⟩
              intro r hr
              have hh := ho.2 (.dual r) trivial ((htradAv _ _).2 hr)
              simpa only [htradPay] using hh
            · simpa only [TradeOutcome.payoff, heq, hq, htradPay] using hs
            · simpa only [TradeOutcome.payoff, heq, hq, htradPay] using hb
          have hbase : ∀ k (p : Payment), Admissible M (some p) k →
              ∃ (c : Contracts) (p' : Payment), c k = some p' ∧
                Admissible M (some p') k ∧ p'.exclusive = p.exclusive ∧
                c (other k) = x.contracts (other k) ∧
                (∀ q, outcomePayoff M c (.dual q) = outcomePayoff M x.contracts (.dual q)) ∧
                IsDualOrder M c b.dual := by
            intro k p had
            obtain ⟨o, ho⟩ := hsome k
            let p' : Payment := ⟨o.normal, p.exclusive⟩
            let c : Contracts := fun j => if j = k then some p' else x.contracts j
            have hpd : ∀ q, outcomePayoff M c (.dual q) = outcomePayoff M x.contracts (.dual q) := by
              intro q
              fin_cases k <;> simp at ho <;> simp [outcomePayoff, c, p', normalTransfer, ho]
              all_goals
                congr 1
                funext j
                fin_cases j <;> simp [ho, normalTransfer]
            have hav' : ∀ q, Available c (.dual q) ↔ Available x.contracts (.dual q) := by
              intro q
              fin_cases k <;> simp at ho <;> simp [Available, c, ho]
            refine ⟨c, p', by simp [c], hadm_ex k p p' rfl had, rfl, ?_, hpd, ?_⟩
            · fin_cases k <;> rfl
            · refine ⟨(hav' _).2 (by simpa [hord] using hav), ?_⟩
              intro q hq
              rw [hpd, hpd]
              have hh := hvalid.1.2 (.dual q) ((hav' q).1 hq)
              simpa only [hord] using hh
          have hnewsum : ∀ k (c : Contracts) q,
              c (other k) = (costPlusOutcome M b x).contracts (other k) →
              (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer =
                chainProfit M q - (x.payoff M).supplier (other k) := by
            intro k c q hc
            fin_cases k <;> simp [other] at hc ⊢ <;>
              simp [outcomePayoff, hc, costPlusOutcome, replacement, normalTransfer, chainProfit] <;> ring
          have htotal : ∀ k, (x.payoff M).supplier k + (x.payoff M).buyer =
              chainProfit M b.dual - (x.payoff M).supplier (other k) := by
            intro k
            fin_cases k <;> simp [other] <;> linarith [hxbuyer]
          have htransferOpt : ∀ k (D : Payoff),
              RFStageCandidate M k (.contract (x.contracts (other k))) D true x.trade →
              (∀ y, RFStageCandidate M k (.contract (x.contracts (other k))) D true y →
                rfStageProduct M k D y ≤ rfStageProduct M k D x.trade) →
              RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k)))
                D true (costPlusOutcome M b x).trade ∧
              (∀ y, RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k)))
                D true y → rfStageProduct M k D y ≤ rfStageProduct M k D (costPlusOutcome M b x).trade) := by
            intro k D hcan hopt
            have hs := hcan.2.2.2.2.1
            have hb := hcan.2.2.2.2.2
            rw [htp] at hs hb
            have hncan : RFStageCandidate M k
                (.contract ((costPlusOutcome M b x).contracts (other k))) D true
                (costPlusOutcome M b x).trade := by
              apply hmkStage
              · exact ⟨_, rfl, ⟨_, hnewvalid.2 k⟩⟩
              · rfl
              · exact ⟨hnewvalid.1.1, fun r hr => hnewvalid.1.2 _ hr⟩
              · change D.supplier k ≤ ((costPlusOutcome M b x).payoff M).supplier k
                rwa [hpay]
              · change D.buyer ≤ ((costPlusOutcome M b x).payoff M).buyer
                rwa [hpay]
            refine ⟨hncan, ?_⟩
            intro y hy
            obtain ⟨p, q, c, hyr, hyo, hcp, had, hcf, ho, hS, hB⟩ := hdecode k _ D y hy
            obtain ⟨cb, pb, hpb, hadb, hexbp, hfb, hpdb, hob⟩ := hbase k p had
            let δ := (outcomePayoff M c (.dual q)).supplier k - (x.payoff M).supplier k
            obtain ⟨cc, hfc, ⟨pc, hpc, hec⟩, hpdc, hoc⟩ := hshift k cb pb δ hpb
            have hxpb : outcomePayoff M cb (.dual b.dual) = x.payoff M := by
              rw [hpdb]; simp [ContractOutcome.payoff, hord]
            have hsp : (outcomePayoff M cc (.dual b.dual)).supplier k =
                (outcomePayoff M c (.dual q)).supplier k := by
              rw [(hpdc _).2, hxpb]; dsimp [δ]; ring
            have hbudget := hnewsum k c q hcf
            have hmq := hmax q ⟨ho.1.1.le, ho.1.2.1.le⟩
            have hbp : (outcomePayoff M c (.dual q)).buyer ≤
                (outcomePayoff M cc (.dual b.dual)).buyer := by
              rw [(hpdc _).1, hxpb]
              have hh := htotal k
              dsimp [δ]
              linarith
            have hcc := hmkStage k (x.contracts (other k)) cc b.dual D
              ⟨pc, hpc, hadm_ex k pb pc hec.symm hadb⟩ (hfc.trans hfb) (hoc _ hob)
              (by rwa [hsp]) (hB.trans hbp)
            have hkey := hopt _ hcc
            unfold rfStageProduct at hkey ⊢
            change nashProduct _ ((tradePayoff M (ordinaryRights cc) (.dual b.dual)).supplier k - _)
              ((tradePayoff M (ordinaryRights cc) (.dual b.dual)).buyer - _) ≤ _ at hkey
            rw [htradPay, htp, hsp] at hkey
            rw [hntp]
            change nashProduct _ ((tradePayoff M y.rights y.order).supplier k - _)
              ((tradePayoff M y.rights y.order).buyer - _) ≤ _
            rw [hyr, hyo, htradPay]
            calc
              _ ≤ nashProduct (M.power k)
                  ((outcomePayoff M c (.dual q)).supplier k - D.supplier k)
                  ((outcomePayoff M cc (.dual b.dual)).buyer - D.buyer) := by
                unfold nashProduct
                exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith [(hpow k).2]))
                  (Real.rpow_nonneg (by linarith) _)
              _ ≤ _ := hkey
          have hnewbase : ∀ k (p : Payment) (S : ℝ), Admissible M (some p) k →
              ∃ (c : Contracts) (pc : Payment), c k = some pc ∧
                pc.exclusive = p.exclusive ∧ Admissible M (some pc) k ∧
                c (other k) = (costPlusOutcome M b x).contracts (other k) ∧
                (outcomePayoff M c (.dual b.dual)).supplier k = S ∧
                (outcomePayoff M c (.dual b.dual)).buyer =
                  (x.payoff M).supplier k + (x.payoff M).buyer - S ∧
                IsDualOrder M c b.dual := by
            intro k p S had
            let pc : Payment := ⟨fun q => M.cost k q + S, p.exclusive⟩
            let c : Contracts := fun j => if j = k then some pc
              else (costPlusOutcome M b x).contracts j
            have hf : c (other k) = (costPlusOutcome M b x).contracts (other k) := by fin_cases k <;> rfl
            have hsp : ∀ q, (outcomePayoff M c (.dual q)).supplier k = S := by
              intro q
              fin_cases k <;> simp [c, pc, outcomePayoff, normalTransfer]
            have hbp : ∀ q, (outcomePayoff M c (.dual q)).buyer =
                chainProfit M q - (x.payoff M).supplier (other k) - S := by
              intro q
              linarith [hnewsum k c q hf, hsp q]
            refine ⟨c, pc, by simp [c], rfl, hadm_ex k p pc rfl had, hf, hsp _, ?_, ?_⟩
            · rw [hbp, ← htotal]
            · refine ⟨?_, ?_⟩
              · fin_cases k <;> simp [Available, c, costPlusOutcome, replacement, hb1, hb2]
              · intro q hq
                rw [hbp, hbp]
                linarith [hmax q ⟨hq.1.le, hq.2.1.le⟩]
          have hnewfrontierEq : ∀ k D y,
              RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) D true y →
              (∀ z, RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) D true z →
                rfStageProduct M k D z ≤ rfStageProduct M k D y) →
              (y.payoff M).supplier k + (y.payoff M).buyer =
                (x.payoff M).supplier k + (x.payoff M).buyer := by
            intro k D y hy hopt
            obtain ⟨p, q, c, hyr, hyo, hcp, had, hcf, ho, hS, hB⟩ := hdecode k _ D y hy
            have hpayy : y.payoff M = outcomePayoff M c (.dual q) := by
              simp only [TradeOutcome.payoff, hyr, hyo, htradPay]
            rw [hpayy]
            have hle : (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer ≤
                (x.payoff M).supplier k + (x.payoff M).buyer := by
              rw [hnewsum k c q hcf, htotal]
              linarith [hmax q ⟨ho.1.1.le, ho.1.2.1.le⟩]
            apply le_antisymm hle
            by_contra hn
            let ε := ((x.payoff M).supplier k + (x.payoff M).buyer -
              ((outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer)) / 2
            have he : 0 < ε := by dsimp [ε]; linarith
            obtain ⟨cn, pn, hpn, hpen, hadpn, hfn, hspn, hbpn, hon⟩ :=
              hnewbase k p ((outcomePayoff M c (.dual q)).supplier k + ε) had
            have hbpn' : (outcomePayoff M cn (.dual b.dual)).buyer =
                (outcomePayoff M c (.dual q)).buyer + ε := by
              rw [hbpn]; dsimp [ε]; ring
            have hcn := hmkStage k ((costPlusOutcome M b x).contracts (other k)) cn b.dual D
              ⟨pn, hpn, hadpn⟩ hfn hon (by rw [hspn]; linarith) (by rw [hbpn']; linarith)
            have hh := hopt _ hcn
            unfold rfStageProduct at hh
            change nashProduct _ ((tradePayoff M (ordinaryRights cn) (.dual b.dual)).supplier k - _)
              ((tradePayoff M (ordinaryRights cn) (.dual b.dual)).buyer - _) ≤ _ at hh
            rw [htradPay, hpayy, hspn, hbpn'] at hh
            have hlt := hnash_strict ((outcomePayoff M c (.dual q)).supplier k - D.supplier k)
              ((outcomePayoff M c (.dual q)).buyer - D.buyer)
              ((outcomePayoff M c (.dual q)).supplier k + ε - D.supplier k)
              ((outcomePayoff M c (.dual q)).buyer + ε - D.buyer) k
              (by linarith) (by linarith) (by linarith) (by linarith)
            exact (not_lt_of_ge hh) hlt
          have hvalidHigh : ∀ k (c cy : Contracts) (pc p : Payment) (y : TradeOutcome),
              c k = some pc → cy k = some p → pc.exclusive = p.exclusive →
              Admissible M (some pc) k → c (other k) = x.contracts (other k) →
              y.rights = ordinaryRights cy → ValidTrade M y →
              (x.payoff M).buyer ≤ (y.payoff M).buyer →
              IsDualOrder M c b.dual →
              (outcomePayoff M c (.dual b.dual)).buyer = (y.payoff M).buyer →
              ValidTrade M ⟨ordinaryRights c, .dual b.dual⟩ := by
            intro k c cy pc p y hpc hp he had hf hyr hy hhigh ho hb
            refine ⟨⟨(htradAv _ _).2 ho.1, ?_⟩, ?_⟩
            · intro r hr
              rw [htradPay, htradPay, hb]
              cases r with
              | none =>
                have hh := hvalid.1.2 .none trivial
                change 0 ≤ (x.payoff M).buyer at hh
                exact hh.trans hhigh
              | dual q =>
                exact (ho.2 q ((htradAv _ _).1 hr)).trans_eq hb
              | single j q =>
                have hra := (htradAv _ _).1 hr
                by_cases hj : j = k
                · subst j
                  have hyav : tradeAvailable y.rights (.single k q) := by
                    rw [hyr]
                    exact (htradAv _ _).2 ⟨hra.1, by simp [hp]⟩
                  have hh := hy.1.2 (.single k q) hyav
                  change (tradePayoff M y.rights (.single k q)).buyer ≤ (y.payoff M).buyer at hh
                  have heq : (outcomePayoff M c (.single k q)).buyer =
                      (tradePayoff M y.rights (.single k q)).buyer := by
                    rw [hyr, htradPay]
                    simp [outcomePayoff, hpc, hp, exclusiveTransfer, he]
                  rwa [heq]
                · have hjo : j = other k := by fin_cases k <;> fin_cases j <;> simp at hj <;> rfl
                  subst j
                  have hh := hvalid.1.2 (.single (other k) q) ⟨hra.1, by simpa [hf] using hra.2⟩
                  change (outcomePayoff M x.contracts (.single (other k) q)).buyer ≤ (x.payoff M).buyer at hh
                  have heq : (outcomePayoff M c (.single (other k) q)).buyer =
                      (outcomePayoff M x.contracts (.single (other k) q)).buyer := by simp [outcomePayoff, hf]
                  rw [heq]
                  exact hh.trans hhigh
            · intro j d hd
              have hd' : c j = d := ProcurementRight.contract.inj hd
              rw [← hd']
              by_cases hj : j = k
              · subst j; rw [hpc]; exact had
              · have hjo : j = other k := by fin_cases k <;> fin_cases j <;> simp at hj <;> rfl
                subst j; rw [hf]
                exact ⟨_, hvalid.2 (other k)⟩
          have hrevDual : ∀ k (E : Payoff) y,
              (∀ (c : Contracts) q (p : Payment), c k = some p → Admissible M (some p) k →
                c (other k) = x.contracts (other k) → IsDualOrder M c q →
                (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer ≤
                  (x.payoff M).supplier k + (x.payoff M).buyer) →
              ValidTrade M y → (x.payoff M).buyer ≤ (y.payoff M).buyer →
              RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) E true y →
              (∀ z, RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) E true z →
                rfStageProduct M k E z ≤ rfStageProduct M k E y) →
              ∃ yo, ValidTrade M yo ∧
                RFStageCandidate M k (.contract (x.contracts (other k))) E true yo ∧
                (∀ z, RFStageCandidate M k (.contract (x.contracts (other k))) E true z →
                  rfStageProduct M k E z ≤ rfStageProduct M k E yo) ∧
                (yo.payoff M).buyer = (y.payoff M).buyer := by
            intro k E y hfront hyvalid hhigh hy hopt
            obtain ⟨p, q, c, hyr, hyo, hcp, had, hcf, ho, hS, hB⟩ := hdecode k _ E y hy
            have hpy : y.payoff M = outcomePayoff M c (.dual q) := by
              simp only [TradeOutcome.payoff, hyr, hyo, htradPay]
            have hbudget := hnewfrontierEq k E y hy hopt
            obtain ⟨cb, pb, hpb, hadb, hexbp, hfb, hpdb, hob⟩ := hbase k p had
            let δ := (y.payoff M).supplier k - (x.payoff M).supplier k
            obtain ⟨cc, hfc, ⟨pc, hpc, hec⟩, hpdc, hoc⟩ := hshift k cb pb δ hpb
            have hxpb : outcomePayoff M cb (.dual b.dual) = x.payoff M := by
              rw [hpdb]; simp [ContractOutcome.payoff, hord]
            have hsp : (outcomePayoff M cc (.dual b.dual)).supplier k = (y.payoff M).supplier k := by
              rw [(hpdc _).2, hxpb]; dsimp [δ]; ring
            have hbp : (outcomePayoff M cc (.dual b.dual)).buyer = (y.payoff M).buyer := by
              rw [(hpdc _).1, hxpb]; dsimp [δ]; linarith only [hbudget]
            have hadpc := hadm_ex k pb pc hec.symm hadb
            have hcc := hmkStage k (x.contracts (other k)) cc b.dual E
              ⟨pc, hpc, hadpc⟩ (hfc.trans hfb) (hoc _ hob)
              (by rw [hsp, hpy]; exact hS) (by rw [hbp, hpy]; exact hB)
            let yo : TradeOutcome := ⟨ordinaryRights cc, .dual b.dual⟩
            have hpyo : yo.payoff M = outcomePayoff M cc (.dual b.dual) := htradPay _ _
            refine ⟨yo, hvalidHigh k cc c pc p y hpc hcp (hec.trans hexbp) hadpc (hfc.trans hfb)
              hyr hyvalid hhigh (hoc _ hob) hbp, hcc, ?_, ?_⟩
            · intro z hz
              obtain ⟨pz, qz, cz, hzr, hzo, hczp, hadz, hczf, hoz, hSz, hBz⟩ := hdecode k _ E z hz
              have hpz : z.payoff M = outcomePayoff M cz (.dual qz) := by
                simp only [TradeOutcome.payoff, hzr, hzo, htradPay]
              have hbound := hfront cz qz pz hczp hadz hczf hoz
              obtain ⟨cn, pn, hpn, hpen, hadpn, hfn, hspn, hbpn, hon⟩ :=
                hnewbase k pz ((z.payoff M).supplier k) hadz
              have hBzn : (z.payoff M).buyer ≤ (outcomePayoff M cn (.dual b.dual)).buyer := by
                rw [hbpn, hpz]; linarith only [hbound]
              have hcn := hmkStage k ((costPlusOutcome M b x).contracts (other k)) cn b.dual E
                ⟨pn, hpn, hadpn⟩ hfn hon (by rw [hspn, hpz]; exact hSz)
                (by rw [hpz] at hBzn; exact hBz.trans hBzn)
              have hh := hopt _ hcn
              unfold rfStageProduct at hh ⊢
              change nashProduct _ ((tradePayoff M (ordinaryRights cn) (.dual b.dual)).supplier k - _)
                ((tradePayoff M (ordinaryRights cn) (.dual b.dual)).buyer - _) ≤ _ at hh
              rw [htradPay, hspn] at hh
              rw [hpyo, hsp, hbp]
              calc
                _ ≤ nashProduct (M.power k) ((z.payoff M).supplier k - E.supplier k)
                    ((outcomePayoff M cn (.dual b.dual)).buyer - E.buyer) := by
                  unfold nashProduct
                  exact mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow (by rw [hpz]; linarith only [hBz])
                      (by linarith only [hBzn]) (by linarith only [(hpow k).2]))
                    (Real.rpow_nonneg (by rw [hpz]; linarith only [hSz]) _)
                _ ≤ _ := hh
            · rw [hpyo, hbp]
          have hsingleReplace : ∀ k (fixed fixed' : Contract) (E : Payoff) (y : TradeOutcome)
              (p pc : Payment), RFStageCandidate M k (.contract fixed) E false y →
              y.rights k = .contract (some p) → pc.exclusive = p.exclusive →
              Admissible M (some pc) k →
              let c : Contracts := fun j => if j = k then some pc else fixed'
              RFStageCandidate M k (.contract fixed') E false ⟨ordinaryRights c, y.order⟩ ∧
                (⟨ordinaryRights c, y.order⟩ : TradeOutcome).payoff M = y.payoff M := by
            intro k fixed fixed' E y p pc hc hp he had
            obtain ⟨q, hq⟩ := hc.2.2.1
            let co : Contracts := fun j => if j = k then some p else fixed
            let c : Contracts := fun j => if j = k then some pc else fixed'
            have hyr : y.rights = ordinaryRights co := by
              have hf := hc.2.1
              funext j
              fin_cases k <;> fin_cases j <;> simp at hp hf <;>
                simpa [ordinaryRights, co, other] using (by assumption : _)
            have hpeq : ∀ z, tradePayoff M (ordinaryRights c) (.single k z) =
                tradePayoff M y.rights (.single k z) := by
              intro z
              rw [hyr, htradPay, htradPay]
              simp [outcomePayoff, c, co, exclusiveTransfer, he]
            have hpays : (⟨ordinaryRights c, y.order⟩ : TradeOutcome).payoff M = y.payoff M := by
              change tradePayoff M (ordinaryRights c) y.order = tradePayoff M y.rights y.order
              rw [hq, hpeq]
            refine ⟨⟨⟨pc, by simp [ordinaryRights, c], had⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩, hpays⟩
            · fin_cases k <;> rfl
            · exact ⟨q, hq⟩
            · rw [hq]
              exact (htradAv _ _).2 ⟨by have hh := hc.2.2.2.1.1.1; simpa [hq, Sourcing.positive] using hh,
                by simp [c]⟩
            · intro r hr hra
              rw [hq] at hr ⊢
              cases r with
              | none => cases hr
              | dual z => cases hr
              | single j z =>
                have hj : k = j := hr
                subst j
                rw [hpeq, hpeq]
                have hh := hc.2.2.2.1.2 (.single k z)
                  (by simpa only [hq] using (show SameSourcingBranch (.single k q) (.single k z) from rfl))
                  (by rw [hyr]; exact (htradAv _ _).2 ⟨((htradAv _ _).1 hra).1, by simp [co]⟩)
                simpa only [hq] using hh
            · change E.supplier k ≤ ((⟨ordinaryRights c, y.order⟩ : TradeOutcome).payoff M).supplier k
              rw [hpays]; exact hc.2.2.2.2.1
            · change E.buyer ≤ ((⟨ordinaryRights c, y.order⟩ : TradeOutcome).payoff M).buyer
              rw [hpays]; exact hc.2.2.2.2.2
          have hrevSingle : ∀ k (E : Payoff) y,
              ValidTrade M y → (x.payoff M).buyer ≤ (y.payoff M).buyer →
              RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) E false y →
              (∀ z, RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) E false z →
                rfStageProduct M k E z ≤ rfStageProduct M k E y) →
              ∃ yo, ValidTrade M yo ∧
                RFStageCandidate M k (.contract (x.contracts (other k))) E false yo ∧
                (∀ z, RFStageCandidate M k (.contract (x.contracts (other k))) E false z →
                  rfStageProduct M k E z ≤ rfStageProduct M k E yo) ∧
                (yo.payoff M).buyer = (y.payoff M).buyer := by
            intro k E y hv hhigh hy hopt
            obtain ⟨p, hp, had⟩ := hy.1
            let cy : Contracts := fun j => if j = k then some p else (costPlusOutcome M b x).contracts (other k)
            have hyr : y.rights = ordinaryRights cy := by
              have hf := hy.2.1
              funext j
              fin_cases k <;> fin_cases j <;> simp at hp hf <;>
                simpa [ordinaryRights, cy, other] using (by assumption : _)
            obtain ⟨cb, pb, hpb, hadb, hexbp, hfb, hpdb, hob⟩ := hbase k p had
            let δ := (x.payoff M).buyer - (y.payoff M).buyer
            obtain ⟨cc, hfc, ⟨pc, hpc, hec⟩, hpdc, hoc⟩ := hshift k cb pb δ hpb
            have hxpb : outcomePayoff M cb (.dual b.dual) = x.payoff M := by
              rw [hpdb]; simp [ContractOutcome.payoff, hord]
            have hbp : (outcomePayoff M cc (.dual b.dual)).buyer = (y.payoff M).buyer := by
              rw [(hpdc _).1, hxpb]; dsimp [δ]; ring
            have hadpc := hadm_ex k pb pc hec.symm hadb
            have hccEq : (fun j => if j = k then some pc else x.contracts (other k)) = cc := by
              funext j
              have hf := hfc.trans hfb
              fin_cases k <;> fin_cases j <;> simp [other] at hpc hf ⊢ <;> first | exact hpc.symm | exact hf.symm
            have hh := hsingleReplace k ((costPlusOutcome M b x).contracts (other k))
              (x.contracts (other k)) E y p pc hy hp (hec.trans hexbp) hadpc
            change RFStageCandidate _ _ _ _ _ ⟨ordinaryRights (fun j => if j = k then some pc else _), _⟩ ∧ _ at hh
            rw [hccEq] at hh
            obtain ⟨hco, hpayco⟩ := hh
            let yo : TradeOutcome := ⟨ordinaryRights cc, y.order⟩
            have hvalidD := hvalidHigh k cc cy pc p y hpc (by simp [cy]) (hec.trans hexbp)
              hadpc (hfc.trans hfb) hyr hv hhigh (hoc _ hob) hbp
            have hvyo : ValidTrade M yo := by
              refine ⟨⟨hco.2.2.2.1.1, ?_⟩, hvalidD.2⟩
              intro r hr
              have hh := hvalidD.1.2 r hr
              change _ ≤ (tradePayoff M (ordinaryRights cc) (.dual b.dual)).buyer at hh
              simp only [htradPay] at hh
              rw [hbp] at hh
              change _ ≤ (yo.payoff M).buyer
              change _ ≤ ((⟨ordinaryRights cc, y.order⟩ : TradeOutcome).payoff M).buyer
              rw [hpayco]
              simpa only [yo, htradPay] using hh
            refine ⟨yo, hvyo, hco, ?_, congrArg Payoff.buyer hpayco⟩
            intro z hz
            obtain ⟨pz, hpz, hadz⟩ := hz.1
            obtain ⟨hzn, hpzn⟩ := hsingleReplace k (x.contracts (other k))
              ((costPlusOutcome M b x).contracts (other k)) E z pz pz hz hpz rfl hadz
            have hh := hopt _ hzn
            unfold rfStageProduct at hh ⊢
            rw [hpzn] at hh
            change _ ≤ nashProduct _ (((⟨ordinaryRights cc, y.order⟩ : TradeOutcome).payoff M).supplier k - _)
              (((⟨ordinaryRights cc, y.order⟩ : TradeOutcome).payoff M).buyer - _)
            rw [hpayco]
            exact hh
          have hfeas : ∀ k (E : Payoff) dual y,
              (∀ (c : Contracts) q (p : Payment), c k = some p → Admissible M (some p) k →
                c (other k) = x.contracts (other k) → IsDualOrder M c q →
                (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer ≤
                  (x.payoff M).supplier k + (x.payoff M).buyer) →
              RFStageCandidate M k (.contract (x.contracts (other k))) E dual y →
              ∃ yn, RFStageCandidate M k (.contract ((costPlusOutcome M b x).contracts (other k))) E dual yn := by
            intro k E dual y hfront hy
            cases dual with
            | false =>
              obtain ⟨p, hp, had⟩ := hy.1
              exact ⟨_, (hsingleReplace k _ _ E y p p hy hp rfl had).1⟩
            | true =>
              obtain ⟨p, q, c, hyr, hyo, hcp, had, hcf, ho, hS, hB⟩ := hdecode k _ E y hy
              have hbound := hfront c q p hcp had hcf ho
              obtain ⟨cn, pn, hpn, hpen, hadpn, hfn, hspn, hbpn, hon⟩ :=
                hnewbase k p ((outcomePayoff M c (.dual q)).supplier k) had
              refine ⟨_, hmkStage k _ cn b.dual E ⟨pn, hpn, hadpn⟩ hfn hon ?_ ?_⟩
              · rwa [hspn]
              · rw [hbpn]; linarith only [hbound, hB]
          have hfall : ∀ (u : ContractOutcome), ValidOutcome M u → u.order = .dual b.dual →
              ∀ k (a : Bool),
              let rights : Rights := fun j => if j = k then quoteRight M b t k a
                else .contract (u.contracts (other k))
              let V := if a then
                max ((u.payoff M).buyer + (u.payoff M).supplier k)
                  (exclusiveProfit M k (solicitedQuantity b k)) - t k
                else (exclusivePayoff M (u.contracts (other k)) (other k) (u.exclusiveOrder (other k))).buyer
              (∃ s, IsTradeOrder M rights s) ∧
              ∀ s, IsTradeOrder M rights s →
                (tradePayoff M rights s).buyer = V ∧
                (tradePayoff M rights s).supplier k = if a then t k else 0 := by
            intro u hu huo k a
            dsimp only
            have hQ : 0 < solicitedQuantity b k := by fin_cases k <;> assumption
            have huoav : Available u.contracts (.dual b.dual) := by simpa [huo] using hu.1.1
            cases a with
            | false =>
              let c : Contracts := fun j => if j = other k then u.contracts (other k) else none
              have heq : (fun j => if j = k then quoteRight M b t k false else
                  ProcurementRight.contract (u.contracts (other k))) = ordinaryRights c := by
                funext j; fin_cases k <;> fin_cases j <;> rfl
              rw [heq]
              have hs := (hu.2 (other k)).1
              have hsform := hs.1
              have hcb : ∀ r, (r = .none ∨ ∃ z, r = .single (other k) z) →
                  outcomePayoff M c r = exclusivePayoff M (u.contracts (other k)) (other k) r := by
                intro r hr; rfl
              have hclass : ∀ r, Available c r → r = .none ∨ ∃ z, r = .single (other k) z := by
                intro r hr
                cases r with
                | none => exact Or.inl rfl
                | dual q =>
                  fin_cases k <;> simp [Available, c, other] at hr
                | single j q =>
                  fin_cases k <;> fin_cases j <;> simp [Available, c, other] at hr ⊢
              have hopt : IsTradeOrder M (ordinaryRights c) (u.exclusiveOrder (other k)) := by
                refine ⟨(htradAv _ _).2 hs.2.1, ?_⟩
                intro r hr
                rw [htradPay, htradPay]
                exact hs.2.2 r (hclass r ((htradAv _ _).1 hr)) ((htradAv _ _).1 hr)
              refine ⟨⟨_, hopt⟩, ?_⟩
              intro s hs'
              have hb1 := hs'.2 _ hopt.1
              have hb2 := hopt.2 _ hs'.1
              constructor
              · simp only [htradPay, hcb _ hsform, Bool.false_eq_true, if_false] at hb1 hb2 ⊢
                exact le_antisymm hb2 hb1
              · rw [htradPay]
                rcases hclass s ((htradAv _ _).1 hs'.1) with rfl | ⟨q, rfl⟩
                · rfl
                · fin_cases k <;> simp [outcomePayoff, other]
            | true =>
              let R : Rights := fun j => if j = k then quoteRight M b t k true
                else .contract (u.contracts (other k))
              let A := (u.payoff M).buyer + (u.payoff M).supplier k
              let E := exclusiveProfit M k (solicitedQuantity b k)
              have hdav : tradeAvailable R (.dual b.dual) := by
                fin_cases k <;>
                  simp [tradeAvailable, Sourcing.positive, R, quoteRight, ProcurementRight.permits,
                    quantityFrom, sourcingQuantity, solicitedQuantity, other, hb1, hb2,
                    Fin.forall_fin_two, huoav.2.2.1, huoav.2.2.2]
              have hsav : tradeAvailable R (.single k (solicitedQuantity b k)) := by
                fin_cases k <;>
                  simp [tradeAvailable, Sourcing.positive, R, quoteRight, ProcurementRight.permits,
                    quantityFrom, sourcingQuantity, solicitedQuantity, exclusiveQuantity, other,
                    hb1, hb2, Fin.forall_fin_two]
              have hdp : (tradePayoff M R (.dual b.dual)).buyer = A - t k := by
                dsimp [A, ContractOutcome.payoff]
                rw [huo]
                fin_cases k <;>
                  simp [tradePayoff, R, quoteRight, ProcurementRight.transfer, quantityFrom,
                    sourcingQuantity, solicitedQuantity, other, outcomePayoff] <;> ring
              have hsp : (tradePayoff M R (.single k (solicitedQuantity b k))).buyer = E - t k := by
                fin_cases k <;>
                  simp [tradePayoff, R, quoteRight, ProcurementRight.transfer, quantityFrom,
                    sourcingQuantity, solicitedQuantity, other, exclusiveQuantity, E, exclusiveProfit,
                    chainProfit, hC0] <;> ring
              have hbound : ∀ r, tradeAvailable R r →
                  (tradePayoff M R r).buyer ≤ max A E - t k ∧
                  (tradePayoff M R r).supplier k = t k := by
                intro r hr
                have hown := hr.2 k
                have hfix := hr.2 (other k)
                cases r with
                | none =>
                  fin_cases k <;>
                    simp [R, quoteRight, ProcurementRight.permits, quantityFrom, sourcingQuantity,
                      solicitedQuantity] at hown <;> exfalso <;> linarith only [hown.1, hown.2]
                | dual q =>
                  have hqav : Available u.contracts (.dual q) := by
                    exact ⟨hr.1.1, hr.1.2, huoav.2.2.1, huoav.2.2.2⟩
                  have hbo := hu.1.2 (.dual q) hqav
                  rw [huo] at hbo
                  have hdiffpay : (tradePayoff M R (.dual q)).buyer ≤ A - t k ∧
                      (tradePayoff M R (.dual q)).supplier k = t k := by
                    fin_cases k <;>
                      simp [R, quoteRight, ProcurementRight.permits, quantityFrom, sourcingQuantity,
                        solicitedQuantity] at hown <;>
                      simp [tradePayoff, R, quoteRight, ProcurementRight.transfer, quantityFrom,
                        sourcingQuantity, solicitedQuantity, other, A, ContractOutcome.payoff, huo,
                        outcomePayoff, hown.2] at hbo ⊢ <;> linarith
                  exact ⟨hdiffpay.1.trans (sub_le_sub_right (le_max_left A E) _), hdiffpay.2⟩
                | single j q =>
                  fin_cases k <;> fin_cases j <;>
                    simp [R, quoteRight, ProcurementRight.permits, quantityFrom, sourcingQuantity,
                      exclusiveQuantity, solicitedQuantity] at hown
                  all_goals try { exfalso; linarith only [hown.1, hown.2] }
                  all_goals
                    rcases hown with ⟨hposq, hq⟩
                    subst q
                    have hEE := le_max_right A E
                    dsimp [E, exclusiveProfit, chainProfit, exclusiveQuantity, solicitedQuantity] at hEE
                    simp only [hC0, sub_zero] at hEE
                    simp [tradePayoff, R, quoteRight, ProcurementRight.transfer, quantityFrom,
                      sourcingQuantity, solicitedQuantity, other, exclusiveQuantity, E, exclusiveProfit,
                      chainProfit, hC0]
                    linarith only [hEE]
              obtain ⟨s, hsav', hsp'⟩ : ∃ s, tradeAvailable R s ∧
                  (tradePayoff M R s).buyer = max A E - t k := by
                by_cases he : A ≤ E
                · exact ⟨_, hsav, by rw [hsp, max_eq_right he]⟩
                · exact ⟨_, hdav, by rw [hdp, max_eq_left (le_of_not_ge he)]⟩
              have hso : IsTradeOrder M R s := ⟨hsav', fun r hr => by rw [hsp']; exact (hbound r hr).1⟩
              refine ⟨⟨s, hso⟩, ?_⟩
              intro r hr
              have h1 := hr.2 s hsav'
              rw [hsp'] at h1
              exact ⟨le_antisymm (hbound r hr.1).1 h1, (hbound r hr.1).2⟩
          have hfallSame : ∀ k a s sn,
              IsTradeOrder M (fun j => if j = k then quoteRight M b t k a
                else .contract (x.contracts (other k))) s →
              IsTradeOrder M (fun j => if j = k then quoteRight M b t k a
                else .contract ((costPlusOutcome M b x).contracts (other k))) sn →
              (tradePayoff M (fun j => if j = k then quoteRight M b t k a
                else .contract ((costPlusOutcome M b x).contracts (other k))) sn).buyer =
                (tradePayoff M (fun j => if j = k then quoteRight M b t k a
                else .contract (x.contracts (other k))) s).buyer ∧
              (tradePayoff M (fun j => if j = k then quoteRight M b t k a
                else .contract ((costPlusOutcome M b x).contracts (other k))) sn).supplier k =
                (tradePayoff M (fun j => if j = k then quoteRight M b t k a
                else .contract (x.contracts (other k))) s).supplier k := by
            intro k a s sn hs hsn
            have ho := (hfall x hvalid hord k a).2 s hs
            have hn := (hfall (costPlusOutcome M b x) hnewvalid rfl k a).2 sn hsn
            constructor
            · rw [hn.1, ho.1]
              cases a
              · exact hexb (other k)
              · simp [hpay]
            · exact hn.2.trans ho.2.symm
          have hDcongr : ∀ k (D E : Payoff), D.buyer = E.buyer → D.supplier k = E.supplier k →
              (∀ fixed dual y, RFStageCandidate M k fixed D dual y ↔ RFStageCandidate M k fixed E dual y) ∧
              (∀ y, rfStageProduct M k D y = rfStageProduct M k E y) := by
            intro k D E hb hs
            constructor
            · intro fixed dual y
              simp only [RFStageCandidate, hb, hs]
            · intro y
              simp only [rfStageProduct, hb, hs]
          have hstageReverse : ∀ k a y,
              (∀ (c : Contracts) q (p : Payment), c k = some p → Admissible M (some p) k →
                c (other k) = x.contracts (other k) → IsDualOrder M c q →
                (outcomePayoff M c (.dual q)).supplier k + (outcomePayoff M c (.dual q)).buyer ≤
                  (x.payoff M).supplier k + (x.payoff M).buyer) →
              IsRFStageSolution M k (.contract ((costPlusOutcome M b x).contracts (other k)))
                (quoteRight M b t k a) y →
              (x.payoff M).buyer ≤ (y.payoff M).buyer →
              ∃ yo, IsRFStageSolution M k (.contract (x.contracts (other k)))
                (quoteRight M b t k a) yo ∧ (yo.payoff M).buyer = (y.payoff M).buyer := by
            intro k a y hfront ⟨sn, hsn, hcase⟩ hhigh
            obtain ⟨so, hso⟩ := (hfall x hvalid hord k a).1
            have hsame := hfallSame k a so sn hso hsn
            let En : Payoff := tradePayoff M (fun j => if j = k then quoteRight M b t k a
              else .contract ((costPlusOutcome M b x).contracts (other k))) sn
            let Eo : Payoff := tradePayoff M (fun j => if j = k then quoteRight M b t k a
              else .contract (x.contracts (other k))) so
            have heq := hDcongr k En Eo hsame.1 hsame.2
            rcases hcase with ⟨hyv, dual, hyc, hyo⟩ | ⟨hn, hy⟩
            · have hrecover : ∃ yo, ValidTrade M yo ∧
                  RFStageCandidate M k (.contract (x.contracts (other k))) En dual yo ∧
                  (∀ z, RFStageCandidate M k (.contract (x.contracts (other k))) En dual z →
                    rfStageProduct M k En z ≤ rfStageProduct M k En yo) ∧
                  (yo.payoff M).buyer = (y.payoff M).buyer := by
                cases dual with
                | false => exact hrevSingle k En y hyv hhigh hyc hyo
                | true => exact hrevDual k En y hfront hyv hhigh hyc hyo
              obtain ⟨yo, hyv', hyc', hyo', hby⟩ := hrecover
              refine ⟨yo, ⟨so, hso, Or.inl ⟨hyv', dual, (heq.1 _ _ _).1 hyc', ?_⟩⟩, hby⟩
              intro z hz
              have hh := hyo' z ((heq.1 _ _ _).2 hz)
              simpa only [heq.2, Eo, TradeOutcome.payoff] using hh
            · let yo : TradeOutcome := ⟨fun j => if j = k then quoteRight M b t k a
                else .contract (x.contracts (other k)), so⟩
              refine ⟨yo, ⟨so, hso, Or.inr ⟨?_, rfl⟩⟩, ?_⟩
              · rintro ⟨dual, z, hz⟩
                have hzn := (heq.1 _ _ _).2 hz
                obtain ⟨zn, hzn'⟩ := hfeas k En dual z hfront hzn
                exact hn ⟨dual, zn, hzn'⟩
              · rw [hy]
                exact hsame.1.symm
          have hother : ∀ k, other (other k) = k := by intro k; fin_cases k <;> rfl
          have hfixedFollower : ∀ leader fixed y, RFxFollower M b t leader fixed y →
              y.rights leader = fixed := by
            intro leader fixed y hy
            obtain ⟨a, ⟨s, hs, hcase⟩, hchoose, htie⟩ := hy
            rcases hcase with ⟨hv, dual, hc, ho⟩ | ⟨hno, hy⟩
            · have hh := hc.2.1
              rwa [hother] at hh
            · rw [hy]
              simp only
              have hn : leader ≠ other leader := by fin_cases leader <;> decide
              simp [hn]
          have hquote_ne : ∀ k a p, quoteRight M b t k a ≠ .contract (some p) := by
            intro k a p
            cases a <;> simp [quoteRight]
          obtain ⟨htnonneg, F, hF, a, ⟨z, hFz, hleader⟩, hbuyermax⟩ := hx.2
          have hzfixed := hfixedFollower i _ z ((hF i).1 _ _ hFz)
          have hFx : F i (x.trade.rights i) x.trade := by
            rcases hleader with ⟨dual, hc, ho⟩ | ⟨hn, hxz⟩
            · exact hc.2.1
            · exfalso
              obtain ⟨p, hp⟩ := hsome i
              rw [← hxz] at hzfixed
              change ProcurementRight.contract (x.contracts i) = _ at hzfixed
              rw [hp] at hzfixed
              exact hquote_ne i a p hzfixed.symm
          obtain ⟨af, ⟨sf, hsf, hstage⟩, hchoose, htie⟩ := (hF i).1 _ _ hFx
          let D : Payoff := tradePayoff M (fun k => if k = other i then quoteRight M b t (other i) af
            else .contract (x.contracts i)) sf
          have hsource :
              RFStageCandidate M (other i) (.contract (x.contracts i)) D true x.trade ∧
              (∀ y, RFStageCandidate M (other i) (.contract (x.contracts i)) D true y →
                rfStageProduct M (other i) D y ≤ rfStageProduct M (other i) D x.trade) := by
            rcases hstage with ⟨hv, dual, hc, ho⟩ | ⟨hn, hxz⟩
            · cases dual
              · have hh := hc.2.2.1
                simp only [Bool.false_eq_true, if_false] at hh
                obtain ⟨q, hq⟩ := hh
                change x.order = _ at hq
                rw [hord] at hq
                cases hq
              · exact ⟨hc, ho⟩
            · exfalso
              obtain ⟨p, hp⟩ := hsome (other i)
              have hh := congrArg (fun y : TradeOutcome => y.rights (other i)) hxz
              change ProcurementRight.contract (x.contracts (other i)) = _ at hh
              rw [hp] at hh
              simp only [if_pos rfl] at hh
              exact hquote_ne (other i) af p hh.symm
          obtain ⟨hDcan, hDopt⟩ := hsource
          have hfrontier := hfront (other i) D (by simpa [hother] using hDcan)
            (by simpa [hother] using hDopt)
          obtain ⟨sn, hsn⟩ := (hfall (costPlusOutcome M b x) hnewvalid rfl (other i) af).1
          have hsf' : IsTradeOrder M (fun j => if j = other i then quoteRight M b t (other i) af
              else .contract (x.contracts (other (other i)))) sf := by simpa only [hother, ContractOutcome.trade, ordinaryRights] using hsf
          have hsame := hfallSame (other i) af sf sn hsf' hsn
          let Dn : Payoff := tradePayoff M (fun j => if j = other i then quoteRight M b t (other i) af
            else .contract ((costPlusOutcome M b x).contracts i)) sn
          have hdeq := hDcongr (other i) D Dn (by simpa only [D, Dn, hother] using hsame.1.symm)
            (by simpa only [D, Dn, hother] using hsame.2.symm)
          have htrans := htransferOpt (other i) D (by simpa only [hother] using hDcan)
            (by simpa only [hother] using hDopt)
          have hnewStageSelected : IsRFStageSolution M (other i)
              (.contract ((costPlusOutcome M b x).contracts i))
              (quoteRight M b t (other i) af) (costPlusOutcome M b x).trade := by
            refine ⟨sn, by simpa only [hother] using hsn, Or.inl ⟨hnewTrade, true, ?_, ?_⟩⟩
            · exact (hdeq.1 _ _ _).1 (by simpa only [hother] using htrans.1)
            · intro y hy
              have hhy := (hdeq.1 _ _ _).2 hy
              have hh := htrans.2 y (by simpa only [hother] using hhy)
              simpa only [hdeq.2, Dn, TradeOutcome.payoff] using hh
          have hnewFollower : RFxFollower M b t i
              (.contract ((costPlusOutcome M b x).contracts i)) (costPlusOutcome M b x).trade := by
            refine ⟨af, hnewStageSelected, ?_, ?_⟩
            · intro a y hy
              rw [hntp]
              by_contra hn
              have hh : (x.payoff M).buyer ≤ (y.payoff M).buyer := le_of_lt (lt_of_not_ge hn)
              obtain ⟨yo, hyo, hpayyo⟩ := hstageReverse (other i) a y hfrontier
                (by simpa only [hother] using hy) hh
              have hle := hchoose a yo (by simpa only [hother, ContractOutcome.trade, ordinaryRights] using hyo)
              rw [htp, hpayyo] at hle
              exact hn hle
            · intro haf y hy
              rw [hntp]
              by_contra hn
              obtain ⟨yo, hyo, hpayyo⟩ := hstageReverse (other i) true y hfrontier
                (by simpa only [hother] using hy) (le_of_not_gt hn)
              have hle := htie haf yo (by simpa only [hother, ContractOutcome.trade, ordinaryRights] using hyo)
              rw [htp, hpayyo] at hle
              exact hn hle
          have hFollowerBuyerUnique : ∀ leader fixed y w,
              RFxFollower M b t leader fixed y → RFxFollower M b t leader fixed w →
              (y.payoff M).buyer = (w.payoff M).buyer := by
            intro leader fixed y w ⟨ay, hsy, hcy, hty⟩ ⟨aw, hsw, hcw, htw⟩
            exact le_antisymm (hcw ay y hsy) (hcy aw w hsw)
          have hSnonneg : 0 ≤ (x.payoff M).supplier (other i) := by
            have hs := hDcan.2.2.2.2.1
            rw [htp] at hs
            have hdf := ((hfall x hvalid hord (other i) af).2 sf hsf').2
            have hd : 0 ≤ D.supplier (other i) := by
              change 0 ≤ (tradePayoff M _ sf).supplier (other i)
              simp only [hother] at hdf
              rw [hdf]
              cases af <;> simp [htnonneg]
            exact hd.trans hs
          have hrejectCan : ∀ s,
              IsTradeOrder M (fun j => if j = other i then quoteRight M b t (other i) false
                else .contract ((costPlusOutcome M b x).contracts i)) s →
              RFStageCandidate M (other i) (.contract ((costPlusOutcome M b x).contracts i))
                (tradePayoff M (fun j => if j = other i then quoteRight M b t (other i) false
                else .contract ((costPlusOutcome M b x).contracts i)) s) true (costPlusOutcome M b x).trade := by
            intro s hs
            have hfs := (hfall (costPlusOutcome M b x) hnewvalid rfl (other i) false).2 s
              (by simpa only [hother] using hs)
            simp only [hother, Bool.false_eq_true, if_false] at hfs
            apply hmkStage
            · exact ⟨_, rfl, ⟨_, hnewvalid.2 (other i)⟩⟩
            · simp only [hother]
            · exact ⟨hnewvalid.1.1, fun r hr => hnewvalid.1.2 _ hr⟩
            · change (tradePayoff M _ s).supplier (other i) ≤ ((costPlusOutcome M b x).payoff M).supplier (other i)
              rw [hfs.2, hpay]; exact hSnonneg
            · change (tradePayoff M _ s).buyer ≤ ((costPlusOutcome M b x).payoff M).buyer
              rw [hfs.1, hpay, hexb]
              exact hBle i
          have hnewNode : ∀ y, RFxFollower M b t i
              (.contract ((costPlusOutcome M b x).contracts i)) y →
              (y.payoff M).buyer = (x.payoff M).buyer ∧
              (∀ q, y.order = .dual q → (y.payoff M).supplier i = (x.payoff M).supplier i) ∧
              (∀ q, y.order ≠ .single i q) := by
            intro y hy
            have hb := hFollowerBuyerUnique i _ y _ hy hnewFollower
            rw [hntp] at hb
            have hf := hfixedFollower i _ y hy
            refine ⟨hb, ?_, ?_⟩
            · intro q hq
              change (tradePayoff M y.rights y.order).supplier i = _
              rw [hq]
              fin_cases i <;>
                simp [tradePayoff, quantityFrom, sourcingQuantity] at hf ⊢ <;>
                simp [hf, ProcurementRight.transfer, quantityFrom, sourcingQuantity,
                  costPlusOutcome, replacement, normalTransfer]
            · intro q hq
              obtain ⟨a, ⟨s, hs, hcase⟩, hchoose, htie⟩ := hy
              rcases hcase with ⟨hv, dual, hc, ho⟩ | ⟨hn, heq⟩
              · cases dual
                · obtain ⟨z, hz⟩ := hc.2.2.1
                  rw [hq] at hz
                  have hh := (Sourcing.single.inj hz).1
                  fin_cases i <;> simp [other] at hh
                · obtain ⟨z, hz⟩ := hc.2.2.1
                  rw [hq] at hz
                  cases hz
              · cases a with
                | false => exact hn ⟨true, _, hrejectCan s hs⟩
                | true =>
                  have hh := hs.1.2 (other i)
                  have hso : s = .single i q := by
                    have hh := congrArg TradeOutcome.order heq
                    exact hh.symm.trans hq
                  rw [hso] at hh
                  fin_cases i <;>
                    simp [quoteRight, ProcurementRight.permits, quantityFrom, sourcingQuantity,
                      exclusiveQuantity, solicitedQuantity, other] at hh <;>
                    linarith only [hh.1, hh.2]
          let xn := (costPlusOutcome M b x).trade
          let F' : Fin 2 → ProcurementRight → TradeOutcome → Prop := fun j d y =>
            if j = i ∧ d = xn.rights i then y = xn else F j d y
          have hquoteNew : ∀ j a, quoteRight M b t j a ≠ xn.rights i := by
            intro j a
            cases a <;> simp [xn, ContractOutcome.trade, ordinaryRights, costPlusOutcome, replacement, quoteRight]
          have hFquote : ∀ j a y, F' j (quoteRight M b t j a) y ↔ F j (quoteRight M b t j a) y := by
            intro j a y
            simp [F', hquoteNew]
          have hFnew : F' i (xn.rights i) xn := by simp [F']
          have hFpolicy : ∀ j, RFContinuationPolicy M b t j (F' j) := by
            intro j
            refine ⟨?_, ?_, ?_⟩
            · intro d y hy
              by_cases hd : j = i ∧ d = xn.rights i
              · simp only [F', hd, if_true] at hy
                rcases hd with ⟨rfl, rfl⟩
                subst y
                exact hnewFollower
              · simp only [F', hd, if_false] at hy
                exact (hF j).1 d y hy
            · intro d hd
              by_cases hh : j = i ∧ d = xn.rights i
              · exact ⟨xn, by simp [F', hh]⟩
              · obtain ⟨y, hy⟩ := (hF j).2.1 d hd
                exact ⟨y, by simp only [F', hh, if_false]; exact hy⟩
            · intro d y w hy hw
              by_cases hh : j = i ∧ d = xn.rights i
              · simp only [F', hh, if_true] at hy hw
                exact hy.trans hw.symm
              · simp only [F', hh, if_false] at hy hw
                exact (hF j).2.2 d y w hy hw
          have hcanNew : ∀ (E : Payoff) dual y,
              RFLeaderCandidate M i (F' i) E dual y →
              y = xn ∨ RFLeaderCandidate M i (F i) E dual y := by
            intro E dual y hy
            by_cases hd : y.rights i = xn.rights i
            · left
              have hh := hy.2.1
              simpa [F', hd] using hh
            · right
              refine ⟨hy.1, ?_, hy.2.2⟩
              have hh := hy.2.1
              simpa [F', hd] using hh
          have hcanMove : ∀ (E : Payoff) dual y,
              RFLeaderCandidate M i (F i) E dual y →
              ∃ w, RFLeaderCandidate M i (F' i) E dual w ∧
                rfStageProduct M i E y = rfStageProduct M i E w := by
            intro E dual y hy
            by_cases hd : y.rights i = xn.rights i
            · have hfy := (hF i).1 _ _ hy.2.1
              rw [hd] at hfy
              have hnode := hnewNode y hfy
              cases dual with
              | false =>
                obtain ⟨q, hq⟩ := hy.2.2.1
                exact False.elim (hnode.2.2 q hq)
              | true =>
                obtain ⟨q, hq⟩ := hy.2.2.1
                have hsp := hnode.2.1 q hq
                refine ⟨xn, ⟨?_, hFnew, ⟨b.dual, rfl⟩, ?_, ?_⟩, ?_⟩
                · exact ⟨_, rfl, ⟨_, hnewvalid.2 i⟩⟩
                · change E.supplier i ≤ ((costPlusOutcome M b x).trade.payoff M).supplier i
                  rw [hntp, ← hsp]
                  exact hy.2.2.2.1
                · change E.buyer ≤ ((costPlusOutcome M b x).trade.payoff M).buyer
                  rw [hntp, ← hnode.1]
                  exact hy.2.2.2.2
                · unfold rfStageProduct
                  change nashProduct _ ((y.payoff M).supplier i - _) ((y.payoff M).buyer - _) =
                    nashProduct _ (((costPlusOutcome M b x).trade.payoff M).supplier i - _)
                      (((costPlusOutcome M b x).trade.payoff M).buyer - _)
                  rw [hntp, hsp, hnode.1]
            · refine ⟨y, ⟨hy.1, ?_, hy.2.2⟩, rfl⟩
              simp only [F', hd, and_false, if_false]
              exact hy.2.1
          have hleaderSource : RFLeaderCandidate M i (F i) (z.payoff M) true x.trade ∧
              (∀ y, RFLeaderCandidate M i (F i) (z.payoff M) true y →
                rfStageProduct M i (z.payoff M) y ≤ rfStageProduct M i (z.payoff M) x.trade) := by
            rcases hleader with ⟨dual, hcan, hopt⟩ | ⟨hn, hxz⟩
            · cases dual with
              | false =>
                obtain ⟨q, hq⟩ := hcan.2.2.1
                change x.order = _ at hq
                rw [hord] at hq
                cases hq
              | true => exact ⟨hcan, hopt⟩
            · exfalso
              obtain ⟨p, hp⟩ := hsome i
              rw [← hxz] at hzfixed
              change ProcurementRight.contract (x.contracts i) = _ at hzfixed
              rw [hp] at hzfixed
              exact hquote_ne i a p hzfixed.symm
          have hleadNew : RFxLeader M b t i (F' i) a xn := by
            refine ⟨z, (hFquote i a z).2 hFz, Or.inl ⟨true, ?_, ?_⟩⟩
            · refine ⟨⟨_, rfl, ⟨_, hnewvalid.2 i⟩⟩, hFnew, ⟨b.dual, rfl⟩, ?_, ?_⟩
              · change _ ≤ ((costPlusOutcome M b x).trade.payoff M).supplier i
                rw [hntp, ← htp]
                exact hleaderSource.1.2.2.2.1
              · change _ ≤ ((costPlusOutcome M b x).trade.payoff M).buyer
                rw [hntp, ← htp]
                exact hleaderSource.1.2.2.2.2
            · intro y hy
              rcases hcanNew _ true y hy with rfl | ho
              · exact le_rfl
              · have hh := hleaderSource.2 y ho
                unfold rfStageProduct at hh ⊢
                change _ ≤ nashProduct _ (((costPlusOutcome M b x).trade.payoff M).supplier i - _)
                  (((costPlusOutcome M b x).trade.payoff M).buyer - _)
                rw [hntp, ← htp]
                exact hh
          refine ⟨htnonneg, F', hFpolicy, a, hleadNew, ?_⟩
          intro j a' y hy
          rw [hntp, ← htp]
          by_cases hj : j = i
          · subst j
            obtain ⟨zz, hzz, hcase⟩ := hy
            have hzzO := (hFquote i a' zz).1 hzz
            rcases hcase with ⟨dual, hcan, hopt⟩ | ⟨hn, hyz⟩
            · rcases hcanNew _ dual y hcan with rfl | hcanO
              · exact le_of_eq (congrArg Payoff.buyer (hntp.trans htp.symm))
              · apply hbuyermax i a' y
                refine ⟨zz, hzzO, Or.inl ⟨dual, hcanO, ?_⟩⟩
                intro w hw
                obtain ⟨wn, hwn, heq⟩ := hcanMove _ dual w hw
                rw [heq]
                exact hopt wn hwn
            · apply hbuyermax i a' y
              refine ⟨zz, hzzO, Or.inr ⟨?_, hyz⟩⟩
              rintro ⟨dual, w, hw⟩
              obtain ⟨wn, hwn, heq⟩ := hcanMove _ dual w hw
              exact hn ⟨dual, wn, hwn⟩
          · have heq : F' j = F j := by
              funext d w
              simp [F', hj]
            rw [heq] at hy
            exact hbuyermax j a' y hy
