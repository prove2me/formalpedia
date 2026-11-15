-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:47:19.136386+00:00
-- url     : https://prove2.me/submissions/dcbb8800-9277-4eb3-913c-c7d40ca15ea6

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_2

set_option autoImplicit false

-- Solutions.StratifyMarketsParticipation
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

namespace StratifyMarkets.Participation

def eligible {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (x : Fin k → ℝ) :=
  Finset.univ.filter (fun i => x i ∈ s)

theorem count_measurable {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    Measurable (fun x : Fin k → ℝ => ((eligible s x).card : ℝ)) := by
  have h (x : Fin k → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
    simp only [Set.indicator,eligible,Finset.sum_boole]
  simp_rw [h]
  exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)

theorem count_median_bounds {k : ℕ} (μ : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    (1/2 : ENNReal) ≤ Measure.pi μ {x | (∑ i, (μ i s).toReal) - 1 < ((eligible s x).card : ℝ)} ∧
    (1/2 : ENNReal) ≤ Measure.pi μ {x | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1} := by
  classical
  let f := fun x => s.indicator (fun _ : ℝ => (1:ℝ)) x
  have hf : Measurable f := measurable_const.indicator hs
  have hber (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, f (x i) = 0 ∨ f (x i) = 1 := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases h : x i ∈ s <;> simp [f, Set.indicator, h]
  have hpi := ProbabilityTheory.iIndepFun_pi (μ := μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  have htail := (theorem_4_2 (Measure.pi μ) k (fun i x => f (x i))
    (fun i => hf.comp (measurable_pi_apply i)) hber hpi).2
  have sum_eq (x : Fin k → ℝ) : ∑ i, f (x i) = ((eligible s x).card : ℝ) := by
    simp only [f,Set.indicator,eligible,Finset.sum_boole]
  have hint (i : Fin k) : Integrable (fun x : Fin k → ℝ => f (x i)) (Measure.pi μ) :=
    ((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr
      ((integrable_const (1:ℝ)).indicator hs)
  have eint (i : Fin k) : (∫ x, f (x i) ∂Measure.pi μ) = (μ i s).toReal := by
    have eq := (measurePreserving_eval μ i).map_eq
    calc
      _ = ∫ y, f y ∂(Measure.pi μ).map (Function.eval i) :=
        (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [eq]; simp [f, integral_indicator hs, measureReal_def]
  rw [integral_finsetSum _ (fun i _ => hint i)] at htail
  simpa only [eint,sum_eq] using htail

theorem gains_integrable_sets {n m : ℕ} (I : DAInstance n m) (A B : Set ℝ)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Integrable (fun x => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) I.law := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  let mask := fun (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
    ((fun i => decide (x.1 i ∈ A)),(fun j => decide (x.2 j ∈ B)))
  have hmask : Measurable mask := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply i).comp measurable_fst) hA
    · apply measurable_pi_iff.mpr
      intro j
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply j).comp measurable_snd) hB
  let g := fun z : ((Fin n → ℝ) × (Fin m → ℝ)) × ((Fin n → Bool) × (Fin m → Bool)) =>
    worstRationedGains (Finset.univ.filter (fun i => z.2.1 i)) (Finset.univ.filter (fun j => z.2.2 j))
      z.1.1 z.1.2
  have hg : Measurable g := by
    apply measurable_from_prod_countable_left
    intro masks
    let bs := Finset.univ.filter (fun i => masks.1 i)
    let ss := Finset.univ.filter (fun j => masks.2 j)
    let opts := bs.powersetCard (min bs.card ss.card) ×ˢ ss.powersetCard (min bs.card ss.card)
    have hn : opts.Nonempty := (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product
      (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
    let f := fun (T : Finset (Fin n) × Finset (Fin m)) (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
      ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j
    have hfn (T) : Measurable (f T) := by
      apply Measurable.sub
      · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
      · exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd
    have heq : (fun x => g (x,masks)) = opts.inf' hn f := by
      funext x
      exact (Finset.inf'_apply hn f x).symm
    rw [heq]
    exact Finset.measurable_sup' (α := ℝᵒᵈ) hn fun T _ => hfn T
  have HM : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) := by
    simpa only [Function.comp_def, id_eq, g, mask, eligible, decide_eq_true_eq] using
      hg.comp (measurable_id.prodMk hmask)
  have buyer_support (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have seller_support (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound HM.aestronglyMeasurable ((n:ℝ)+m)
  filter_upwards [ae_all_iff.mpr buyer_support, ae_all_iff.mpr seller_support] with x hx hy
  unfold worstRationedGains
  let bs := eligible A x.1
  let ss := eligible B x.2
  have nonempty : ((bs.powersetCard (min bs.card ss.card)) ×ˢ ss.powersetCard (min bs.card ss.card)).Nonempty :=
    (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
  obtain ⟨pair,_,h⟩ := Finset.exists_mem_eq_inf' nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)
  change ‖Finset.inf' _ nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)‖ ≤ _
  rw [h,Real.norm_eq_abs,abs_le]
  have h1 : (∑ i ∈ pair.1, x.1 i) ≤ n := by
    calc _ ≤ ∑ _i ∈ pair.1, (1:ℝ) := Finset.sum_le_sum fun i _ => (hx i).2
         _ ≤ _ := by simpa using (show (pair.1.card:ℝ) ≤ n by exact_mod_cast (show pair.1.card ≤ n by simpa using Finset.card_le_univ pair.1))
  have h2 : (∑ j ∈ pair.2, x.2 j) ≤ m := by
    calc _ ≤ ∑ _j ∈ pair.2, (1:ℝ) := Finset.sum_le_sum fun j _ => (hy j).2
         _ ≤ _ := by simpa using (show (pair.2.card:ℝ) ≤ m by exact_mod_cast (show pair.2.card ≤ m by simpa using Finset.card_le_univ pair.2))
  have h3 := Finset.sum_nonneg (s := pair.1) (fun i _ => (hx i).1)
  have h4 := Finset.sum_nonneg (s := pair.2) (fun j _ => (hy j).1)
  constructor <;> linarith

theorem gains_integrable {n m : ℕ} (I : DAInstance n m) (q : ℝ) :
    Integrable (fun x => worstRationedGains (eligible (Ici q) x.1) (eligible (Iic q) x.2) x.1 x.2) I.law :=
  gains_integrable_sets I _ _ measurableSet_Ici measurableSet_Iic

theorem nonneg_gains {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (q : ℝ) :
    0 ≤ worstRationedGains (eligible (Ici q) v) (eligible (Iic q) c) v c := by
  apply Finset.le_inf'
  intro T hT
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp hT
  obtain ⟨inB,cB⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨inS,cS⟩ := Finset.mem_powersetCard.mp hS
  have sc : (∑ j ∈ T.2, c j) ≤ ∑ _j ∈ T.2, q := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp (inS hj)).2
  have vb : (∑ _i ∈ T.1, q) ≤ ∑ i ∈ T.1, v i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp (inB hi)).2
  exact sub_nonneg.mpr (sc.trans ((by simp [cB,cS] : (∑ _j ∈ T.2, q) ≤ ∑ _i ∈ T.1, q).trans vb))

/-- The leave-one-out comparison behind (4.10) whenever expected demand
is at least one unit below expected supply. Each side is an independent
heterogeneous family; removing one eligible-side coordinate is allowed. -/
theorem extra_participant_wins {k l : ℕ}
    (μ : Fin k → Measure ℝ) (ν : Fin l → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (gap : (∑ i, (μ i s).toReal) + 2 ≤ ∑ j, (ν j t).toReal) :
    (1/4 : ℝ) ≤ (((Measure.pi μ).prod (Measure.pi ν))
      {x | (eligible s x.1).card < (eligible t x.2).card}).toReal := by
  let B := {x : Fin k → ℝ | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1}
  let S := {y : Fin l → ℝ | (∑ j, (ν j t).toReal) - 1 < ((eligible t y).card : ℝ)}
  have b := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds μ s hs).2
  have c := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds ν t ht).1
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi μ) B).toReal at b
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi ν) S).toReal at c
  norm_num at b c
  have subset : B ×ˢ S ⊆ {x | (eligible s x.1).card < (eligible t x.2).card} := by
    intro x hx
    obtain ⟨h1,h2⟩ := hx
    change ((eligible s x.1).card : ℝ) < (∑ i, (μ i s).toReal) + 1 at h1
    change (∑ j, (ν j t).toReal) - 1 < ((eligible t x.2).card : ℝ) at h2
    exact_mod_cast (show ((eligible s x.1).card : ℝ) < ((eligible t x.2).card : ℝ) by linarith)
  have h := measureReal_mono (μ := (Measure.pi μ).prod (Measure.pi ν)) subset
  apply le_trans _ h
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr b) (sub_nonneg.mpr c)]

end StratifyMarkets.Participation
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_5
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.Participation

private theorem midpoint_gains {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (lo hi : ℝ)
    (ord : lo ≤ hi) (lam : ℝ) (large : 4 ≤ lam)
    (hb : lam-3 < ((eligible (Ici hi) v).card : ℝ))
    (hs : lam-3 < ((eligible (Iic lo) c).card : ℝ)) :
    lam/4 * ((hi-lo)/2) ≤ worstRationedGains (eligible (Ici ((hi+lo)/2)) v)
      (eligible (Iic ((hi+lo)/2)) c) v c := by
  classical
  let q := (hi+lo)/2
  let B := eligible (Ici q) v
  let S := eligible (Iic q) c
  have lower : lo ≤ q := by dsimp [q]; linarith
  have upper : q ≤ hi := by dsimp [q]; linarith
  have subB : eligible (Ici hi) v ⊆ B := by
    intro i h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,upper.trans (Finset.mem_filter.mp h).2⟩
  have subS : eligible (Iic lo) c ⊆ S := by
    intro j h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp h).2 : c j ≤ lo).trans lower⟩
  apply Finset.le_inf'
  intro pair h
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp h
  obtain ⟨inB,cardB⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨inS,cardS⟩ := Finset.mem_powersetCard.mp hS
  change pair.1.card = min B.card S.card at cardB
  change pair.2.card = min B.card S.card at cardS
  have posB i (hiB : i ∈ pair.1) : 0 ≤ v i-q := sub_nonneg.mpr (Finset.mem_filter.mp (inB hiB)).2
  have posS j (hjS : j ∈ pair.2) : 0 ≤ q-c j := sub_nonneg.mpr (Finset.mem_filter.mp (inS hjS)).2
  have same : (pair.1.card : ℝ) = pair.2.card := by exact_mod_cast cardB.trans cardS.symm
  have split : (∑ i ∈ pair.1, v i) - ∑ j ∈ pair.2, c j =
      (∑ i ∈ pair.1, (v i-q)) + ∑ j ∈ pair.2, (q-c j) := by
    simp [Finset.sum_sub_distrib, same]
  rw [split]
  rcases le_total B.card S.card with hbcard | hscard
  · have eq : pair.1 = B := Finset.eq_of_subset_of_card_le inB (by simpa only [min_eq_left hbcard] using cardB.ge)
    have hh : lam/4 * ((hi-lo)/2) ≤ (∑ i ∈ pair.1, (v i-q)) := by
      calc
        _ ≤ ((eligible (Ici hi) v).card : ℝ) * ((hi-lo)/2) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ = ∑ i ∈ eligible (Ici hi) v, ((hi-lo)/2) := by simp
        _ ≤ ∑ i ∈ eligible (Ici hi) v, (v i-q) := by
          apply Finset.sum_le_sum
          intro i hi'
          have hi' := (Finset.mem_filter.mp hi').2
          change hi ≤ v i at hi'
          dsimp [q]; linarith
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (eq ▸ subB) (fun i hi _ => posB i hi)
    exact hh.trans (le_add_of_nonneg_right (Finset.sum_nonneg posS))
  · have eq : pair.2 = S := Finset.eq_of_subset_of_card_le inS (by simpa only [min_eq_right hscard] using cardS.ge)
    have hh : lam/4 * ((hi-lo)/2) ≤ (∑ j ∈ pair.2, (q-c j)) := by
      calc
        _ ≤ ((eligible (Iic lo) c).card : ℝ) * ((hi-lo)/2) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ = ∑ j ∈ eligible (Iic lo) c, ((hi-lo)/2) := by simp
        _ ≤ ∑ j ∈ eligible (Iic lo) c, (q-c j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj := (Finset.mem_filter.mp hj).2
          change c j ≤ lo at hj
          dsimp [q]; linarith
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (eq ▸ subS) (fun j hj _ => posS j hj)
    exact hh.trans (le_add_of_nonneg_left (Finset.sum_nonneg posB))

theorem solution {n m : ℕ} (I : DAInstance n m) (pt pbar plow : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt)
    (hpbar : I.IsExcessSupplyPrice pbar) (hplow : I.IsExcessDemandPrice plow) :
    I.expB pt / 32 * (pbar - plow) ≤ I.worstRationed ((pbar + plow) / 2) := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  let lam := I.expB pt
  let q := (pbar+plow)/2
  have hB : Antitone I.expB := fun x y hxy => Finset.sum_le_sum fun i _ => measureReal_mono (Ici_subset_Ici.mpr hxy)
  have hS : Monotone I.expS := fun x y hxy => Finset.sum_le_sum fun i _ => measureReal_mono (Iic_subset_Iic.mpr hxy)
  have hlo : plow ≤ pt := by by_contra! h; linarith only [hpt.2,hplow.2,hB h.le,hS h.le]
  have hhi : pt ≤ pbar := by by_contra! h; linarith only [hpt.2,hpbar.2,hB h.le,hS h.le]
  let buyers := {v : Fin n → ℝ | lam - 3 < ((eligible (Ici pbar) v).card : ℝ)}
  let sellers := {c : Fin m → ℝ | lam - 3 < ((eligible (Iic plow) c).card : ℝ)}
  let E := buyers ×ˢ sellers
  have meas {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
      MeasurableSet {x : Fin k → ℝ | lam-3 < ((eligible s x).card : ℝ)} := by
    have hcast (x : Fin k → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
      simp only [Set.indicator,eligible,Finset.sum_boole]
    simp_rw [hcast]
    exact measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ =>
      ((measurable_const.indicator hs).comp (measurable_pi_apply i)))
  have hE : MeasurableSet E := (meas _ measurableSet_Ici).prod (meas _ measurableSet_Iic)
  have pb : (1/2 : ENNReal) ≤ Measure.pi I.μB buyers := by
    apply (count_median_bounds I.μB (Ici pbar) measurableSet_Ici).1.trans (measure_mono ?_)
    intro v hv
    change I.expB pbar - 1 < ((eligible (Ici pbar) v).card : ℝ) at hv
    change I.expB pt - 3 < _
    linarith only [hv,hpbar.2,hS hhi,hpt.2]
  have ps : (1/2 : ENNReal) ≤ Measure.pi I.μS sellers := by
    apply (count_median_bounds I.μS (Iic plow) measurableSet_Iic).1.trans (measure_mono ?_)
    intro c hc
    change I.expS plow - 1 < ((eligible (Iic plow) c).card : ℝ) at hc
    change I.expB pt - 3 < _
    linarith only [hc,hplow.2,hB hlo]
  have prob : (1/4 : ℝ) ≤ (I.law E).toReal := by
    change _ ≤ (((Measure.pi I.μB).prod (Measure.pi I.μS)) (buyers ×ˢ sellers)).toReal
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    have hb := ENNReal.toReal_mono (measure_ne_top _ _) pb
    have hs := ENNReal.toReal_mono (measure_ne_top _ _) ps
    norm_num at hb hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hs)]
  let gain := lam/4*((pbar-plow)/2)
  have hg : 0 ≤ gain := mul_nonneg (by dsimp [lam]; linarith) (by linarith)
  have lower (x : (Fin n → ℝ) × (Fin m → ℝ)) :
      E.indicator (fun _ => gain) x ≤ worstRationedGains (eligible (Ici q) x.1) (eligible (Iic q) x.2) x.1 x.2 := by
    by_cases h : x ∈ E
    · rw [Set.indicator_of_mem h]
      exact midpoint_gains x.1 x.2 plow pbar (hlo.trans hhi) lam hlam h.1 h.2
    · rw [Set.indicator_of_notMem h]
      exact nonneg_gains _ _ _
  have hh := integral_mono ((integrable_const gain (μ := I.law)).indicator hE) (gains_integrable I q) lower
  rw [integral_indicator hE, setIntegral_const] at hh
  change (I.law E).toReal * gain ≤ I.worstRationed q at hh
  have h := (mul_le_mul_of_nonneg_right prob hg).trans hh
  dsimp [gain,lam,q] at h
  linarith only [h]
end
