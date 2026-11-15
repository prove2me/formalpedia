-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_13
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:52:21.741123+00:00
-- url     : https://prove2.me/submissions/54bbb37d-e39a-4da0-987d-752e098d5a68

import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_12
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_3_1

set_option autoImplicit false

-- Solutions.StratifyMarketsSuperAgents
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

theorem vmax_meas {n : ℕ} [NeZero n] : Measurable (vmax (n := n)) := by
  have h := Finset.measurable_sup' Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin n => ℝ) i)
  have heq : vmax (n := n) = Finset.univ.sup' Finset.univ_nonempty
      (fun i (v : Fin n → ℝ) => v i) := by
    funext v
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i (w : Fin n → ℝ) => w i) v).symm
  rw [heq]
  exact h

theorem cmin_meas {m : ℕ} [NeZero m] : Measurable (cmin (m := m)) := by
  have h := Finset.measurable_sup' (α := ℝᵒᵈ) Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin m => ℝᵒᵈ) i)
  have heq : cmin (m := m) = Finset.univ.inf' Finset.univ_nonempty
      (fun i (c : Fin m → ℝ) => c i) := by
    funext c
    exact (Finset.inf'_apply Finset.univ_nonempty (fun i (w : Fin m → ℝ) => w i) c).symm
  rw [heq]
  exact h

private theorem extremum_law {k : ℕ} (μ : Fin k → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hn : ∀ j, NullSingletonClass (μ j)) (hs : ∀ j, μ j (Icc 0 1) = 1)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) (attains : ∀ x, ∃ j, f x = x j) :
    IsProbabilityMeasure ((Measure.pi μ).map f) ∧ NullSingletonClass ((Measure.pi μ).map f) ∧
      (Measure.pi μ).map f (Icc 0 1) = 1 := by
  let : IsProbabilityMeasure ((Measure.pi μ).map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine ⟨inferInstance, ⟨fun r => ?_⟩, ?_⟩
  · rw [Measure.map_apply hf (measurableSet_singleton _)]
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ≠ r :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae (by
        let := hn i
        exact (μ i).ae_ne r)
    have null : ∀ᵐ x ∂Measure.pi μ, f x ≠ r := by
      filter_upwards [ae_all_iff.mpr coord] with x hx
      obtain ⟨i,hi⟩ := attains x
      exact hi ▸ hx i
    exact compl_mem_ae_iff.mp null
  · rw [Measure.map_apply hf measurableSet_Icc]
    apply (mem_ae_iff_prob_eq_one (hf measurableSet_Icc)).mp
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ∈ Icc (0 : ℝ) 1 :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (hs i))
    filter_upwards [ae_all_iff.mpr coord] with x hx
    obtain ⟨i,hi⟩ := attains x
    change f x ∈ Icc 0 1
    rw [hi]
    exact hx i

/-- The extrema in the double-auction profile define an admissible atomless
bilateral instance; the buyer and seller are sampled independently. -/
noncomputable def superAgents {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) : BTInstance := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ i, IsProbabilityMeasure (I.μS i) := I.isProb_S
  have hB := extremum_law I.μB I.noAtoms_B I.support_B vmax vmax_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  have hS := extremum_law I.μS I.noAtoms_S I.support_S cmin cmin_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  exact ⟨_, _, hB.1, hS.1, hB.2.1, hS.2.1, hB.2.2, hS.2.2⟩

private theorem super_integral {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(superAgents I).law = ∫ x, f (cmin x.2, vmax x.1) ∂I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  change (∫ x, f x ∂(((Measure.pi I.μS).map cmin).prod ((Measure.pi I.μB).map vmax))) = _
  rw [Measure.map_prod_map _ _ cmin_meas vmax_meas, integral_map (cmin_meas.prodMap vmax_meas).aemeasurable hf.aestronglyMeasurable]
  have swap : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _)
      ((Measure.pi I.μB).prod (Measure.pi I.μS)) ((Measure.pi I.μS).prod (Measure.pi I.μB)) :=
    Measure.measurePreserving_swap
  exact (swap.integral_comp' (fun z => f ((Prod.map cmin vmax) z))).symm

theorem superAgents_first_best {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    (superAgents I).FB = ∫ x, max (vmax x.1 - cmin x.2) 0 ∂I.law :=
  super_integral I (fun x => max (x.2-x.1) 0) (by fun_prop)

theorem superAgents_strat {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (σ : Stratification) :
    (superAgents I).strat σ = ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  apply Finset.sum_congr rfl
  intro k _
  apply super_integral
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)))
  · exact measurable_snd.sub measurable_fst
  · exact measurable_const

/-- Equation (4.35) transports the bilateral theorem to the exact super-agent
integrals of the double auction. -/
theorem superAgents_bilateral_guarantee {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    ∃ σ : Stratification, 1/(12*Real.exp 1) * (∫ x, max (vmax x.1-cmin x.2) 0 ∂I.law) ≤
      ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  obtain ⟨σ,hσ⟩ := theorem_3_1 (superAgents I)
  exact ⟨σ, by simpa only [superAgents_first_best, superAgents_strat] using hσ⟩

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsThresholdMass
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

namespace StratifyMarkets.ThresholdMass

/-- Under the product law, restricting all coordinates to a larger set still
leaves a positive fraction of profiles with a coordinate in the smaller set.
The statement also covers zero probability of the larger set. -/
theorem box_hit {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {A B : Set ℝ} (hAB : A ⊆ B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (1 - Real.exp (-(∑ i, (μ i).real A))) * (Measure.pi μ).real (univ.pi fun _ => B) ≤
      (Measure.pi μ).real ((univ.pi fun _ => B) \ (univ.pi fun _ => B \ A)) := by
  classical
  let u := fun i => (μ i).real B
  let v := fun i => (μ i).real A
  have term (i) : (μ i).real (B \ A) ≤ u i * Real.exp (-v i) := by
    rw [measureReal_sdiff hAB hA]
    have huv : u i ≤ 1 := measureReal_le_one
    have hv : 0 ≤ v i := measureReal_nonneg
    have e := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-v i)) (show 0 ≤ u i from measureReal_nonneg)
    change u i - v i ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) hv]
  have prod := Finset.prod_le_prod (s := Finset.univ) (fun i _ => measureReal_nonneg (μ := μ i) (s := B \ A))
    (fun i _ => term i)
  have sub : (univ.pi fun _ : Fin n => B \ A) ⊆ (univ.pi fun _ => B) :=
    fun _ hx i hi => (hx i hi).1
  rw [measureReal_sdiff sub (MeasurableSet.univ_pi (fun _ => hB.diff hA))]
  simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib] at prod
  change (∏ i, (μ i).real (B \ A)) ≤ (∏ i, (μ i).real B) * Real.exp (-(∑ i, (μ i).real A)) at prod
  change (1 - Real.exp (-(∑ i, (μ i).real A))) * (∏ i, (μ i).real B) ≤
    (∏ i, (μ i).real B) - ∏ i, (μ i).real (B \ A)
  linarith

theorem upper_tail {n : ℕ} [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {p t b : ℝ} (ht : t ≤ b) :
    (1-Real.exp (-(∑ i, (μ i).real (Icc t b)))) * (Measure.pi μ).real (vmax ⁻¹' Icc p b) ≤
      (Measure.pi μ).real (vmax ⁻¹' Icc t b) := by
  let box := univ.pi (fun _ : Fin n => Iic b)
  have sub {q : ℝ} : vmax ⁻¹' Icc q b ⊆ box := by
    intro x h i _
    exact (Finset.le_sup' x (Finset.mem_univ i)).trans h.2
  have eq : (box \ univ.pi (fun _ : Fin n => Iic b \ Icc t b)) = vmax ⁻¹' Icc t b := by
    ext x
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    change vmax x = x i at hi
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨?_, hi ▸ hx i (mem_univ _)⟩
      by_contra! bad
      apply hn
      intro j hj
      refine ⟨hx j hj, ?_⟩
      intro h
      exact (not_le_of_gt bad) (h.1.trans (Finset.le_sup' x (Finset.mem_univ j)))
    · intro h
      refine ⟨sub (q := t) h, ?_⟩
      intro H
      exact (H i (mem_univ _)).2 (hi ▸ h)
  have E : 0 ≤ 1-Real.exp (-(∑ i, (μ i).real (Icc t b))) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => measureReal_nonneg)))
  have bound := box_hit μ (A := Icc t b) (B := Iic b) (fun _ h => h.2) measurableSet_Icc measurableSet_Iic
  rw [← eq]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (sub (q := p))) E).trans bound

theorem lower_tail {m : ℕ} [NeZero m] (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {a t p : ℝ} (ha : a ≤ t) :
    (1-Real.exp (-(∑ i, (μ i).real (Icc a t)))) * (Measure.pi μ).real (cmin ⁻¹' Icc a p) ≤
      (Measure.pi μ).real (cmin ⁻¹' Icc a t) := by
  let box := univ.pi (fun _ : Fin m => Ici a)
  have sub {q : ℝ} : cmin ⁻¹' Icc a q ⊆ box := by
    intro x h i _
    exact h.1.trans (Finset.inf'_le x (Finset.mem_univ i))
  have eq : (box \ univ.pi (fun _ : Fin m => Ici a \ Icc a t)) = cmin ⁻¹' Icc a t := by
    ext x
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
    change cmin x = x i at hi
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨hi ▸ hx i (mem_univ _), ?_⟩
      by_contra! bad
      apply hn
      intro j hj
      refine ⟨hx j hj, ?_⟩
      intro h
      exact (not_le_of_gt bad) ((Finset.inf'_le x (Finset.mem_univ j)).trans h.2)
    · intro h
      refine ⟨sub h, ?_⟩
      intro H
      exact (H i (mem_univ _)).2 (hi ▸ h)
  have E : 0 ≤ 1-Real.exp (-(∑ i, (μ i).real (Icc a t))) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => measureReal_nonneg)))
  have bound := box_hit μ (A := Icc a t) (B := Ici a) (fun _ h => h.1) measurableSet_Icc measurableSet_Ici
  rw [← eq]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (sub (q := p))) E).trans bound

end StratifyMarkets.ThresholdMass
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_13
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.ThresholdMass

private noncomputable def payoff {X Y : Type*} (v : X → ℝ) (c : Y → ℝ) (a p b : ℝ) (z : X × Y) : ℝ :=
  if a ≤ c z.2 ∧ c z.2 ≤ p ∧ p ≤ v z.1 ∧ v z.1 ≤ b then v z.1 - c z.2 else 0

/-- Moving the price up preserves all of the buyer surplus above the new
price. The seller part is multiplied by the fraction of buyers still eligible. -/
private theorem raise_price {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (v : X → ℝ) (c : Y → ℝ) (hv : Measurable v) (hc : Measurable c)
    {a p t b K : ℝ} (hap : a ≤ p) (hpt : p ≤ t) (htb : t ≤ b)
    (k0 : 0 ≤ K) (k1 : K ≤ 1)
    (mass : K * μ.real (v ⁻¹' Icc p b) ≤ μ.real (v ⁻¹' Icc t b)) :
    K * (∫ z, payoff v c a p b z ∂μ.prod ν) ≤ ∫ z, payoff v c a t b z ∂μ.prod ν := by
  classical
  let B := fun q => v ⁻¹' Icc q b
  let S := fun q => c ⁻¹' Icc a q
  have hB (q) : MeasurableSet (B q) := hv measurableSet_Icc
  have hS (q) : MeasurableSet (S q) := hc measurableSet_Icc
  let oneB := fun q => (B q).indicator (fun _ => (1:ℝ))
  let oneS := (S p).indicator (fun _ => (1:ℝ))
  let buy := (B t).indicator (fun x => v x-t)
  let sell := (S p).indicator (fun y => t-c y)
  have ib : Integrable buy μ := by
    apply Integrable.of_bound ((hv.sub measurable_const).indicator (hB t)).aestronglyMeasurable (b-t)
    filter_upwards with x
    change ‖buy x‖ ≤ b-t
    by_cases h : x ∈ B t
    · rw [show buy x = v x-t from Set.indicator_of_mem h _, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.1)]
      exact sub_le_sub_right h.2 t
    · simp [buy,h,sub_nonneg.mpr htb]
  have is : Integrable sell ν := by
    apply Integrable.of_bound ((measurable_const.sub hc).indicator (hS p)).aestronglyMeasurable (t-a)
    filter_upwards with y
    change ‖sell y‖ ≤ t-a
    by_cases h : y ∈ S p
    · rw [show sell y = t-c y from Set.indicator_of_mem h _, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (h.2.trans hpt))]
      exact sub_le_sub_left h.1 t
    · simp [sell,h,sub_nonneg.mpr (hap.trans hpt)]
  have iB (q) : Integrable (oneB q) μ := (integrable_const _).indicator (hB q)
  have iS : Integrable oneS ν := (integrable_const _).indicator (hS p)
  have ip {q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) : Integrable (payoff v c a q b) (μ.prod ν) := by
    have hs : MeasurableSet {z : X × Y | a ≤ c z.2 ∧ c z.2 ≤ q ∧ q ≤ v z.1 ∧ v z.1 ≤ b} :=
      (measurableSet_le measurable_const (hc.comp measurable_snd)).inter
        ((measurableSet_le (hc.comp measurable_snd) measurable_const).inter
          ((measurableSet_le measurable_const (hv.comp measurable_fst)).inter (measurableSet_le (hv.comp measurable_fst) measurable_const)))
    apply Integrable.of_bound (Measurable.ite hs ((hv.comp measurable_fst).sub (hc.comp measurable_snd)) measurable_const).aestronglyMeasurable (b-a)
    filter_upwards with z
    change ‖if a ≤ c z.2 ∧ c z.2 ≤ q ∧ q ≤ v z.1 ∧ v z.1 ≤ b then v z.1 - c z.2 else (0:ℝ)‖ ≤ _
    split_ifs with h
    · rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (h.2.1.trans h.2.2.1))]
      linarith only [h.1,h.2.2.2]
    · simp [sub_nonneg.mpr (haq.trans hqb)]
  let approx := fun (q : ℝ) (z : X × Y) => buy z.1 * oneS z.2 + oneB q z.1 * sell z.2
  have ia (q) : Integrable (approx q) (μ.prod ν) := (ib.mul_prod iS).add ((iB q).mul_prod is)
  have posB (x) : 0 ≤ buy x := Set.indicator_nonneg (fun _ h => sub_nonneg.mpr h.1) x
  have posS (y) : 0 ≤ sell y := Set.indicator_nonneg (fun _ h => sub_nonneg.mpr (h.2.trans hpt)) y
  have posOneB (q x) : 0 ≤ oneB q x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have posOneS (y) : 0 ≤ oneS y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have old := integral_mono (ip hap (hpt.trans htb)) (ia p) (fun z => by
    change payoff v c a p b z ≤ buy z.1 * oneS z.2 + oneB p z.1 * sell z.2
    by_cases hx : z.1 ∈ B p ∧ z.2 ∈ S p
    · have deal : a ≤ c z.2 ∧ c z.2 ≤ p ∧ p ≤ v z.1 ∧ v z.1 ≤ b := ⟨hx.2.1,hx.2.2,hx.1⟩
      simp only [payoff,if_pos deal,oneS,oneB,sell,Set.indicator_of_mem hx.1,Set.indicator_of_mem hx.2,mul_one,one_mul]
      by_cases hh : z.1 ∈ B t
      · rw [show buy z.1 = v z.1-t from Set.indicator_of_mem hh _]; linarith
      · have hn : v z.1 < t := lt_of_not_ge fun H => hh ⟨H,hx.1.2⟩
        rw [show buy z.1 = 0 from Set.indicator_of_notMem hh _]; linarith
    · have no : ¬(a ≤ c z.2 ∧ c z.2 ≤ p ∧ p ≤ v z.1 ∧ v z.1 ≤ b) := fun h => hx ⟨h.2.2,h.1,h.2.1⟩
      rw [payoff,if_neg no]
      exact add_nonneg (mul_nonneg (posB _) (posOneS _)) (mul_nonneg (posOneB _ _) (posS _)))
  have new := integral_mono (ia t) (ip (hap.trans hpt) htb) (fun z => by
    by_cases h1 : z.1 ∈ B t <;> by_cases h2 : z.2 ∈ S p
    · have deal : a ≤ c z.2 ∧ c z.2 ≤ t ∧ t ≤ v z.1 ∧ v z.1 ≤ b := ⟨h2.1,h2.2.trans hpt,h1⟩
      simp [approx,oneB,oneS,buy,sell,payoff,h1,h2,deal]
    all_goals
      have hp : 0 ≤ payoff v c a t b z := by
        unfold payoff
        split_ifs with h
        · exact sub_nonneg.mpr (h.2.1.trans h.2.2.1)
        · exact le_rfl
      simpa [approx,oneB,oneS,buy,sell,h1,h2] using hp)
  have ea (q) : (∫ z, approx q z ∂μ.prod ν) =
      (∫ x, buy x ∂μ) * ν.real (S p) + μ.real (B q) * (∫ y, sell y ∂ν) := by
    dsimp only [approx]
    rw [integral_add (ib.mul_prod iS) ((iB q).mul_prod is), integral_prod_mul, integral_prod_mul]
    simp [oneB,oneS,integral_indicator (hB q),integral_indicator (hS p)]
  rw [ea p] at old
  rw [ea t] at new
  refine (mul_le_mul_of_nonneg_left old k0).trans (le_trans ?_ new)
  rw [mul_add,← mul_assoc]
  have hb := mul_nonneg (integral_nonneg (μ := μ) posB) (measureReal_nonneg (μ := ν) (s := S p))
  have h1 := mul_le_mul_of_nonneg_right k1 hb
  have h2 := mul_le_mul_of_nonneg_right mass (integral_nonneg (μ := ν) posS)
  dsimp only [B] at *
  linarith only [h1,h2]

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b) :
    (1 / 4 ≤ I.expBuyersIn p b → ∀ tB : ℝ, p ≤ tB → tB ≤ b → I.expBuyersIn tB b = 1 / 4 →
      (1 - Real.exp (-(1 / 4))) * I.superFP a p b ≤ I.superFP a tB b ∧
      (I.expSellersIn a tB ≤ 1 / 4 → 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a tB b)) ∧
    (1 / 4 ≤ I.expSellersIn a p → ∀ tS : ℝ, a ≤ tS → tS ≤ p → I.expSellersIn a tS = 1 / 4 →
      (1 - Real.exp (-(1 / 4))) * I.superFP a p b ≤ I.superFP a tS b ∧
      (I.expBuyersIn tS b ≤ 1 / 4 → 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a tS b)) := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let K := 1 - Real.exp (-(1/4))
  have k0 : 0 ≤ K := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have k1 : K ≤ 1 := by dsimp [K]; linarith [Real.exp_pos (-(1/4))]
  have kmin : (1/7 : ℝ) ≤ 3/4*K := by
    have e := Real.add_one_le_exp (1/4)
    have z := Real.exp_pos (1/4)
    have u := Real.exp_neg (1/4)
    have r : Real.exp (-(1/4)) ≤ 4/5 := by
      rw [u,inv_le_iff_one_le_mul₀ z]; linarith
    dsimp [K]; linarith
  have nonneg : 0 ≤ I.superFP a p b := integral_nonneg fun z => by
    change 0 ≤ (if _ then _ else (0:ℝ))
    split_ifs with h
    · exact sub_nonneg.mpr (h.2.1.trans h.2.2.1)
    · exact le_rfl
  have finish {q : ℝ} (hq : a ≤ q) (hqb : q ≤ b)
      (move : K * I.superFP a p b ≤ I.superFP a q b) (hB : I.expBuyersIn q b ≤ 1/4) (hS : I.expSellersIn a q ≤ 1/4) :
      1/7 * I.superFP a p b ≤ I.worstRationedIn a q b := by
    have H := lemma_4_12 I a b q ha hab hb hq hqb hB hS
    have one := mul_le_mul_of_nonneg_right kmin nonneg
    linarith only [one,mul_le_mul_of_nonneg_left move (by norm_num : (0:ℝ) ≤ 3/4),H]
  constructor
  · intro _ t hpt htb hm
    have prob := upper_tail I.μB (p := p) htb
    change (1-Real.exp (-I.expBuyersIn t b)) * _ ≤ _ at prob
    rw [hm] at prob
    have move := raise_price (Measure.pi I.μB) (Measure.pi I.μS) vmax cmin vmax_meas cmin_meas hap hpt htb k0 k1 prob
    exact ⟨move, finish (hap.trans hpt) htb move hm.le⟩
  · intro _ t hat htp hm
    have prob := lower_tail I.μS (p := p) hat
    change (1-Real.exp (-I.expSellersIn a t)) * _ ≤ _ at prob
    rw [hm] at prob
    have pr (q) : ((fun x : Fin m → ℝ => -cmin x) ⁻¹' Icc (-q) (-a)) = cmin ⁻¹' Icc a q := by
      ext x; simp [and_comm,Set.mem_preimage]
    rw [← pr p, ← pr t] at prob
    have move := raise_price (Measure.pi I.μS) (Measure.pi I.μB) (fun y => -cmin y) (fun x => -vmax x)
      cmin_meas.neg vmax_meas.neg (neg_le_neg hpb) (neg_le_neg htp) (neg_le_neg hat) k0 k1 prob
    have sw : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _) I.law ((Measure.pi I.μS).prod (Measure.pi I.μB)) := Measure.measurePreserving_swap
    have eq (q) : (∫ z, payoff (fun y => -cmin y) (fun x => -vmax x) (-b) (-q) (-a) z
        ∂((Measure.pi I.μS).prod (Measure.pi I.μB))) = I.superFP a q b := by
      rw [← sw.integral_comp']
      apply integral_congr_ae
      filter_upwards with x
      change payoff (fun y => -cmin y) (fun x => -vmax x) (-b) (-q) (-a) (x.2,x.1) = payoff vmax cmin a q b x
      simp [payoff,and_comm,and_left_comm,and_assoc,sub_eq_add_neg,add_comm]
    rw [eq,eq] at move
    exact ⟨move, fun hB => finish hat (htp.trans hpb) move hB hm.le⟩
end
