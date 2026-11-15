-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:36:32.366835+00:00
-- url     : https://prove2.me/submissions/a2bc3d4e-c347-44c1-b900-ab15f86f6d88

import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification
import Mathlib

set_option autoImplicit false

-- Solutions.StratifyMarketsBilateralPricing
section
open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace StratifyMarkets.DoubleAuction.PricingProof

private theorem supported {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : μ (Icc 0 1) = 1) : ∀ᵐ c ∂μ, c ∈ Icc (0 : ℝ) 1 :=
  (mem_ae_iff_prob_eq_one measurableSet_Icc).2 h

private theorem tailAnti (I : BTInstance) : Antitone I.Fbar := by
  letI := I.isProb_B
  exact fun _ _ h => measureReal_mono (Ici_subset_Ici.mpr h)

private theorem tailCont (I : BTInstance) : ContinuousOn I.Fbar (Icc 0 1) := by
  letI := I.isProb_B
  letI := I.noAtoms_B
  have hint : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici 0) I.μB := (integrable_const 1).integrableOn
  apply ContinuousOn.mono (s := Ici (0:ℝ)) _ (fun _ h => h.1)
  change ContinuousOn (fun b => (I.μB (Ici b)).toReal) (Ici 0)
  simpa only [setIntegral_one_eq_measureReal, measureReal_def] using hint.continuousOn_Ici_primitive_Ici

private theorem tailBound (I : BTInstance) (s : ℝ) : I.Fbar s ≤ 1 := by
  letI := I.isProb_B
  exact measureReal_le_one

private theorem tailEnds (I : BTInstance) : I.Fbar 0 = 1 ∧ I.Fbar 1 = 0 := by
  letI := I.isProb_B
  letI := I.noAtoms_B
  have h := supported I.support_B
  constructor
  · have u := (mem_ae_iff_prob_eq_one (measurableSet_Ici (a:=0))).1
      (h.mono fun _ hc => hc.1)
    simp [BTInstance.Fbar,u]
  · have e : Ici (1:ℝ) =ᵐ[I.μB] (∅ : Set ℝ) := by
      filter_upwards [h,I.μB.ae_ne 1] with x hx ne
      apply propext
      change (1 ≤ x) ↔ False
      simp [show ¬1 ≤ x by grind [hx.2]]
    simp [BTInstance.Fbar,measure_congr e]

private def half (k : ℕ) : ℝ := (1/2:ℝ)^k

private theorem half_pos (k : ℕ) : 0 < half k := by unfold half; positivity
private theorem half_succ (k : ℕ) : half (k+1) = half k / 2 := by simp [half,pow_succ,div_eq_mul_inv]
private theorem halfStrict : StrictAnti half :=
  strictAnti_nat_of_succ_lt (fun k => by rw [half_succ]; linarith [half_pos k])

private theorem quantiles (I : BTInstance) :
    ∃ q : ℕ → ℝ, q 0 = 0 ∧ StrictMono q ∧ (∀ k, q k ∈ Icc 0 1) ∧ (∀ k, I.Fbar (q k) = half k) := by
  have ex (k : ℕ) : ∃ t ∈ Icc (0:ℝ) 1, I.Fbar t = half k := by
    apply intermediate_value_Icc' zero_le_one (tailCont I)
    rw [(tailEnds I).1,(tailEnds I).2]
    exact ⟨(half_pos k).le,show half k ≤ half 0 from halfStrict.antitone (Nat.zero_le k)⟩
  choose t ht eval using ex
  let q (k : ℕ) := if k=0 then (0:ℝ) else t k
  have qm (k) : q k ∈ Icc (0:ℝ) 1 := by by_cases h : k=0 <;> simp [q,h,ht]
  have qe (k) : I.Fbar (q k) = half k := by
    by_cases h : k=0
    · subst k; simp [q,half,(tailEnds I).1]
    · simp [q,h,eval]
  refine ⟨q,by simp [q],?_,qm,qe⟩
  intro i j h
  by_contra! hn
  have bad := tailAnti I hn
  rw [qe,qe] at bad
  exact (halfStrict h).not_ge bad

private structure Optimal (I : BTInstance) (c p : ℝ) : Prop where
  mem : p ∈ Icc 0 1
  above : c ≤ p
  max : ∀ s ∈ Icc (0:ℝ) 1, (s-c)*I.Fbar s ≤ (p-c)*I.Fbar p
  active : 0 < I.Fbar p ∨ p=1

private theorem optimalExists (I : BTInstance) (c : ℝ) (hc : c ∈ Icc 0 1) :
    ∃ p, Optimal I c p := by
  have cont : ContinuousOn (fun s => (s-c)*I.Fbar s) (Icc 0 1) :=
    (continuous_id.sub continuous_const).continuousOn.mul (tailCont I)
  obtain ⟨p,hp,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) cont
  have mx := isMaxOn_iff.mp hm
  by_cases pos : 0 < (p-c)*I.Fbar p
  · have signs := (mul_pos_iff.mp pos).resolve_right (fun h => h.2.not_ge ENNReal.toReal_nonneg)
    exact ⟨p,hp,(sub_pos.mp signs.1).le,mx,Or.inl signs.2⟩
  · refine ⟨1,⟨zero_le_one,le_rfl⟩,hc.2,?_,Or.inr rfl⟩
    intro s hs
    rw [(tailEnds I).2,mul_zero]
    exact (mx s hs).trans (le_of_not_gt pos)

private theorem optMono (I : BTInstance) {c d p r : ℝ} (cd : c < d)
    (hp : Optimal I c p) (hr : Optimal I d r) : p ≤ r := by
  by_contra! rev
  have h1 := hp.max r hr.mem
  have h2 := hr.max p hp.mem
  have tail := tailAnti I rev.le
  have prod : 0 ≤ (d-c) * (I.Fbar p-I.Fbar r) := by linarith only [h1,h2]
  have eq : I.Fbar p = I.Fbar r :=
    le_antisymm tail (sub_nonneg.mp (nonneg_of_mul_nonneg_right prod (sub_pos.mpr cd)))
  rcases hr.active with pos|one
  · rw [eq] at h2
    exact (not_le_of_gt (mul_lt_mul_of_pos_right (sub_lt_sub_right rev d) pos)) h2
  · linarith [hp.mem.2]

private theorem optValue (I : BTInstance) {c p : ℝ} (h : Optimal I c p) :
    I.sellerProfitAt c = (p-c)*I.Fbar p := by
  have b : BddAbove (Set.range fun s : Icc (0:ℝ) 1 => ((s:ℝ)-c)*I.Fbar s) :=
    ⟨(p-c)*I.Fbar p,by rintro _ ⟨s,rfl⟩;exact h.max s s.2⟩
  apply le_antisymm (ciSup_le (fun s : Icc (0:ℝ) 1 => h.max s s.2))
  exact le_ciSup b (⟨p,h.mem⟩ : Icc (0:ℝ) 1)

private theorem findBin (I : BTInstance) {q : ℕ → ℝ} (z : q 0 = 0)
    (qe : ∀ k, I.Fbar (q k) = half k) {p : ℝ} (p0 : 0 ≤ p) (active : 0 < I.Fbar p) :
    ∃ k, q k ≤ p ∧ p < q (k+1) := by
  have tend : Tendsto half atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n,hn⟩ := ((tend.eventually (gt_mem_nhds active)).exists)
  have ex : ∃ n, p < q n := ⟨n,lt_of_not_ge (fun h => hn.not_ge ((qe n).symm ▸ tailAnti I h))⟩
  let n := Nat.find ex
  have hit : p < q n := Nat.find_spec ex
  obtain ⟨k,hk⟩ : ∃ k, n=k+1 := Nat.exists_eq_succ_of_ne_zero (by intro h;rw [h,z] at hit; linarith)
  refine ⟨k,le_of_not_gt (Nat.find_min ex (show k < n by omega)),hk ▸ hit⟩

private structure Bins (I : BTInstance) where
  seller : ℕ → ℝ
  buyer : ℕ → ℝ
  sellers : Monotone seller
  buyers : Monotone buyer
  seller_mem : ∀ k, seller k ∈ Icc 0 1
  buyer_mem : ∀ k, buyer k ∈ Icc 0 1
  tradable : ∀ k, seller (k+1) ≤ buyer k
  mass : ∀ k, I.μB.real (Icc (buyer k) (buyer (k+1))) = half k / 4
  dominates : ∀ c ∈ Icc (0:ℝ) 1, 0 < I.sellerProfitAt c →
    ∃ k, c ∈ Icc (seller k) (seller (k+1)) ∧
      I.sellerProfitAt c/4 < (buyer k-c)*(half k / 4)

private theorem makeBins (I : BTInstance) : Nonempty (Bins I) := by
  classical
  letI := I.isProb_B
  letI := I.noAtoms_B
  obtain ⟨q,z,qm,qmem,qe⟩ := quantiles I
  choose p hp using fun c : Icc (0:ℝ) 1 => optimalExists I c c.2
  let S (k : ℕ) := insert (0:ℝ) {c | ∃ h : c ∈ Icc (0:ℝ) 1, p ⟨c,h⟩ < q k}
  let cut (k : ℕ) := sSup (S k)
  have bound (k) (x : ℝ) (hx : x ∈ S k) : x ≤ q k := by
    rcases hx with rfl|⟨h,hh⟩
    · exact (qmem k).1
    · exact (hp ⟨x,h⟩).above.trans hh.le
  have bdd (k) : BddAbove (S k) := ⟨q k, fun x hx => bound k x hx⟩
  have ne (k) : (S k).Nonempty := ⟨0,Or.inl rfl⟩
  have maxcut (k) : cut k ≤ q k := csSup_le (ne k) (bound k)
  have cut0 (k) : 0 ≤ cut k := le_csSup (bdd k) (Or.inl rfl : (0:ℝ) ∈ S k)
  have cutm : Monotone cut := by
    intro k j hj
    apply csSup_le (ne k)
    intro x hx
    apply le_csSup (bdd j)
    rcases hx with rfl|⟨h,hh⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h,hh.trans_le (qm.monotone hj)⟩
  refine ⟨⟨cut,fun k => q (k+1),cutm,fun k j h => qm.monotone (by omega),
    fun k => ⟨cut0 k,(maxcut k).trans (qmem k).2⟩,fun k => qmem _,fun k => maxcut _,?_,?_⟩⟩
  · intro k
    rw [← measureReal_congr (μ:=I.μB) Ico_ae_eq_Icc,← Ici_sdiff_Ici,
      measureReal_sdiff (Ici_subset_Ici.mpr (qm.monotone (by omega))) measurableSet_Ici]
    change I.Fbar (q (k+1))-I.Fbar (q (k+1+1)) = _
    rw [qe,qe,half_succ (k+1),half_succ k]
    ring
  · intro c hc positive
    let u : Icc (0:ℝ) 1 := ⟨c,hc⟩
    have opt := hp u
    have val := optValue I opt
    change I.sellerProfitAt c = (p u-c)*I.Fbar (p u) at val
    rw [val] at positive
    have signs := (mul_pos_iff.mp positive).resolve_right (fun h => h.2.not_ge ENNReal.toReal_nonneg)
    obtain ⟨k,hlo,hhi⟩ := findBin I z qe opt.mem.1 signs.2
    have cutle : cut k ≤ c := by
      apply csSup_le (ne k)
      intro d hd
      rcases hd with rfl|⟨hd,pd⟩
      · exact hc.1
      · by_contra! rev
        have cmp := optMono I rev opt (hp ⟨d,hd⟩)
        linarith
    refine ⟨k,⟨cutle,le_csSup (bdd _) (Or.inr ⟨hc,hhi⟩ : c ∈ S (k+1))⟩,?_⟩
    have comp : I.Fbar (p u) ≤ half k := (tailAnti I hlo).trans_eq (qe k)
    have h1 := mul_le_mul_of_nonneg_left comp signs.1.le
    have h2 := mul_lt_mul_of_pos_right (sub_lt_sub_right hhi c) (half_pos k)
    rw [val]
    linarith

namespace Bins

private def line {I : BTInstance} (B : Bins I) (k : ℕ) (c : ℝ) :=
  if c ∈ Icc (B.seller k) (B.seller (k+1)) then (B.buyer k-c)*(half k/4) else 0

private theorem lineBounds {I : BTInstance} (B : Bins I) (k : ℕ) (c : ℝ) :
    0 ≤ B.line k c ∧ B.line k c ≤ half k := by
  unfold line
  split
  · rename_i h
    have lo := (B.seller_mem k).1.trans h.1
    have hi := h.2.trans (B.tradable k)
    have y := (B.buyer_mem k).2
    have hh := half_pos k
    exact ⟨mul_nonneg (sub_nonneg.mpr hi) (by positivity),by nlinarith [mul_nonneg (sub_nonneg.mpr (show B.buyer k-c ≤ 1 by linarith)) hh.le]⟩
  · exact ⟨le_rfl,(half_pos k).le⟩

private theorem lineMeas {I : BTInstance} (B : Bins I) (k : ℕ) : Measurable (B.line k) :=
  Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

private def matching {I : BTInstance} (B : Bins I) (n : ℕ) : OrderedMatching where
  N := n
  mB := fun k => B.buyer k.val
  mS := fun k => B.seller k.val
  zero_le_mB := (B.buyer_mem 0).1
  mB_le_one := (B.buyer_mem n).2
  mB_mono := fun _ _ h => B.buyers h
  zero_le_mS := (B.seller_mem 0).1
  mS_le_one := (B.seller_mem n).2
  mS_mono := fun _ _ h => B.sellers h
  tradable := fun k => B.tradable k

private def rectangle {I : BTInstance} (B : Bins I) (k : ℕ) (x : ℝ × ℝ) : ℝ :=
  if B.seller k ≤ x.1 ∧ x.1 ≤ B.seller (k+1) ∧ B.buyer k ≤ x.2 ∧ x.2 ≤ B.buyer (k+1) then x.2 - x.1 else 0

private theorem rectInt {I : BTInstance} (B : Bins I) (k : ℕ) : Integrable (B.rectangle k) I.law := by
  letI := I.isProb_B
  letI := I.isProb_S
  haveI : IsProbabilityMeasure I.law := inferInstanceAs (IsProbabilityMeasure (I.μS.prod I.μB))
  have hm : Measurable (B.rectangle k) := by
    apply Measurable.ite _ (measurable_snd.sub measurable_fst) measurable_const
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
       ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const)))
  apply (integrable_const (μ := I.law) (1:ℝ)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_le]
  unfold rectangle
  split <;> grind [(B.seller_mem k).1,(B.buyer_mem (k+1)).2,B.tradable k]

private theorem lineInt {I : BTInstance} (B : Bins I) (k : ℕ) : Integrable (B.line k) I.μS := by
  letI := I.isProb_S
  apply (integrable_const (μ := I.μS) (half k)).mono' (B.lineMeas k).aestronglyMeasurable
  exact Eventually.of_forall (fun c => by rw [Real.norm_eq_abs,abs_of_nonneg (B.lineBounds k c).1];exact (B.lineBounds k c).2)

private theorem line_le_rectangle {I : BTInstance} (B : Bins I) (k : ℕ) :
    (∫ c, B.line k c ∂I.μS) ≤ ∫ x, B.rectangle k x ∂I.law := by
  letI := I.isProb_B
  letI := I.isProb_S
  rw [show (∫ x, B.rectangle k x ∂I.law) = ∫ c, ∫ v, B.rectangle k (c,v) ∂I.μB ∂I.μS from
    integral_prod _ (B.rectInt k)]
  apply integral_mono_ae (B.lineInt k) (B.rectInt k).integral_prod_left
  apply Eventually.of_forall
  intro c
  unfold line
  split
  · rename_i hc
    let t := Icc (B.buyer k) (B.buyer (k+1))
    have tmeas : MeasurableSet t := measurableSet_Icc
    have lower (v : ℝ) : t.indicator (fun _ => B.buyer k - c) v ≤ B.rectangle k (c,v) := by
      simp only [rectangle,Set.indicator_apply,t,mem_Icc,hc.1,hc.2,true_and]
      split_ifs <;> grind
    have hi : Integrable (fun v => B.rectangle k (c,v)) I.μB := by
      have eq : (fun v => B.rectangle k (c,v)) = t.indicator (fun v => v-c) := by
        funext v; simp [rectangle,t,Set.indicator_apply,hc.1,hc.2]
      rw [eq]
      apply IntegrableOn.integrable_indicator _ tmeas
      exact (continuous_id.sub continuous_const).continuousOn.integrableOn_compact isCompact_Icc
    have bound := integral_mono ((integrable_const _).indicator tmeas) hi lower
    rw [integral_indicator_const _ tmeas,smul_eq_mul] at bound
    change I.μB.real (Icc _ _) * _ ≤ _ at bound
    rw [B.mass] at bound
    linarith
  · rename_i hc
    have eq : (fun v => B.rectangle k (c,v)) = 0 := by
      funext v
      simp only [rectangle,Pi.zero_apply]
      split <;> grind [mem_Icc]
    change 0 ≤ ∫ v, B.rectangle k (c,v) ∂I.μB
    rw [eq]
    exact (integral_zero (μ:=I.μB) (G:=ℝ)).ge

private theorem finiteGain {I : BTInstance} (B : Bins I) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∫ c, B.line k c ∂I.μS) ≤ I.orderedMatching (B.matching n) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum (fun k _ => B.line_le_rectangle k)

end Bins

theorem sellerMatching (I : BTInstance) :
    ∃ M : OrderedMatching, 1 / 4 * I.sellerProfit ≤ I.orderedMatching M := by
  classical
  letI := I.isProb_S
  obtain ⟨B⟩ := makeBins I
  by_cases pos : 0 < I.sellerProfit
  swap
  · exact ⟨B.matching 0,(show 1/4*I.sellerProfit ≤ 0 by linarith).trans (by simpa using B.finiteGain 0)⟩
  have prInt : Integrable I.sellerProfitAt I.μS := by
    by_contra h
    exact pos.ne' (integral_undef h)
  have halfSum : Summable half := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let total (c : ℝ) := ∑' k, B.line k c
  have sum (c) : Summable (fun k => B.line k c) :=
    Summable.of_nonneg_of_le (fun k => (B.lineBounds k c).1) (fun k => (B.lineBounds k c).2) halfSum
  have t0 (c) : 0 ≤ total c := tsum_nonneg (fun k => (B.lineBounds k c).1)
  have tInt : Integrable total I.μS := by
    apply (integrable_const (μ:=I.μS) (∑' k, half k)).mono' (Measurable.tsum (fun k => B.lineMeas k)).aestronglyMeasurable
    apply Eventually.of_forall
    intro c
    rw [Real.norm_eq_abs,abs_of_nonneg (t0 c)]
    exact (sum c).tsum_le_tsum (fun k => (B.lineBounds k c).2) halfSum
  have strict (c) (hc : c ∈ Icc (0:ℝ) 1) (hp : 0 < I.sellerProfitAt c) :
      I.sellerProfitAt c/4 < total c := by
    obtain ⟨k,hm,gt⟩ := B.dominates c hc hp
    have lower : (B.buyer k-c)*(half k/4) = B.line k c := by simp [Bins.line,hm]
    exact gt.trans_le (lower ▸ (sum c).le_tsum k (fun i _ => (B.lineBounds i c).1))
  let frac (c : ℝ) := I.sellerProfitAt c / 4
  have fInt : Integrable frac I.μS := prInt.div_const _
  have hle : frac ≤ᵐ[I.μS] total := (supported I.support_S).mono (fun c hc => by
    by_cases hp : 0 < I.sellerProfitAt c
    · exact (strict c hc hp).le
    · dsimp [frac]; linarith [t0 c])
  have greater : (∫ c, frac c ∂I.μS) < ∫ c, total c ∂I.μS := by
    refine lt_of_le_of_ne (integral_mono_ae fInt tInt hle) ?_
    intro eq
    have same := (integral_eq_iff_of_ae_le fInt tInt hle).1 eq
    apply pos.not_ge
    apply integral_nonpos_of_ae
    filter_upwards [same,supported I.support_S] with c ce hc
    by_contra! hp
    exact (strict c hc hp).ne ce
  have normBound : Summable (fun k => ∫ c, ‖B.line k c‖ ∂I.μS) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _)) _ halfSum
    intro k
    calc
      _ ≤ ∫ _, half k ∂I.μS := integral_mono (B.lineInt k).norm (integrable_const _) (fun c => by
        rw [Real.norm_eq_abs,abs_of_nonneg (B.lineBounds k c).1]; exact (B.lineBounds k c).2)
      _ = half k := by simp
  have limit := (hasSum_integral_of_summable_integral_norm B.lineInt normBound).tendsto_sum_nat
  obtain ⟨n,hn⟩ := (limit.eventually (lt_mem_nhds greater)).exists
  have fe : (∫ c, frac c ∂I.μS) = 1 / 4 * I.sellerProfit := by
    simp only [frac,div_eq_mul_inv,integral_mul_const,BTInstance.sellerProfit,one_mul,mul_comm,integral_const_mul]
  exact ⟨B.matching n,(fe ▸ hn.le).trans (B.finiteGain n)⟩

/-- Swap buyer and seller and replace both prices by their complements. -/
private def reflect : ℝ ≃ᵐ ℝ where
  toFun := fun x => 1-x
  invFun := fun x => 1-x
  left_inv := by intro;ring
  right_inv := by intro;ring
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

private theorem reflectAtoms (μ : Measure ℝ) [NullSingletonClass μ] : NullSingletonClass (μ.map reflect) := by
  refine ⟨fun x => ?_⟩
  rw [Measure.map_apply reflect.measurable (measurableSet_singleton x)]
  have pre : reflect ⁻¹' {x} = {1-x} := by
    ext t
    change (1-t=x) ↔ (t=1-x)
    constructor <;> intro h <;> linarith
  simp [pre]

private theorem reflectSupport (μ : Measure ℝ) (h : μ (Icc 0 1) = 1) :
    μ.map reflect (Icc 0 1) = 1 := by
  rw [Measure.map_apply reflect.measurable measurableSet_Icc]
  have pre : reflect ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext t
    change (0 ≤ 1-t ∧ 1-t ≤ 1) ↔ (0 ≤ t ∧ t ≤ 1)
    grind
  rwa [pre]

private def swapMarket (I : BTInstance) : BTInstance where
  μB := I.μS.map reflect
  μS := I.μB.map reflect
  isProb_B := by letI := I.isProb_S; exact Measure.isProbabilityMeasure_map reflect.measurable.aemeasurable
  isProb_S := by letI := I.isProb_B; exact Measure.isProbabilityMeasure_map reflect.measurable.aemeasurable
  noAtoms_B := by letI := I.noAtoms_S; exact reflectAtoms _
  noAtoms_S := by letI := I.noAtoms_B; exact reflectAtoms _
  support_B := reflectSupport _ I.support_S
  support_S := reflectSupport _ I.support_B

private theorem swapTail (I : BTInstance) (p : ℝ) : (swapMarket I).Fbar p = I.G (1-p) := by
  unfold BTInstance.Fbar BTInstance.G
  change (I.μS.map reflect (Ici p)).toReal = _
  rw [Measure.map_apply reflect.measurable measurableSet_Ici]
  have eq : reflect ⁻¹' Ici p = Iic (1-p) := by
    ext t
    change p ≤ 1-t ↔ t ≤ 1-p
    constructor <;> intro h <;> linarith
  rw [eq]

private theorem swapProfitAt (I : BTInstance) (v : ℝ) :
    (swapMarket I).sellerProfitAt (reflect v) = I.buyerProfitAt v := by
  unfold BTInstance.sellerProfitAt BTInstance.buyerProfitAt iSup
  congr 1
  ext u
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨⟨1-(s:ℝ),by constructor <;> linarith [s.2.1,s.2.2]⟩,?_⟩
    change (v-(1-s))*I.G (1-s) = ((s:ℝ)-(1-v))*(swapMarket I).Fbar s
    rw [swapTail]
    ring
  · rintro ⟨b,rfl⟩
    refine ⟨⟨1-(b:ℝ),by constructor <;> linarith [b.2.1,b.2.2]⟩,?_⟩
    change ((1-b)-(1-v))*(swapMarket I).Fbar (1-b) = (v-(b:ℝ))*I.G b
    rw [swapTail,sub_sub_cancel]
    ring

private theorem swapProfit (I : BTInstance) : (swapMarket I).sellerProfit = I.buyerProfit := by
  change (∫ c, (swapMarket I).sellerProfitAt c ∂I.μB.map reflect) = _
  rw [integral_map_equiv]
  exact integral_congr_ae (Eventually.of_forall (fun _ => swapProfitAt I _))

private def swapMatching (M : OrderedMatching) : OrderedMatching where
  N := M.N
  mB := fun k => 1 - M.mS k.rev
  mS := fun k => 1 - M.mB k.rev
  zero_le_mB := by simpa using sub_nonneg.mpr M.mS_le_one
  mB_le_one := by simp [M.zero_le_mS]
  mB_mono := fun _ _ h => sub_le_sub_left (M.mS_mono (Fin.rev_le_rev.mpr h)) _
  zero_le_mS := by simpa using sub_nonneg.mpr M.mB_le_one
  mS_le_one := by simp [M.zero_le_mB]
  mS_mono := fun _ _ h => sub_le_sub_left (M.mB_mono (Fin.rev_le_rev.mpr h)) _
  tradable := by intro i; simpa only [Fin.rev_castSucc,Fin.rev_succ] using sub_le_sub_left (M.tradable i.rev) 1

private theorem swapIntegral (I : BTInstance) (f : ℝ × ℝ → ℝ) :
    (∫ y, f y ∂(swapMarket I).law) = ∫ x, f (1-x.2,1-x.1) ∂I.law := by
  letI := I.isProb_B
  letI := I.isProb_S
  change (∫ y, f y ∂(I.μB.map reflect).prod (I.μS.map reflect)) = _
  rw [Measure.map_prod_map _ _ reflect.measurable reflect.measurable]
  change (∫ y, f y ∂(I.μB.prod I.μS).map (reflect.prodCongr reflect)) = _
  rw [integral_map_equiv]
  exact (integral_prod_swap (μ:=I.μB) (ν:=I.μS) (fun x => f ((reflect.prodCongr reflect) x))).symm

private def score (M : OrderedMatching) (k : Fin M.N) (x : ℝ × ℝ) : ℝ :=
  if M.mS k.castSucc ≤ x.1 ∧ x.1 ≤ M.mS k.succ ∧ M.mB k.castSucc ≤ x.2 ∧ x.2 ≤ M.mB k.succ then x.2-x.1 else 0

private theorem swapScore (M : OrderedMatching) (k : Fin M.N) (x : ℝ × ℝ) :
    score M k (1-x.2,1-x.1) = score (swapMatching M) k.rev x := by
  simp only [score,swapMatching,Fin.rev_succ,Fin.rev_castSucc,Fin.rev_rev]
  split_ifs <;> grind

private theorem swapGain (I : BTInstance) (M : OrderedMatching) :
    (swapMarket I).orderedMatching M = I.orderedMatching (swapMatching M) := by
  let g (k : Fin M.N) := ∫ x, score (swapMatching M) k x ∂I.law
  change (∑ k, ∫ x, score M k x ∂(swapMarket I).law) = ∑ k, g k
  rw [← Equiv.sum_comp Fin.revPerm g]
  apply Finset.sum_congr rfl
  intro k _
  rw [swapIntegral]
  exact integral_congr_ae (Eventually.of_forall (fun x => swapScore M k x))

theorem buyerMatching (I : BTInstance) :
    ∃ M : OrderedMatching, 1 / 4 * I.buyerProfit ≤ I.orderedMatching M := by
  obtain ⟨M,h⟩ := sellerMatching (swapMarket I)
  rw [swapProfit,swapGain] at h
  exact ⟨swapMatching M,h⟩

end StratifyMarkets.DoubleAuction.PricingProof
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_3_5
section
open StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) :
    (∃ M : OrderedMatching, 1 / 4 * I.sellerProfit ≤ I.orderedMatching M) ∧
    (∃ M : OrderedMatching, 1 / 4 * I.buyerProfit ≤ I.orderedMatching M) :=
  ⟨PricingProof.sellerMatching I, PricingProof.buyerMatching I⟩
end
