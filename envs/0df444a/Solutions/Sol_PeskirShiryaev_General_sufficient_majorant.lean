-- Prove2me | solution 1 for PeskirShiryaev.General.sufficient_majorant
-- status  : ACCEPTED   (disprove)
-- author  : @ShouqiaoWang
-- created : 2026-10-30T13:05:40.848538+00:00
-- url     : https://prove2.me/submissions/0815fa84-0ef0-498e-8b7b-2f68cea94bc3

import Mathlib
import Definitions.Def_PeskirShiryaev_General_StoppingProblem


-- NonBorel

open MeasureTheory Set TopologicalSpace
open scoped Topology

namespace ContactCounterexample
abbrev Baire := ℕ → ℕ
noncomputable def basis : ℕ → Set (Baire × Baire) :=
  (exists_seq_basis (Baire × Baire)).choose
lemma basis_spec : IsTopologicalBasis (range basis) :=
  (exists_seq_basis (Baire × Baire)).choose_spec

def universalClosed (a x y : Baire) : Prop :=
  ∀ n, a n = 0 ∨ (x,y) ∉ basis n

lemma universalClosed_closed :
    IsClosed {p : Baire × (Baire × Baire) | universalClosed p.1 p.2.1 p.2.2} := by
  simp only [universalClosed, setOf_forall]
  change IsClosed (⋂ n, {p : Baire × (Baire × Baire) | p.1 n = 0 ∨ p.2 ∉ basis n})
  apply isClosed_iInter
  intro n
  exact (isClosed_eq ((continuous_apply n).comp continuous_fst) continuous_const).union
    ((basis_spec.isOpen (mem_range_self n)).isClosed_compl.preimage continuous_snd)

lemma represents_closed (C : Set (Baire × Baire)) (hC : IsClosed C) :
    ∃ a : Baire, ∀ x y, universalClosed a x y ↔ (x,y) ∈ C := by
  classical
  refine ⟨fun n => if basis n ⊆ Cᶜ then 1 else 0, ?_⟩
  intro x y
  constructor
  · intro h
    by_contra hn
    obtain ⟨U, ⟨n, rfl⟩, hU, hUC⟩ := basis_spec.exists_subset_of_mem_open hn hC.isOpen_compl
    have := h n
    simp only [if_pos hUC, Nat.one_ne_zero, false_or] at this
    exact this hU
  · intro h n
    by_cases hn : basis n ⊆ Cᶜ
    · right
      exact fun hm => hn hm h
    · left
      simp [hn]

lemma represents_analytic (A : Set Baire) (hA : AnalyticSet A) :
    ∃ a : Baire, ∀ x, (∃ y, universalClosed a x y) ↔ x ∈ A := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · obtain ⟨a, ha⟩ := represents_closed ∅ isClosed_empty
    exact ⟨a, fun x => by simp [ha]⟩
  · obtain ⟨a, ha⟩ := represents_closed {p : Baire × Baire | p.1 = f p.2}
      (isClosed_eq continuous_fst (hf.comp continuous_snd))
    refine ⟨a, fun x => ?_⟩
    simp only [ha, mem_setOf_eq, mem_range]
    exact exists_congr fun y => eq_comm

lemma diagonal_not_measurable :
    ¬ MeasurableSet {a : Baire | ∃ y, universalClosed a a y} := by
  intro h
  obtain ⟨a, ha⟩ := represents_analytic _ h.compl.analyticSet
  have hh := ha a
  change (∃ y, universalClosed a a y) ↔ ¬ (∃ y, universalClosed a a y) at hh
  exact iff_not_self hh
end ContactCounterexample

-- BaireCoding

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

namespace ContactCounterexample
abbrev Bits := ℕ → Bool
abbrev InfiniteZeros := {b : Bits // {n | b n = false}.Infinite}
noncomputable def zeroIndex (b : InfiniteZeros) (n : ℕ) : ℕ := Nat.nth (fun i => b.val i = false) n

lemma continuous_zeroIndex (n : ℕ) : Continuous (fun b : InfiniteZeros => zeroIndex b n) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro b
  apply tendsto_nhds_of_eventually_eq
  let k := zeroIndex b n
  have he : ∀ i ∈ Finset.range (k+1), ∀ᶠ c : InfiniteZeros in 𝓝 b, c.val i = b.val i := by
    intro i hi
    exact ((continuous_apply i).comp continuous_subtype_val).continuousAt.eventually
      (isOpen_discrete {b.val i} |>.mem_nhds rfl)
  filter_upwards [Filter.eventually_all_finset (Finset.range (k+1)) |>.mpr he] with c hc
  have hk : c.val k = false := (hc k (by simp)).trans (Nat.nth_mem_of_infinite b.property n)
  have hcount : Nat.count (fun i => c.val i = false) k = Nat.count (fun i => b.val i = false) k := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [hc i (by simpa using (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))]
  have hcnum : Nat.count (fun i => c.val i = false) k = n :=
    hcount.trans (Nat.count_nth_of_infinite b.property n)
  change Nat.nth (fun i => c.val i = false) n = k
  rw [← hcnum]
  exact Nat.nth_count hk

noncomputable def decode (b : InfiniteZeros) : Baire
  | 0 => zeroIndex b 0
  | n+1 => zeroIndex b (n+1) - zeroIndex b n - 1

lemma continuous_decode : Continuous decode := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_zeroIndex 0
  | succ n => exact ((continuous_zeroIndex (n+1)).sub (continuous_zeroIndex n)).sub continuous_const

def positions (a : Baire) : ℕ → ℕ
  | 0 => a 0
  | n+1 => positions a n + a (n+1) + 1

lemma positions_strictMono (a : Baire) : StrictMono (positions a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [positions]
  omega

noncomputable def encode (a : Baire) : InfiniteZeros := by
  classical
  refine ⟨fun i => if i ∈ range (positions a) then false else true, ?_⟩
  change Set.Infinite {n | (if n ∈ range (positions a) then false else true) = false}
  simpa only [ite_eq_left_iff, Bool.true_eq_false, imp_false, not_not, Set.setOf_mem_eq] using
    Set.infinite_range_of_injective (positions_strictMono a).injective

lemma zeroIndex_encode (a : Baire) (n : ℕ) : zeroIndex (encode a) n = positions a n := by
  classical
  have hi : {i | (encode a).val i = false} = range (positions a) := by
    ext i
    simp [encode]
  have hh := Nat.nth_comp_of_strictMono (p := fun i => (encode a).val i = false)
    (positions_strictMono a) (fun k hk => hi ▸ hk)
    (n := n) (fun hf => ((encode a).property hf).elim)
  have he : (fun i => (encode a).val (positions a i) = false) = fun _ => True := by
    funext i
    simp [encode]
  rw [he] at hh
  simpa [zeroIndex] using hh.symm

lemma decode_encode (a : Baire) : decode (encode a) = a := by
  funext n
  cases n with
  | zero => simp [decode, zeroIndex_encode, positions]
  | succ n =>
    simp only [decode, zeroIndex_encode, positions]
    omega

lemma decode_surjective : Function.Surjective decode := fun a => ⟨encode a, decode_encode a⟩
end ContactCounterexample

-- CantorCoding

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped Topology

namespace ContactCounterexample
noncomputable def point (b : Bits) : ℝ := (cantorSetHomeomorphNatToBool.symm b).val

lemma point_mem (b : Bits) : point b ∈ cantorSet :=
  (cantorSetHomeomorphNatToBool.symm b).property

lemma point_digits (b : Bits) : point b = Real.ofDigits (fun i => cond (b i) (2 : Fin 3) 0) := rfl

lemma point_embedding : Topology.IsEmbedding point :=
  Topology.IsEmbedding.subtypeVal.comp cantorSetHomeomorphNatToBool.symm.isEmbedding

lemma point_range : range point = cantorSet := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩; exact point_mem b
  · intro hx
    exact ⟨cantorSetHomeomorphNatToBool ⟨x,hx⟩,
      congrArg Subtype.val (cantorSetHomeomorphNatToBool.symm_apply_apply ⟨x,hx⟩)⟩

lemma point_le_of_prefix {b c : Bits} {N : ℕ}
    (ht : ∀ n, N ≤ n → b n = true) (hp : ∀ n, n < N → c n = b n) :
    point c ≤ point b := by
  simp only [point_digits, Real.ofDigits]
  apply Real.summable_ofDigitsTerm.tsum_le_tsum _ Real.summable_ofDigitsTerm
  intro n
  simp only [Real.ofDigitsTerm]
  by_cases hn : n < N
  · rw [hp n hn]
  · rw [ht n (by omega)]
    cases c n <;> simp <;> positivity

noncomputable def endpointBits (F : Finset ℕ) : Bits := fun n => decide (n ∉ F)

lemma endpoint_tail (F : Finset ℕ) : ∀ n, F.sup id + 1 ≤ n → endpointBits F n = true := by
  intro n hn
  simp only [endpointBits, decide_eq_true_eq]
  intro hm
  have := Finset.le_sup (f := id) hm
  simp only [id_eq] at this
  omega

lemma endpoint_gap (F : Finset ℕ) : ∃ ε : ℝ, 0 < ε ∧
    ∀ t, t ∈ cantorSet → point (endpointBits F) ≤ t →
      t < point (endpointBits F) + ε → t = point (endpointBits F) := by
  let b := endpointBits F
  let N := F.sup id + 1
  let C : Set Bits := {c | ∀ n ∈ Finset.range N, c n = b n}
  have hC : IsOpen C := by
    simp only [C, Set.setOf_forall]
    apply isOpen_biInter_finset
    intro n hn
    exact (isOpen_discrete ({b n} : Set Bool)).preimage
      (show Continuous (fun c : Bits => c n) from continuous_apply n)
  obtain ⟨U,hU,hUC⟩ := point_embedding.isInducing.isOpen_iff.mp hC
  have hbU : point b ∈ U := by
    have : b ∈ C := by simp [C]
    rw [← hUC] at this
    exact this
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU (point b) hbU
  refine ⟨ε,hε,?_⟩
  intro t ht hle hlt
  obtain ⟨c,rfl⟩ := point_range.symm ▸ ht
  apply le_antisymm _ hle
  apply point_le_of_prefix (endpoint_tail F)
  intro n hn
  have hpc : point c ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith)
  have hc : c ∈ C := by rw [← hUC]; exact hpc
  exact hc n (Finset.mem_range.mpr hn)

noncomputable def goodSet : Set ℝ := point '' {b : Bits | {n | b n = false}.Infinite}

lemma goodSet_subset : goodSet ⊆ cantorSet := by
  rintro _ ⟨b,hb,rfl⟩
  exact point_mem b

lemma goodSet_iff (t : ℝ) : t ∈ goodSet ↔
    t ∈ cantorSet ∧ ∀ F : Finset ℕ, t ≠ point (endpointBits F) := by
  classical
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨point_mem b, ?_⟩
    intro F he
    have heq := point_embedding.injective he
    have hfin : {n | endpointBits F n = false}.Finite := by
      simpa [endpointBits] using F.finite_toSet
    exact hb (heq ▸ hfin)
  · rintro ⟨ht,hneq⟩
    obtain ⟨b,rfl⟩ := point_range.symm ▸ ht
    refine ⟨b,?_,rfl⟩
    by_contra hb
    have hf : {n | b n = false}.Finite := Set.not_infinite.mp hb
    apply hneq hf.toFinset
    congr 1
    funext n
    simp only [endpointBits, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    cases b n <;> simp
end ContactCounterexample

-- RightContinuousZeros

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped Topology

namespace ContactCounterexample
lemma rightContinuous_interval (a b w t : ℝ) :
    ContinuousWithinAt (fun s => if s ∈ Ico a b then w else 0) (Ici t) t := by
  classical
  apply tendsto_nhds_of_eventually_eq
  by_cases ha : t < a
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha)] with s hs
    simp only [mem_Iio] at hs
    simp [not_le.mpr ha, not_le.mpr hs]
  · by_cases hb : t < b
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with s hs hsb
      simp only [mem_Ici, mem_Iio] at hs hsb
      simp [not_lt.mp ha, hb, (not_lt.mp ha).trans hs, hsb]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_Ici] at hs
      have : ¬ s < b := not_lt.mpr ((not_lt.mp hb).trans hs)
      simp [hb, this]

noncomputable def gap (F : Finset ℕ) : ℝ := (endpoint_gap F).choose
lemma gap_pos (F : Finset ℕ) : 0 < gap F := (endpoint_gap F).choose_spec.1
lemma gap_spec (F : Finset ℕ) : ∀ t, t ∈ cantorSet → point (endpointBits F) ≤ t →
    t < point (endpointBits F) + gap F → t = point (endpointBits F) :=
  (endpoint_gap F).choose_spec.2

noncomputable def weight (F : Finset ℕ) : ℝ := (1/2 : ℝ) ^ Encodable.encode F
lemma weight_pos (F : Finset ℕ) : 0 < weight F := by unfold weight; positivity
lemma weight_summable : Summable weight := by
  exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).comp_injective Encodable.encode_injective

noncomputable def bump (F : Finset ℕ) (t : ℝ) : ℝ :=
  if t ∈ Ico (point (endpointBits F)) (point (endpointBits F) + gap F) then weight F else 0
lemma bump_nonneg (F : Finset ℕ) (t : ℝ) : 0 ≤ bump F t := by
  unfold bump
  split_ifs <;> positivity [weight_pos F]
lemma bump_bound (F : Finset ℕ) (t : ℝ) : ‖bump F t‖ ≤ weight F := by
  unfold bump
  split_ifs <;> simp [abs_of_pos (weight_pos F), le_of_lt (weight_pos F)]
lemma bumps_summable (t : ℝ) : Summable (fun F => bump F t) :=
  weight_summable.of_norm_bounded (fun F => bump_bound F t)

noncomputable def background (t : ℝ) : ℝ := infDist t cantorSet + ∑' F, bump F t
lemma background_nonneg (t : ℝ) : 0 ≤ background t :=
  add_nonneg infDist_nonneg (tsum_nonneg (fun F => bump_nonneg F t))

lemma background_rightContinuous (t : ℝ) : ContinuousWithinAt background (Ici t) t := by
  apply ContinuousWithinAt.add (continuous_infDist_pt cantorSet).continuousWithinAt
  apply tendsto_tsum_of_dominated_convergence weight_summable
  · intro F
    exact rightContinuous_interval _ _ _ _
  · exact Eventually.of_forall fun s F => bump_bound F s

lemma background_zero_iff (t : ℝ) : background t = 0 ↔ t ∈ goodSet := by
  classical
  rw [goodSet_iff]
  constructor
  · intro h
    have hd : infDist t cantorSet = 0 := by
      have : 0 ≤ ∑' F, bump F t := tsum_nonneg (fun F => bump_nonneg F t)
      have : 0 ≤ infDist t cantorSet := infDist_nonneg
      unfold background at h
      linarith
    refine ⟨(isClosed_cantorSet.mem_iff_infDist_zero ⟨0,zero_mem_cantorSet⟩).mpr hd, ?_⟩
    intro F ht
    have hterm := (bumps_summable t).le_tsum F (fun i hi => bump_nonneg i t)
    have hb : bump F t = weight F := by
      simp [bump,ht,gap_pos]
    have hw := weight_pos F
    unfold background at h
    linarith
  · rintro ⟨ht,hneq⟩
    have hb : ∀ F, bump F t = 0 := by
      intro F
      unfold bump
      rw [if_neg]
      intro hmem
      exact hneq F (gap_spec F t ht hmem.1 hmem.2)
    simp [background,infDist_zero_of_mem ht,hb]
end ContactCounterexample

-- PathConstruction

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped Topology NNReal

namespace ContactCounterexample
noncomputable def goodToBits (t : goodSet) : InfiniteZeros :=
  ⟨cantorSetHomeomorphNatToBool ⟨t.val,goodSet_subset t.property⟩, by
    obtain ⟨b,hb,he⟩ := t.property
    have hsame : cantorSetHomeomorphNatToBool ⟨t.val,goodSet_subset t.property⟩ = b := by
      apply cantorSetHomeomorphNatToBool.symm.injective
      apply Subtype.ext
      simpa [point] using he.symm
    rwa [hsame]⟩

lemma continuous_goodToBits : Continuous goodToBits := by
  apply Continuous.subtype_mk
  exact cantorSetHomeomorphNatToBool.continuous.comp
    (continuous_subtype_val.subtype_mk _)

noncomputable def goodDecode (t : goodSet) : Baire := decode (goodToBits t)
lemma continuous_goodDecode : Continuous goodDecode := continuous_decode.comp continuous_goodToBits

lemma goodDecode_surjective : Function.Surjective goodDecode := by
  intro a
  let b := encode a
  let t : goodSet := ⟨point b.val, ⟨b.val,b.property,rfl⟩⟩
  refine ⟨t, ?_⟩
  have hb : goodToBits t = b := by
    apply Subtype.ext
    exact cantorSetHomeomorphNatToBool.apply_symm_apply b.val
  change decode (goodToBits t) = a
  rw [hb]
  exact decode_encode a

lemma exists_testing_function : ∃ h : C(Baire × ℝ, ℝ),
    (∀ p, 0 ≤ h p) ∧
    (∀ (a : Baire) (t : goodSet), h (a,t.val) = 0 ↔ universalClosed a a (goodDecode t)) := by
  let C : Set (Baire × goodSet) := {p | universalClosed p.1 p.1 (goodDecode p.2)}
  have hC : IsClosed C := universalClosed_closed.preimage
    (continuous_fst.prodMk (continuous_fst.prodMk (continuous_goodDecode.comp continuous_snd)))
  have hi : Topology.IsInducing (fun p : Baire × goodSet => (p.1,p.2.val)) :=
    (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal).isInducing
  obtain ⟨D,hD,hDC⟩ := hi.isClosed_iff.mp hC
  obtain ⟨h,hh,hbounds⟩ :=
    perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.mp inferInstance D hD
  refine ⟨h,fun p => (hbounds p).1,?_⟩
  intro a t
  have he : (a,t) ∈ (fun p : Baire × goodSet => (p.1,p.2.val)) ⁻¹' D ↔ (a,t) ∈ C := by
    rw [hDC]
  simpa only [hh, mem_preimage, mem_singleton_iff, C, mem_setOf_eq] using he

noncomputable def testFunction : C(Baire × ℝ, ℝ) := exists_testing_function.choose
lemma test_nonneg (a : Baire) (t : ℝ) : 0 ≤ testFunction (a,t) :=
  exists_testing_function.choose_spec.1 (a,t)
lemma test_zero (a : Baire) (t : goodSet) :
    testFunction (a,t.val) = 0 ↔ universalClosed a a (goodDecode t) :=
  exists_testing_function.choose_spec.2 a t

noncomputable def path (a : Baire) (t : ℝ) : ℝ := background t + testFunction (a,t)
lemma path_nonneg (a : Baire) (t : ℝ) : 0 ≤ path a t :=
  add_nonneg (background_nonneg t) (test_nonneg a t)
lemma path_rightContinuous (a : Baire) (t : ℝ) : ContinuousWithinAt (path a) (Ici t) t := by
  apply (background_rightContinuous t).add
  exact (testFunction.continuous.comp (continuous_const.prodMk continuous_id)).continuousWithinAt
lemma measurable_path (t : ℝ) : Measurable (fun a => path a t) := by
  exact measurable_const.add
    (testFunction.continuous.comp (continuous_id.prodMk continuous_const)).measurable

lemma path_zero_iff (a : Baire) (t : ℝ) : path a t = 0 ↔
    ∃ ht : t ∈ goodSet, universalClosed a a (goodDecode ⟨t,ht⟩) := by
  constructor
  · intro h
    have hb : background t = 0 := by
      have := background_nonneg t
      have := test_nonneg a t
      unfold path at h
      linarith
    have ht := (background_zero_iff t).mp hb
    refine ⟨ht,(test_zero a ⟨t,ht⟩).mp ?_⟩
    simpa [path,hb] using h
  · rintro ⟨ht,hU⟩
    have hb := (background_zero_iff t).mpr ht
    have hh := (test_zero a ⟨t,ht⟩).mpr hU
    simp [path,hb,hh]

lemma exists_path_zero (a : Baire) : (∃ t : ℝ≥0, path a t = 0) ↔
    ∃ y, universalClosed a a y := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨hs,hU⟩ := (path_zero_iff a t).mp ht
    exact ⟨_,hU⟩
  · rintro ⟨y,hy⟩
    obtain ⟨t,ht⟩ := goodDecode_surjective y
    have hpos := (cantorSet_subset_unitInterval (goodSet_subset t.property)).1
    refine ⟨⟨t.val,hpos⟩,(path_zero_iff a t.val).mpr ⟨t.property,?_⟩⟩
    simpa [ht] using hy

lemma path_zero_time_le (a : Baire) (t : ℝ≥0) (h : path a t = 0) : t ≤ 1 := by
  obtain ⟨ht,-⟩ := (path_zero_iff a t).mp h
  exact (cantorSet_subset_unitInterval (goodSet_subset ht)).2
end ContactCounterexample

-- CounterexampleModel

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter Metric
open scoped Topology NNReal ENNReal

namespace ContactCounterexample
open PeskirShiryaev.General
abbrev Sample := ℝ ⊕ Baire
instance : MeasurableSingletonClass Sample where
  measurableSet_singleton x := by
    cases x with
    | inl x => simpa using (measurableSet_singleton x).inl_image (β := Baire)
    | inr a => simpa using (measurableSet_singleton a).inr_image (α := ℝ)
noncomputable def process (t : ℝ≥0) : Sample → State 1
  | Sum.inl x => fun _ => x + (t : ℝ)
  | Sum.inr a => fun _ => -path a t
noncomputable def law (x : State 1) : Measure Sample := Measure.dirac (Sum.inl (x 0))
noncomputable def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace Sample) := ⊤

lemma process_measurable (t : ℝ≥0) : Measurable (process t) := by
  apply Measurable.sumElim
  · exact measurable_pi_lambda _ (fun i => measurable_id.add_const _)
  · exact measurable_pi_lambda _ (fun i => (measurable_path t).neg)

lemma process_rc (ω : Sample) : RightContinuousPaths process ω := by
  intro t
  cases ω with
  | inl x =>
    apply Continuous.continuousWithinAt
    exact continuous_pi fun i => continuous_const.add NNReal.continuous_coe
  | inr a =>
    apply continuousWithinAt_pi.mpr
    intro i
    apply ContinuousWithinAt.neg
    exact (path_rightContinuous a t).comp NNReal.continuous_coe.continuousWithinAt
      (fun s hs => hs)

lemma law_measurable (A : Set Sample) (hA : MeasurableSet A) : Measurable (fun x => law x A) := by
  simp only [law, Measure.dirac_apply' _ hA]
  exact (measurable_const.indicator hA).comp (measurable_inl.comp (measurable_pi_apply 0))

lemma process_starts (x : State 1) : ∀ᵐ ω ∂law x, process 0 ω = x := by
  rw [law, ae_dirac_eq]
  change (fun _ : Fin 1 => x 0 + (0 : ℝ≥0)) = x
  funext i
  simp [Subsingleton.elim i (0 : Fin 1)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma process_markov (x : State 1) (τ : Sample → ℝ≥0∞)
    (hτ : IsStoppingTime filtration τ) (hfin : ∀ᵐ ω ∂law x, τ ω < ⊤)
    (s : ℝ≥0) (f : State 1 → ℝ) (hf : Measurable f)
    (hb : Bornology.IsBounded (range f)) :
    (law x)[fun ω => f (process ((τ ω).toNNReal + s) ω) | hτ.measurableSpace]
      =ᵐ[law x] (fun ω => ∫ ω', f (process s ω') ∂law (process (τ ω).toNNReal ω)) := by
  have he := condExp_congr_ae (m := hτ.measurableSpace)
    (ae_eq_dirac (a := Sum.inl (x 0)) (fun ω => f (process ((τ ω).toNNReal + s) ω)))
  refine he.trans ((Filter.EventuallyEq.of_eq
    (condExp_const (μ := Measure.dirac (Sum.inl (x 0) : Sample)) hτ.measurableSpace_le
      (f (process ((τ (Sum.inl (x 0))).toNNReal + s) (Sum.inl (x 0)))))).trans ?_)
  simp only [Filter.EventuallyEq, law, ae_dirac_eq, Filter.eventually_pure, integral_dirac, process, NNReal.coe_add]
  congr 1
  funext i
  ring

lemma process_qlc (x : State 1) (τ : Sample → ℝ≥0∞) (τn : ℕ → Sample → ℝ≥0∞)
    (hτ : IsStoppingTime filtration τ) (hn : ∀ n, IsStoppingTime filtration (τn n))
    (hm : ∀ ω, Monotone (fun n => τn n ω))
    (ht : ∀ᵐ ω ∂law x, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) :
    ∀ᵐ ω ∂law x, τ ω < ⊤ →
      Tendsto (fun n => process (τn n ω).toNNReal ω) atTop (𝓝 (process (τ ω).toNNReal ω)) := by
  rw [law, ae_dirac_eq] at ht ⊢
  change τ (Sum.inl (x 0)) < ⊤ → _
  intro hfin
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_const_nhds.add
    (NNReal.continuous_coe.continuousAt.tendsto.comp
      ((ENNReal.tendsto_toNNReal hfin.ne).comp ht))

noncomputable def model : MarkovModel 1 Sample where
  dimension_pos := by norm_num
  P := law
  probability := fun x => inferInstanceAs (IsProbabilityMeasure (Measure.dirac (Sum.inl (x 0) : Sample)))
  measurable_laws := law_measurable
  filtration := filtration
  filtration_rightContinuous := ⟨le_top⟩
  X := process
  adapted := fun t => process_measurable t
  starts := process_starts
  rightContinuous := process_rc
  strongMarkov := process_markov
  leftContinuous_stopping := process_qlc

noncomputable def gain (x : State 1) : ℝ := -min |x 0| 1
noncomputable def majorant (x : State 1) : ℝ := -min (max (x 0) 0) 1
lemma gain_continuous : Continuous gain := by unfold gain; fun_prop
lemma majorant_continuous : Continuous majorant := by unfold majorant; fun_prop
lemma gain_bound (x : State 1) : |gain x| ≤ 1 := by
  unfold gain
  rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
  exact min_le_right _ _
lemma gain_le_majorant (x : State 1) : gain x ≤ majorant x := by
  unfold gain majorant
  gcongr
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma gain_integrable : GainIntegrable model gain := by
  refine ⟨gain_continuous.measurable, fun x => ⟨aemeasurable_dirac, ?_⟩⟩
  change (∫⁻ ω, gainSup model gain ω ∂Measure.dirac (Sum.inl (x 0) : Sample)) < ⊤
  rw [lintegral_dirac]
  apply lt_of_le_of_lt _ (by simp : (1 : ℝ≥0∞) < ⊤)
  apply iSup_le
  intro t
  simpa [model] using ENNReal.ofReal_le_ofReal (gain_bound (process t (Sum.inl (x 0))))

lemma reward_at (F : State 1 → ℝ) (σ : Sample → ℝ≥0∞) (x : State 1)
    (hσ : Admissible model x σ) :
    (∫ ω, reward model F σ ω ∂model.P x) = F (fun _ => x 0 + (σ (Sum.inl (x 0))).toReal) := by
  have hfin : σ (Sum.inl (x 0)) < ⊤ := by
    simpa only [model, law, ae_dirac_eq, Filter.eventually_pure] using hσ.2
  change (∫ ω, reward model F σ ω ∂Measure.dirac (Sum.inl (x 0) : Sample)) = _
  rw [integral_dirac]
  simp [reward,hfin.ne,model,process,ENNReal.toReal]

lemma majorant_superharmonic : Superharmonic model majorant := by
  refine ⟨majorant_continuous.measurable, ?_⟩
  intro x σ hσ
  refine ⟨integrable_dirac (by finiteness), ?_⟩
  rw [reward_at _ _ _ hσ]
  unfold majorant
  gcongr
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

lemma majorant_least : LeastMajorant model gain majorant := by
  refine ⟨majorant_superharmonic, gain_le_majorant, ?_⟩
  intro H hH hHG x
  by_cases hx : 0 ≤ x 0
  · have : majorant x = gain x := by simp [majorant,gain,max_eq_left hx,abs_of_nonneg hx]
    rw [this]
    exact hHG x
  · let t : ℝ≥0 := ⟨-x 0,by linarith⟩
    let σ : Sample → ℝ≥0∞ := fun _ => t
    have hσ : Admissible model x σ := ⟨isStoppingTime_const _ t,by simp [σ]⟩
    have hh := (hH.2 x σ hσ).2
    rw [reward_at _ _ _ hσ] at hh
    have hc : (fun _ : Fin 1 => x 0 + (σ (Sum.inl (x 0))).toReal) = 0 := by
      ext i
      change x 0 + (-x 0) = 0
      ring
    rw [hc] at hh
    have hg := hHG 0
    simp [gain] at hg
    have hv : majorant x = 0 := by simp [majorant,max_eq_right (le_of_not_ge hx)]
    linarith

lemma contact_iff (x : State 1) : majorant x = gain x ↔ 0 ≤ x 0 := by
  unfold majorant gain
  constructor
  · intro h
    by_contra hx
    have hx' : x 0 < 0 := lt_of_not_ge hx
    rw [max_eq_right hx'.le, abs_of_neg hx'] at h
    have hh : 0 < min (-x 0) 1 := lt_min (neg_pos.mpr hx') (by norm_num)
    simp only [min_eq_left (by norm_num : (0:ℝ) ≤ 1),neg_zero] at h
    linarith
  · intro hx
    simp [max_eq_left hx,abs_of_nonneg hx]
end ContactCounterexample

-- Disproof

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open PeskirShiryaev.General

namespace ContactCounterexample
lemma fake_contact_finite (a : Baire) :
    contactTime model gain majorant (Sum.inr a) < ⊤ ↔ ∃ y, universalClosed a a y := by
  rw [← exists_path_zero a]
  unfold contactTime entryTime
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨⟨t,ht⟩, hfin⟩
    refine ⟨t,?_⟩
    have hh := (contact_iff _).mp ht
    change 0 ≤ -path a t at hh
    exact le_antisymm (by linarith) (path_nonneg a t)
  · rintro ⟨t,ht⟩
    refine ⟨⟨t,?_⟩,ENNReal.coe_lt_top⟩
    apply (contact_iff _).mpr
    change 0 ≤ -path a t
    simp [ht]

lemma contact_not_stopping : ¬ IsStoppingTime model.filtration (contactTime model gain majorant) := by
  intro h
  have hm : Measurable (fun a : Baire => contactTime model gain majorant (Sum.inr a)) :=
    h.measurable'.comp measurable_inr
  have hs := hm (t := Iio ⊤) measurableSet_Iio
  apply diagonal_not_measurable
  convert hs using 1
  ext a
  exact (fake_contact_finite a).symm
end ContactCounterexample

theorem solution : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (M : MarkovModel d Ω) (G Vhat : State d → ℝ) (hG : GainIntegrable M G)
    (hmajorant : LeastMajorant M G Vhat)
    (hlsc : LowerSemicontinuous Vhat) (husc : UpperSemicontinuous G),
    IsStoppingTime M.filtration (contactTime M G Vhat) ∧
    (((∀ x, ∀ᵐ ω ∂M.P x, contactTime M G Vhat ω < ⊤) →
      Vhat = value M G ∧ Optimal M G (contactTime M G Vhat)) ∧
    ((∃ x, M.P x {ω | contactTime M G Vhat ω < ⊤} < 1) →
      ¬ ∃ τ : Ω → ℝ≥0∞, Optimal M G τ))) := by
  intro h
  exact ContactCounterexample.contact_not_stopping
    (h ContactCounterexample.model ContactCounterexample.gain ContactCounterexample.majorant
      ContactCounterexample.gain_integrable ContactCounterexample.majorant_least
      ContactCounterexample.majorant_continuous.lowerSemicontinuous
      ContactCounterexample.gain_continuous.upperSemicontinuous).1
