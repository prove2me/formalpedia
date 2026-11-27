-- Prove2me | solution 1 for ProcessingNetworks.Stability.equivalent_stability_conditions
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:13:58.255174+00:00
-- url     : https://prove2.me/submissions/6b9f4ef1-f336-4b5a-bd74-82765d736037

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability
open scoped ENNReal

namespace PN1EquivCounterexample

/-! ### Unit exponential distribution -/

noncomputable def exp1Dens (x : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (Real.exp (-x)) else 0

lemma measurable_exp1Dens : Measurable exp1Dens := by
  unfold exp1Dens
  exact Measurable.ite measurableSet_Ioi
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp measurable_neg))
    measurable_const

noncomputable def exp1Measure : Measure ℝ :=
  volume.withDensity exp1Dens

lemma exp1Measure_le_volume : exp1Measure ≤ volume := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [exp1Measure, withDensity_apply _ hs]
  calc ∫⁻ x in s, exp1Dens x ∂volume
      ≤ ∫⁻ _ in s, (1 : ℝ≥0∞) ∂volume := by
        refine lintegral_mono fun x => ?_
        unfold exp1Dens
        split_ifs with hx
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith))
        · simp
    _ = volume s := by simp

lemma exp1Measure_Iic_zero : exp1Measure (Set.Iic 0) = 0 := by
  rw [exp1Measure, withDensity_apply _ measurableSet_Iic]
  have h : ∀ x ∈ Set.Iic (0 : ℝ), exp1Dens x = 0 := by
    intro x hx
    simp only [exp1Dens, Set.mem_Iic] at hx ⊢
    rw [if_neg (not_lt.mpr hx)]
  rw [setLIntegral_congr_fun measurableSet_Iic h]
  simp

lemma exp1Measure_Ioi (s : ℝ) (hs : 0 ≤ s) :
    exp1Measure (Set.Ioi s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [exp1Measure, withDensity_apply _ measurableSet_Ioi]
  have hcongr : ∀ x ∈ Set.Ioi s, exp1Dens x = ENNReal.ofReal (Real.exp (-x)) := by
    intro x hx
    simp only [exp1Dens, Set.mem_Ioi] at hx ⊢
    rw [if_pos (by linarith)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi s) volume :=
    integrableOn_exp_neg_Ioi s
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-x)).le)]
  have hval : ∫ x in Set.Ioi s, Real.exp (-x) = Real.exp (-s) := by
    have hderiv : ∀ x ∈ Set.Ici s,
        HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg
      simpa [Function.comp_def, Pi.neg_def] using h1
    have htend : Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simpa using h1.neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
    simpa using h
  rw [hval]

instance isProbabilityMeasure_exp1Measure : IsProbabilityMeasure exp1Measure := by
  constructor
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi 0) :=
    Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr (Set.mem_Iic.mp h1) (Set.mem_Ioi.mp h2)
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := Set.Iic_union_Ioi
  rw [← huniv, measure_union hdisj measurableSet_Ioi,
    exp1Measure_Iic_zero, exp1Measure_Ioi 0 le_rfl]
  simp


/-! ### Clock space: i.i.d. Exp(1) coordinates -/

noncomputable def μc : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => exp1Measure)

instance : IsProbabilityMeasure μc := by unfold μc; infer_instance

/-- Clock sequences with all entries positive and infinitely many entries `≥ 1`. -/
def Good : Set (ℕ → ℝ) := {u | (∀ n, 0 < u n) ∧ ∀ N, ∃ n, N ≤ n ∧ 1 ≤ u n}

lemma measurableSet_Good : MeasurableSet Good := by
  have : Good = (⋂ n, {u : ℕ → ℝ | 0 < u n}) ∩ ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), {u : ℕ → ℝ | 1 ≤ u n} := by
    ext u; simp [Good]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => ?_)
    (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => ?_)
  · exact measurableSet_lt measurable_const (measurable_pi_apply n)
  · exact measurableSet_le measurable_const (measurable_pi_apply n)

lemma μc_eval (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    μc {u | u n ∈ s} = exp1Measure s :=
  (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => exp1Measure) n).measure_preimage
    hs.nullMeasurableSet

lemma exp1Measure_Iio_one_lt : exp1Measure (Set.Iio 1) < 1 := by
  have h : exp1Measure (Set.Iio 1) = 1 - exp1Measure (Set.Ici 1) := by
    rw [← prob_compl_eq_one_sub measurableSet_Ici, Set.compl_Ici]
  rw [h]
  have hpos : exp1Measure (Set.Ici 1) ≠ 0 := by
    intro h0
    have hle : exp1Measure (Set.Ioi 1) ≤ exp1Measure (Set.Ici 1) :=
      measure_mono Set.Ioi_subset_Ici_self
    rw [h0, exp1Measure_Ioi 1 zero_le_one] at hle
    have : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-1)) :=
      ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    exact absurd hle (not_le.mpr this)
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos

lemma μc_eventually_small (N : ℕ) : μc {u | ∀ n, N ≤ n → u n < 1} = 0 := by
  set c := exp1Measure (Set.Iio 1)
  have hbound : ∀ K : ℕ, μc {u | ∀ n, N ≤ n → u n < 1} ≤ c ^ K := by
    intro K
    have hsub : {u : ℕ → ℝ | ∀ n, N ≤ n → u n < 1} ⊆
        Set.pi (↑(Finset.Ico N (N + K))) (fun _ => Set.Iio (1 : ℝ)) := by
      intro u hu i hi
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact hu i hi.1
    calc μc {u | ∀ n, N ≤ n → u n < 1}
        ≤ μc (Set.pi (↑(Finset.Ico N (N + K))) (fun _ => Set.Iio (1 : ℝ))) := measure_mono hsub
      _ = c ^ K := by
        rw [μc, Measure.infinitePi_pi (μ := fun _ : ℕ => exp1Measure)
          (s := Finset.Ico N (N + K)) (t := fun _ => Set.Iio (1 : ℝ)) (fun _ _ => measurableSet_Iio)]
        simp [c]
  have ht : Tendsto (fun K : ℕ => c ^ K) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one exp1Measure_Iio_one_lt
  exact le_antisymm (ge_of_tendsto' ht hbound) bot_le

lemma ae_Good : ∀ᵐ u ∂μc, u ∈ Good := by
  have hsub : Goodᶜ ⊆ (⋃ n, {u : ℕ → ℝ | u n ∈ Set.Iic 0}) ∪ ⋃ N, {u | ∀ n, N ≤ n → u n < 1} := by
    intro u hu
    by_cases h1 : ∀ n, 0 < u n
    · right
      have h2 : ¬ ∀ N, ∃ n, N ≤ n ∧ 1 ≤ u n := fun h2 => hu ⟨h1, h2⟩
      push Not at h2
      obtain ⟨N, hN⟩ := h2
      exact Set.mem_iUnion.mpr ⟨N, hN⟩
    · left
      push Not at h1
      obtain ⟨n, hn⟩ := h1
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [ae_iff]
  refine measure_mono_null (fun u hu => hsub hu) ?_
  refine measure_union_null (measure_iUnion_null fun n => ?_) (measure_iUnion_null fun N => ?_)
  · rw [μc_eval n measurableSet_Iic, exp1Measure_Iic_zero]
  · exact μc_eventually_small N

open Classical in
/-- The clocks: coordinates of `u` on `Good`, and constantly `1` off `Good` (a null set). -/
noncomputable def clk (n : ℕ) (u : ℕ → ℝ) : ℝ := if u ∈ Good then u n else 1

lemma measurable_clk (n : ℕ) : Measurable (clk n) := by
  classical
  unfold clk
  exact Measurable.ite measurableSet_Good (measurable_pi_apply n) measurable_const

lemma clk_ae (n : ℕ) : (fun u : ℕ → ℝ => u n) =ᵐ[μc] clk n := by
  filter_upwards [ae_Good] with u hu
  simp [clk, hu]

lemma clk_pos (n : ℕ) (u : ℕ → ℝ) : 0 < clk n u := by
  unfold clk; split_ifs with h
  · exact h.1 n
  · exact one_pos

lemma clk_io (u : ℕ → ℝ) (N : ℕ) : ∃ n, N ≤ n ∧ 1 ≤ clk n u := by
  unfold clk; split_ifs with h
  · exact h.2 N
  · exact ⟨N, le_rfl, le_rfl⟩

/-- Partial sums of the clocks. -/
noncomputable def S (n : ℕ) (u : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, clk k u

lemma S_strictMono (u : ℕ → ℝ) : StrictMono (fun n => S n u) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [S, Finset.sum_range_succ, lt_add_iff_pos_right]
  exact clk_pos n u

lemma S_tendsto (u : ℕ → ℝ) : Tendsto (fun n => S n u) atTop atTop := by
  have hm : ∀ m : ℕ, ∃ N, (m : ℝ) ≤ S N u := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp [S]⟩
    | succ m ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨n, hNn, hn⟩ := clk_io u N
      refine ⟨n + 1, ?_⟩
      have h1 : S N u ≤ S n u := (S_strictMono u).monotone hNn
      have h2 : S (n + 1) u = S n u + clk n u := by simp [S, Finset.sum_range_succ]
      push_cast
      linarith
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := hm ⌈b⌉₊
  refine ⟨N, fun a ha => ?_⟩
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ S N u := hN
    _ ≤ S a u := (S_strictMono u).monotone ha

/-! ### The sample space: clocks plus an unobserved initial bit -/

structure Ωc : Type where
  u : ℕ → ℝ
  b : Bool

instance : MeasurableSpace Ωc := MeasurableSpace.comap Ωc.u inferInstance

lemma measurable_mk : Measurable (fun u : ℕ → ℝ => (⟨u, true⟩ : Ωc)) := by
  intro s hs
  obtain ⟨C, hC, rfl⟩ := hs
  exact hC

lemma measurable_u : Measurable Ωc.u := comap_measurable _

noncomputable instance : MeasureSpace Ωc :=
  ⟨Measure.map (fun u : ℕ → ℝ => (⟨u, true⟩ : Ωc)) μc⟩

instance : IsProbabilityMeasure (ℙ : Measure Ωc) :=
  Measure.isProbabilityMeasure_map measurable_mk.aemeasurable

lemma vol_u {C : Set (ℕ → ℝ)} (hC : MeasurableSet C) :
    ℙ {ω : Ωc | ω.u ∈ C} = μc C := by
  show Measure.map _ μc (Ωc.u ⁻¹' C) = _
  rw [Measure.map_apply measurable_mk ⟨C, hC, rfl⟩]
  rfl

/-- The (outer) measure of any set equals that of its saturation along the bit coordinate. -/
lemma vol_sat (s : Set Ωc) : ℙ s = ℙ {ω : Ωc | ∃ ω' ∈ s, ω'.u = ω.u} := by
  apply le_antisymm
  · exact measure_mono fun ω hω => ⟨ω, hω, rfl⟩
  · have hT : MeasurableSet (toMeasurable ℙ s) := measurableSet_toMeasurable _ _
    obtain ⟨C, _, hCT⟩ := MeasurableSpace.measurableSet_comap.mp hT
    have hsub : {ω : Ωc | ∃ ω' ∈ s, ω'.u = ω.u} ⊆ toMeasurable ℙ s := by
      rintro ω ⟨ω', hω', hu⟩
      have h1 : ω' ∈ toMeasurable ℙ s := subset_toMeasurable _ _ hω'
      rw [← hCT] at h1 ⊢
      simpa [Set.mem_preimage, hu] using h1
    calc ℙ {ω : Ωc | ∃ ω' ∈ s, ω'.u = ω.u} ≤ ℙ (toMeasurable ℙ s) := measure_mono hsub
      _ = ℙ s := measure_toMeasurable s

lemma vol_full (s : Set Ωc) (h : ∀ u, ∃ b, (⟨u, b⟩ : Ωc) ∈ s) : ℙ s = 1 := by
  rw [vol_sat]
  have : {ω : Ωc | ∃ ω' ∈ s, ω'.u = ω.u} = Set.univ := by
    ext ω
    obtain ⟨b, hb⟩ := h ω.u
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨_, hb, rfl⟩
  rw [this, measure_univ]

open Classical in
lemma vol_b (Q : Bool → Prop) :
    ℙ {ω : Ωc | Q ω.b} = if ∃ b, Q b then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨b, hb⟩ := h
    exact vol_full _ fun _ => ⟨b, hb⟩
  · have : {ω : Ωc | Q ω.b} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hq => h ⟨_, hq⟩
    rw [this, measure_empty]

lemma vol_indep (A : Set (ℕ → ℝ)) (B : Set Bool) :
    ℙ ({ω : Ωc | ω.u ∈ A} ∩ {ω : Ωc | ω.b ∈ B}) =
      ℙ {ω : Ωc | ω.u ∈ A} * ℙ {ω : Ωc | ω.b ∈ B} := by
  rcases B.eq_empty_or_nonempty with hB | ⟨b, hb⟩
  · subst hB; simp
  · have h1 : ℙ {ω : Ωc | ω.b ∈ B} = 1 := vol_full _ fun _ => ⟨b, hb⟩
    rw [h1, mul_one, vol_sat, vol_sat {ω : Ωc | ω.u ∈ A}]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨ω', ⟨hA, _⟩, hu⟩; exact ⟨ω', hA, hu⟩
    · rintro ⟨ω', hA, hu⟩; exact ⟨⟨ω'.u, b⟩, ⟨hA, hb⟩, hu⟩

/-! ### The two-state alternating chain -/

noncomputable def jmp (x : Bool) : PMF Bool := PMF.pure (!x)

def rt (_ : Bool) : ℝ := 1

def Yb (n : ℕ) (b : Bool) : Bool := xor b n.bodd

def Yc (n : ℕ) (ω : Ωc) : Bool := Yb n ω.b

noncomputable def clock (n : ℕ) (ω : Ωc) : ℝ := clk n ω.u

lemma jumpTime_eq (n : ℕ) (ω : Ωc) : jumpTime rt Yc clock n ω = S n ω.u := by
  induction n with
  | zero => simp [jumpTime, S]
  | succ n ih => simp [jumpTime, ih, S, Finset.sum_range_succ, rt, clock]

open Classical in
noncomputable def idx (t : ℝ) (u : ℕ → ℝ) : ℕ :=
  if h : ∃ n : ℕ, t < S (n + 1) u then Nat.find h else 0

noncomputable def Xc (t : ℝ) (ω : Ωc) : Bool := Yb (idx t ω.u) ω.b

lemma idx_eq (u : ℕ → ℝ) (n : ℕ) (t : ℝ) (h1 : S n u ≤ t) (h2 : t < S (n + 1) u) :
    idx t u = n := by
  classical
  have hex : ∃ m : ℕ, t < S (m + 1) u := ⟨n, h2⟩
  rw [idx, dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex h2
  · by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec hex
    have hle : S (Nat.find hex + 1) u ≤ S n u := (S_strictMono u).monotone (by omega)
    linarith

def fc (x : Bool) : (Fin 0 → ℕ) × (Fin 1 → ℕ) := (Fin.elim0, fun _ => if x then 1 else 0)

noncomputable def Nc (t : ℝ) (ω : Ωc) : Fin 0 → ℕ := (fc (Xc t ω)).1
noncomputable def Zc (t : ℝ) (ω : Ωc) : Fin 1 → ℕ := (fc (Xc t ω)).2

lemma Yb_succ (n : ℕ) (b : Bool) : Yb (n + 1) b = !(Yb n b) := by
  unfold Yb; rw [Nat.bodd_succ]; cases b <;> cases n.bodd <;> rfl

noncomputable def counterM : MarkovRepresentation Bool 1 0 Nc Zc where
  jump := jmp
  rate := rt
  Y := Yc
  clock := clock
  X := Xc
  f := fc
  rate_pos := fun _ => one_pos
  jump_irrefl := by intro x; cases x <;> simp [jmp, PMF.pure_apply]
  jump_chain := by
    classical
    intro n path y
    change ℙ {ω : Ωc | (∀ k : Fin (n + 1), Yb k ω.b = path k) ∧ Yb (n + 1) ω.b = y} =
      ℙ {ω : Ωc | ∀ k : Fin (n + 1), Yb k ω.b = path k} * jmp (path (Fin.last n)) y
    rw [vol_b (fun b => (∀ k : Fin (n + 1), Yb k b = path k) ∧ Yb (n + 1) b = y),
      vol_b (fun b => ∀ k : Fin (n + 1), Yb k b = path k)]
    by_cases hP : ∃ b, ∀ k : Fin (n + 1), Yb k b = path k
    · obtain ⟨b, hb⟩ := hP
      have huniq : ∀ b', (∀ k : Fin (n + 1), Yb k b' = path k) → b' = b := by
        intro b' hb'
        have h0 := hb' 0
        have h0' := hb 0
        simp [Yb] at h0 h0'
        rw [h0, h0']
      have hlast : path (Fin.last n) = Yb n b := by rw [← hb (Fin.last n)]; simp
      rw [if_pos (show ∃ b, ∀ k : Fin (n + 1), Yb k b = path k from ⟨b, hb⟩), one_mul, jmp, PMF.pure_apply, hlast]
      by_cases hy : y = !(Yb n b)
      · rw [if_pos hy, if_pos]
        exact ⟨b, hb, by rw [Yb_succ, hy]⟩
      · rw [if_neg hy, if_neg]
        rintro ⟨b', hb', hy'⟩
        rw [huniq b' hb', Yb_succ] at hy'
        exact hy hy'.symm
    · rw [if_neg hP, if_neg (fun ⟨b, hb, _⟩ => hP ⟨b, hb⟩), zero_mul]
  clock_pos := fun n ω => clk_pos n ω.u
  clock_exp := by
    intro n s hs
    change ℙ {ω : Ωc | ω.u ∈ {u : ℕ → ℝ | s < clk n u}} = _
    rw [vol_u (measurableSet_lt measurable_const (measurable_clk n))]
    have hcongr : {u : ℕ → ℝ | s < clk n u} =ᵐ[μc] {u : ℕ → ℝ | u n ∈ Set.Ioi s} := by
      filter_upwards [ae_Good] with u hu
      show (s < clk n u) = (u n ∈ Set.Ioi s)
      simp only [clk, if_pos hu, Set.mem_Ioi]
    rw [measure_congr hcongr, μc_eval n measurableSet_Ioi, exp1Measure_Ioi s hs]
  clock_iid := by
    have hcoord : iIndepFun (fun n (u : ℕ → ℝ) => u n) μc :=
      iIndepFun_infinitePi (P := fun _ : ℕ => exp1Measure) (X := fun _ x => x)
        (fun _ => measurable_id)
    have hclk : iIndepFun (fun n (u : ℕ → ℝ) => clk n u) μc :=
      hcoord.congr fun n => clk_ae n
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hclk ⊢
    intro S' sets hsets
    have hinter : (⋂ i ∈ S', (fun ω : Ωc => clock i ω) ⁻¹' sets i) =
        {ω : Ωc | ω.u ∈ ⋂ i ∈ S', clk i ⁻¹' sets i} := by
      ext ω; simp [clock]
    rw [hinter, vol_u (Finset.measurableSet_biInter S'
      fun i hi => measurable_clk i (hsets i hi)), hclk S' hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    exact (vol_u (measurable_clk i (hsets i hi))).symm
  clock_indep_jumpChain := by
    rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S1, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht1
    obtain ⟨S2, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht2
    exact vol_indep {u | (fun n => clk n u) ∈ S1} {b | (fun n => Yb n b) ∈ S2}
  nonexplosive := by
    intro ω
    simp only [jumpTime_eq]
    exact S_tendsto ω.u
  sample_path := by
    intro ω n t h1 h2
    rw [jumpTime_eq] at h1 h2
    change Yb (idx t ω.u) ω.b = Yb n ω.b
    rw [idx_eq ω.u n t h1 h2]
  irreducible := by
    intro x y
    by_cases h : y = x
    · subst h; exact ⟨0, by simp [stepIter, PMF.pure_apply]⟩
    · refine ⟨1, ?_⟩
      have hy : y = !x := by cases x <;> cases y <;> simp_all
      subst hy
      simp [stepIter, jmp, PMF.pure_apply]
  sample_path_eq := fun _ _ => rfl
  finite_fiber := fun _ => Set.toFinite _
  empty_state := ⟨false, by
    refine Prod.ext (funext fun i => Fin.elim0 i) (funext fun _ => ?_)
    simp [fc]⟩

lemma stationary_iff (π : PMF Bool) :
    IsStationaryDistribution jmp rt π ↔ π true = π false := by
  unfold IsStationaryDistribution
  simp only [rt, ENNReal.ofReal_one, mul_one, tsum_bool, jmp, PMF.pure_apply]
  constructor
  · intro h
    have := h true
    exact (by simpa using this : π false = π true).symm
  · intro h y
    cases y <;> simp [h]

lemma unique_stationary : HasUniqueStationaryDistribution jmp rt := by
  have hval : ∀ π : PMF Bool, IsStationaryDistribution jmp rt π → ∀ b, π b = 2⁻¹ := by
    intro π hπ
    have h := (stationary_iff π).mp hπ
    have hsum : π false + π true = 1 := by
      have := π.tsum_coe
      rwa [tsum_bool] at this
    have hf : π false = 2⁻¹ := by
      apply ENNReal.eq_inv_of_mul_eq_one_left
      rw [mul_two]
      rw [h] at hsum
      exact hsum
    intro b
    cases b
    · exact hf
    · rw [h, hf]
  refine ⟨PMF.uniformOfFintype Bool, ?_, ?_⟩
  · show IsStationaryDistribution jmp rt (PMF.uniformOfFintype Bool)
    rw [stationary_iff]
    simp [PMF.uniformOfFintype_apply]
  · intro π hπ
    ext b
    rw [hval π hπ b]
    simp [PMF.uniformOfFintype_apply]

lemma prob_Z_eq_one (t : ℝ) (x : Bool) : ℙ {ω : Ωc | Zc t ω = (fc x).2} = 1 := by
  apply vol_full
  intro u
  refine ⟨xor x (idx t u).bodd, ?_⟩
  show (fc (Yb (idx t u) (xor x (idx t u).bodd))).2 = (fc x).2
  congr 2
  unfold Yb
  cases x <;> cases (idx t u).bodd <;> rfl

lemma not_convergesInDistribution : ¬ ConvergesInDistribution Zc := by
  rintro ⟨π, hπ⟩
  have hone : ∀ x : Bool, π (fc x).2 = 1 := by
    intro x
    have h := hπ (fc x).2
    have hconst : (fun t : ℝ => (ℙ {ω : Ωc | Zc t ω = (fc x).2}).toReal) = fun _ => 1 := by
      funext t; rw [prob_Z_eq_one]; simp
    rw [hconst] at h
    have h1 : (π (fc x).2).toReal = 1 := tendsto_nhds_unique h tendsto_const_nhds
    exact (ENNReal.toReal_eq_one_iff _).mp h1
  have hsupp := (PMF.apply_eq_one_iff π _).mp (hone true)
  have hmem : (fc false).2 ∈ π.support := by
    rw [PMF.mem_support_iff, hone false]; exact one_ne_zero
  rw [hsupp, Set.mem_singleton_iff] at hmem
  have := congrFun hmem 0
  simp [fc] at this

end PN1EquivCounterexample

theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z),
    (PositiveRecurrent M.jump M.rate ↔ HasUniqueStationaryDistribution M.jump M.rate) ∧
    (HasUniqueStationaryDistribution M.jump M.rate ↔ ConvergesInDistribution Z) ∧
    (PositiveRecurrent M.jump M.rate →
      ∃ π : PMF Xstate, IsStationaryDistribution M.jump M.rate π ∧
        ∀ (h : Xstate → ℝ), (∃ C, ∀ x, |h x| ≤ C) →
          ℙ {ω | Tendsto (fun t : ℝ => t⁻¹ * ∫ s in Set.Ioc (0 : ℝ) t, h (M.X s ω))
                    atTop (nhds (∑' x, (π x).toReal * h x))}
            = 1)) := by
  intro h
  have h2 := (h PN1EquivCounterexample.counterM).2.1
  exact PN1EquivCounterexample.not_convergesInDistribution
    (h2.mp PN1EquivCounterexample.unique_stationary)
