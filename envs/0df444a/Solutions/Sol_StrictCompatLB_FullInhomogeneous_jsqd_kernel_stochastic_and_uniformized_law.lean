-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.jsqd_kernel_stochastic_and_uniformized_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:42:08.338198+00:00
-- url     : https://prove2.me/submissions/9df1a09a-e061-432e-a023-d692e27e5402

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace SC9a4

/-! Child C3a of the decomposition of theorem_3_6_full (9a4ecffb): on a connected
compatibility graph with at least one server, the JSQ(d) jump kernel is stochastic. -/

/-- A connected compatibility graph with a server gives every dispatcher a neighbour. -/
theorem nbrW_nonempty_of_connected (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (N : ℕ) (hN : 1 ≤ N) (hc : (compatGraph M G N).Connected) (w : Fin (M N)) :
    (nbrW M G N w).Nonempty := by
  obtain ⟨p⟩ := hc.preconnected (Sum.inr w) (Sum.inl ⟨0, hN⟩)
  cases p with
  | cons h _ =>
    rw [compatGraph, SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, ⟨v, w', h1, _, _⟩ | ⟨v, w', _, h2, h3⟩⟩
    · simp at h1
    · refine ⟨v, ?_⟩
      simp only [Sum.inr.injEq] at h2
      subst h2
      simp [nbrW, h3]

theorem argminSet_nonempty {N : ℕ} (U : Finset (Fin N)) (z : Fin N → ℕ) (hU : U.Nonempty) :
    (argminSet U z).Nonempty := by
  obtain ⟨u, hu, hmin⟩ := U.exists_min_image z hU
  exact ⟨u, Finset.mem_filter.2 ⟨hu, hmin⟩⟩

theorem sum_argmin_indicator {N : ℕ} (U : Finset (Fin N)) (z : Fin N → ℕ) (hU : U.Nonempty) :
    ∑ v : Fin N, (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) = 1 := by
  rw [← Finset.sum_filter]
  have hf : (Finset.univ.filter fun v => v ∈ argminSet U z) = argminSet U z := by
    ext; simp
  rw [hf, Finset.sum_const, nsmul_eq_mul]
  have : ((argminSet U z).card : ℝ) ≠ 0 := by
    exact_mod_cast (argminSet_nonempty U z hU).card_pos.ne'
  field_simp

theorem jsqdRoute_sum (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) (hne : (nbrW M G N w).Nonempty) :
    ∑ v, jsqdRoute M G N d w z v = 1 := by
  unfold jsqdRoute
  have hk : 1 ≤ min d (nbrW M G N w).card := le_min hd hne.card_pos
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
      ∑ v : Fin N, (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) = 1 := by
    intro U hU
    rw [Finset.mem_powersetCard] at hU
    apply sum_argmin_indicator
    rw [← Finset.card_pos, hU.2]
    omega
  rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
    mul_one]
  have : ((((nbrW M G N w).card.choose (min d (nbrW M G N w).card)) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (min_le_right _ _)).ne'
  field_simp

theorem jsqdRoute_nonneg (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) : 0 ≤ jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  apply mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  split_ifs <;> positivity

theorem jsqdKernel_stochastic (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (hM : 0 < M N) (hne : ∀ w, (nbrW M G N w).Nonempty) :
    IsStochasticKernel (jsqdKernel lam d M G N) := by
  constructor
  · intro z z'
    unfold jsqdKernel lbKernel
    have h1 : 0 ≤ lam / (lam + 1) := by positivity
    have h2 : 0 ≤ 1 / (lam + 1) := by positivity
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg h1 (by positivity))
      apply Finset.sum_nonneg; intro w _; apply Finset.sum_nonneg; intro v _
      apply mul_nonneg (jsqdRoute_nonneg M G N d w z v); split_ifs <;> norm_num
    · apply mul_nonneg (mul_nonneg h2 (by positivity))
      apply Finset.sum_nonneg; intro v _; split_ifs <;> norm_num
  · intro z
    unfold jsqdKernel lbKernel
    have hA : HasSum (fun z' : Fin N → ℕ => ∑ w : Fin (M N), ∑ v : Fin N,
        jsqdRoute M G N d w z v * (if z' = arrive z v then (1 : ℝ) else 0))
        (∑ w : Fin (M N), ∑ v : Fin N, jsqdRoute M G N d w z v) := by
      apply hasSum_sum; intro w _
      apply hasSum_sum; intro v _
      have := hasSum_ite_eq (arrive z v) (jsqdRoute M G N d w z v)
      convert this using 1
      funext z'
      split_ifs <;> simp
    have hB : HasSum (fun z' : Fin N → ℕ => ∑ v : Fin N, (if z' = depart z v then (1 : ℝ) else 0))
        (∑ v : Fin N, (1 : ℝ)) := by
      apply hasSum_sum; intro v _
      exact hasSum_ite_eq (depart z v) 1
    have hC := (hA.mul_left (lam / (lam + 1) * (1 / (M N : ℝ)))).add
      (hB.mul_left (1 / (lam + 1) * (1 / (N : ℝ))))
    have hval : lam / (lam + 1) * (1 / (M N : ℝ)) *
        (∑ w : Fin (M N), ∑ v : Fin N, jsqdRoute M G N d w z v) +
        1 / (lam + 1) * (1 / (N : ℝ)) * (∑ v : Fin N, (1 : ℝ)) = 1 := by
      rw [Finset.sum_congr rfl (fun w _ => jsqdRoute_sum M G N d hd w z (hne w))]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hM' : (M N : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hl : lam + 1 ≠ 0 := by linarith
      field_simp
    rw [hval] at hC
    exact hC

/-- C3a assembled: connected graph with a server ⇒ the JSQ(d) kernel is stochastic. -/
theorem jsqdKernel_stochastic_of_connected (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (hM : 0 < M N) (hc : (compatGraph M G N).Connected) :
    IsStochasticKernel (jsqdKernel lam d M G N) :=
  jsqdKernel_stochastic lam hlam d hd M G N hN hM
    (nbrW_nonempty_of_connected M G N hN hc)

/-! Child C3b of the decomposition of theorem_3_6_full (9a4ecffb): for a stochastic kernel
on a countable discrete state space, a positive clock rate and any initial probability
vector, a uniformized law exists. Construction: random-mapping representation of the chain
(iid random maps `S → S` with independent rows `K z`) times an iid exponential clock;
nonexplosion by the second Borel-Cantelli lemma (infinitely many gaps exceed 1). -/

section C3b

open ProbabilityTheory

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The measure on `S` with point masses `v z`. -/
noncomputable def vecMeasure (v : S → ℝ) : Measure S :=
  Measure.sum (fun z => ENNReal.ofReal (v z) • Measure.dirac z)

theorem vecMeasure_singleton (v : S → ℝ) (z : S) :
    vecMeasure v {z} = ENNReal.ofReal (v z) := by
  rw [vecMeasure, Measure.sum_apply _ (measurableSet_singleton z)]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton z)]
  rw [tsum_eq_single z]
  · simp
  · intro b hb
    simp [Set.indicator, hb]

theorem vecMeasure_isProb (v : S → ℝ) (hv : StrictCompatLB.MeanField.IsProbVec v) :
    IsProbabilityMeasure (vecMeasure v) := by
  constructor
  rw [vecMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hv.1 hv.2.summable, hv.2.tsum_eq, ENNReal.ofReal_one]

/-- The chain driven by an initial state and a sequence of random maps. -/
def chainMap (ω : S × (ℕ → S → S)) : ℕ → S
  | 0 => ω.1
  | n + 1 => ω.2 n (chainMap ω n)

theorem measurable_chainMap :
    Measurable (chainMap : S × (ℕ → S → S) → ℕ → S) := by
  refine measurable_pi_iff.2 fun n => ?_
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hev : Measurable (fun p : (S → S) × S => p.1 p.2) :=
      measurable_from_prod_countable_left fun y => measurable_pi_apply y
    have hpair : Measurable (fun ω : S × (ℕ → S → S) => (ω.2 n, chainMap ω n)) :=
      ((measurable_pi_apply n).comp measurable_snd).prodMk ih
    exact hev.comp hpair

theorem chainMap_preimage (n : ℕ) (zs : ℕ → S) :
    chainMap ⁻¹' {x : ℕ → S | ∀ j ≤ n, x j = zs j} =
      ({zs 0} : Set S) ×ˢ Set.pi (Finset.range n : Set ℕ)
        (fun j => {g : S → S | g (zs j) = zs (j + 1)}) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_le _), fun j hj => ?_⟩
    have h1 := h j hj.le
    have h2 := h (j + 1) hj
    simp only [chainMap] at h2
    rw [h1] at h2
    exact h2
  · rintro ⟨h0, hs⟩ j hj
    induction j with
    | zero => exact h0
    | succ j ih =>
      simp only [chainMap]
      rw [ih (Nat.le_of_succ_le hj)]
      exact hs j hj

/-- Positivity and divergence of an iid exponential clock, almost surely. -/
theorem expClock_ae (rate : ℝ) (hr : 0 < rate) :
    haveI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => expMeasure rate)),
      (∀ k, 0 < x k) ∧ Tendsto (fun n => ∑ k ∈ Finset.range n, x k) atTop atTop := by
  haveI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  set C : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => expMeasure rate) with hCdef
  have hmapC : ∀ k, C.map (fun x => x k) = expMeasure rate := fun k =>
    Measure.infinitePi_map_eval _ k
  -- positivity
  have hIic0 : expMeasure rate (Set.Iic 0) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr]
    simp
  have hpos : ∀ᵐ x ∂C, ∀ k, 0 < x k := by
    refine ae_all_iff.2 fun k => ?_
    refine ae_of_ae_map (measurable_pi_apply k).aemeasurable ?_
    rw [hmapC k, ae_iff]
    have : {a : ℝ | ¬ 0 < a} = Set.Iic 0 := by ext a; simp
    rw [this, hIic0]
  -- infinitely many gaps exceed one
  have hIoi : expMeasure rate (Set.Ioi 1) ≠ 0 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
      cdf_expMeasure_eq hr]
    simp only [zero_le_one, if_true, mul_one]
    have hlt : ENNReal.ofReal (1 - Real.exp (-rate)) < 1 :=
      ENNReal.ofReal_lt_one.2 (by linarith [Real.exp_pos (-rate)])
    exact (tsub_pos_of_lt hlt).ne'
  set s : ℕ → Set (ℕ → ℝ) := fun k => {x | 1 < x k} with hsdef
  have hsm : ∀ k, MeasurableSet (s k) := fun k =>
    (measurable_pi_apply k) measurableSet_Ioi
  have hCs : ∀ k, C (s k) = expMeasure rate (Set.Ioi 1) := by
    intro k
    rw [← hmapC k, Measure.map_apply (measurable_pi_apply k) measurableSet_Ioi]
    rfl
  have hind : iIndepSet s C := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro T
    have : (⋂ i ∈ T, s i) = Set.pi (T : Set ℕ) (fun _ => Set.Ioi (1 : ℝ)) := by
      ext x; simp [hsdef, Set.mem_pi]
    rw [this, hCdef, Measure.infinitePi_pi (fun _ : ℕ => expMeasure rate) (fun _ _ => measurableSet_Ioi)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hCdef, hCs i]
  have hsum : (∑' k, C (s k)) = ∞ := by
    simp_rw [hCs]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hIoi
  have hlim := measure_limsup_eq_one hsm hind hsum
  have hfreq : ∀ᵐ x ∂C, ∃ᶠ k in atTop, 1 < x k := by
    rw [ae_iff]
    have hm : MeasurableSet (Filter.limsup s atTop) := MeasurableSet.measurableSet_limsup hsm
    have := (prob_compl_eq_zero_iff hm).2 hlim
    convert this using 2
    ext x
    simp [mem_limsup_iff_frequently_mem, hsdef]
  filter_upwards [hpos, hfreq] with x hx hf
  refine ⟨hx, ?_⟩
  have hmono : Monotone (fun n => ∑ k ∈ Finset.range n, x k) := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    linarith [hx n]
  refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
  have key : ∀ m : ℕ, ∃ n, (m : ℝ) ≤ ∑ k ∈ Finset.range n, x k := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hkn, hk⟩ := (Filter.frequently_atTop.1 hf) n
      refine ⟨k + 1, ?_⟩
      rw [Finset.sum_range_succ]
      have := hmono hkn
      push_cast
      linarith
  obtain ⟨n, hn⟩ := key ⌈b⌉₊
  exact ⟨n, (Nat.le_ceil b).trans hn⟩

/-- C3b: existence of a uniformized law for every initial probability vector. -/
theorem exists_uniformizedLaw (K : S → S → ℝ) (hK : StrictCompatLB.MeanField.IsStochasticKernel K)
    (rate : ℝ) (hr : 0 < rate) (μ : S → ℝ) (hμ : StrictCompatLB.MeanField.IsProbVec μ) :
    ∃ P : Measure (StrictCompatLB.FullInhomogeneous.ChainSample S),
      StrictCompatLB.FullInhomogeneous.IsUniformizedLaw P K rate μ := by
  haveI hKp : ∀ z, IsProbabilityMeasure (vecMeasure (K z)) := fun z =>
    vecMeasure_isProb _ ⟨hK.1 z, hK.2 z⟩
  haveI := vecMeasure_isProb μ hμ
  haveI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  obtain ⟨F, hFdef⟩ : ∃ F : Measure (S → S),
      F = Measure.infinitePi (fun z => vecMeasure (K z)) := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure F := by rw [hFdef]; infer_instance
  obtain ⟨Q, hQdef⟩ : ∃ Q : Measure (S × (ℕ → S → S)),
      Q = (vecMeasure μ).prod (Measure.infinitePi (fun _ : ℕ => F)) := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure Q := by rw [hQdef]; infer_instance
  obtain ⟨A, hAdef⟩ : ∃ A : Measure (ℕ → S), A = Q.map chainMap := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure A := by
    rw [hAdef]; exact Measure.isProbabilityMeasure_map measurable_chainMap.aemeasurable
  obtain ⟨C, hCdef⟩ : ∃ C : Measure (ℕ → ℝ),
      C = Measure.infinitePi (fun _ : ℕ => expMeasure rate) := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure C := by rw [hCdef]; infer_instance
  have hsnd : (A.prod C).map Prod.snd = C := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmarg : ∀ k, (A.prod C).map (fun ω : (ℕ → S) × (ℕ → ℝ) => ω.2 k) = expMeasure rate := by
    intro k
    rw [show (fun ω : (ℕ → S) × (ℕ → ℝ) => ω.2 k) = (fun x : ℕ → ℝ => x k) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply k) measurable_snd, hsnd, hCdef,
      Measure.infinitePi_map_eval]
  have hFsing : ∀ z z' : S, F {g : S → S | g z = z'} = ENNReal.ofReal (K z z') := by
    intro z z'
    have : {g : S → S | g z = z'} = (fun g : S → S => g z) ⁻¹' {z'} := rfl
    rw [this, ← Measure.map_apply (measurable_pi_apply z) (measurableSet_singleton z'), hFdef,
      Measure.infinitePi_map_eval, vecMeasure_singleton]
  refine ⟨A.prod C, inferInstance, hμ, ?_, ?_, hmarg, ?_, ?_⟩
  · -- cylinder law
    intro n zs
    have hcylm : MeasurableSet {x : ℕ → S | ∀ j ≤ n, x j = zs j} := by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (measurableSet_singleton (zs j)).preimage (measurable_pi_apply j)
    have hset : {ω : StrictCompatLB.FullInhomogeneous.ChainSample S | ∀ j ≤ n, ω.1 j = zs j} =
        {x : ℕ → S | ∀ j ≤ n, x j = zs j} ×ˢ (Set.univ : Set (ℕ → ℝ)) := by
      ext ω; simp
    rw [hset, Measure.prod_prod, measure_univ, mul_one, hAdef,
      Measure.map_apply measurable_chainMap hcylm, chainMap_preimage, hQdef, Measure.prod_prod,
      Measure.infinitePi_pi (fun _ : ℕ => F) (t := fun j => {g : S → S | g (zs j) = zs (j + 1)})
        (fun j _ => (measurableSet_singleton (zs (j + 1))).preimage (measurable_pi_apply (zs j))),
      vecMeasure_singleton, ENNReal.ofReal_mul (hμ.1 _),
      ENNReal.ofReal_prod_of_nonneg (fun j _ => hK.1 _ _)]
    congr 1
    exact Finset.prod_congr rfl fun j _ => hFsing _ _
  · -- iid clock
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map
      (X := fun k (ω : (ℕ → S) × (ℕ → ℝ)) => ω.2 k) (fun k => (measurable_pi_apply k).comp measurable_snd)]
    simp_rw [hmarg]
    rw [← hCdef]
    exact hsnd
  · -- chain independent of the clock
    exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  · -- nonexplosion
    refine ae_of_ae_map (p := fun x : ℕ → ℝ => (∀ k, 0 < x k) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range n, x k) atTop atTop) measurable_snd.aemeasurable ?_
    rw [hsnd, hCdef]
    exact expClock_ae rate hr

end C3b

/-- C3 assembled for the queueing model: on a connected graph with a server, the JSQ(d) kernel
is stochastic and every initial probability vector has a uniformized law at rate (lam+1)N. -/
theorem jsqd_C3 (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (hM : 0 < M N) (hc : (compatGraph M G N).Connected) :
    IsStochasticKernel (jsqdKernel lam d M G N) ∧
      ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (StrictCompatLB.FullInhomogeneous.ChainSample (Fin N → ℕ)),
          StrictCompatLB.FullInhomogeneous.IsUniformizedLaw P (jsqdKernel lam d M G N)
            ((lam + 1) * (N : ℝ)) μ := by
  have hK := jsqdKernel_stochastic_of_connected lam hlam d hd M G N hN hM hc
  refine ⟨hK, fun μ hμ => exists_uniformizedLaw _ hK _ ?_ μ hμ⟩
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  positivity

end SC9a4

open StrictCompatLB.FullInhomogeneous in
theorem solution : ∀ (lam : ℝ), 0 ≤ lam → ∀ (d : ℕ), 1 ≤ d →
    ∀ (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ), 1 ≤ N → 0 < M N →
    (compatGraph M G N).Connected →
    IsStochasticKernel (jsqdKernel lam d M G N) ∧
      ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (ChainSample (Fin N → ℕ)),
          IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ := by
  intro lam hlam d hd M G N hN hM hc
  exact SC9a4.jsqd_C3 lam hlam d hd M G N hN hM hc
