-- Prove2me | solution 1 for StochSchedPrec.CMNS.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:55:32.30455+00:00
-- url     : https://prove2.me/submissions/8e7ee1e1-c83b-48be-a1b7-e641ffd26d7a

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem SSP27_delayed_meas {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V) (p S : V → ℝ) (k : V) :
    Measurable fun t => IsDelayed A r L p S k t := by
  classical
  have hlt : ∀ c : ℝ, Measurable fun t : ℝ => t < c := fun c =>
    measurableSet_setOfPred.1 measurableSet_Iio
  have hle : ∀ c : ℝ, Measurable fun t : ℝ => c ≤ t := fun c =>
    measurableSet_setOfPred.1 measurableSet_Ici
  have hav : ∀ i, Measurable fun t => avail A r p S i t := fun i =>
    (hle (r i)).and (Measurable.forall fun i' => Measurable.imp measurable_const (hle _))
  have hfirst : ∀ (q : V → ℝ → Prop), (∀ i, Measurable (q i)) → ∀ k,
      Measurable fun t => IsFirstWith L (fun i => q i t) k := by
    intro q hq k
    exact (hq k).and (Measurable.forall fun i => Measurable.imp (hq i) measurable_const)
  refine Measurable.and (Measurable.exists fun i => ?_) ?_
  · exact (hfirst (fun i t => t < S i) (fun i => hlt _) i).and (hav i).not
  · exact hfirst (fun i t => t < S i ∧ avail A r p S i t) (fun i => (hlt _).and (hav i)) k

open StochSchedPrec.CMNS in
theorem SSP27_det {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (μ : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V))
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) (j : V) :
    β * ∑ i ∈ outOfOrder L S j, μ i ≤ m * chainLength A r tb p S j := by
  classical
  obtain ⟨hfeas, ⟨ord, hmono, hdec⟩, _, _⟩ := hS
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- feasibility along chains
  have hchain : ∀ z y, Relation.TransGen A z y → S z + p z ≤ S y := by
    intro z y h
    induction h with
    | single hab => exact hfeas.2.1 _ _ hab
    | @tail b c _ hbc ih =>
      have := hfeas.2.1 _ _ hbc
      linarith [hp b]
  have hS0 : ∀ i, 0 ≤ S i := fun i => le_trans (hr i) (hfeas.1 i)
  -- the indicator of "some job after `j` is deliberately delayed"
  set g : ℝ → ℝ := fun s =>
    if ∃ k, L.symm j < L.symm k ∧ IsDelayed A r L p S k s then (1 : ℝ) else 0 with hg
  have hgm : Measurable g := Measurable.ite
    (Measurable.exists fun k => measurable_const.and (SSP27_delayed_meas A r L p S k)).setOf
    measurable_const measurable_const
  have hg01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1 := by
    intro s; simp only [hg]; split_ifs <;> norm_num
  have hgII : ∀ a b, IntervalIntegrable g volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hgm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun s => by
      show ‖g s‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hg01 s).1]; exact (hg01 s).2
  -- if `c ∈ B_j` is available on `[t0, S c)`, then `g` vanishes there
  have hzero : ∀ c, L.symm c ≤ L.symm j → ∀ t0, t0 ≤ S c →
      (∀ s, t0 ≤ s → s < S c → avail A r p S c s) → ∫ s in t0..S c, g s = 0 := by
    intro c hc t0 ht0 hav
    rw [intervalIntegral.integral_of_le ht0, ← integral_Ico_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Ico (g := fun _ => (0 : ℝ))]
    · simp
    intro s hs
    simp only [hg]
    rw [if_neg]
    rintro ⟨k, hk, hd⟩
    have := hd.2.2 c ⟨hs.2, hav s hs.1 hs.2⟩
    exact absurd (lt_of_lt_of_le hk this) (not_lt.2 hc)
  have hsplit : ∀ a b c : ℝ, ∫ s in a..c, g s = (∫ s in a..b, g s) + ∫ s in b..c, g s :=
    fun a b c => (intervalIntegral.integral_add_adjacent_intervals (hgII a b) (hgII b c)).symm
  have hle1 : ∀ a b : ℝ, a ≤ b → ∫ s in a..b, g s ≤ b - a := by
    intro a b hab
    have := intervalIntegral.integral_mono_on hab (hgII a b) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun s _ => (hg01 s).2)
    simpa using this
  have hcard : ∀ c, (Finset.univ.filter fun y => Relation.TransGen A y c).card ≤ Fintype.card V :=
    fun c => Finset.card_filter_le _ _
  -- the chain claim
  have claim : ∀ n c, L.symm c ≤ L.symm j →
      (Finset.univ.filter fun y => Relation.TransGen A y c).card ≤ n →
      ∫ s in (0 : ℝ)..S c, g s ≤ chainLengthAux A r tb p S n c - p c := by
    intro n
    induction n with
    | zero =>
      intro c hc hn
      have hnp : ∀ y, ¬ Relation.TransGen A y c := by
        intro y hy
        have : y ∈ Finset.univ.filter fun y => Relation.TransGen A y c := by simp [hy]
        have := Finset.card_pos.2 ⟨y, this⟩
        omega
      simp only [chainLengthAux, add_sub_cancel_right]
      rw [hsplit 0 (r c) (S c), hzero c hc (r c) (hfeas.1 c)
        (fun s hs _ => ⟨hs, fun y hy => absurd hy (hnp y)⟩)]
      have := hle1 0 (r c) (hr c)
      linarith
    | succ n ih =>
      intro c hc hn
      simp only [chainLengthAux]
      split
      · rename_i hnone
        -- no critical predecessor: all predecessors complete by `r c`
        have hpred : ∀ y, Relation.TransGen A y c → S y + p y ≤ r c := by
          by_contra hcon
          push Not at hcon
          obtain ⟨y0, hy0, hy0r⟩ := hcon
          obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image
            (Finset.univ.filter fun y => Relation.TransGen A y c) (fun y => S y + p y)
            ⟨y0, by simp [hy0]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          dsimp only [critPred] at hnone
          split_ifs at hnone with hne
          apply hne
          refine ⟨y, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hy, ?_, fun i' hi' => hymax i' (by simp [hi'])⟩
          have := hymax y0 (by simp [hy0])
          linarith
        rw [hsplit 0 (r c) (S c), hzero c hc (r c) (hfeas.1 c)
          (fun s hs _ => ⟨hs, fun y hy => le_trans (hpred y hy) hs⟩)]
        have := hle1 0 (r c) (hr c)
        linarith
      · rename_i k hk
        have hkM : Relation.TransGen A k c ∧ r c < S k + p k ∧
            ∀ i', Relation.TransGen A i' c → S i' + p i' ≤ S k + p k := by
          dsimp only [critPred] at hk
          split_ifs at hk with hne
          have hmem := Finset.min'_mem _ (hne.image tb)
          rw [Finset.mem_image] at hmem
          obtain ⟨y, hyM, hyeq⟩ := hmem
          have : k = y := by
            have := Option.some.inj hk
            rw [← this, ← hyeq, Equiv.symm_apply_apply]
          subst this
          simpa using hyM
        obtain ⟨hkc, hkr, hkmax⟩ := hkM
        have hLk : L.symm k ≤ L.symm j := le_trans (hLE k c hkc).le hc
        have hsub : (Finset.univ.filter fun y => Relation.TransGen A y k) ⊂
            (Finset.univ.filter fun y => Relation.TransGen A y c) := by
          refine Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.2 ⟨k, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
            exact hy.trans hkc
          · simp [hkc]
          · simp [hacyc k]
        have hnk := Finset.card_lt_card hsub
        have ihk := ih k hLk (by omega)
        have hCk : S k + p k ≤ S c := hchain k c hkc
        rw [hsplit 0 (S k) (S c), hsplit (S k) (S k + p k) (S c),
          hzero c hc (S k + p k) hCk
            (fun s hs _ => ⟨by linarith, fun y hy => le_trans (hkmax y hy) hs⟩)]
        have := hle1 (S k) (S k + p k) (by linarith [hp k])
        linarith
  have hgj : ∫ s in (0 : ℝ)..S j, g s ≤ chainLength A r tb p S j - p j :=
    claim (Fintype.card V) j le_rfl (hcard j)
  -- charges of out-of-order jobs
  set f : V → ℝ → ℝ := fun i s =>
    if IsDelayed A r L p S i s then ((m : ℝ) - (busy p S s : ℝ)) else 0 with hf
  have hbusy_le : ∀ s, (busy p S s : ℝ) ≤ m := fun s => by exact_mod_cast hfeas.2.2 s
  have hf0 : ∀ i s, 0 ≤ f i s := by
    intro i s; simp only [hf]; split_ifs
    · linarith [hbusy_le s]
    · exact le_rfl
  have hbusy_eq : ∀ t, (busy p S t : ℝ) = ∑ j, if S j ≤ t ∧ t < S j + p j then (1 : ℝ) else 0 := by
    intro t; unfold busy; rw [Finset.sum_boole]
  have hbm : Measurable fun t => (busy p S t : ℝ) := by
    simp only [hbusy_eq]
    refine Finset.measurable_fun_sum _ (fun j _ => Measurable.ite ?_ measurable_const
      measurable_const)
    exact ((measurableSet_setOfPred.1 measurableSet_Ici).and
      (measurableSet_setOfPred.1 measurableSet_Iio)).setOf
  have hfm : ∀ i, Measurable (f i) := fun i =>
    Measurable.ite (SSP27_delayed_meas A r L p S i).setOf (measurable_const.sub hbm) measurable_const
  have hfII : ∀ i a b, IntervalIntegrable (f i) volume a b := by
    intro i a b
    refine (intervalIntegrable_const (c := (m : ℝ))).mono_fun' (hfm i).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    show ‖f i s‖ ≤ (m : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 i s)]
    simp only [hf]; split_ifs
    · have : (0 : ℝ) ≤ busy p S s := Nat.cast_nonneg _
      linarith
    · exact_mod_cast Nat.zero_le m
  have hO : ∀ i ∈ outOfOrder L S j, β * μ i ≤ ∫ s in (0 : ℝ)..S j, f i s := by
    intro i hi
    simp only [outOfOrder, after, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hLji, hSij⟩ := hi
    have hord : ord.symm i ≤ ord.symm j := by
      by_contra h; push Not at h
      have := hmono j i h; linarith
    have hthr : β * μ i ≤ charge m A r L p S i (S i) := by
      rcases (hdec i).2.2 with hfirst | ⟨_, _, h⟩
      · exact absurd (hfirst.2 j hord) (not_le.2 hLji)
      · exact h
    have hmono' : ∫ s in (0 : ℝ)..S i, f i s ≤ ∫ s in (0 : ℝ)..S j, f i s := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hfII i 0 (S i)) (hfII i (S i) (S j))]
      have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hSij.le (fun s _ => hf0 i s)
      linarith
    exact le_trans hthr hmono'
  have hpt : ∀ s, ∑ i ∈ outOfOrder L S j, f i s ≤ m * g s := by
    intro s
    by_cases hex : ∃ i ∈ outOfOrder L S j, IsDelayed A r L p S i s
    · obtain ⟨i0, hi0, hd0⟩ := hex
      have hLi0 : L.symm j < L.symm i0 := by
        simp only [outOfOrder, after, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
        exact hi0.1
      have hg1 : g s = 1 := by simp only [hg]; rw [if_pos ⟨i0, hLi0, hd0⟩]
      rw [hg1, Finset.sum_eq_single i0]
      · simp only [hf, if_pos hd0]
        have : (0 : ℝ) ≤ busy p S s := Nat.cast_nonneg _
        linarith
      · intro i _ hne
        simp only [hf]
        rw [if_neg]
        intro hd
        apply hne
        apply L.symm.injective
        exact le_antisymm (hd.2.2 i0 hd0.2.1) (hd0.2.2 i hd.2.1)
      · intro h; exact absurd hi0 h
    · push Not at hex
      rw [Finset.sum_eq_zero (fun i hi => by simp only [hf]; rw [if_neg (hex i hi)])]
      exact mul_nonneg hmR.le (hg01 s).1
  have htot : ∑ i ∈ outOfOrder L S j, ∫ s in (0 : ℝ)..S j, f i s ≤ m * ∫ s in (0 : ℝ)..S j, g s := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hfII i 0 (S j)),
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (hS0 j)
      (by
        have := IntervalIntegrable.sum (outOfOrder L S j) (fun i _ => hfII i 0 (S j))
        rwa [show (∑ i ∈ outOfOrder L S j, f i) = fun x => ∑ i ∈ outOfOrder L S j, f i x from
          funext fun x => Finset.sum_apply x _ _] at this) ((hgII 0 (S j)).const_mul _)
      (fun s _ => hpt s)
  have h1 : β * ∑ i ∈ outOfOrder L S j, μ i ≤ ∑ i ∈ outOfOrder L S j, ∫ s in (0 : ℝ)..S j, f i s := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hO
  have h2 := mul_le_mul_of_nonneg_left hgj hmR.le
  have h3 : (m : ℝ) * (chainLength A r tb p S j - p j) ≤ m * chainLength A r tb p S j := by
    nlinarith [hp j]
  linarith

open StochSchedPrec.CMNS in
theorem SSP28aux_chain_meas {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) (r : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V)) :
    ∀ n j, Measurable (fun x : (V → ℝ) × (V → ℝ) => chainLengthAux A r tb x.1 x.2 n j) := by
  classical
  have hlt : ∀ f g : (V → ℝ) × (V → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun x => f x < g x :=
    fun f g hf hg => measurableSet_setOfPred.1 (measurableSet_lt hf hg)
  have hle : ∀ f g : (V → ℝ) × (V → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun x => f x ≤ g x :=
    fun f g hf hg => measurableSet_setOfPred.1 (measurableSet_le hf hg)
  have hc : ∀ i, Measurable (fun x : (V → ℝ) × (V → ℝ) => x.2 i + x.1 i) := fun i =>
    ((measurable_pi_apply i).comp measurable_snd).add ((measurable_pi_apply i).comp measurable_fst)
  intro n
  induction n with
  | zero =>
    intro j
    exact measurable_const.add ((measurable_pi_apply j).comp measurable_fst)
  | succ n ih =>
    intro j
    let Mf : (V → ℝ) × (V → ℝ) → Finset V := fun x => Finset.univ.filter fun i =>
      Relation.TransGen A i j ∧ r j < x.2 i + x.1 i ∧
        ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 i + x.1 i
    let Φ : Finset V → Option V := fun T =>
      if h : T.Nonempty then some (tb.symm ((T.image tb).min' (h.image tb))) else none
    let Ψ : Finset V → (V → ℝ) × (V → ℝ) → ℝ := fun T x =>
      match Φ T with
      | none => r j + x.1 j
      | some i => x.1 j + chainLengthAux A r tb x.1 x.2 n i
    have hcp : ∀ x : (V → ℝ) × (V → ℝ), critPred A r tb x.1 x.2 j = Φ (Mf x) := by
      intro x
      unfold critPred
      simp only [Φ, Mf]
    have heq : (fun x : (V → ℝ) × (V → ℝ) => chainLengthAux A r tb x.1 x.2 (n + 1) j)
        = fun x => ∑ T : Finset V, if Mf x = T then Ψ T x else 0 := by
      funext x
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true, chainLengthAux, hcp x, Ψ]
      rfl
    rw [heq]
    refine Finset.measurable_fun_sum _ (fun T _ => ?_)
    refine Measurable.ite ?_ ?_ measurable_const
    · have : {x : (V → ℝ) × (V → ℝ) | Mf x = T} = {x | ∀ i, (Relation.TransGen A i j ∧
          r j < x.2 i + x.1 i ∧ ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 i + x.1 i)
            ↔ i ∈ T} := by
        ext x
        simp only [Set.mem_setOf_eq, Finset.ext_iff, Mf, Finset.mem_filter, Finset.mem_univ,
          true_and]
      rw [this]
      refine measurableSet_setOfPred.2 (Measurable.forall fun i => Measurable.iff ?_ measurable_const)
      refine Measurable.and measurable_const (Measurable.and (hlt _ _ measurable_const (hc i)) ?_)
      exact Measurable.forall fun i' => Measurable.imp measurable_const (hle _ _ (hc i') (hc i))
    · simp only [Ψ]
      cases Φ T with
      | none => exact measurable_const.add ((measurable_pi_apply j).comp measurable_fst)
      | some i => exact ((measurable_pi_apply j).comp measurable_fst).add (ih i)

open StochSchedPrec.CMNS in
theorem SSP28aux_chain_bound {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (tb : V ≃ Fin (Fintype.card V)) (p S : V → ℝ)
    (hp : ∀ j, 0 ≤ p j) :
    ∀ n j, 0 ≤ chainLengthAux A r tb p S n j ∧
      chainLengthAux A r tb p S n j ≤ ∑ k, r k + (n + 1) * ∑ k, p k := by
  have hrs : ∀ j, r j ≤ ∑ k, r k := fun j =>
    Finset.single_le_sum (fun k _ => hr k) (Finset.mem_univ j)
  have hps : ∀ j, p j ≤ ∑ k, p k := fun j =>
    Finset.single_le_sum (fun k _ => hp k) (Finset.mem_univ j)
  have hP0 : 0 ≤ ∑ k, p k := Finset.sum_nonneg (fun k _ => hp k)
  intro n
  induction n with
  | zero =>
    intro j
    simp only [chainLengthAux]
    refine ⟨add_nonneg (hr j) (hp j), ?_⟩
    simp only [Nat.cast_zero, zero_add, one_mul]
    linarith [hrs j, hps j]
  | succ n ih =>
    intro j
    simp only [chainLengthAux]
    split
    · refine ⟨add_nonneg (hr j) (hp j), ?_⟩
      push_cast
      nlinarith [hrs j, hps j]
    · rename_i i _
      obtain ⟨h1, h2⟩ := ih i
      refine ⟨add_nonneg (hp j) h1, ?_⟩
      push_cast
      nlinarith [hps j]


open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 < β)
    (tb : V ≃ Fin (Fintype.card V))
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσm : AEMeasurable (fun ω => σ (fun k => P k ω)) Pr) (j : V) :
    1 / (m : ℝ) * ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, (∫ ω', P i ω' ∂Pr) ∂Pr
      ≤ 1 / β * ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr := by
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμdef
  have hμnn : ∀ j, 0 ≤ μ j := fun j => integral_nonneg (fun ω => hP.2.1 j ω)
  have hXm : Measurable (fun ω k => P k ω) := measurable_pi_lambda _ (fun k => hP.1 k)
  have hY : AEMeasurable (fun ω => ((fun k => P k ω), σ (fun k => P k ω))) Pr :=
    hXm.aemeasurable.prodMk hσm
  have hpnn : ∀ ω, ∀ k, 0 ≤ (fun k => P k ω) k := fun ω k => hP.2.1 k ω
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set fl : Ω → ℝ := fun ω => chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j with hfl
  set fOμ : Ω → ℝ := fun ω => ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, μ i with hfOμ
  have hsumP : Integrable (fun ω => ∑ k, P k ω) Pr :=
    integrable_finsetSum _ (fun k _ => hP.2.2.1 k)
  have hflm : AEStronglyMeasurable fl Pr :=
    ((SSP28aux_chain_meas A r tb (Fintype.card V) j).comp_aemeasurable hY).aestronglyMeasurable
  have hOmeas : Measurable (fun x : (V → ℝ) × (V → ℝ) => ∑ i ∈ outOfOrder L x.2 j, μ i) := by
    have : (fun x : (V → ℝ) × (V → ℝ) => ∑ i ∈ outOfOrder L x.2 j, μ i)
        = fun x => ∑ i ∈ after L j, if x.2 i < x.2 j then μ i else 0 := by
      funext x
      rw [outOfOrder, Finset.sum_filter]
    rw [this]
    refine Finset.measurable_fun_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
    exact measurableSet_lt ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_snd)
  have hfOμm : AEStronglyMeasurable fOμ Pr :=
    (hOmeas.comp_aemeasurable hY).aestronglyMeasurable
  have hfOμi : Integrable fOμ Pr := by
    refine (integrable_const (∑ k, μ k)).mono' hfOμm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => hμnn i))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hμnn i)
  have hlb : ∀ ω, 0 ≤ fl ω ∧ fl ω ≤ ∑ k, r k + ((Fintype.card V : ℕ) + 1) * ∑ k, P k ω := by
    intro ω
    exact SSP28aux_chain_bound A r hr tb (fun k => P k ω) (σ (fun k => P k ω)) (hpnn ω)
      (Fintype.card V) j
  have hfli : Integrable fl Pr := by
    refine ((integrable_const (∑ k, r k)).add
      (hsumP.const_mul ((Fintype.card V : ℕ) + 1 : ℝ))).mono' hflm
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hlb ω).1]
    exact (hlb ω).2
  have hpt : ∀ ω, 1 / (m : ℝ) * fOμ ω ≤ 1 / β * fl ω := by
    intro ω
    have h := SSP27_det m hm A hacyc r hr L hLE β μ tb (fun k => P k ω) (hpnn ω)
      (σ (fun k => P k ω)) (hσ _ (hpnn ω)) j
    have h' : β * fOμ ω ≤ m * fl ω := h
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul, div_le_div_iff₀ hmR hβ]
    linarith
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_mono (hfOμi.const_mul _) (hfli.const_mul _) hpt
