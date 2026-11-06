-- Prove2me | solution 1 for StochSchedPrec.CMNS.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:59:36.912198+00:00
-- url     : https://prove2.me/submissions/adf8ed29-8918-42a5-b15d-a1c63c69866b

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem SSP_obs24 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (β : ℝ) (hβ : 0 ≤ β) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) :
    (∀ (j : V) (t : ℝ), charge m A r L p S j t ≤ β * μ j) ∧
    (∀ (j : V) (t : ℝ), availTime A r p S j ≤ t → t < S j →
      ∀ k, IsDelayed A r L p S k t → k ∈ before L j) ∧
    (∀ t : ℝ, busy p S t < m → (∃ i, t < S i ∧ avail A r p S i t) →
      ∃ k, IsDelayed A r L p S k t) := by
  classical
  obtain ⟨hfeas, _, hidle, hthr⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · -- (i): the charge never exceeds the threshold
    intro k t
    -- measurability in time
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
    have hD : Measurable fun t => IsDelayed A r L p S k t := by
      refine Measurable.and (Measurable.exists fun i => ?_) ?_
      · exact (hfirst (fun i t => t < S i) (fun i => hlt _) i).and (hav i).not
      · exact hfirst (fun i t => t < S i ∧ avail A r p S i t) (fun i => (hlt _).and (hav i)) k
    have hbusy_eq : ∀ t, (busy p S t : ℝ) = ∑ j, if S j ≤ t ∧ t < S j + p j then (1 : ℝ) else 0 := by
      intro t
      unfold busy
      rw [Finset.sum_boole]
    have hbm : Measurable fun t => (busy p S t : ℝ) := by
      simp only [hbusy_eq]
      refine Finset.measurable_fun_sum _ (fun j _ => Measurable.ite ?_ measurable_const
        measurable_const)
      exact ((hle (S j)).and (hlt _)).setOf
    set f : ℝ → ℝ := fun s => if IsDelayed A r L p S k s then ((m : ℝ) - (busy p S s : ℝ)) else 0
      with hf
    have hfm : Measurable f := Measurable.ite hD.setOf (measurable_const.sub hbm) measurable_const
    have hbusy_le : ∀ s, (busy p S s : ℝ) ≤ m := fun s => by exact_mod_cast hfeas.2.2 s
    have hbusy_card : ∀ s, (busy p S s : ℝ) ≤ Fintype.card V := fun s => by
      unfold busy
      exact_mod_cast Finset.card_filter_le _ _
    have hf0 : ∀ s, 0 ≤ f s := by
      intro s
      simp only [hf]
      split_ifs
      · linarith [hbusy_le s]
      · exact le_rfl
    have hfb : ∀ s, ‖f s‖ ≤ m := by
      intro s
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 s)]
      simp only [hf]
      split_ifs
      · have : (0 : ℝ) ≤ busy p S s := Nat.cast_nonneg _
        linarith
      · exact_mod_cast Nat.zero_le m
    have hII : ∀ a b, IntervalIntegrable f volume a b := by
      intro a b
      refine (intervalIntegrable_const (c := (m : ℝ))).mono_fun' hfm.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall hfb
    set F : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..s, f x with hFdef
    have hFeq : ∀ s, charge m A r L p S k s = F s := fun s => rfl
    have hFc : Continuous F := intervalIntegral.continuous_primitive hII 0
    have hpos : ∀ s, 0 < f s → F s < β * μ k := by
      intro s hs
      simp only [hf] at hs
      split_ifs at hs with hd
      · have hb : busy p S s < m := by
          have : (busy p S s : ℝ) < m := by linarith
          exact_mod_cast this
        rw [← hFeq]
        exact hthr s k hb hd
      · exact absurd hs (lt_irrefl 0)
    have hc0 : 0 ≤ β * μ k := mul_nonneg hβ (hμ k)
    rw [hFeq]
    rcases le_or_gt t 0 with ht | ht
    · have : F t = -∫ x in t..0, f x := by
        simp only [hFdef]; rw [intervalIntegral.integral_symm]
      rw [this]
      have : 0 ≤ ∫ x in t..0, f x := intervalIntegral.integral_nonneg ht (fun x _ => hf0 x)
      linarith
    by_contra hcon
    push Not at hcon
    set K := {x ∈ Set.Icc (0 : ℝ) t | F x ≤ β * μ k} with hK
    have hKc : IsClosed K := isClosed_Icc.inter (isClosed_le hFc continuous_const)
    have h0K : (0 : ℝ) ∈ K := by
      refine ⟨⟨le_rfl, ht.le⟩, ?_⟩
      simp [hFdef, hc0]
    have hKb : BddAbove K := ⟨t, fun x hx => hx.1.2⟩
    set t0 := sSup K with ht0
    have ht0K : t0 ∈ K := hKc.csSup_mem ⟨0, h0K⟩ hKb
    have ht0t : t0 < t := by
      rcases lt_or_eq_of_le ht0K.1.2 with h | h
      · exact h
      · exfalso; have := ht0K.2; rw [h] at this; linarith
    have hzero : ∀ x ∈ Set.Ioc t0 t, f x = 0 := by
      intro x hx
      have hFx : β * μ k < F x := by
        by_contra hle'
        push Not at hle'
        have hxK : x ∈ K := ⟨⟨by linarith [ht0K.1.1, hx.1], hx.2⟩, hle'⟩
        have := le_csSup hKb hxK
        linarith [hx.1]
      rcases lt_or_eq_of_le (hf0 x) with h | h
      · have := hpos x h; linarith
      · exact h.symm
    have hint0 : ∫ x in t0..t, f x = 0 := by
      rw [intervalIntegral.integral_of_le ht0t.le]
      rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => hzero x hx)]
      simp
    have hsplit : F t - F t0 = ∫ x in t0..t, f x := by
      simp only [hFdef]
      exact intervalIntegral.integral_interval_sub_left (hII 0 t) (hII 0 t0)
    have := ht0K.2
    linarith
  · -- (ii)
    intro j t hav ht k hk
    have hjav : avail A r p S j t := by
      unfold availTime at hav
      rw [Finset.fold_max_le] at hav
      refine ⟨hav.1, fun i hi => hav.2 i ?_⟩
      simp [hi]
    have := hk.2.2 j ⟨ht, hjav⟩
    simp [before, this]
  · -- (iii)
    intro t hb ⟨i, hi⟩
    obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i => t < S i ∧ avail A r p S i t) (fun i => L.symm i)
      ⟨i, by simp [hi]⟩
    obtain ⟨i0, hi0, hi0min⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i => t < S i) (fun i => L.symm i) ⟨i, by simp [hi.1]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hi0
    have hfirst0 : IsFirstWith L (fun i => t < S i) i0 :=
      ⟨hi0, fun i' hi' => hi0min i' (by simp [hi'])⟩
    refine ⟨k, ⟨i0, hfirst0, hidle t hb i0 hfirst0⟩, hk, fun i' hi' => hkmin i' (by simp [hi'])⟩

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
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L)
    (β : ℝ) (hβ : 0 ≤ β) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (tb : V ≃ Fin (Fintype.card V))
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) (j : V) :
    S j + p j ≤ ((m : ℝ) - 1) / m * chainLength A r tb p S j + 1 / (m : ℝ) * r j
      + 1 / (m : ℝ) * (∑ i ∈ before L j, (p i + β * μ i) + ∑ i ∈ outOfOrder L S j, p i) := by
  classical
  have hobs := SSP_obs24 m hm A hacyc r hr hAss L β hβ μ hμ p hp S hS
  obtain ⟨hfeas, _, hidle, _⟩ := hS
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hchain : ∀ z y, Relation.TransGen A z y → S z + p z ≤ S y := by
    intro z y h
    induction h with
    | single hab => exact hfeas.2.1 _ _ hab
    | @tail b c _ hbc ih =>
      have := hfeas.2.1 _ _ hbc
      linarith [hp b]
  have hS0 : ∀ i, 0 ≤ S i := fun i => le_trans (hr i) (hfeas.1 i)
  -- busy as a sum of indicators
  have hbusy_eq : ∀ t, (busy p S t : ℝ) = ∑ i, (Set.Ico (S i) (S i + p i)).indicator 1 t := by
    intro t
    unfold busy
    simp only [Set.indicator_apply, Set.mem_Ico, Pi.one_apply]
    rw [Finset.sum_boole]
  have hind_m : ∀ i, Measurable ((Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ)) :=
    fun i => measurable_const.indicator measurableSet_Ico
  have hbm : Measurable fun t => (busy p S t : ℝ) := by
    simp only [hbusy_eq]
    exact Finset.measurable_fun_sum _ (fun i _ => hind_m i)
  have hbusy_le : ∀ s, (busy p S s : ℝ) ≤ m := fun s => by exact_mod_cast hfeas.2.2 s
  have hbusy_card : ∀ s, (busy p S s : ℝ) ≤ Fintype.card V := fun s => by
    unfold busy; exact_mod_cast Finset.card_filter_le _ _
  set f : V → ℝ → ℝ := fun i s =>
    if IsDelayed A r L p S i s then ((m : ℝ) - (busy p S s : ℝ)) else 0 with hf
  have hf0 : ∀ i s, 0 ≤ f i s := by
    intro i s; simp only [hf]; split_ifs
    · linarith [hbusy_le s]
    · exact le_rfl
  have hfle : ∀ i s, f i s ≤ m := by
    intro i s; simp only [hf]; split_ifs
    · have : (0 : ℝ) ≤ busy p S s := Nat.cast_nonneg _
      linarith
    · exact_mod_cast Nat.zero_le m
  have hfm : ∀ i, Measurable (f i) := fun i =>
    Measurable.ite (SSP27_delayed_meas A r L p S i).setOf (measurable_const.sub hbm) measurable_const
  set ψ : ℝ → ℝ := fun s => (busy p S s : ℝ) + ∑ k ∈ before L j, f k s with hψ
  have hψm : Measurable ψ :=
    hbm.add (Finset.measurable_fun_sum _ (fun k _ => hfm k))
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s =>
    add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ => hf0 k s))
  set Mb : ℝ := Fintype.card V + Fintype.card V * m
  have hψb : ∀ s, ψ s ≤ Mb := by
    intro s
    have h1 : ∑ k ∈ before L j, f k s ≤ ∑ k ∈ before L j, (m : ℝ) :=
      Finset.sum_le_sum (fun k _ => hfle k s)
    have h2 : ∑ k ∈ before L j, (m : ℝ) ≤ Fintype.card V * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hmR.le
    simp only [hψ, Mb]
    linarith [hbusy_card s]
  have hII : ∀ a b, IntervalIntegrable ψ volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := Mb)).mono_fun' hψm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    show ‖ψ s‖ ≤ Mb
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 s)]; exact hψb s
  have hsplit : ∀ a b c : ℝ, ∫ s in a..c, ψ s = (∫ s in a..b, ψ s) + ∫ s in b..c, ψ s :=
    fun a b c => (intervalIntegral.integral_add_adjacent_intervals (hII a b) (hII b c)).symm
  have hIO : ∀ a b : ℝ, IntegrableOn ψ (Set.Ico a b) := by
    intro a b
    refine Integrable.mono' (g := fun _ => Mb) (integrableOn_const (by simp))
      hψm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 s)]; exact hψb s
  have hlow : ∀ a b c : ℝ, a ≤ b → (∀ s, a ≤ s → s < b → c ≤ ψ s) →
      c * (b - a) ≤ ∫ s in a..b, ψ s := by
    intro a b c hab hc
    have h1 : ∫ s in Set.Ico a b, c ≤ ∫ s in Set.Ico a b, ψ s :=
      setIntegral_mono_on (integrableOn_const (by simp)) (hIO a b)
        measurableSet_Ico (fun s hs => hc s hs.1 hs.2)
    rw [setIntegral_const, Real.volume_real_Ico_of_le hab, smul_eq_mul] at h1
    rw [intervalIntegral.integral_of_le hab, ← integral_Ico_eq_integral_Ioc]
    linarith
  have hgap : ∀ c, L.symm c ≤ L.symm j → ∀ s, s < S c → avail A r p S c s → (m : ℝ) ≤ ψ s := by
    intro c hc s hs hav
    have hsum0 : 0 ≤ ∑ k ∈ before L j, f k s := Finset.sum_nonneg (fun k _ => hf0 k s)
    by_cases hb : busy p S s < m
    · obtain ⟨k, hk⟩ := hobs.2.2 s hb ⟨c, hs, hav⟩
      have hkB : k ∈ before L j := by
        have := hk.2.2 c ⟨hs, hav⟩
        simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_trans this hc
      have h1 : f k s ≤ ∑ k ∈ before L j, f k s :=
        Finset.single_le_sum (fun k _ => hf0 k s) hkB
      have h2 : f k s = (m : ℝ) - busy p S s := by simp only [hf, if_pos hk]
      simp only [hψ]
      linarith
    · push Not at hb
      have : (m : ℝ) ≤ busy p S s := by exact_mod_cast hb
      simp only [hψ]
      linarith
  have hproc : ∀ k s, S k ≤ s → s < S k + p k → (1 : ℝ) ≤ ψ s := by
    intro k s h1 h2
    have hb : 1 ≤ busy p S s := by
      unfold busy
      exact Finset.card_pos.2 ⟨k, by simp [h1, h2]⟩
    have hsum0 : 0 ≤ ∑ k ∈ before L j, f k s := Finset.sum_nonneg (fun k _ => hf0 k s)
    have : (1 : ℝ) ≤ busy p S s := by exact_mod_cast hb
    simp only [hψ]
    linarith
  have hnn : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ s in a..b, ψ s := fun a b hab =>
    intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hab (fun s _ => hψ0 s)
  have claim : ∀ n c, L.symm c ≤ L.symm j →
      (Finset.univ.filter fun y => Relation.TransGen A y c).card ≤ n →
      (m : ℝ) * S c - ((m : ℝ) - 1) * (chainLengthAux A r tb p S n c - p c) - r c
        ≤ ∫ s in (0 : ℝ)..S c, ψ s := by
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
      rw [hsplit 0 (r c) (S c)]
      have h1 := hlow (r c) (S c) m (hfeas.1 c)
        (fun s hs hs' => hgap c hc s hs' ⟨hs, fun y hy => absurd hy (hnp y)⟩)
      have h2 := hnn 0 (r c) (hr c)
      nlinarith
    | succ n ih =>
      intro c hc hn
      simp only [chainLengthAux]
      split
      · rename_i hnone
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
        simp only [add_sub_cancel_right]
        rw [hsplit 0 (r c) (S c)]
        have h1 := hlow (r c) (S c) m (hfeas.1 c)
          (fun s hs hs' => hgap c hc s hs' ⟨hs, fun y hy => le_trans (hpred y hy) hs⟩)
        have h2 := hnn 0 (r c) (hr c)
        nlinarith
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
        have hrk := hAss k c hkc
        have hpc : p c + chainLengthAux A r tb p S n k - p c = chainLengthAux A r tb p S n k := by ring
        rw [hpc, hsplit 0 (S k) (S c), hsplit (S k) (S k + p k) (S c)]
        have h1 := hlow (S k) (S k + p k) 1 (by linarith [hp k])
          (fun s hs hs' => hproc k s hs hs')
        have h2 := hlow (S k + p k) (S c) m hCk
          (fun s hs hs' => hgap c hc s hs' ⟨by linarith, fun y hy => le_trans (hkmax y hy) hs⟩)
        nlinarith
  have hcl := claim (Fintype.card V) j le_rfl (Finset.card_filter_le _ _)
  -- upper bound on the integral of ψ over [0, S j)
  have hbII : IntervalIntegrable (fun s => (busy p S s : ℝ)) volume 0 (S j) := by
    refine (intervalIntegrable_const (c := (Fintype.card V : ℝ))).mono_fun' hbm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    show ‖(busy p S s : ℝ)‖ ≤ Fintype.card V
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact hbusy_card s
  have hfII : ∀ k, IntervalIntegrable (f k) volume 0 (S j) := by
    intro k
    refine (intervalIntegrable_const (c := (m : ℝ))).mono_fun' (hfm k).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    show ‖f k s‖ ≤ (m : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 k s)]; exact hfle k s
  have hsumII : IntervalIntegrable (fun s => ∑ k ∈ before L j, f k s) volume 0 (S j) := by
    have := IntervalIntegrable.sum (before L j) (fun k _ => hfII k)
    rwa [show (∑ k ∈ before L j, f k) = fun x => ∑ k ∈ before L j, f k x from
      funext fun x => Finset.sum_apply x _ _] at this
  have hU1 : ∫ s in (0 : ℝ)..S j, ψ s = (∫ s in (0 : ℝ)..S j, (busy p S s : ℝ))
      + ∑ k ∈ before L j, ∫ s in (0 : ℝ)..S j, f k s := by
    simp only [hψ]
    rw [intervalIntegral.integral_add hbII hsumII, intervalIntegral.integral_finsetSum
      (fun k _ => hfII k)]
  have hU2 : ∑ k ∈ before L j, ∫ s in (0 : ℝ)..S j, f k s ≤ ∑ k ∈ before L j, β * μ k :=
    Finset.sum_le_sum (fun k _ => hobs.1 k (S j))
  set T := Finset.univ.filter fun i => S i < S j with hT
  have hindI : ∀ i, Integrable ((Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ)) :=
    fun i => (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by simp))
  have hU3 : ∫ s in (0 : ℝ)..S j, (busy p S s : ℝ) ≤ ∑ i ∈ T, p i := by
    rw [intervalIntegral.integral_of_le (hS0 j), ← integral_Ico_eq_integral_Ioc]
    have hsT : Integrable (fun s => ∑ i ∈ T, (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s) :=
      integrable_finsetSum _ (fun i _ => hindI i)
    have hbIO : IntegrableOn (fun s => (busy p S s : ℝ)) (Set.Ico 0 (S j)) :=
      Integrable.mono' (g := fun _ => (Fintype.card V : ℝ)) (integrableOn_const (by simp))
        hbm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact hbusy_card s)
    have h1 : ∫ s in Set.Ico 0 (S j), (busy p S s : ℝ)
        ≤ ∫ s in Set.Ico 0 (S j), ∑ i ∈ T, (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s := by
      refine setIntegral_mono_on hbIO hsT.integrableOn measurableSet_Ico (fun s hs => ?_)
      rw [hbusy_eq s]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => S i < S j)]
      have : ∑ i ∈ Finset.univ.filter (fun i => ¬ S i < S j),
          (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        rw [Set.indicator_of_notMem]
        simp only [Set.mem_Ico, not_and, not_lt]
        intro h; exfalso; linarith [hs.2]
      rw [this, add_zero]
    have h2 : ∫ s in Set.Ico 0 (S j), ∑ i ∈ T, (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s
        ≤ ∫ s, ∑ i ∈ T, (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s :=
      setIntegral_le_integral hsT (Filter.Eventually.of_forall fun s =>
        Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) s))
    have h3 : ∫ s, ∑ i ∈ T, (Set.Ico (S i) (S i + p i)).indicator (1 : ℝ → ℝ) s = ∑ i ∈ T, p i := by
      rw [integral_finsetSum _ (fun i _ => hindI i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_indicator_one measurableSet_Ico, Real.volume_real_Ico_of_le (by linarith [hp i])]
      ring
    linarith
  have hU4 : ∑ i ∈ T, p i ≤ ∑ i ∈ before L j, p i - p j + ∑ i ∈ outOfOrder L S j, p i := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun i => L.symm i ≤ L.symm j)]
    have hjB : j ∈ before L j := by simp [before]
    have e1 : ∑ i ∈ T.filter (fun i => L.symm i ≤ L.symm j), p i ≤ ∑ i ∈ (before L j).erase j, p i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i _ _ => hp i)
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine Finset.mem_erase.2 ⟨?_, by simp [before, hi.2]⟩
      rintro rfl; exact lt_irrefl _ hi.1
    have e2 : T.filter (fun i => ¬ L.symm i ≤ L.symm j) = outOfOrder L S j := by
      ext i
      simp only [hT, outOfOrder, after, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      tauto
    rw [e2, ← Finset.sum_erase_eq_sub hjB]
    linarith
  -- final algebra
  set ℓ := chainLength A r tb p S j
  have hcl' : (m : ℝ) * S j - ((m : ℝ) - 1) * (ℓ - p j) - r j ≤ ∫ s in (0 : ℝ)..S j, ψ s := hcl
  have hBsplit : ∑ i ∈ before L j, (p i + β * μ i)
      = ∑ i ∈ before L j, p i + ∑ i ∈ before L j, β * μ i := Finset.sum_add_distrib
  have key : (m : ℝ) * (S j + p j) ≤ ((m : ℝ) - 1) * ℓ + r j
      + (∑ i ∈ before L j, (p i + β * μ i) + ∑ i ∈ outOfOrder L S j, p i) := by
    rw [hBsplit]
    nlinarith
  have hR : ((m : ℝ) - 1) / m * ℓ + 1 / (m : ℝ) * r j
      + 1 / (m : ℝ) * (∑ i ∈ before L j, (p i + β * μ i) + ∑ i ∈ outOfOrder L S j, p i)
      = (((m : ℝ) - 1) * ℓ + r j
      + (∑ i ∈ before L j, (p i + β * μ i) + ∑ i ∈ outOfOrder L S j, p i)) / m := by
    field_simp
  rw [hR, le_div_iff₀ hmR]
  linarith
