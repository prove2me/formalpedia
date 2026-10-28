-- Prove2me | solution 1 for ScheduledQueue.Diffusion.reversed_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:42:21.161923+00:00
-- url     : https://prove2.me/submissions/de69902c-9297-4c70-b47c-c41f9088589e

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting
import Theorems.Thm_ScheduledQueue_Diffusion_count_decomposition

open Set Filter Topology MeasureTheory ProbabilityTheory

section RealLemmas

variable (b : ℤ → ℝ) (t : ℝ)

/-- right-continuous count -/
noncomputable def SQR_Rc (u : ℝ) : ℕ := {m : ℤ | b m ∈ Ioc 0 u}.ncard
/-- left-continuous count -/
noncomputable def SQR_Lc (u : ℝ) : ℕ := {m : ℤ | b m ∈ Ioo 0 u}.ncard

lemma SQR_bdd (ht : 0 ≤ t) (hfin : {m : ℤ | b m ∈ Ioc 0 t}.Finite) (g : ℕ → ℝ) :
    ∃ M : ℝ, ∀ u : ℝ, u ≤ t → g (SQR_Rc b u) ≤ M ∧ g (SQR_Lc b u) ≤ M := by
  set n := {m : ℤ | b m ∈ Ioc 0 t}.ncard
  refine ⟨(Finset.range (n + 1)).sup' (by simp) g, fun u hu => ⟨?_, ?_⟩⟩
  · apply Finset.le_sup'
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Set.ncard_le_ncard (fun m hm => ?_) hfin
    simp only [mem_setOf_eq, mem_Ioc] at hm ⊢
    exact ⟨hm.1, hm.2.trans hu⟩
  · apply Finset.le_sup'
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Set.ncard_le_ncard (fun m hm => ?_) hfin
    simp only [mem_setOf_eq, mem_Ioo, mem_Ioc] at hm ⊢
    exact ⟨hm.1, hm.2.le.trans hu⟩

lemma SQR_left_right (ht : 0 ≤ t) (hfin : {m : ℤ | b m ∈ Ioc 0 t}.Finite)
    (hnot : ∀ m, b m ≠ t) (g : ℕ → ℝ) :
    (⨆ u : Icc 0 t, (g (SQR_Lc b u) - u)) = ⨆ u : Icc 0 t, (g (SQR_Rc b u) - u) := by
  obtain ⟨M, hM⟩ := SQR_bdd b t ht hfin g
  have hne : Nonempty (Icc 0 t) := ⟨⟨0, le_rfl, ht⟩⟩
  have hbddL : BddAbove (Set.range fun u : Icc 0 t => g (SQR_Lc b u) - u) := by
    refine ⟨M, ?_⟩; rintro _ ⟨⟨u, hu0, hu1⟩, rfl⟩; have := (hM u hu1).2; simp only; linarith
  have hbddR : BddAbove (Set.range fun u : Icc 0 t => g (SQR_Rc b u) - u) := by
    refine ⟨M, ?_⟩; rintro _ ⟨⟨u, hu0, hu1⟩, rfl⟩; have := (hM u hu1).1; simp only; linarith
  apply le_antisymm
  · refine ciSup_le (fun ⟨u, hu0, hu1⟩ => ?_)
    simp only
    set Pu := {m : ℤ | b m ∈ Ioo 0 u} with hPu
    have hPfin : Pu.Finite := hfin.subset (fun m hm => by
      simp only [hPu, mem_setOf_eq, mem_Ioo, mem_Ioc] at hm ⊢; exact ⟨hm.1, hm.2.le.trans hu1⟩)
    rcases Pu.eq_empty_or_nonempty with hP | hP
    · have hL : SQR_Lc b u = 0 := by simp only [SQR_Lc]; rw [← hPu, hP, Set.ncard_empty]
      have hR : SQR_Rc b 0 = 0 := by simp [SQR_Rc]
      have := le_ciSup hbddR ⟨0, le_rfl, ht⟩
      simp only [hR] at this
      rw [hL]; linarith
    · -- the largest point below `u`
      obtain ⟨m0, hm0, hmax⟩ := hPfin.exists_maximalFor b Pu hP
      set u' := b m0
      have hm0' : b m0 ∈ Ioo 0 u := hm0
      have hmax' : ∀ m ∈ Pu, b m ≤ u' := by
        intro m hm
        by_contra hc
        push Not at hc
        have := hmax hm hc.le
        linarith
      have hRL : SQR_Rc b u' = SQR_Lc b u := by
        simp only [SQR_Rc, SQR_Lc]
        congr 1; ext m
        simp only [mem_setOf_eq, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_lt h2 hm0'.2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hmax' m ⟨h1, h2⟩⟩
      have := le_ciSup hbddR ⟨u', hm0'.1.le, (hm0'.2.le.trans hu1)⟩
      simp only [hRL] at this
      have : u' ≤ u := hm0'.2.le
      linarith
  · refine ciSup_le (fun ⟨u, hu0, hu1⟩ => ?_)
    simp only
    rcases eq_or_lt_of_le hu1 with hut | hut
    · -- `u = t`: the two counts agree
      have hRL : SQR_Rc b u = SQR_Lc b u := by
        simp only [SQR_Rc, SQR_Lc]
        congr 1; ext m
        simp only [mem_setOf_eq, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 (by rw [hut]; exact hnot m)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2.le⟩
      rw [hRL]
      exact le_ciSup hbddL ⟨u, hu0, hu1⟩
    · refine le_of_forall_pos_le_add (fun ε hε => ?_)
      set Q := {m : ℤ | b m ∈ Ioc u t} with hQ
      have hQfin : Q.Finite := hfin.subset (fun m hm => by
        simp only [hQ, mem_setOf_eq, mem_Ioc] at hm ⊢; exact ⟨lt_of_le_of_lt hu0 hm.1, hm.2⟩)
      obtain ⟨δ, hδ0, hδt, hδQ⟩ : ∃ δ : ℝ, 0 < δ ∧ u + δ ≤ t ∧ ∀ m ∈ Q, u + δ ≤ b m := by
        rcases Q.eq_empty_or_nonempty with hQe | hQne
        · refine ⟨t - u, by linarith, by linarith, fun m hm => ?_⟩
          rw [hQe] at hm; exact absurd hm (Set.notMem_empty _)
        · obtain ⟨m1, hm1, hmin⟩ := hQfin.exists_minimalFor b Q hQne
          have hm1' : b m1 ∈ Ioc u t := hm1
          refine ⟨b m1 - u, by linarith [hm1'.1], by linarith [hm1'.2], fun m hm => ?_⟩
          by_contra hc; push Not at hc
          have := hmin hm (by linarith)
          linarith
      set u'' := u + min δ ε / 2 with hu''
      have hmin0 : 0 < min δ ε := lt_min hδ0 hε
      have hu''1 : u < u'' := by rw [hu'']; linarith
      have hu''2 : u'' ≤ t := by
        have : min δ ε ≤ δ := min_le_left _ _
        rw [hu'']; linarith
      have hLR : SQR_Lc b u'' = SQR_Rc b u := by
        simp only [SQR_Rc, SQR_Lc]
        congr 1; ext m
        simp only [mem_setOf_eq, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_contra hc; push Not at hc
          have hmQ : m ∈ Q := ⟨hc, by linarith⟩
          have := hδQ m hmQ
          have : min δ ε ≤ δ := min_le_left _ _
          linarith
        · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_lt h2 hu''1⟩
      have := le_ciSup hbddL ⟨u'', by linarith, hu''2⟩
      simp only [hLR] at this
      have : min δ ε ≤ ε := min_le_right _ _
      linarith

lemma SQR_jump (ht : 0 ≤ t) (hfin : {m : ℤ | b m ∈ Ioc 0 t}.Finite) (g : ℕ → ℝ) :
    (⨆ u : Icc 0 t, (g (SQR_Rc b u) - u)) =
      ⨆ m : ℤ, (if b m ∈ Ioc 0 t then g (SQR_Rc b (b m)) - b m else g 0) := by
  obtain ⟨M, hM⟩ := SQR_bdd b t ht hfin g
  have hne : Nonempty (Icc 0 t) := ⟨⟨0, le_rfl, ht⟩⟩
  have hbddR : BddAbove (Set.range fun u : Icc 0 t => g (SQR_Rc b u) - u) := by
    refine ⟨M, ?_⟩; rintro _ ⟨⟨u, hu0, hu1⟩, rfl⟩; have := (hM u hu1).1; simp only; linarith
  have hR0 : SQR_Rc b 0 = 0 := by simp [SQR_Rc]
  have hbddH : BddAbove (Set.range fun m : ℤ =>
      (if b m ∈ Ioc 0 t then g (SQR_Rc b (b m)) - b m else g 0)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨m, rfl⟩
    simp only
    split_ifs with hm
    · have := (hM (b m) hm.2).1; linarith [hm.1]
    · have := (hM 0 ht).1; rw [hR0] at this; exact this
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℤ, b m0 ∉ Ioc 0 t := by
    obtain ⟨m0, hm0⟩ := hfin.infinite_compl.nonempty
    exact ⟨m0, hm0⟩
  apply le_antisymm
  · refine ciSup_le (fun ⟨u, hu0, hu1⟩ => ?_)
    simp only
    set Pu := {m : ℤ | b m ∈ Ioc 0 u} with hPu
    have hPfin : Pu.Finite := hfin.subset (fun m hm => by
      simp only [hPu, mem_setOf_eq, mem_Ioc] at hm ⊢; exact ⟨hm.1, hm.2.trans hu1⟩)
    rcases Pu.eq_empty_or_nonempty with hP | hP
    · have hR : SQR_Rc b u = 0 := by simp only [SQR_Rc]; rw [← hPu, hP, Set.ncard_empty]
      have := le_ciSup hbddH m0
      simp only [hm0, if_false] at this
      rw [hR]; linarith
    · obtain ⟨m1, hm1, hmax⟩ := hPfin.exists_maximalFor b Pu hP
      have hm1' : b m1 ∈ Ioc 0 u := hm1
      have hmax' : ∀ m ∈ Pu, b m ≤ b m1 := by
        intro m hm
        by_contra hc
        push Not at hc
        have := hmax hm hc.le
        linarith
      have hRR : SQR_Rc b (b m1) = SQR_Rc b u := by
        simp only [SQR_Rc]
        congr 1; ext m
        simp only [mem_setOf_eq, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans hm1'.2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hmax' m ⟨h1, h2⟩⟩
      have hin : b m1 ∈ Ioc 0 t := ⟨hm1'.1, hm1'.2.trans hu1⟩
      have := le_ciSup hbddH m1
      simp only [hin, if_true, hRR] at this
      linarith [hm1'.2]
  · refine ciSup_le (fun m => ?_)
    split_ifs with hm
    · exact le_ciSup hbddR ⟨b m, hm.1.le, hm.2⟩
    · have := le_ciSup hbddR ⟨0, le_rfl, ht⟩
      simp only [hR0, sub_zero] at this
      exact this

end RealLemmas

lemma SQR_fract_pres (q : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    (volume.restrict (Icc (0 : ℝ) 1)) {u | Int.fract (u - q) ∈ A} =
      (volume.restrict (Icc (0 : ℝ) 1)) A := by
  have hS : MeasurableSet {u : ℝ | Int.fract (u - q) ∈ A} :=
    (measurable_id.sub_const q).fract hA
  have hIcc : (volume.restrict (Icc (0 : ℝ) 1)) = volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have hIoo : (volume.restrict (Ioc (0 : ℝ) 1)) = volume.restrict (Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  set ψ : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle) with hψ
  set g : UnitAddCircle → ENNReal := fun z => A.indicator 1 ((AddCircle.equivIco 1 0 z : ℝ))
    with hg
  have hgψ : ∀ x : ℝ, g (ψ x) = A.indicator 1 (Int.fract x) := by
    intro x
    simp only [hg, hψ]
    rw [AddCircle.coe_equivIco_mk_apply]
    simp
  rw [hIcc, ← lintegral_indicator_one hS, ← lintegral_indicator_one hA]
  have e1 : ∫⁻ u, {u : ℝ | Int.fract (u - q) ∈ A}.indicator 1 u ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      ∫⁻ u in Ioc (0 : ℝ) (0 + 1), (fun z => g (z + ψ (-q))) (ψ u) := by
    simp only [zero_add]
    refine lintegral_congr (fun u => ?_)
    have : ψ u + ψ (-q) = ψ (u - q) := by
      simp only [hψ]; rw [sub_eq_add_neg, AddCircle.coe_add]
    simp only [this, hgψ]
    simp [Set.indicator]
  have e2 : ∫⁻ u in Ioc (0 : ℝ) (0 + 1), (fun z => g (z + ψ (-q))) (ψ u) =
      ∫⁻ u in Ioc (0 : ℝ) (0 + 1), g (ψ u) := by
    rw [UnitAddCircle.lintegral_preimage 0 (fun z => g (z + ψ (-q))),
      UnitAddCircle.lintegral_preimage 0 g]
    exact lintegral_add_right_eq_self g (ψ (-q))
  rw [e1, e2, zero_add, hIoo]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
  rw [hgψ]
  have : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
  rw [this]

lemma SQR_refl_pres (q : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    (volume.restrict (Icc (0 : ℝ) 1)) {u | Int.fract (q - u) ∈ A} =
      (volume.restrict (Icc (0 : ℝ) 1)) A := by
  set S' := {w : ℝ | Int.fract (w - (1 - q)) ∈ A} with hS'
  have hS'm : MeasurableSet S' := (measurable_id.sub_const _).fract hA
  have e : {u : ℝ | Int.fract (q - u) ∈ A} = (fun u => 1 - u) ⁻¹' S' := by
    ext u; simp only [hS', mem_setOf_eq, mem_preimage]
    have : 1 - u - (1 - q) = q - u := by ring
    rw [this]
  have hm : MeasurableSet {u : ℝ | Int.fract (q - u) ∈ A} := by
    rw [e]; exact (measurable_const.sub measurable_id) hS'm
  rw [Measure.restrict_apply hm, e]
  have e2 : (fun u : ℝ => 1 - u) ⁻¹' S' ∩ Icc 0 1 = (fun u : ℝ => 1 - u) ⁻¹' (S' ∩ Icc 0 1) := by
    ext u; simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  rw [e2, (Measure.measurePreserving_sub_left volume (1 : ℝ)).measure_preimage
    (hS'm.inter measurableSet_Icc).nullMeasurableSet, ← Measure.restrict_apply hS'm]
  exact SQR_fract_pres (1 - q) A hA

lemma SQR_encard_meas {α : Type*} [MeasurableSpace α] (A : ℤ → Set α)
    (hA : ∀ j, MeasurableSet (A j)) : Measurable (fun p => {j : ℤ | p ∈ A j}.encard) := by
  set Ψ : α → ENNReal := fun p => ∑' j : ℤ, {j : ℤ | p ∈ A j}.indicator 1 j with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.ennreal_tsum (fun j => ?_)
    have : (fun p : α => {j : ℤ | p ∈ A j}.indicator (1 : ℤ → ENNReal) j) = (A j).indicator 1 := by
      funext p; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator (hA j)
  have hΨeq : ∀ p, Ψ p = (({j : ℤ | p ∈ A j}.encard : ℕ∞) : ENNReal) := by
    intro p
    simp only [hΨ]
    rw [← tsum_subtype]; simp only [Pi.one_apply]; rw [ENNReal.tsum_set_one]
  apply measurable_to_countable'
  intro n
  have : (fun p => {j : ℤ | p ∈ A j}.encard) ⁻¹' {n} = Ψ ⁻¹' {(n : ENNReal)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, hΨeq, ENat.toENNReal_inj]
  rw [this]
  exact hΨm (measurableSet_singleton _)

lemma SQR_ncard_meas {α : Type*} [MeasurableSpace α] (A : ℤ → Set α)
    (hA : ∀ j, MeasurableSet (A j)) : Measurable (fun p => {j : ℤ | p ∈ A j}.ncard) := by
  have : (fun p => {j : ℤ | p ∈ A j}.ncard) = (fun x : ℕ∞ => x.toNat) ∘
      (fun p => {j : ℤ | p ∈ A j}.encard) := by
    funext p; simp [Set.ncard_def]
  rw [this]
  exact Measurable.of_discrete.comp (SQR_encard_meas A hA)

/-- time reversal of the input around `t = q h` -/
noncomputable def SQR_Refl (q : ℝ) (p : ℝ × (ℤ → ℝ)) : ℝ × (ℤ → ℝ) :=
  (Int.fract (q - p.1), fun m => -p.2 (⌊q - p.1⌋ - m))

lemma SQR_Refl_meas (q : ℝ) : Measurable (SQR_Refl q) := by
  have h1 : Measurable (fun p : ℝ × (ℤ → ℝ) => Int.fract (q - p.1)) :=
    (measurable_const.sub measurable_fst).fract
  have h2 : Measurable (fun p : ℝ × (ℤ → ℝ) => fun m : ℤ => -p.2 (⌊q - p.1⌋ - m)) := by
    refine measurable_pi_lambda _ (fun m => ?_)
    have hF : Measurable (fun r : (ℤ → ℝ) × ℤ => -r.1 (r.2 - m)) :=
      measurable_from_prod_countable_left (fun K => (measurable_pi_apply (K - m)).neg)
    have hG : Measurable (fun p : ℝ × (ℤ → ℝ) => (p.2, ⌊q - p.1⌋)) :=
      measurable_snd.prodMk (measurable_const.sub measurable_fst).floor
    exact hF.comp hG
  exact h1.prodMk h2

lemma SQR_Refl_law (q : ℝ) (μ μm : Measure (ℤ → ℝ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μm]
    (hμ : ∀ K : ℤ, μ.map (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) = μm) :
    ((volume.restrict (Icc (0 : ℝ) 1)).prod μ).map (SQR_Refl q) =
      (volume.restrict (Icc (0 : ℝ) 1)).prod μm := by
  set lam := volume.restrict (Icc (0 : ℝ) 1) with hlam
  haveI : IsFiniteMeasure lam := by
    rw [hlam]; exact isFiniteMeasure_restrict.mpr (by simp)
  symm
  refine Measure.prod_eq (fun A B hA hB => ?_)
  rw [Measure.map_apply (SQR_Refl_meas q) (hA.prod hB),
    Measure.prod_apply ((SQR_Refl_meas q) (hA.prod hB))]
  have hsh : ∀ K : ℤ, Measurable (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) :=
    fun K => measurable_pi_lambda _ (fun m => (measurable_pi_apply (K - m)).neg)
  have hS : MeasurableSet {u : ℝ | Int.fract (q - u) ∈ A} :=
    (measurable_const.sub measurable_id).fract hA
  have hpt : ∀ u : ℝ, μ (Prod.mk u ⁻¹' (SQR_Refl q ⁻¹' A ×ˢ B)) =
      {u : ℝ | Int.fract (q - u) ∈ A}.indicator (fun _ => μm B) u := by
    intro u
    by_cases hu : Int.fract (q - u) ∈ A
    · have e : Prod.mk u ⁻¹' (SQR_Refl q ⁻¹' A ×ˢ B) =
          (fun (x : ℤ → ℝ) (m : ℤ) => -x (⌊q - u⌋ - m)) ⁻¹' B := by
        ext x; simp [SQR_Refl, hu]
      rw [e, ← Measure.map_apply (hsh _) hB, hμ]
      simp [Set.indicator, hu]
    · have e : Prod.mk u ⁻¹' (SQR_Refl q ⁻¹' A ×ˢ B) = ∅ := by
        ext x; simp [SQR_Refl, hu]
      rw [e]
      simp [Set.indicator, hu]
  simp_rw [hpt]
  rw [lintegral_indicator_const hS, SQR_refl_pres q A hA, mul_comm]

/-- the order-reversing permutation of `1, …, n` -/
def SQR_sig (n i : ℕ) : ℕ := if 1 ≤ i ∧ i ≤ n then n + 1 - i else i

lemma SQR_sig_invol (n : ℕ) : Function.Involutive (SQR_sig n) := by
  intro i
  simp only [SQR_sig]
  split_ifs with h1 h2 <;> omega

/-- reversal of the first `n` service times -/
def SQR_rev (n : ℕ) (v : ℕ → ℝ) : ℕ → ℝ := fun i => v (SQR_sig n i)

lemma SQR_rev_meas : Measurable (fun r : ℕ × (ℕ → ℝ) => SQR_rev r.1 r.2) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_from_prod_countable_right (fun n => measurable_pi_apply (SQR_sig n i))

/-- the count of the input `p` in `(0, s]` -/
noncomputable def SQR_cnt (h : ℝ) (p : ℝ × (ℤ → ℝ)) (s : ℝ) : ℕ :=
  {m : ℤ | (m : ℝ) * h + h * p.1 + p.2 m ∈ Ioc 0 s}.ncard

lemma SQR_cnt_meas (h s : ℝ) : Measurable (fun p => SQR_cnt h p s) := by
  apply SQR_ncard_meas (fun m => {p : ℝ × (ℤ → ℝ) | (m : ℝ) * h + h * p.1 + p.2 m ∈ Ioc 0 s})
  intro m
  have : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + h * p.1 + p.2 m) := by fun_prop
  exact this measurableSet_Ioc

noncomputable def SQR_Psi (h t : ℝ) (z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ)) :
    (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) :=
  (SQR_Refl (t / h) z.1, SQR_rev (SQR_cnt h z.1 t) z.2)

lemma SQR_Psi_meas (h t : ℝ) : Measurable (SQR_Psi h t) :=
  ((SQR_Refl_meas _).comp measurable_fst).prodMk
    (SQR_rev_meas.comp (((SQR_cnt_meas h t).comp measurable_fst).prodMk measurable_snd))

lemma SQR_Psi_law (h t : ℝ) (μ μm : Measure (ℤ → ℝ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μm] (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν]
    (hμ : ∀ K : ℤ, μ.map (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) = μm)
    (hν : ∀ n : ℕ, ν.map (SQR_rev n) = ν) :
    (((volume.restrict (Icc (0 : ℝ) 1)).prod μ).prod ν).map (SQR_Psi h t) =
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μm).prod ν := by
  set lam := volume.restrict (Icc (0 : ℝ) 1) with hlam
  haveI : IsFiniteMeasure lam := by
    rw [hlam]; exact isFiniteMeasure_restrict.mpr (by simp)
  symm
  refine Measure.prod_eq (fun C D hC hD => ?_)
  rw [Measure.map_apply (SQR_Psi_meas h t) (hC.prod hD),
    Measure.prod_apply ((SQR_Psi_meas h t) (hC.prod hD))]
  have hrevm : ∀ n, Measurable (SQR_rev n) := fun n =>
    measurable_pi_lambda _ (fun i => measurable_pi_apply (SQR_sig n i))
  have hS : MeasurableSet (SQR_Refl (t / h) ⁻¹' C) := (SQR_Refl_meas _) hC
  have hpt : ∀ p : ℝ × (ℤ → ℝ), ν (Prod.mk p ⁻¹' (SQR_Psi h t ⁻¹' C ×ˢ D)) =
      (SQR_Refl (t / h) ⁻¹' C).indicator (fun _ => ν D) p := by
    intro p
    by_cases hp : SQR_Refl (t / h) p ∈ C
    · have e : Prod.mk p ⁻¹' (SQR_Psi h t ⁻¹' C ×ˢ D) = SQR_rev (SQR_cnt h p t) ⁻¹' D := by
        ext v; simp [SQR_Psi, hp]
      rw [e, ← Measure.map_apply (hrevm _) hD, hν]
      simp [Set.indicator, hp]
    · have e : Prod.mk p ⁻¹' (SQR_Psi h t ⁻¹' C ×ˢ D) = ∅ := by
        ext v; simp [SQR_Psi, hp]
      rw [e]
      simp [Set.indicator, hp]
  simp_rw [hpt]
  rw [lintegral_indicator_const hS, ← Measure.map_apply (SQR_Refl_meas _) hC,
    SQR_Refl_law (t / h) μ μm hμ, mul_comm]

lemma SQR_sum_rev (v : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.Ioc (n - k) n, v i = ∑ i ∈ Finset.Icc 1 k, SQR_rev n v i := by
  refine Finset.sum_nbij' (fun i => n + 1 - i) (fun i => n + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢; omega
  · intro i hi
    simp only [Finset.mem_Ioc] at hi
    simp only [SQR_rev, SQR_sig]
    rw [if_pos (by omega)]
    congr 1; omega

/-- the pathwise time-reversal identity -/
lemma SQR_path (h t : ℝ) (hh : 0 < h) (ht : 0 ≤ t) (p : ℝ × (ℤ → ℝ)) (v : ℕ → ℝ)
    (hF : {j : ℤ | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 t}.Finite)
    (hN0 : ∀ j : ℤ, (j : ℝ) * h + h * p.1 + p.2 j ≠ 0)
    (hNt : ∀ j : ℤ, (j : ℝ) * h + h * p.1 + p.2 j ≠ t) :
    (⨆ s : Icc 0 t, ((∑ i ∈ Finset.Ioc (SQR_cnt h p s) (SQR_cnt h p t), v i) - (t - s))) =
      ⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (SQR_cnt h (SQR_Psi h t (p, v)).1 s),
        (SQR_Psi h t (p, v)).2 i) - s) := by
  set a : ℤ → ℝ := fun j => (j : ℝ) * h + h * p.1 + p.2 j with ha
  set K : ℤ := ⌊t / h - p.1⌋ with hK
  set n := SQR_cnt h p t with hn
  set b : ℤ → ℝ := fun m => (m : ℝ) * h + h * (SQR_Refl (t / h) p).1 + (SQR_Refl (t / h) p).2 m
    with hb
  have hbm : ∀ m, b m = t - a (K - m) := by
    intro m
    simp only [hb, ha, SQR_Refl, hK]
    have e1 : Int.fract (t / h - p.1) = (t / h - p.1) - ⌊t / h - p.1⌋ := (Int.self_sub_floor _).symm
    rw [e1]; push_cast
    field_simp
    ring
  have hKinj : Function.Injective (fun j : ℤ => K - j) := sub_right_injective
  -- the reflected points in an interval
  have himg : ∀ (S : Set ℝ), {m : ℤ | b m ∈ S} = (fun j : ℤ => K - j) '' {j : ℤ | t - a j ∈ S} := by
    intro S
    ext m
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hm; refine ⟨K - m, ?_, by ring⟩; rw [← hbm]; exact hm
    · rintro ⟨j, hj, rfl⟩; rw [hbm]; have : K - (K - j) = j := by ring
      rw [this]; exact hj
  have hfinb : {m : ℤ | b m ∈ Ioc 0 t}.Finite := by
    rw [himg]
    refine Set.Finite.image _ (hF.subset (fun j hj => ?_))
    simp only [mem_setOf_eq, mem_Ioc] at hj ⊢
    refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm (hN0 j)), by linarith⟩
  have hnotb : ∀ m, b m ≠ t := by
    intro m hm; rw [hbm] at hm; exact hN0 (K - m) (by linarith)
  set g : ℕ → ℝ := fun k => ∑ i ∈ Finset.Icc 1 k, SQR_rev n v i with hg
  -- counting identity
  have hcount : ∀ u : ℝ, 0 ≤ u → u ≤ t → SQR_cnt h p (t - u) + SQR_Lc b u = n := by
    intro u hu0 hu1
    have e1 : SQR_Lc b u = {j : ℤ | a j ∈ Ioc (t - u) t}.ncard := by
      simp only [SQR_Lc]
      rw [himg, Set.ncard_image_of_injective _ hKinj]
      congr 1; ext j
      simp only [mem_setOf_eq, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne (by linarith) (by
          intro hc; exact hNt j (by linarith)), by linarith⟩
    have hdisj : Disjoint {j : ℤ | a j ∈ Ioc 0 (t - u)} {j : ℤ | a j ∈ Ioc (t - u) t} := by
      rw [Set.disjoint_left]
      intro j h1 h2
      simp only [mem_setOf_eq, mem_Ioc] at h1 h2
      linarith [h1.2, h2.1]
    have hf1 : {j : ℤ | a j ∈ Ioc 0 (t - u)}.Finite := hF.subset (fun j hj => by
        simp only [mem_setOf_eq, mem_Ioc] at hj ⊢; exact ⟨hj.1, by linarith [hj.2]⟩)
    have hf2 : {j : ℤ | a j ∈ Ioc (t - u) t}.Finite := hF.subset (fun j hj => by
        simp only [mem_setOf_eq, mem_Ioc] at hj ⊢; exact ⟨by linarith [hj.1], hj.2⟩)
    rw [e1, hn]
    show {j : ℤ | a j ∈ Ioc 0 (t - u)}.ncard + {j : ℤ | a j ∈ Ioc (t - u) t}.ncard =
      {j : ℤ | a j ∈ Ioc 0 t}.ncard
    rw [← Set.ncard_union_eq hdisj hf1 hf2]
    congr 1; ext j
    simp only [mem_union, mem_setOf_eq, mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hc : a j ≤ t - u
      · left; exact ⟨h1, hc⟩
      · right; push Not at hc; exact ⟨hc, h2⟩
  -- reindex the left side by `u = t - s`
  set e : Icc (0 : ℝ) t ≃ Icc (0 : ℝ) t :=
    { toFun := fun u => ⟨t - u, by constructor <;> linarith [u.2.1, u.2.2]⟩
      invFun := fun u => ⟨t - u, by constructor <;> linarith [u.2.1, u.2.2]⟩
      left_inv := fun u => by ext; simp
      right_inv := fun u => by ext; simp } with he
  rw [← Equiv.iSup_comp e]
  have hL : ∀ u : Icc (0 : ℝ) t,
      ((∑ i ∈ Finset.Ioc (SQR_cnt h p (e u)) n, v i) - (t - (e u : ℝ))) =
        g (SQR_Lc b u) - u := by
    rintro ⟨u, hu0, hu1⟩
    have hc := hcount u hu0 hu1
    simp only [he, Equiv.coe_fn_mk]
    have hk : SQR_Lc b u ≤ n := by omega
    have e2 : SQR_cnt h p (t - u) = n - SQR_Lc b u := by omega
    rw [e2, SQR_sum_rev v n _ hk]
    simp only [hg] <;> ring
  simp_rw [hL]
  rw [SQR_left_right b t ht hfinb hnotb g]
  rfl

lemma SQRD_noatom (h c d : ℝ) (hh : 0 < h) :
    (volume.restrict (Icc (0:ℝ) 1)) {v : ℝ | d + v * h = c} = 0 := by
  have hsub : {v : ℝ | d + v * h = c} ⊆ {(c - d) / h} := by
    intro v hv
    simp only [mem_setOf_eq] at hv
    simp only [mem_singleton_iff]
    field_simp; linarith
  refine measure_mono_null hsub ?_
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

lemma SQRD_ae_sched {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (d c : ℝ) :
    ∀ᵐ ω ∂P, d + U ω * h ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [hin.uniform.measure_eq (p := fun v => d + v * h = c)
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact SQRD_noatom h c d hh

lemma SQRD_ae_arr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (i : ℤ) (d c : ℝ) :
    ∀ᵐ ω ∂P, d + U ω * h + ξ i ω ≠ c := by
  have hind : IndepFun U (ξ i) P := hin.indep_shift.comp measurable_id (measurable_pi_apply i)
  have hUm : AEMeasurable U P := hin.uniform.aemeasurable
  have hξm : AEMeasurable (ξ i) P := (hin.measurable i).aemeasurable
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hUm hξm).mp hind
  set S : Set (ℝ × ℝ) := {p | d + p.1 * h + p.2 = c} with hSdef
  have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have e1 : P {ω | d + U ω * h + ξ i ω = c} = P.map (fun ω => (U ω, ξ i ω)) S := by
    rw [Measure.map_apply_of_aemeasurable (hUm.prodMk hξm) hS]; rfl
  rw [e1, hmap, Measure.prod_apply_symm hS, hin.uniform.map_eq]
  have : ∀ y : ℝ, (volume.restrict (Icc (0:ℝ) 1)) ((fun x => (x, y)) ⁻¹' S) = 0 := by
    intro y
    have := SQRD_noatom h (c - y) d hh
    refine measure_mono_null ?_ this
    intro v hv
    simp only [hSdef, mem_preimage, mem_setOf_eq] at hv
    simp only [mem_setOf_eq]; linarith
  simp [this]

/-- the reversed-time functional -/
noncomputable def SQR_Phi (h t : ℝ) (z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ)) : ℝ :=
  ⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (SQR_cnt h z.1 s), z.2 i) - s)

/-- its countable representation -/
noncomputable def SQR_Phi2 (h t : ℝ) (z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ)) : ℝ :=
  ⨆ m : ℤ, (if (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t then
    (∑ i ∈ Finset.Icc 1 (SQR_cnt h z.1 ((m : ℝ) * h + h * z.1.1 + z.1.2 m)), z.2 i) -
      ((m : ℝ) * h + h * z.1.1 + z.1.2 m)
    else ∑ i ∈ Finset.Icc 1 0, z.2 i)

lemma SQR_Phi_eq (h t : ℝ) (ht : 0 ≤ t) (z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ))
    (hfin : {m : ℤ | (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}.Finite) :
    SQR_Phi h t z = SQR_Phi2 h t z :=
  SQR_jump (fun m : ℤ => (m : ℝ) * h + h * z.1.1 + z.1.2 m) t ht hfin
    (fun k => ∑ i ∈ Finset.Icc 1 k, z.2 i)

lemma SQR_Phi2_meas (h t : ℝ) : Measurable (SQR_Phi2 h t) := by
  have hG : Measurable (fun r : ℕ × (ℕ → ℝ) => ∑ i ∈ Finset.Icc 1 r.1, r.2 i) :=
    measurable_from_prod_countable_right
      (fun k => by
        show Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i)
        exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  refine Measurable.iSup (fun m => ?_)
  have harr : ∀ m' : ℤ, Measurable
      (fun z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) => (m' : ℝ) * h + h * z.1.1 + z.1.2 m') := by
    intro m'; fun_prop
  refine Measurable.ite ((harr m) measurableSet_Ioc) ?_ ?_
  · have hk : Measurable (fun z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) =>
        SQR_cnt h z.1 ((m : ℝ) * h + h * z.1.1 + z.1.2 m)) := by
      apply SQR_ncard_meas (fun m' => {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
        0 < (m' : ℝ) * h + h * z.1.1 + z.1.2 m' ∧
          (m' : ℝ) * h + h * z.1.1 + z.1.2 m' ≤ (m : ℝ) * h + h * z.1.1 + z.1.2 m})
      intro m'
      exact (measurableSet_lt measurable_const (harr m')).inter
        (measurableSet_le (harr m') (harr m))
    exact (hG.comp (hk.prodMk measurable_snd)).sub (harr m)
  · exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd)

lemma SQR_bad_meas (h t : ℝ) : MeasurableSet {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
    ¬ {m : ℤ | (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}.Finite} := by
  have hm := SQR_encard_meas (fun m : ℤ => {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
    (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}) (fun m => by
      have : Measurable (fun z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) => (m : ℝ) * h + h * z.1.1 + z.1.2 m) := by
        fun_prop
      exact this measurableSet_Ioc)
  have e : {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
      ¬ {m : ℤ | (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}.Finite} =
      (fun z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) => {m : ℤ | z ∈ {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
        (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}}.encard) ⁻¹' {⊤} := by
    ext z
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, Set.encard_eq_top_iff]
    rfl
  rw [e]
  exact hm (measurableSet_singleton _)

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) :
    ∀ t : ℝ, 0 ≤ t →
      IdentDistrib (workload h ξ U V t)
        (fun ω => ⨆ s : Icc 0 t,
          ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h (fun j ω' => -ξ j ω') U s ω), V i ω) - s)) P P := by
  intro t ht
  -- the reflected input `-ξ`
  set ξ' : ℤ → Ω → ℝ := fun j ω => -ξ j ω with hξ'
  have hin' : ScheduledQueue.Stability.ScheduledInput P ξ' U :=
    { measurable := fun j => (hin.measurable j).neg
      indep := hin.indep.comp (fun _ x => -x) (fun _ => measurable_neg)
      identDistrib := fun j => (hin.identDistrib j).comp measurable_neg
      integrable := hin.integrable.neg
      uniform := hin.uniform
      indep_shift := by
        have hm : Measurable (fun (f : ℤ → ℝ) (j : ℤ) => -f j) :=
          measurable_pi_lambda _ (fun j => (measurable_pi_apply j).neg)
        exact hin.indep_shift.comp measurable_id hm }
  set lam := volume.restrict (Icc (0 : ℝ) 1) with hlam
  have hUm : AEMeasurable U P := hin.uniform.aemeasurable
  have hξm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hin.measurable
  have hξ'm : Measurable (fun ω j => ξ' j ω) := measurable_pi_lambda _ hin'.measurable
  have hVm : Measurable (fun ω i => V i ω) := measurable_pi_lambda _ hV.measurable
  set μ := P.map (fun ω j => ξ j ω) with hμdef
  set μm := P.map (fun ω j => ξ' j ω) with hμmdef
  set ν := P.map (fun ω i => V i ω) with hνdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hξm.aemeasurable
  haveI : IsProbabilityMeasure μm := Measure.isProbabilityMeasure_map hξ'm.aemeasurable
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hVm.aemeasurable
  set X : Ω → (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) := fun ω => ((U ω, fun j => ξ j ω), fun i => V i ω)
    with hX
  set Y : Ω → (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) := fun ω => ((U ω, fun j => ξ' j ω), fun i => V i ω)
    with hY
  have hpairm : AEMeasurable (fun ω => (U ω, fun j => ξ j ω)) P := hUm.prodMk hξm.aemeasurable
  have hpair'm : AEMeasurable (fun ω => (U ω, fun j => ξ' j ω)) P := hUm.prodMk hξ'm.aemeasurable
  have hXm : AEMeasurable X P := hpairm.prodMk hVm.aemeasurable
  have hYm : AEMeasurable Y P := hpair'm.prodMk hVm.aemeasurable
  -- laws of the inputs
  have hX_law : P.map X = (lam.prod μ).prod ν := by
    have hind : IndepFun (fun ω => (U ω, fun j => ξ j ω)) (fun ω i => V i ω) P :=
      hV.indep_input.symm
    rw [hX, (indepFun_iff_map_prod_eq_prod_map_map hpairm hVm.aemeasurable).mp hind,
      (indepFun_iff_map_prod_eq_prod_map_map hUm hξm.aemeasurable).mp hin.indep_shift,
      hin.uniform.map_eq]
  have hY_law : P.map Y = (lam.prod μm).prod ν := by
    have hneg : Measurable (fun p : ℝ × (ℤ → ℝ) => (p.1, fun j => -p.2 j)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ (fun j =>
        ((measurable_pi_apply j).comp measurable_snd).neg))
    have hind : IndepFun (fun ω => (U ω, fun j => ξ' j ω)) (fun ω i => V i ω) P :=
      hV.indep_input.symm.comp hneg measurable_id
    rw [hY, (indepFun_iff_map_prod_eq_prod_map_map hpair'm hVm.aemeasurable).mp hind,
      (indepFun_iff_map_prod_eq_prod_map_map hUm hξ'm.aemeasurable).mp hin'.indep_shift,
      hin.uniform.map_eq]
  -- invariances
  have hμ : ∀ K : ℤ, μ.map (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) = μm := by
    intro K
    have hsh : Measurable (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) :=
      measurable_pi_lambda _ (fun m => (measurable_pi_apply (K - m)).neg)
    rw [hμdef, Measure.map_map hsh hξm]
    have hbij : Function.Injective (fun m : ℤ => K - m) := sub_right_injective
    have hiind : iIndepFun (fun m => ξ' (K - m)) P := hin'.indep.precomp hbij
    have e : (fun (x : ℤ → ℝ) (m : ℤ) => -x (K - m)) ∘ (fun ω j => ξ j ω) =
        fun ω m => ξ' (K - m) ω := rfl
    rw [e, hiind.map_fun_eq_infinitePi_map (fun m => hin'.measurable _), hμmdef,
      hin'.indep.map_fun_eq_infinitePi_map hin'.measurable]
    congr 1
    funext m
    rw [(hin'.identDistrib (K - m)).map_eq, (hin'.identDistrib m).map_eq]
  have hν : ∀ n : ℕ, ν.map (SQR_rev n) = ν := by
    intro n
    have hrevm : Measurable (SQR_rev n) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (SQR_sig n i))
    rw [hνdef, Measure.map_map hrevm hVm]
    have hiind : iIndepFun (fun i => V (SQR_sig n i)) P :=
      hV.indep.precomp (SQR_sig_invol n).injective
    have e : SQR_rev n ∘ (fun ω i => V i ω) = fun ω i => V (SQR_sig n i) ω := rfl
    rw [e, hiind.map_fun_eq_infinitePi_map (fun i => hV.measurable _),
      hV.indep.map_fun_eq_infinitePi_map hV.measurable]
    congr 1
    funext i
    rw [(hV.identDistrib (SQR_sig n i)).map_eq, (hV.identDistrib i).map_eq]
  -- the transformed input has the law of `Y`
  have hΨX : IdentDistrib (SQR_Psi h t ∘ X) Y P P := by
    refine ⟨(SQR_Psi_meas h t).comp_aemeasurable hXm, hYm, ?_⟩
    rw [← AEMeasurable.map_map_of_aemeasurable (SQR_Psi_meas h t).aemeasurable hXm, hX_law,
      SQR_Psi_law h t μ μm ν hμ hν, hY_law]
  -- the bad set is null
  have hbad : (P.map Y) {z : (ℝ × (ℤ → ℝ)) × (ℕ → ℝ) |
      ¬ {m : ℤ | (m : ℝ) * h + h * z.1.1 + z.1.2 m ∈ Ioc 0 t}.Finite} = 0 := by
    rw [Measure.map_apply_of_aemeasurable hYm (SQR_bad_meas h t)]
    have hfin := count_decomposition P h hh ξ' U hin' t ht
    have hgood : ∀ᵐ ω ∂P, {m : ℤ | (m : ℝ) * h + h * (Y ω).1.1 + (Y ω).1.2 m ∈ Ioc 0 t}.Finite := by
      filter_upwards [hfin] with ω hω
      exact hω.2.2.2.2.1
    rw [ae_iff] at hgood
    exact measure_mono_null (fun ω hω => hω) hgood
  have hΦ : AEMeasurable (SQR_Phi h t) (P.map Y) := by
    refine (SQR_Phi2_meas h t).aemeasurable.congr ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun z hz => ?_) hbad
    simp only [mem_setOf_eq] at hz ⊢
    intro hf
    exact hz (SQR_Phi_eq h t ht z hf).symm
  have hmain : IdentDistrib (SQR_Phi h t ∘ (SQR_Psi h t ∘ X)) (SQR_Phi h t ∘ Y) P P :=
    hΨX.comp_of_aemeasurable (by rw [hΨX.map_eq]; exact hΦ)
  -- pathwise identity
  have hfinX := count_decomposition P h hh ξ U hin t ht
  have hN : ∀ c : ℝ, ∀ᵐ ω ∂P, ∀ j : ℤ, (j : ℝ) * h + h * U ω + ξ j ω ≠ c := by
    intro c
    rw [ae_all_iff]; intro j
    filter_upwards [SQRD_ae_arr P h hh ξ U hin j ((j : ℝ) * h) c] with ω hω
    rw [mul_comm h (U ω)]; exact hω
  have hW : workload h ξ U V t =ᵐ[P] SQR_Phi h t ∘ (SQR_Psi h t ∘ X) := by
    filter_upwards [hfinX, hN 0, hN t] with ω hF hN0 hNt
    exact SQR_path h t hh ht (U ω, fun j => ξ j ω) (fun i => V i ω) hF.2.2.2.2.1 hN0 hNt
  have hWm : AEMeasurable (workload h ξ U V t) P :=
    hmain.aemeasurable_fst.congr hW.symm
  exact (IdentDistrib.of_ae_eq hWm hW).trans hmain
