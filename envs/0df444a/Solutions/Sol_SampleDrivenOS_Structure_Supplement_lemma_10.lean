-- Prove2me | solution 1 for SampleDrivenOS.Structure.Supplement.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:47.436836+00:00
-- url     : https://prove2.me/submissions/ee0c8019-3f13-4cf9-8c8a-312eb9906095

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

open SampleDrivenOS
open SampleDrivenOS.Structure
open SampleDrivenOS.Structure.Supplement

theorem solution (p : ℝ) (hp : 0 ≤ p ∧ p < 1) (t : ℕ → ℝ)
    (ht : IsThresholds p t) (N : ℕ) (hN : 1 ≤ N) :
    thresholdRatio (N + 1) p t ≤ thresholdRatio N p t := by
      classical
      -- generic measurability by factoring through finitely many measurable sets
      have hfac : ∀ (n : ℕ) (ι : Type) [Fintype ι] (S : ι → Set (Fin n → ℝ)),
          (∀ i, MeasurableSet (S i)) → ∀ g : (Fin n → ℝ) → ℝ,
          (∀ u v, (∀ i, (u ∈ S i ↔ v ∈ S i)) → g u = g v) → Measurable g := by
        intro n ι _ S hS g hg
        let vec : (Fin n → ℝ) → (ι → Bool) := fun u i => decide (u ∈ S i)
        have hvec : Measurable vec := by
          refine measurable_pi_iff.mpr fun i => measurable_to_bool ?_
          have : (fun u => vec u i) ⁻¹' {true} = S i := by ext u; simp [vec]
          rw [this]; exact hS i
        let G : (ι → Bool) → ℝ := fun v => if h : ∃ u, vec u = v then g h.choose else 0
        have hgG : g = G ∘ vec := by
          funext u
          have h : ∃ u', vec u' = vec u := ⟨u, rfl⟩
          simp only [Function.comp, G, dif_pos h]
          symm; apply hg; intro i
          have := congrFun h.choose_spec i
          simpa [vec] using this
        rw [hgG]; exact (measurable_of_countable G).comp hvec
      -- characterization of firstItem
      have hfi : ∀ (n : ℕ) (A : Finset (Fin n)) (u : Fin n → ℝ) (c : Fin n),
          firstItem A u = some c ↔
            (c ∈ A ∧ (∀ b ∈ A, u c ≤ u b) ∧ (∀ b ∈ A, u b ≤ u c → c ≤ b)) := by
        intro n A u c
        unfold firstItem
        simp only
        split_ifs with h
        · rw [Option.some_inj]
          constructor
          · rintro rfl
            have hm := Finset.min'_mem _ h
            rw [Finset.mem_filter] at hm
            refine ⟨hm.1, hm.2, fun b hb hbc => Finset.min'_le _ _ ?_⟩
            rw [Finset.mem_filter]
            exact ⟨hb, fun b' hb' => le_trans hbc (hm.2 b' hb')⟩
          · rintro ⟨hcA, hcmin, hcle⟩
            have hcB : c ∈ A.filter (fun a => ∀ b ∈ A, u a ≤ u b) := by
              rw [Finset.mem_filter]; exact ⟨hcA, hcmin⟩
            have hm := Finset.min'_mem _ h
            rw [Finset.mem_filter] at hm
            apply le_antisymm (Finset.min'_le _ _ hcB)
            exact hcle _ hm.1 (hm.2 c hcA)
        · simp only [false_iff]
          rintro ⟨hcA, hcmin, -⟩
          exact h ⟨c, by rw [Finset.mem_filter]; exact ⟨hcA, hcmin⟩⟩
      have hmax : ∀ (s s' : Finset ℝ) (hs : s.Nonempty) (hs' : s'.Nonempty), s = s' →
          s.max' hs = s'.max' hs' := by
        rintro s s' hs hs' rfl; rfl
      -- rank of a castSucc item ignores the last item
      have hrank : ∀ (u' : Fin (N+1) → ℝ) (a : Fin N),
          clockRank u' a.castSucc = clockRank (fun i => u' i.castSucc) a := by
        intro u' a
        unfold clockRank
        congr 1
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
        simp [Fin.castSucc_lt_castSucc_iff, not_lt.mpr (Fin.le_last a.castSucc)]
      have hrankb : ∀ (n : ℕ) (u : Fin n → ℝ) (a : Fin n), clockRank u a < n + 2 := by
        intro n u a
        unfold clockRank
        have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun b : Fin n => b < a ∧ u b ≤ u a)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      -- invariance of the choice under comparison data
      have hinv : ∀ (u v : Fin N → ℝ), (∀ a b, (u a ≤ u b ↔ v a ≤ v b)) →
          (∀ a, (p ≤ u a ↔ p ≤ v a)) → (∀ a (k : Fin (N+2)), (t k ≤ u a ↔ t k ≤ v a)) →
          thresholdChoice N p t u = thresholdChoice N p t v := by
        intro u v h1 h2 h3
        have hr : ∀ a, clockRank u a = clockRank v a := by
          intro a; unfold clockRank; congr 1; congr 1
          apply Finset.filter_congr; intro b _; rw [h1]
        have hA : Finset.univ.filter (fun a => p ≤ u a ∧ t (clockRank u a) ≤ u a)
            = Finset.univ.filter (fun a => p ≤ v a ∧ t (clockRank v a) ≤ v a) := by
          apply Finset.filter_congr; intro a _
          rw [hr a, h2 a]
          have := h3 a ⟨clockRank v a, hrankb N v a⟩
          simp only at this
          rw [this]
        unfold thresholdChoice
        rw [hA]
        apply Option.ext; intro c
        rw [hfi, hfi]
        simp only [h1]
      have hoinv : ∀ (n : ℕ) (w : Fin n → ℝ) (u v : Fin n → ℝ), (∀ a, (p ≤ u a ↔ p ≤ v a)) →
          clockOffline p w u = clockOffline p w v := by
        intro n w u v h2
        unfold clockOffline
        apply hmax
        congr 2
        apply Finset.filter_congr; intro a _; exact h2 a
      have hmeasO : ∀ (n : ℕ) (w : Fin n → ℝ), Measurable (clockOffline p w) := by
        intro n w
        refine hfac n (Fin n) (fun a => {u | p ≤ u a}) ?_ _ ?_
        · intro a; exact measurableSet_le measurable_const (measurable_pi_apply a)
        · intro u v h; exact hoinv n w u v (fun a => h a)
      have hmeasR : ∀ (w : Fin N → ℝ), Measurable (fun u => (thresholdChoice N p t u).elim 0 w) := by
        intro w
        refine hfac N ((Fin N × Fin N) ⊕ (Fin N ⊕ (Fin N × Fin (N+2))))
          (Sum.elim (fun ab : Fin N × Fin N => {u : Fin N → ℝ | u ab.1 ≤ u ab.2})
            (Sum.elim (fun a : Fin N => {u : Fin N → ℝ | p ≤ u a})
              (fun ak : Fin N × Fin (N+2) => {u : Fin N → ℝ | t ak.2 ≤ u ak.1}))) ?_ _ ?_
        · rintro ((⟨a, b⟩) | a | (⟨a, k⟩))
          · exact measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b)
          · exact measurableSet_le measurable_const (measurable_pi_apply a)
          · exact measurableSet_le measurable_const (measurable_pi_apply a)
        · intro u v h
          rw [hinv u v (fun a b => h (Sum.inl (a, b))) (fun a => h (Sum.inr (Sum.inl a)))
            (fun a k => h (Sum.inr (Sum.inr (a, k))))]
      -- measure facts
      have hν : MeasureTheory.IsProbabilityMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) :=
        ⟨by simp⟩
      have hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (arrivalLaw n) := by
        intro n; unfold arrivalLaw; infer_instance
      have hπ : MeasureTheory.MeasurePreserving (fun (u : Fin (N+1) → ℝ) (i : Fin N) => u i.castSucc)
          (arrivalLaw (N+1)) (arrivalLaw N) := by
        have h1 := MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (N+1) => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
            (Set.Icc (0:ℝ) 1)) (Fin.last N)
        have h2 := (MeasureTheory.measurePreserving_snd
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0:ℝ) 1))
          (ν := MeasureTheory.Measure.pi (fun _ : Fin N =>
            (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0:ℝ) 1)))).comp h1
        unfold arrivalLaw
        convert h2 using 1
        funext u i
        simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init]
      have hproj : ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
          ∫ u, F (fun i => u i.castSucc) ∂(arrivalLaw (N+1)) = ∫ u, F u ∂(arrivalLaw N) := by
        intro F hF
        rw [← hπ.map_eq, MeasureTheory.integral_map hπ.measurable.aemeasurable
          hF.aestronglyMeasurable]
      have hOb : ∀ (n : ℕ) (w : Fin n → ℝ) (u : Fin n → ℝ),
          |clockOffline p w u| ≤ ∑ a, |w a| := by
        intro n w u
        unfold clockOffline
        have hm := Finset.max'_mem (insert 0 ((Finset.univ.filter (fun a => p ≤ u a)).image w))
          (by simp)
        rw [Finset.mem_insert, Finset.mem_image] at hm
        rcases hm with h | ⟨a, -, h⟩
        · rw [h]; simp only [abs_zero]; exact Finset.sum_nonneg (fun a _ => abs_nonneg _)
        · rw [← h]
          exact Finset.single_le_sum (f := fun a => |w a|) (fun a _ => abs_nonneg _)
            (Finset.mem_univ a)
      have hOge : ∀ (n : ℕ) (w : Fin n → ℝ) (u : Fin n → ℝ) (a : Fin n), p ≤ u a →
          w a ≤ clockOffline p w u := by
        intro n w u a ha
        unfold clockOffline
        apply Finset.le_max'
        rw [Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨a, by simp [ha], rfl⟩
      have hO0 : ∀ (n : ℕ) (w : Fin n → ℝ) (u : Fin n → ℝ), 0 ≤ clockOffline p w u := by
        intro n w u
        unfold clockOffline
        apply Finset.le_max'
        exact Finset.mem_insert_self _ _
      have hRb : ∀ (n : ℕ) (w : Fin n → ℝ) (u : Fin n → ℝ),
          |(thresholdChoice n p t u).elim 0 w| ≤ ∑ a, |w a| := by
        intro n w u
        cases thresholdChoice n p t u with
        | none => simp only [Option.elim_none, abs_zero]; exact Finset.sum_nonneg (fun a _ => abs_nonneg _)
        | some a =>
          simp only [Option.elim_some]
          exact Finset.single_le_sum (f := fun a => |w a|) (fun a _ => abs_nonneg _)
            (Finset.mem_univ a)
      have hR0 : ∀ (n : ℕ) (w : Fin n → ℝ), IsWeights w → ∀ u,
          0 ≤ (thresholdChoice n p t u).elim 0 w := by
        intro n w hw u
        cases thresholdChoice n p t u with
        | none => simp
        | some a => simpa using hw.1 a
      have hRnn : ∀ (n : ℕ) (w : Fin n → ℝ), IsWeights w → 0 ≤ thresholdReward n p t w := by
        intro n w hw
        unfold thresholdReward
        exact MeasureTheory.integral_nonneg (fun u => hR0 n w hw u)
      -- positivity of the offline mean for the all-ones instance
      have hpos1 : 0 < clockOfflineMean p (fun _ : Fin N => (1:ℝ)) := by
        unfold clockOfflineMean
        let i0 : Fin N := ⟨0, hN⟩
        have hset : MeasurableSet {u : Fin N → ℝ | p ≤ u i0} :=
          measurableSet_le measurable_const (measurable_pi_apply i0)
        have hmeas : (arrivalLaw N).real {u : Fin N → ℝ | p ≤ u i0} = 1 - p := by
          have hpre : {u : Fin N → ℝ | p ≤ u i0} = Function.eval i0 ⁻¹' Set.Ici p := by
            ext u; simp
          rw [MeasureTheory.Measure.real, hpre]
          unfold arrivalLaw
          rw [(MeasureTheory.measurePreserving_eval _ i0).measure_preimage
            measurableSet_Ici.nullMeasurableSet]
          rw [MeasureTheory.Measure.restrict_apply measurableSet_Ici]
          have : Set.Ici p ∩ Set.Icc (0:ℝ) 1 = Set.Icc p 1 := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h3⟩; exact ⟨h1, le_trans hp.1 h1, h3⟩
          rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hp.2])]
        have hint : MeasureTheory.Integrable (clockOffline p (fun _ : Fin N => (1:ℝ)))
            (arrivalLaw N) :=
          MeasureTheory.Integrable.of_bound (hmeasO N _).aestronglyMeasurable _
            (Filter.Eventually.of_forall (fun u => by
              rw [Real.norm_eq_abs]; exact hOb N _ u))
        calc (0:ℝ) < 1 - p := by linarith [hp.2]
          _ = ∫ u, {u : Fin N → ℝ | p ≤ u i0}.indicator 1 u ∂(arrivalLaw N) := by
            rw [MeasureTheory.integral_indicator_one hset, hmeas]
          _ ≤ _ := by
            apply MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun u => Set.indicator_nonneg (fun _ _ => zero_le_one) u))
              hint
            refine Filter.Eventually.of_forall (fun u => ?_)
            dsimp only
            by_cases hu : p ≤ u i0
            · rw [Set.indicator_of_mem (by exact hu)]
              exact hOge N (fun _ => (1:ℝ)) u i0 hu
            · rw [Set.indicator_of_notMem (by exact hu)]
              exact hO0 N _ u
      unfold thresholdRatio
      apply le_csInf
      · exact ⟨_, fun _ => 1, ⟨fun _ => zero_le_one, fun _ _ _ => le_refl _⟩, hpos1, rfl⟩
      rintro r ⟨w, hw, hpos, rfl⟩
      let w' : Fin (N+1) → ℝ := fun i => if h : (i:ℕ) < N then w ⟨i, h⟩ else 0
      have hw'c : ∀ a : Fin N, w' a.castSucc = w a := by
        intro a; simp [w', a.isLt]
      have hw'l : w' (Fin.last N) = 0 := by simp [w']
      have hw' : IsWeights w' := by
        constructor
        · intro j; simp only [w']; split_ifs
          · exact hw.1 _
          · exact le_refl _
        · intro i j hij
          simp only [w']
          by_cases hj : (j:ℕ) < N
          · have hi : (i:ℕ) < N := lt_of_le_of_lt hij hj
            rw [dif_pos hj, dif_pos hi]
            exact hw.2 (show (⟨i, hi⟩ : Fin N) ≤ ⟨j, hj⟩ from hij)
          · rw [dif_neg hj]; split_ifs
            · exact hw.1 _
            · exact le_refl _
      have hA : clockOfflineMean p w' = clockOfflineMean p w := by
        unfold clockOfflineMean
        rw [← hproj _ (hmeasO N w)]
        congr 1; funext u
        unfold clockOffline
        apply hmax
        ext x
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Fin.exists_fin_succ', hw'c, hw'l]
        constructor
        · rintro (h | (⟨a, ha⟩ | ⟨-, h⟩))
          · exact Or.inl h
          · exact Or.inr ⟨a, ha⟩
          · exact Or.inl h.symm
        · rintro (h | ⟨a, ha⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨a, ha⟩)
      have hB : thresholdReward (N+1) p t w' ≤ thresholdReward N p t w := by
        unfold thresholdReward
        rw [← hproj _ (hmeasR w)]
        apply MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun u => hR0 (N+1) w' hw' u))
        · exact MeasureTheory.Integrable.of_bound
            ((hmeasR w).comp hπ.measurable).aestronglyMeasurable _
            (Filter.Eventually.of_forall (fun u => by
              rw [Real.norm_eq_abs]; exact hRb N w _))
        refine Filter.Eventually.of_forall (fun u' => ?_)
        have hnn := hR0 N w hw (fun i => u' i.castSucc)
        dsimp only
        rcases hc : thresholdChoice (N+1) p t u' with _ | c
        · simpa using hnn
        · induction c using Fin.lastCases with
          | last => simpa [hw'l] using hnn
          | cast c0 =>
            have hc0 : thresholdChoice N p t (fun i => u' i.castSucc) = some c0 := by
              unfold thresholdChoice at hc ⊢
              rw [hfi] at hc ⊢
              obtain ⟨hmem, hmin, hle⟩ := hc
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem hmin hle ⊢
              rw [hrank] at hmem
              refine ⟨hmem, ?_, ?_⟩
              · intro b hb
                exact hmin b.castSucc (by rw [hrank]; exact hb)
              · intro b hb hbc
                exact Fin.castSucc_le_castSucc_iff.mp (hle b.castSucc (by rw [hrank]; exact hb) hbc)
            simp only [hc0, Option.elim_some, hw'c]
            exact le_refl _
      have hbdd : BddBelow {r : ℝ | ∃ w : Fin (N+1) → ℝ, IsWeights w ∧ 0 < clockOfflineMean p w ∧
          r = thresholdReward (N+1) p t w / clockOfflineMean p w} := by
        refine ⟨0, ?_⟩
        rintro r ⟨v, hv, hvpos, rfl⟩
        exact div_nonneg (hRnn _ v hv) hvpos.le
      calc sInf _ ≤ thresholdReward (N+1) p t w' / clockOfflineMean p w' :=
            csInf_le hbdd ⟨w', hw', hA ▸ hpos, rfl⟩
        _ ≤ _ := by
          rw [hA]; exact div_le_div_of_nonneg_right hB hpos.le
