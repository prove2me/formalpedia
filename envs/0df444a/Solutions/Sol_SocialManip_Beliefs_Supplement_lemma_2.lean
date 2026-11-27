-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:05.430799+00:00
-- url     : https://prove2.me/submissions/5a03dfe2-17ae-4e57-8f0f-ddf665603dab

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game
import Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA

open MeasureTheory

open SocialManip
open SocialManip.Beliefs
open SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- Refutation of the contemporaneous reconstruction in printed Lemma 2(b). Bayesian 0 sees
DeGroot 1, who sees DeGroot 2 only through the lagged social update. Before the first exchange,
agent 2's private news cannot enter agent 0's observations. Failure occurs on an open set of
positive DeGroot rows, so no Lebesgue-null generic exception can remove it. -/
theorem solution :
    ∀ Z : Set ({i : Fin 3 // i ∉ ({0} : Finset (Fin 3))} → Fin 3 → ℝ), volume Z = 0 →
      ∃ M : AModel 3, M.Standing ∧ M.Assumption2 ∧ M.B = {0} ∧ M.N 0 = {1} ∧
        M.Δ = 1 ∧ M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧
        M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧ (∀ i, M.lam i = 1) ∧
        (∀ i, M.p i = 4 / 5) ∧ (∀ i ∉ M.B, ∀ j, 0 < M.α i j) ∧
        degrootRows ({0} : Finset (Fin 3)) M.α ∉ Z ∧
        let σP : APrincipalStrategy 3 := fun _ => Measure.dirac (truthfulAction 3)
        ∃ R : AReporting 3, AValidReporting M (1 / 2) σP R ∧
          ¬ ∃ g : LocalHistory 3 (1 / 2) → ℝ,
            Measurable g ∧ ∀ᵐ z ∂(trueLaw M State.S false (truthfulAction 3)),
              beliefA M R (1 / 2) 2 z =
                g (obsWith M R (1 / 2) 0 z) := by
                  -- (K1) measurability of received counts, for any model
                  have hcountMeas : ∀ (M : AModel 3) (i : Fin 3) (t : ℝ) (s : State),
                      Measurable (fun z : Full 3 => countA M z i t s) := by
                    intro M i t s
                    have hnc : ∀ (P : ℕ → Full 3 → Prop), (∀ k, MeasurableSet {z | P k z}) →
                        Measurable (fun z => {k | P k z}.ncard) := by
                      intro P hP
                      have hF : ∀ F : Finset ℕ, MeasurableSet {z | {k | P k z} = (↑F : Set ℕ)} := by
                        intro F
                        have : {z | {k | P k z} = (↑F : Set ℕ)} = ⋂ k, {z | P k z ↔ k ∈ F} := by
                          ext z; simp [Set.ext_iff]
                        rw [this]
                        refine MeasurableSet.iInter fun k => ?_
                        by_cases hk : k ∈ F
                        · simpa [hk] using hP k
                        · convert (hP k).compl using 1
                          ext z; simp [hk]
                      refine measurable_to_countable' fun m => ?_
                      have : (fun z => {k | P k z}.ncard) ⁻¹' {m} =
                          (⋃ F : Finset ℕ, ⋃ (_ : F.card = m), {z | {k | P k z} = (↑F : Set ℕ)}) ∪
                          (if m = 0 then (⋃ F : Finset ℕ, {z | {k | P k z} = (↑F : Set ℕ)})ᶜ else ∅) := by
                        ext z
                        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
                          Set.mem_setOf_eq, exists_prop]
                        constructor
                        · intro h
                          by_cases hfin : {k | P k z}.Finite
                          · left
                            refine ⟨hfin.toFinset, ?_, by simp⟩
                            rw [← h, Set.ncard_eq_toFinset_card _ hfin]
                          · right
                            have hm : m = 0 := by rw [← h]; exact Set.Infinite.ncard hfin
                            subst hm
                            simp only [if_true, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
                            intro F hF
                            exact hfin (hF ▸ F.finite_toSet)
                        · rintro (⟨F, hFm, hFz⟩ | h)
                          · rw [hFz, Set.ncard_coe_finset, hFm]
                          · by_cases hm : m = 0
                            · subst hm
                              simp only [if_true, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq,
                                not_exists] at h
                              have hinf : ¬ {k | P k z}.Finite := by
                                intro hfin
                                exact h hfin.toFinset (by simp)
                              exact Set.Infinite.ncard hinf
                            · simp [hm] at h
                      rw [this]
                      refine MeasurableSet.union (MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => hF F) ?_
                      split_ifs
                      · exact (MeasurableSet.iUnion fun F => hF F).compl
                      · exact MeasurableSet.empty
                    have hsig : ∀ k, Measurable (fun z : Full 3 => orgSignal M z i k) := by
                      intro k
                      unfold orgSignal
                      refine Measurable.ite ?_ measurable_const measurable_const
                      refine measurableSet_lt ?_ ?_
                      · exact measurable_subtype_coe.comp ((measurable_pi_apply (i, k)).comp
                          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
                      · exact (measurable_of_countable (fun y : State => organicProbS (M.p i) y)).comp
                          (measurable_fst.comp measurable_fst)
                    have harr : ∀ k, Measurable (fun z : Full 3 => orgArrival z i k) := by
                      intro k
                      unfold orgArrival
                      refine Measurable.div ?_ ?_
                      · exact Finset.measurable_sum _ fun l _ => (measurable_pi_apply (i, l)).comp
                          (measurable_fst.comp measurable_snd)
                      · exact (measurable_pi_apply i).comp
                          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
                    have hparr : ∀ k, Measurable (fun z : Full 3 => prinArrival z i k) := by
                      intro k
                      unfold prinArrival
                      refine Measurable.div ?_ ?_
                      · exact Finset.measurable_sum _ fun l _ => (measurable_pi_apply (i, l)).comp
                          (measurable_fst.comp (measurable_snd.comp measurable_snd))
                      · exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp
                          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
                    unfold countA
                    refine Measurable.add ?_ ?_
                    · refine hnc _ fun k => ?_
                      exact (measurableSet_le (harr k) measurable_const).inter
                        ((hsig k) (measurableSet_singleton s))
                    · refine Measurable.ite ?_ (hnc _ fun k => measurableSet_le (hparr k) measurable_const)
                        measurable_const
                      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
                      · exact measurableSet_eq_fun (by fun_prop) measurable_const
                      · exact measurableSet_lt measurable_const ((measurable_pi_apply i).comp
                          (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
                          (measurable_snd.comp (measurable_snd.comp measurable_fst))))))
                      · exact measurableSet_eq_fun (by fun_prop) measurable_const
                  -- the main construction, for any model satisfying the listed equations
                  have key : ∀ M : AModel 3, M.B = {0} → M.N 0 = {1} → M.Δ = 1 → M.q = 1 / 2 →
                      M.μ0 = 1 / 2 → (∀ i, M.lam i = 1) → (∀ i, M.p i = 4 / 5) → 0 < M.θ 2 →
                      IsProbabilityMeasure (M.ν 0) → M.ν 0 {r | ∀ j, 9 / 10 < r j}ᶜ = 0 →
                      let σP : APrincipalStrategy 3 := fun _ => Measure.dirac (truthfulAction 3)
                      ∃ R : AReporting 3, AValidReporting M (1 / 2) σP R ∧
                        ¬ ∃ g : LocalHistory 3 (1 / 2) → ℝ,
                          Measurable g ∧ ∀ᵐ z ∂(trueLaw M State.S false (truthfulAction 3)),
                            beliefA M R (1 / 2) 2 z = g (obsWith M R (1 / 2) 0 z) := by
                    intro M hB hN hΔ hq hμ hlam hp hθ2 hνP hνS σP
                    -- DeGroot report from a received count, at time s
                    let HdP : ℕ × ℕ → ℝ → Fin 3 → ℝ := fun c s i =>
                      if s = 0 then 1 / 2 else M.θ i * (1 - BUS (M.p i) M.q c.1 c.2) + (∑ j, M.α i j) * (1 / 2)
                    let loc : RawPath 3 → (t : ℝ) → LocalHistory 3 t := fun h t =>
                      (fun s => h s 0, fun s j => if j = 1 then HdP (h s 1) s 1 else 0)
                    let O : (t : ℝ) → Full 3 → LocalHistory 3 t := fun t z => loc (receivedPath M z) t
                    let Q : Measure (Full 3) := subjLaw M σP 0
                    have hOm : ∀ t, Measurable (O t) := by
                      intro t
                      have hrp : ∀ (s : ℝ) (j : Fin 3), Measurable (fun z : Full 3 => receivedPath M z s j) :=
                        fun s j => (hcountMeas M j s State.S).prodMk (hcountMeas M j s State.R)
                      refine Measurable.prodMk ?_ ?_
                      · exact measurable_pi_lambda _ fun s => hrp s 0
                      · refine measurable_pi_lambda _ fun s => measurable_pi_lambda _ fun j => ?_
                        by_cases hj : j = 1
                        · simp only [hj, if_true]
                          exact (measurable_of_countable (fun c : ℕ × ℕ => HdP c s 1)).comp (hrp s 1)
                        · simp only [hj, if_false]
                          exact measurable_const
                    have hfac : ∀ t : ℝ, ∃ G : LocalHistory 3 t → ℝ, Measurable G ∧
                        Q[indR | MeasurableSpace.comap (O t) inferInstance] = G ∘ O t := by
                      intro t
                      exact (stronglyMeasurable_condExp (μ := Q) (f := (indR : Full 3 → ℝ))
                        (m := MeasurableSpace.comap (O t) inferInstance)).measurable.exists_eq_measurable_comp
                    choose G hGm hGeq using hfac
                    let realize : RawPath 3 → ReportPath 3 := fun h t i =>
                      if t = 0 then 1 / 2 else if i = 0 then ((clampProb (G t (loc h t)) : ℝ)) else HdP (h t i) t i
                    let R : AReporting 3 := ⟨fun t _ ℓ => clampProb (G t ℓ), fun _ _ _ => clampProb (1 / 2), realize⟩
                    have hreal1 : ∀ h s, realize h s 1 = HdP (h s 1) s 1 := by
                      intro h s
                      by_cases hs : s = 0
                      · simp [realize, HdP, hs]
                      · simp [realize, hs]
                    have hlocEq : ∀ (h : RawPath 3) (H : ReportPath 3) t,
                        (∀ s ∈ Set.Icc (0 : ℝ) t, H s 1 = HdP (h s 1) s 1) →
                        localHistory M.N h H t 0 = loc h t := by
                      intro h H t hH
                      simp only [localHistory, loc, hN, Finset.mem_singleton]
                      refine Prod.ext rfl ?_
                      funext s j
                      by_cases hj : j = 1
                      · subst hj; simp only [if_true]; exact hH s s.2
                      · simp [hj]
                    have hloc : ∀ h t, localHistory M.N h (realize h) t 0 = loc h t :=
                      fun h t => hlocEq h (realize h) t (fun s _ => hreal1 h s)
                    have hobs : ∀ t, obsWith M R t 0 = O t := by
                      intro t; funext z
                      exact hloc (receivedPath M z) t
                    have hbel0 : ∀ t z, beliefA M R t 0 z = if t = 0 then 1 / 2 else (clampProb (G t (O t z)) : ℝ) := by
                      intro t z
                      by_cases ht : t = 0
                      · simp [beliefA, R, realize, ht]
                      · simp [beliefA, R, realize, ht, O]
                    have hbel2 : ∀ z, beliefA M R (1 / 2) 2 z = HdP (receivedPath M z (1 / 2) 2) (1 / 2) 2 := by
                      intro z
                      simp [beliefA, R, realize, HdP]
                    have hgrid : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → (((⌈t / M.Δ⌉₊ - 1 : ℕ) : ℝ) * M.Δ) = 0 := by
                      intro t h0 h1
                      have : ⌈t / M.Δ⌉₊ = 1 := by
                        rw [hΔ, div_one, Nat.ceil_eq_iff (by norm_num)]
                        constructor
                        · simpa using h0
                        · push_cast; linarith
                      rw [this]; simp
                    have hcl : Measurable clampProb := by
                      unfold clampProb; exact continuous_projIcc.measurable
                    refine ⟨R, ⟨?_, ?_⟩, ?_⟩
                    · -- (K2) operational
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · intro t _ i
                        exact ⟨hcl.comp (hGm t), measurable_const⟩
                      · intro h t ht i
                        show realize h t i = _
                        by_cases ht0 : t = 0
                        · simp [realize, ht0, priorOf, hq]; norm_num
                        have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
                        rw [if_neg ht0, hgrid t htpos ht.2]
                        by_cases hi : i = 0
                        · subst hi
                          rw [if_pos (by rw [hB]; simp)]
                          show realize h t 0 = (clampProb (G t (localHistory M.N h (realize h) t 0)) : ℝ)
                          rw [hloc]; simp [realize, ht0]
                        · rw [if_neg (by rw [hB]; simpa using hi)]
                          have hz : ∀ j, realize h 0 j = 1 / 2 := fun j => by simp [realize]
                          show _ = M.θ i * rawBU M h i t + ∑ j, M.α i j * realize h 0 j
                          simp only [hz, realize, ht0, hi, if_false, HdP, ← Finset.sum_mul]; rfl
                      · intro h H hH
                        have h0 : ∀ i, H 0 i = 1 / 2 := by
                          intro i
                          have := hH 0 ⟨le_refl _, by norm_num⟩ i
                          rw [this]; simp [priorOf, hq]; norm_num
                        have hdeg : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, i ≠ 0 → H t i = realize h t i := by
                          intro t ht i hi
                          by_cases ht0 : t = 0
                          · subst ht0; rw [h0]; simp [realize]
                          have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
                          rw [hH t ht i, if_neg ht0, if_neg (by rw [hB]; simpa using hi), hgrid t htpos ht.2]
                          simp only [h0, realize, ht0, hi, if_false, HdP]
                          rw [← Finset.sum_mul]; rfl
                        intro t ht i
                        by_cases hi : i = 0
                        · subst hi
                          by_cases ht0 : t = 0
                          · subst ht0; rw [h0]; simp [R, realize]
                          rw [hH t ht 0, if_neg ht0, if_pos (by rw [hB]; simp)]
                          show (clampProb (G t (localHistory M.N h H t 0)) : ℝ) = realize h t 0
                          rw [hlocEq h H t (fun s hs => by
                            rw [hdeg s ⟨hs.1, hs.2.trans ht.2⟩ 1 (by decide), hreal1])]
                          simp [realize, ht0]
                        · exact hdeg t ht i hi
                      · intro t _
                        let locP : (ρ : RawPrefix 3 t) → (s : Set.Icc (0 : ℝ) t) → LocalHistory 3 s := fun ρ s =>
                          (fun u => ρ ⟨u.1, u.2.1, u.2.2.trans s.2.2⟩ 0,
                           fun u j => if j = 1 then HdP (ρ ⟨u.1, u.2.1, u.2.2.trans s.2.2⟩ 1) u 1 else 0)
                        let f : RawPrefix 3 t → ReportPrefix 3 t := fun ρ s i =>
                          if (s : ℝ) = 0 then 1 / 2 else if i = 0 then ((clampProb (G s (locP ρ s)) : ℝ))
                          else HdP (ρ s i) s i
                        refine ⟨f, ?_, fun h s i => rfl⟩
                        rw [measurable_pi_iff]; intro s; rw [measurable_pi_iff]; intro i
                        by_cases hs : (s : ℝ) = 0
                        · simp only [f, hs, if_true]; exact measurable_const
                        by_cases hi : i = 0
                        · simp only [f, hs, hi, if_false, if_true]
                          have hlm : Measurable (fun ρ : RawPrefix 3 t => locP ρ s) := by
                            refine Measurable.prodMk ?_ ?_
                            · exact measurable_pi_lambda _ fun u =>
                                (measurable_pi_apply 0).comp (measurable_pi_apply _)
                            · refine measurable_pi_lambda _ fun u => measurable_pi_lambda _ fun j => ?_
                              by_cases hj : j = 1
                              · simp only [hj, if_true]
                                exact (measurable_of_countable (fun c : ℕ × ℕ => HdP c u 1)).comp
                                  ((measurable_pi_apply 1).comp (measurable_pi_apply _))
                              · simp only [hj, if_false]; exact measurable_const
                          exact continuous_subtype_val.measurable.comp
                            (hcl.comp ((hGm s).comp hlm))
                        · simp only [f, hs, hi, if_false]
                          exact (measurable_of_countable (fun c : ℕ × ℕ => HdP c s i)).comp
                            ((measurable_pi_apply i).comp (measurable_pi_apply s))
                    · intro t ht i hi
                      rw [hB, Finset.mem_singleton] at hi
                      subst hi
                      refine ⟨?_, ?_⟩
                      · -- (K3/K4) state posterior
                        have hact : ∀ (y : State) (τ : Bool), (if τ then Measure.dirac (truthfulAction 3) else σP y)
                            = Measure.dirac (truthfulAction 3) := by
                          intro y τ; cases τ <;> rfl
                        have hw : ∀ (y : State) (τ : Bool),
                            ENNReal.ofReal (priorOf M.q y * (if τ then M.μ0 else 1 - M.μ0)) = ENNReal.ofReal (1 / 4) := by
                          intro y τ; congr 1; cases y <;> cases τ <;> simp [priorOf, hq, hμ] <;> norm_num
                        have hbaseP : IsProbabilityMeasure (baseMeasure 3) := by
                          unfold baseMeasure; infer_instance
                        have hunivS : (Finset.univ : Finset State) = {State.S, State.R} := rfl
                        set K : State → Bool → Measure (Params 3) := fun y τ => (Measure.dirac y).prod ((Measure.dirac τ).prod
                                ((Measure.dirac (truthfulAction 3)).prod (M.ν 0))) with hK
                        set mix : Measure (Params 3) := ∑ y : State, ∑ τ : Bool, ENNReal.ofReal (1 / 4) • K y τ with hmix
                        have hQeq : Q = mix.prod (baseMeasure 3) := by
                          show subjLaw M σP 0 = _
                          unfold subjLaw
                          simp only [hact, hw, hmix, hK]
                        have hterm : ∀ (y : State) (τ : Bool), IsProbabilityMeasure (K y τ) := by
                          intro y τ; simp only [hK]; infer_instance
                        have hmixapp : ∀ s, mix s = ENNReal.ofReal (1 / 4) * (K State.S true s + K State.S false s +
                            (K State.R true s + K State.R false s)) := by
                          intro s
                          simp only [hmix, Measure.finsetSum_apply, hunivS, Finset.sum_pair (show State.S ≠ State.R by decide),
                            Fintype.sum_bool, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
                          ring
                        have hmixP : IsProbabilityMeasure mix := by
                          constructor
                          rw [hmixapp]
                          simp only [measure_univ]
                          have h14 : ENNReal.ofReal (1 / 4) = 4⁻¹ := by
                            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
                          rw [h14, show (1 : ENNReal) + 1 + (1 + 1) = 4 by norm_num]
                          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
                        have hQP : IsProbabilityMeasure Q := by
                          rw [hQeq]; infer_instance
                        have hindRm : Measurable (indR : Full 3 → ℝ) := by
                          unfold indR
                          exact (Measurable.of_discrete (f := fun s : State => if s = State.R then (1:ℝ) else 0)).comp
                            (measurable_fst.fst)
                        have hindR01 : ∀ z : Full 3, 0 ≤ (indR z : ℝ) ∧ indR z ≤ 1 := by
                          intro z; unfold indR; split_ifs <;> norm_num
                        have hindRi : Integrable (indR : Full 3 → ℝ) Q :=
                          Integrable.of_bound hindRm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
                            rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hindR01 z])
                        set m := MeasurableSpace.comap (O t) (inferInstance : MeasurableSpace (LocalHistory 3 t)) with hm
                        have hle : m ≤ _ := (hOm t).comap_le
                        have hsig : infoSigma M R t 0 = m := by unfold infoSigma; rw [hobs]
                        have hcl : Measurable (fun r : ℝ => (clampProb r : ℝ)) :=
                          (continuous_subtype_val.comp continuous_projIcc).measurable
                        have hbm : Measurable[m] (beliefA M R t 0) := by
                          have : beliefA M R t 0 = fun z => if t = 0 then 1 / 2 else (clampProb (G t (O t z)) : ℝ) :=
                            funext (hbel0 t)
                          rw [this]
                          by_cases ht0 : t = 0
                          · simp only [ht0, if_true]; exact measurable_const
                          · simp only [ht0, if_false]
                            exact hcl.comp ((hGm t).comp (comap_measurable (O t)))
                        unfold IsHistoryPosterior
                        rw [hsig]
                        refine ⟨by rw [hobs]; exact hOm t, hbm, ?_, hindRi, ?_⟩
                        · refine Integrable.of_bound (hbm.mono hle le_rfl).aestronglyMeasurable 1 (ae_of_all _ fun z => ?_)
                          rw [hbel0]; split_ifs
                          · norm_num
                          · have := (clampProb (G t (O t z))).2
                            rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
                        · intro U hU
                          show ∫ z in U, beliefA M R t 0 z ∂Q = ∫ z in U, indR z ∂Q
                          by_cases ht0 : t = 0
                          · subst ht0
                            obtain ⟨V, hV, rfl⟩ := hU
                            clear hbm hsig hle hm m
                            have hexp : ∀ᵐ x ∂(ProbabilityTheory.expMeasure 1), 0 < x := by
                              have h := ProbabilityTheory.cdf_expMeasure_eq (r := 1) one_pos 0
                              rw [ProbabilityTheory.cdf_eq_real] at h
                              simp at h
                              rw [ae_iff]
                              have : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext; simp
                              rw [this]; exact (measureReal_eq_zero_iff).mp h
                            have hbase : ∀ᵐ ω ∂(baseMeasure 3), ∀ k, 0 < ω.1 k := by
                              unfold baseMeasure
                              exact Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr fun k =>
                                (measurePreserving_eval_infinitePi _ k).quasiMeasurePreserving.ae hexp)
                            have hKae : ∀ y τ, ∀ᵐ p ∂(K y τ), p.2.2.1 = truthfulAction 3 ∧ ∀ j, 9 / 10 < p.2.2.2 j := by
                              intro y τ
                              have hW : ∀ᵐ w ∂((Measure.dirac (truthfulAction 3)).prod (M.ν 0)),
                                  w.1 = truthfulAction 3 ∧ ∀ j, 9 / 10 < w.2 j := by
                                have h1 : ∀ᵐ w ∂((Measure.dirac (truthfulAction 3)).prod (M.ν 0)), w.1 = truthfulAction 3 :=
                                  Measure.quasiMeasurePreserving_fst.ae (by rw [ae_dirac_eq (α := AAction 3)]; exact (Filter.eventually_pure (a := truthfulAction 3) (p := fun x => x = truthfulAction 3)).mpr rfl)
                                have h2 : ∀ᵐ w ∂((Measure.dirac (truthfulAction 3)).prod (M.ν 0)), ∀ j, 9 / 10 < w.2 j :=
                                  Measure.quasiMeasurePreserving_snd.ae (by rw [ae_iff]; exact hνS)
                                filter_upwards [h1, h2] with w hw1 hw2 using ⟨hw1, hw2⟩
                              simp only [hK]
                              exact Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hW)
                            have hmixae : ∀ᵐ p ∂mix, p.2.2.1 = truthfulAction 3 ∧ ∀ j, 9 / 10 < p.2.2.2 j := by
                              rw [ae_iff, hmixapp]
                              simp only [ae_iff.mp (hKae _ _), add_zero, mul_zero]
                            have hcount : ∀ᵐ z ∂Q, ∀ st, countA M z 0 0 st = 0 := by
                              rw [hQeq]
                              filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmixae,
                                Measure.quasiMeasurePreserving_snd.ae hbase] with z hz1 hz2
                              intro st
                              unfold countA
                              have hset : {k : ℕ | orgArrival z 0 k ≤ 0 ∧ orgSignal M z 0 k = st} = ∅ := by
                                ext k
                                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
                                intro hk; exfalso
                                have : 0 < orgArrival z 0 k := by
                                  unfold orgArrival
                                  exact div_pos (Finset.sum_pos (fun l _ => hz2 (0, l)) ⟨0, by simp⟩)
                                    (by linarith [hz1.2 0])
                                linarith
                              rw [hset, Set.ncard_empty, hz1.1]
                              simp [truthfulAction]
                            set c0 : LocalHistory 3 0 := (fun _ => (0, 0), fun _ j => if j = 1 then 1 / 2 else 0) with hc0
                            have hconst : ∀ᵐ z ∂Q, O 0 z = c0 := by
                              filter_upwards [hcount] with z hz
                              have hs0 : ∀ s : Set.Icc (0:ℝ) 0, (s : ℝ) = 0 := fun s => le_antisymm s.2.2 s.2.1
                              refine Prod.ext ?_ ?_
                              · funext s
                                simp only [O, loc, hc0, receivedPath, hs0 s, hz]
                              · funext s j
                                simp only [O, loc, hc0, HdP, hs0 s, if_true]
                            have hb : ∀ z, beliefA M R 0 0 z = 1 / 2 := fun z => by rw [hbel0]; simp
                            simp only [hb]
                            have hIR : ∫ z, indR z ∂Q = 1 / 2 := by
                              have hSm : MeasurableSet {z : Full 3 | z.1.1 = State.R} :=
                                measurable_fst.fst (measurableSet_singleton State.R)
                              have hind : (indR : Full 3 → ℝ) = {z : Full 3 | z.1.1 = State.R}.indicator 1 := by
                                funext z; unfold indR; simp [Set.indicator]
                              rw [hind, integral_indicator_one hSm]
                              have hset : {z : Full 3 | z.1.1 = State.R} = {p : Params 3 | p.1 = State.R} ×ˢ Set.univ := by
                                ext; simp
                              have hset2 : {p : Params 3 | p.1 = State.R} = {State.R} ×ˢ Set.univ := by ext; simp
                              rw [measureReal_def, hset, hQeq, Measure.prod_prod, measure_univ, mul_one, hmixapp, hset2]
                              simp only [hK, Measure.prod_prod, measure_univ, mul_one, Measure.dirac_apply,
                                Set.indicator, Set.mem_singleton_iff]
                              simp only [show (State.S = State.R) = False by simp, if_false]
                              norm_num
                            by_cases hcV : c0 ∈ V
                            · have hU : (O 0 ⁻¹' V) =ᵐ[Q] (Set.univ : Set (Full 3)) := by
                                rw [Filter.eventuallyEq_set]; filter_upwards [hconst] with z hz; simp [hz, hcV]
                              rw [setIntegral_congr_set hU, setIntegral_congr_set hU]
                              simp only [Measure.restrict_univ]
                              rw [hIR]; simp
                            · have hU : (O 0 ⁻¹' V) =ᵐ[Q] (∅ : Set (Full 3)) := by
                                rw [Filter.eventuallyEq_set]; filter_upwards [hconst] with z hz; simp [hz, hcV]
                              rw [setIntegral_congr_set hU, setIntegral_congr_set hU]
                              simp
                          · have hae : ∀ᵐ z ∂Q, beliefA M R t 0 z = Q[indR | m] z := by
                              have h1 := condExp_nonneg (μ := Q) (m := m) (ae_of_all _ fun z => (hindR01 z).1)
                              have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := m) (R := (1:ℝ)) (f := indR)
                                (ae_of_all _ fun z => by rw [abs_le]; constructor <;> linarith [hindR01 z])
                              filter_upwards [h1, h2] with z hz1 hz2
                              rw [hbel0, if_neg ht0]
                              rw [hGeq t] at hz1 hz2 ⊢
                              simp only [Function.comp_apply, Pi.zero_apply] at hz1 hz2 ⊢
                              rw [abs_le] at hz2
                              unfold clampProb
                              rw [Set.projIcc_of_mem _ ⟨hz1, hz2.2⟩]
                            rw [setIntegral_congr_ae (hle _ hU) (hae.mono fun z hz _ => hz)]
                            exact setIntegral_condExp hle hindRi hU
                      · -- (K5) type posterior
                        let K : Measure (AAction 3 × (Fin 3 → ℝ)) := (Measure.dirac (truthfulAction 3)).prod (M.ν 0)
                        let mix : Measure (Params 3) := ∑ y : State, ∑ τ : Bool,
                          ENNReal.ofReal (priorOf M.q y * (1 / 2)) • (Measure.dirac y).prod ((Measure.dirac τ).prod K)
                        have hQ : Q = mix.prod (baseMeasure 3) := by
                          show subjLaw M σP 0 = _
                          unfold subjLaw
                          congr 1
                          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun τ _ => ?_
                          cases τ <;> simp [σP, hμ, K] <;> norm_num
                        have hmixfin : IsFiniteMeasure mix := by
                          constructor
                          simp only [mix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
                          refine ENNReal.sum_lt_top.2 fun y _ => ENNReal.sum_lt_top.2 fun τ _ => ?_
                          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
                        have hbaseP : IsProbabilityMeasure (baseMeasure 3) := by
                          unfold baseMeasure; infer_instance
                        have hfin : IsFiniteMeasure Q := by
                          rw [hQ]; infer_instance
                        let φ1 : Params 3 → Params 3 := fun p => (p.1, !p.2.1, p.2.2)
                        have hφ1 : Measurable φ1 :=
                          measurable_fst.prodMk (((measurable_of_countable (fun b : Bool => !b)).comp
                            measurable_snd.fst).prodMk measurable_snd.snd)
                        let φ : Full 3 → Full 3 := Prod.map φ1 id
                        have hφ : Measurable φ := hφ1.prodMap measurable_id
                        have hφd : ∀ (y : State) (τ : Bool),
                            ((Measure.dirac y).prod ((Measure.dirac τ).prod K)).map φ1 =
                              (Measure.dirac y).prod ((Measure.dirac (!τ)).prod K) := by
                          intro y τ
                          have : φ1 = Prod.map id (Prod.map (fun b : Bool => !b) id) := rfl
                          rw [this, ← Measure.map_prod_map _ _ measurable_id
                            ((measurable_of_countable (fun b : Bool => !b)).prodMap measurable_id),
                            ← Measure.map_prod_map _ _ (measurable_of_countable (fun b : Bool => !b)) measurable_id,
                            Measure.map_id, Measure.map_id, Measure.map_dirac' (measurable_of_countable _)]
                        have hmix : mix.map φ1 = mix := by
                          simp only [mix]
                          rw [Measure.map_finset_sum' hφ1.aemeasurable]
                          refine Finset.sum_congr rfl fun y _ => ?_
                          rw [Measure.map_finset_sum' hφ1.aemeasurable]
                          simp only [Fintype.sum_bool]
                          rw [Measure.map_smul, Measure.map_smul, hφd, hφd]
                          simp only [Bool.not_true, Bool.not_false]
                          rw [add_comm]
                        have hmapQ : Q.map φ = Q := by
                          rw [hQ, ← Measure.map_prod_map _ _ hφ1 measurable_id, hmix, Measure.map_id]
                        have htp : ∀ z, typePosterior M R t 0 z = 1 / 2 := by
                          intro z
                          show ((clampProb (1 / 2) : unitInterval) : ℝ) = 1 / 2
                          simp only [clampProb, Set.coe_projIcc]
                          norm_num
                        have htpf : typePosterior M R t 0 = fun _ => 1 / 2 := funext htp
                        have hindTm : Measurable (indT : Full 3 → ℝ) := by
                          unfold indT
                          exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
                            measurable_const measurable_const
                        have hindTi : Integrable (indT : Full 3 → ℝ) Q :=
                          Integrable.of_bound hindTm.aestronglyMeasurable 1
                            (ae_of_all _ fun z => by unfold indT; split_ifs <;> simp)
                        refine ⟨by rw [hobs]; exact hOm t, ?_, ?_, hindTi, ?_⟩
                        · rw [htpf]; exact measurable_const
                        · rw [htpf]; exact integrable_const _
                        · intro U hU
                          obtain ⟨V, hV, rfl⟩ := hU
                          rw [hobs, htpf]
                          change ∫ z in O t ⁻¹' V, (1 / 2 : ℝ) ∂Q = ∫ z in O t ⁻¹' V, indT z ∂Q
                          have hUm : MeasurableSet (O t ⁻¹' V) := hOm t hV
                          have hφU : φ ⁻¹' (O t ⁻¹' V) = O t ⁻¹' V := rfl
                          have hflip : ∀ z, indT (φ z) = 1 - indT z := by
                            intro z
                            simp only [indT, φ, φ1, Prod.map]
                            rcases z with ⟨⟨_, τ, _⟩, _⟩
                            cases τ <;> norm_num
                          have h1 : ∫ z in O t ⁻¹' V, indT z ∂Q = ∫ z in O t ⁻¹' V, (1 - indT z) ∂Q := by
                            calc ∫ z in O t ⁻¹' V, indT z ∂Q = ∫ z in O t ⁻¹' V, indT z ∂(Q.map φ) := by
                                  rw [hmapQ]
                              _ = ∫ z in φ ⁻¹' (O t ⁻¹' V), indT (φ z) ∂Q :=
                                  setIntegral_map hUm hindTm.aestronglyMeasurable hφ.aemeasurable
                              _ = _ := by rw [hφU]; simp_rw [hflip]
                          rw [integral_sub (integrable_const _).integrableOn hindTi.integrableOn] at h1
                          rw [setIntegral_const] at h1 ⊢
                          simp only [smul_eq_mul] at h1 ⊢
                          linarith
                    · -- (K6) no factorization
                      rintro ⟨g, -, hg⟩
                      let ΨC : (Fin 3 × ℕ → unitInterval) → (Fin 3 × ℕ → unitInterval) :=
                        fun c k => if k.1 = 2 then unitInterval.symm (c k) else c k
                      have hm : ∀ k : Fin 3 × ℕ, Measurable
                          (fun x : unitInterval => if k.1 = 2 then unitInterval.symm x else x) := by
                        intro k; by_cases hk : k.1 = 2
                        · simp only [hk, if_true]; exact unitInterval.measurable_symm
                        · simp only [hk, if_false]; exact measurable_id
                      have hΨC : MeasurePreserving ΨC
                          (Measure.infinitePi fun _ : Fin 3 × ℕ => (volume : Measure unitInterval))
                          (Measure.infinitePi fun _ : Fin 3 × ℕ => (volume : Measure unitInterval)) := by
                        refine ⟨measurable_pi_lambda _ (fun k => (hm k).comp (measurable_pi_apply k)), ?_⟩
                        show Measure.map (fun (c : Fin 3 × ℕ → unitInterval) (k : Fin 3 × ℕ) =>
                          (fun x : unitInterval => if k.1 = 2 then unitInterval.symm x else x) (c k)) _ = _
                        refine (Measure.infinitePi_map_pi
                          (μ := fun _ : Fin 3 × ℕ => (volume : Measure unitInterval)) hm).trans ?_
                        congr 1; funext k
                        by_cases hk : k.1 = 2
                        · simp only [hk, if_true]; exact unitInterval.measurePreserving_symm.map_eq
                        · simp only [hk, if_false]; exact Measure.map_id'
                      let Ψ : Full 3 → Full 3 := Prod.map id (Prod.map id (Prod.map id ΨC))
                      have : IsProbabilityMeasure (baseMeasure 3) := by unfold baseMeasure; infer_instance
                      have hΨ : MeasurePreserving Ψ (trueLaw M State.S false (truthfulAction 3))
                          (trueLaw M State.S false (truthfulAction 3)) :=
                        (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
                          ((MeasurePreserving.id _).prod hΨC))
                      have hrecv : ∀ z s, ∀ i ≠ (2 : Fin 3), receivedPath M (Ψ z) s i = receivedPath M z s i := by
                        intro z s i hi
                        simp [receivedPath, countA, orgSignal, orgArrival, prinArrival, Ψ, ΨC, hi]
                      have hOinv : ∀ z, O (1 / 2) (Ψ z) = O (1 / 2) z := by
                        intro z
                        simp only [O, loc]
                        refine Prod.ext (funext fun s => hrecv z _ 0 (by decide)) (funext fun s => funext fun j => ?_)
                        simp only
                        rw [hrecv z _ 1 (by decide)]
                      have h1 := hΨ.quasiMeasurePreserving.ae hg
                      have hae : ∀ᵐ z ∂(trueLaw M State.S false (truthfulAction 3)),
                          beliefA M R (1 / 2) 2 (Ψ z) = beliefA M R (1 / 2) 2 z := by
                        filter_upwards [hg, h1] with z hz hz'
                        rw [hz', hz, hobs, hOinv]
                      let EA : Set (Fin 3 × ℕ → ℝ) := {a | a (2, 0) ≤ 1 / 4 ∧ 1 / 2 < a (2, 1) ∧ ∀ l, 0 ≤ a (2, l)}
                      let EC : Set (Fin 3 × ℕ → unitInterval) := {c | (c (2, 0) : ℝ) < 1 / 5}
                      let p0 : Params 3 := (State.S, false, truthfulAction 3, M.lam)
                      let E : Set (Full 3) := {p0} ×ˢ (EA ×ˢ (Set.univ ×ˢ EC))
                      have hEpos : trueLaw M State.S false (truthfulAction 3) E ≠ 0 := by
                        simp only [trueLaw, baseMeasure, E]
                        rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ,
                          Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul, one_mul]
                        refine mul_ne_zero ?_ ?_
                        · have hI : ProbabilityTheory.expMeasure 1 (Set.Iio 0) = 0 := by
                            have h0 := ProbabilityTheory.cdf_expMeasure_eq one_pos 0
                            rw [ProbabilityTheory.cdf_eq_real] at h0
                            simp at h0
                            exact measure_mono_null Set.Iio_subset_Iic_self ((measureReal_eq_zero_iff).mp h0)
                          have hN : Measure.infinitePi (fun _ : Fin 3 × ℕ => ProbabilityTheory.expMeasure 1)
                              {a : Fin 3 × ℕ → ℝ | ∀ l, 0 ≤ a (2, l)}ᶜ = 0 := by
                            have : {a : Fin 3 × ℕ → ℝ | ∀ l, 0 ≤ a (2, l)}ᶜ =
                                ⋃ l : ℕ, Function.eval ((2 : Fin 3), l) ⁻¹' Set.Iio 0 := by
                              ext a; simp
                            rw [this]
                            refine measure_iUnion_null fun l => ?_
                            rw [(measurePreserving_eval_infinitePi _ _).measure_preimage
                              measurableSet_Iio.nullMeasurableSet]
                            exact hI
                          have hbox : EA = (Set.pi ↑({((2 : Fin 3), 0), ((2 : Fin 3), 1)} : Finset (Fin 3 × ℕ))
                              (fun k => if k = ((2 : Fin 3), 0) then Set.Iic (1 / 4 : ℝ) else Set.Ioi (1 / 2)))
                                ∩ {a | ∀ l, 0 ≤ a (2, l)} := by
                            ext a; simp [EA]
                            exact and_assoc.symm
                          rw [hbox, measure_inter_conull hN, Measure.infinitePi_pi]
                          · rw [Finset.prod_pair (by decide)]
                            simp only [if_true, show ((2 : Fin 3), 1) ≠ ((2 : Fin 3), 0) by decide, if_false]
                            refine mul_ne_zero ?_ ?_
                            · intro h
                              have := ProbabilityTheory.cdf_expMeasure_eq one_pos (1 / 4)
                              rw [ProbabilityTheory.cdf_eq_real, measureReal_def, h] at this
                              norm_num at this
                              linarith [Real.exp_lt_one_iff.mpr (show -(1 / 4 : ℝ) < 0 by norm_num)]
                            · rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
                              intro h
                              have h1 : (1 : ENNReal) ≤ ProbabilityTheory.expMeasure 1 (Set.Iic (1 / 2)) :=
                                tsub_eq_zero_iff_le.mp h
                              have h2 : ProbabilityTheory.expMeasure 1 (Set.Iic (1 / 2)) = 1 :=
                                le_antisymm prob_le_one h1
                              have := ProbabilityTheory.cdf_expMeasure_eq one_pos (1 / 2)
                              rw [ProbabilityTheory.cdf_eq_real, measureReal_def, h2] at this
                              norm_num at this
                              linarith [Real.exp_pos (-(1 / 2 : ℝ))]
                          · intro k _; split_ifs
                            · exact measurableSet_Iic
                            · exact measurableSet_Ioi
                        · show Measure.infinitePi (fun _ : Fin 3 × ℕ => (volume : Measure unitInterval))
                            (Function.eval ((2 : Fin 3), 0) ⁻¹'
                              Set.Iio (⟨1 / 5, by norm_num, by norm_num⟩ : unitInterval)) ≠ 0
                          rw [(measurePreserving_eval_infinitePi _ _).measure_preimage
                            measurableSet_Iio.nullMeasurableSet, unitInterval.volume_Iio]
                          norm_num
                      have harr : ∀ z : Full 3, z.1 = p0 → z.2.1 ∈ EA → ∀ k,
                          orgArrival z 2 k ≤ 1 / 2 ↔ k = 0 := by
                        rintro ⟨z1, a, b, c⟩ hz1 ha k
                        simp only at hz1 ha ⊢
                        subst hz1
                        obtain ⟨ha0, ha1, hnn⟩ := ha
                        simp only [orgArrival, p0, hlam, div_one]
                        constructor
                        · intro hk
                          by_contra hk0
                          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
                          rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hk
                          have : 0 ≤ ∑ i ∈ Finset.range m, a (2, i + 1 + 1) :=
                            Finset.sum_nonneg (fun i _ => hnn _)
                          linarith [hnn 0]
                        · rintro rfl; simp; linarith
                      have hcnt : ∀ z : Full 3, z.1 = p0 → z.2.1 ∈ EA → ∀ s,
                          countA M z 2 (1 / 2) s = if orgSignal M z 2 0 = s then 1 else 0 := by
                        intro z hz1 ha s
                        have hset : {k : ℕ | orgArrival z 2 k ≤ 1 / 2 ∧ orgSignal M z 2 k = s} =
                            if orgSignal M z 2 0 = s then {0} else ∅ := by
                          ext k
                          simp only [Set.mem_setOf_eq, harr z hz1 ha k]
                          by_cases h : orgSignal M z 2 0 = s
                          · simp only [h, if_true, Set.mem_singleton_iff]
                            constructor
                            · exact fun h' => h'.1
                            · rintro rfl; exact ⟨rfl, h⟩
                          · simp only [h, if_false, Set.mem_empty_iff_false, iff_false]
                            rintro ⟨rfl, h'⟩; exact h h'
                        have hx : z.1.2.2.1.2.1 2 = false := by rw [hz1]; rfl
                        unfold countA
                        rw [hset]
                        simp only [hx, Bool.false_eq_true, false_and, if_false, add_zero]
                        split_ifs <;> simp
                      have hEsub : E ⊆ {z | ¬ (beliefA M R (1 / 2) 2 (Ψ z) = beliefA M R (1 / 2) 2 z)} := by
                        rintro ⟨z1, a, b, c⟩ ⟨hz1, ha, -, hc⟩
                        have hz1' : z1 = p0 := hz1
                        have hΨ1 : (Ψ (z1, a, b, c)).1 = p0 := hz1'
                        have hΨa : (Ψ (z1, a, b, c)).2.1 ∈ EA := ha
                        have hc' : (c (2, 0) : ℝ) < 1 / 5 := hc
                        have hsig1 : orgSignal M (z1, a, b, c) 2 0 = State.S := by
                          simp only [orgSignal, hz1', p0, organicProbS, if_true, hp]
                          rw [if_pos]; linarith
                        have hsig2 : orgSignal M (Ψ (z1, a, b, c)) 2 0 = State.R := by
                          simp only [orgSignal, Ψ, ΨC, Prod.map, id, hz1', p0, organicProbS, if_true, hp,
                            unitInterval.coe_symm_eq]
                          rw [if_neg]; linarith
                        have e1 : receivedPath M (z1, a, b, c) (1 / 2) 2 = (1, 0) := by
                          rw [show receivedPath M (z1, a, b, c) (1 / 2) 2 = (countA M (z1, a, b, c) 2 (1 / 2) State.S,
                            countA M (z1, a, b, c) 2 (1 / 2) State.R) from rfl, hcnt _ hz1' ha, hcnt _ hz1' ha, hsig1]
                          simp
                        have e2 : receivedPath M (Ψ (z1, a, b, c)) (1 / 2) 2 = (0, 1) := by
                          rw [show receivedPath M (Ψ (z1, a, b, c)) (1 / 2) 2 =
                            (countA M (Ψ (z1, a, b, c)) 2 (1 / 2) State.S,
                            countA M (Ψ (z1, a, b, c)) 2 (1 / 2) State.R) from rfl, hcnt _ hΨ1 hΨa,
                            hcnt _ hΨ1 hΨa, hsig2]
                          simp
                        simp only [Set.mem_setOf_eq]
                        rw [hbel2, hbel2, e1, e2]
                        intro h
                        simp only [HdP, BUS, hp, hq] at h
                        norm_num at h
                        nlinarith [hθ2]
                      exact hEpos (measure_mono_null hEsub (ae_iff.mp hae))
                  intro Z hZ
                  obtain ⟨f, hfpos, hflt, hfZ⟩ : ∃ f : ({i : Fin 3 // i ∉ ({0} : Finset (Fin 3))} → Fin 3 → ℝ),
                      (∀ i j, 0 < f i j) ∧ (∀ i j, f i j < 1 / 4) ∧ f ∉ Z := by
                    let U : Set ({i : Fin 3 // i ∉ ({0} : Finset (Fin 3))} → Fin 3 → ℝ) :=
                      ⋂ i, ⋂ j, (fun f => f i j) ⁻¹' Set.Ioo (0 : ℝ) (1 / 4)
                    have hUo : IsOpen U :=
                      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
                        isOpen_Ioo.preimage (by fun_prop)
                    have hUne : U.Nonempty := ⟨fun _ _ => 1 / 8, by
                      simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo]; intro i j; norm_num⟩
                    have hpos := hUo.measure_pos volume hUne
                    by_contra hcon
                    push Not at hcon
                    have hsub : U ⊆ Z := by
                      intro g hg
                      simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo] at hg
                      exact hcon g (fun i j => (hg i j).1) (fun i j => (hg i j).2)
                    have := measure_mono (μ := volume) hsub
                    rw [hZ] at this
                    exact absurd (le_antisymm this (zero_le)) hpos.ne'
                  let ρ : Measure ℝ := (ProbabilityTheory.gaussianReal 0 1).map (fun x => 9 / 10 + Real.exp x)
                  have hgm : Measurable (fun x : ℝ => 9 / 10 + Real.exp x) := by fun_prop
                  have hρP : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hgm.aemeasurable
                  have hρS : ρ (Set.Iic (9 / 10)) = 0 := by
                    show Measure.map _ _ _ = 0
                    rw [Measure.map_apply hgm measurableSet_Iic]
                    have : (fun x : ℝ => 9 / 10 + Real.exp x) ⁻¹' Set.Iic (9 / 10) = ∅ := by
                      ext x; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
                      linarith [Real.exp_pos x]
                    rw [this, measure_empty]
                  have hρpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.Ioi (9 / 10)).Nonempty → 0 < ρ U := by
                    intro U hU hne
                    obtain ⟨u, huU, hu⟩ := hne
                    show 0 < Measure.map _ _ _
                    rw [Measure.map_apply hgm hU.measurableSet]
                    have hVo : IsOpen ((fun x : ℝ => 9 / 10 + Real.exp x) ⁻¹' U) := hU.preimage (by fun_prop)
                    have hVne : ((fun x : ℝ => 9 / 10 + Real.exp x) ⁻¹' U).Nonempty := by
                      refine ⟨Real.log (u - 9 / 10), ?_⟩
                      simp only [Set.mem_preimage]
                      have hu' : (0:ℝ) < u - 9 / 10 := by simp only [Set.mem_Ioi] at hu; linarith
                      rw [Real.exp_log hu']
                      convert huU using 1; ring
                    have hvol := hVo.measure_pos volume hVne
                    rw [pos_iff_ne_zero] at hvol ⊢
                    intro h0
                    exact hvol (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero h0)
                  let ν : Measure (Fin 3 → ℝ) := Measure.pi (fun _ => ρ)
                  have hνP : IsProbabilityMeasure ν := by
                    haveI := hρP
                    infer_instance
                  have hνS : ν {r | ∀ j, 9 / 10 < r j}ᶜ = 0 := by
                    haveI := hρP
                    have hsub : {r : Fin 3 → ℝ | ∀ j, 9 / 10 < r j}ᶜ ⊆
                        ⋃ j, (fun r : Fin 3 → ℝ => r j) ⁻¹' Set.Iic (9 / 10) := by
                      intro r hr
                      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hr
                      obtain ⟨j, hj⟩ := hr
                      exact Set.mem_iUnion.2 ⟨j, hj⟩
                    refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
                    exact Measure.pi_eval_preimage_null (μ := fun _ => ρ) hρS
                  have hνpos : ∀ j, ∀ U : Set ℝ, IsOpen U → (U ∩ Set.Ioi (9 / 10)).Nonempty →
                      0 < ν {r | r j ∈ U} := by
                    intro j U hU hne
                    haveI := hρP
                    have := (measurePreserving_eval (fun _ : Fin 3 => ρ) j).measure_preimage
                      hU.measurableSet.nullMeasurableSet
                    show 0 < ν ((fun r : Fin 3 → ℝ => r j) ⁻¹' U)
                    rw [this]
                    exact hρpos U hU hne
                  let α : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if h : i = 0 then 0 else f ⟨i, by simpa using h⟩ j
                  let M : AModel 3 := ⟨{0}, (fun i => 1 - ∑ j, α i j), α, (fun _ => 4 / 5), 1 / 2, 1 / 2,
                    (fun _ => 1), 9 / 10, 2, 1, 1, 0, (fun i => if i = 0 then {1} else Finset.univ), (fun _ => ν)⟩
                  have hθ : ∀ i, i ≠ 0 → 1 / 4 < M.θ i := by
                    intro i hi
                    show 1 / 4 < 1 - ∑ j, α i j
                    simp only [α, dif_neg hi, Fin.sum_univ_three]
                    linarith [hflt ⟨i, by simpa using hi⟩ 0, hflt ⟨i, by simpa using hi⟩ 1,
                      hflt ⟨i, by simpa using hi⟩ 2]
                  have hBi : ∀ i, i ∉ M.B → i ≠ 0 := by
                    intro i hi; simpa [M] using hi
                  have hαpos : ∀ i ∉ M.B, ∀ j, 0 < M.α i j := by
                    intro i hi j
                    show 0 < α i j
                    simp only [α, dif_neg (hBi i hi)]
                    exact hfpos _ _
                  refine ⟨M, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, hαpos, ?_, ?_⟩
                  · -- Standing
                    refine ⟨fun i => ?_, fun i hi => (lt_trans (by norm_num) (hθ i (hBi i hi))).le,
                      fun i hi j => (hαpos i hi j).le, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_,
                      ?_, ?_, fun i hi => ?_, fun i hi j => ?_⟩
                    · show (1:ℝ) / 2 ≤ 4 / 5 ∧ (4:ℝ) / 5 < 1
                      norm_num
                    · show 1 - ∑ j, α i j + ∑ j, α i j = 1
                      ring
                    all_goals try (show (_:ℝ) < _; norm_num)
                    · refine ⟨hνP, ?_, hνpos⟩
                      have : (Set.univ.pi fun _ => Set.Ioi (M.lamLow)) = {r : Fin 3 → ℝ | ∀ j, 9 / 10 < r j} := by
                        ext r; simp [M]
                      rw [this]; exact hνS
                    · have h0 := hBi i hi
                      have : M.N i = Finset.univ := by simp [M, h0]
                      rw [this]
                      simp only [Finset.mem_univ, true_iff]
                      exact hαpos i hi j
                  · -- Assumption2
                    have hmax : M.lamMax = 1 := ciSup_const (ι := Fin 3) (a := (1:ℝ))
                    refine ⟨?_, fun i => ?_, ⟨0, ?_⟩, ⟨⟨0, ?_⟩, fun i hi => ?_⟩, ?_⟩
                    · rw [hmax]; show (1:ℝ) < 9 / 10 + 2 / 2; norm_num
                    · rw [hmax]; show (4:ℝ) / 5 < (2 + 1) / (2 * 1); norm_num
                    · show (2 + 9 / 10) / (2 * (9 / 10) + 2) < (4:ℝ) / 5; norm_num
                    · show (1:ℝ) / 2 < 4 / 5; norm_num
                    · show 0 < M.θ i ↔ (1:ℝ) / 2 < 4 / 5
                      constructor
                      · intro _; norm_num
                      · intro _; linarith [hθ i (hBi i hi)]
                    · intro i j hij
                      unfold AModel.Linked
                      fin_cases i <;> fin_cases j
                      all_goals first
                        | exact absurd rfl hij
                        | (apply Relation.TransGen.single; simp [M]; done)
                        | (apply Relation.TransGen.tail (Relation.TransGen.single (b := (1 : Fin 3)) ?_) ?_ <;>
                            simp [M])
                  · have : degrootRows ({0} : Finset (Fin 3)) M.α = f := by
                      funext i j
                      show α i.1 j = f i j
                      have h : i.1 ≠ 0 := by simpa using i.2
                      simp only [α, dif_neg h]
                    rw [this]; exact hfZ
                  · exact key M rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (by linarith [hθ 2 (by decide)])
                      hνP hνS
