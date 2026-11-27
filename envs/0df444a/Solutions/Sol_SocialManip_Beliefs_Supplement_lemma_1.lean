-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:46.561089+00:00
-- url     : https://prove2.me/submissions/310b086a-fa06-4510-8e33-c132e70af724

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

/-- A generic all-DeGroot finite-horizon counterexample to the printed “every equilibrium”
claim. Before the first social exchange a positive-rate R stream strictly improves the chance
of action R in state R. With small positive cost the principal targets both agents. -/
theorem solution :
    ∀ Z : Set ({i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ), volume Z = 0 →
      ∃ M : AModel 2, M.Standing ∧ M.Assumption2 ∧ M.B = ∅ ∧
        M.Δ = 1 ∧ M.ε = 1 / 10 ∧ M.b = 0 ∧ M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧
        M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧
        (∀ i, M.lam i = 1) ∧ (∀ i, M.p i = 4 / 5) ∧
        (∀ i j, 0 < M.α i j) ∧ (∀ i, 0 < M.θ i) ∧
        degrootRows (∅ : Finset (Fin 2)) M.α ∉ Z ∧
        ∃ (σP : APrincipalStrategy 2) (R : AReporting 2) (σA : AAgentStrategy 2),
          AIsEquilibrium M (1 / 2) σP R σA ∧
            σP State.R {a | ∃ i, a.2.1 i = true} = 1 := by
              intro Z hZ
              have hbox : ∃ f : {i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ, f ∉ Z ∧
                  ∀ i j, 0 < f i j ∧ f i j < 1 / 4 := by
                by_contra hcon
                push_neg at hcon
                have hsub : (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Ioo (0:ℝ) (1/4)) ⊆ Z := by
                  intro f hf
                  by_contra hfZ
                  obtain ⟨i, j, hij⟩ := hcon f hfZ
                  have := hf i (Set.mem_univ _) j (Set.mem_univ _)
                  exact absurd this.2 (not_lt.mpr (hij this.1))
                have h0 := measure_mono_null hsub hZ
                rw [volume_pi_pi] at h0
                simp only [volume_pi_pi, Real.volume_Ioo] at h0
                norm_num at h0
              obtain ⟨f, hfZ, hf⟩ := hbox
              set α : Matrix (Fin 2) (Fin 2) ℝ := fun i j => f ⟨i, by simp⟩ j with hα
              set θ : Fin 2 → ℝ := fun i => 1 - ∑ j, α i j with hθ
              have hαpos : ∀ i j, 0 < α i j := fun i j => (hf _ j).1
              have hαlt : ∀ i j, α i j < 1 / 4 := fun i j => (hf _ j).2
              have hθpos : ∀ i, 0 < θ i := by
                intro i; simp only [hθ, Fin.sum_univ_two]; linarith [hαlt i 0, hαlt i 1]
              have hsoc : ∀ i, ∑ j, α i j * (1/2) = (1 - θ i) / 2 := by
                intro i; simp only [hθ, ← Finset.sum_mul]; ring
              let M : AModel 2 := ⟨∅, θ, α, fun _ => 4/5, 1/2, 1/2, fun _ => 1, 9/10, 2, 1, 1/10, 0,
                fun _ => Finset.univ, fun _ => 0⟩
              let R : AReporting 2 := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun h t i => if t = 0 then 1/2 else
                θ i * (1 - BUS (4/5) (1/2) (h t i).1 (h t i).2) + ∑ j, α i j * (1/2)⟩
              let σD : DeGrootStrategy 2 := fun _ π => if 1/2 < π then 1 else 0
              let σA : AAgentStrategy 2 := ⟨σD, fun _ _ => 0⟩
              let astar : AAction 2 := (State.R, fun _ => true, fun _ => 2)
              let σP : APrincipalStrategy 2 := fun _ => Measure.dirac astar
              have hlamMax : M.lamMax = 1 := by
                simp [AModel.lamMax, M]
              have hStanding : M.Standing := by
                refine ⟨fun i => by norm_num [M], fun i _ => (hθpos i).le, fun i _ j => (hαpos i j).le,
                  fun i _ => by simp [M, hθ], by norm_num [M], by norm_num [M], by norm_num [M],
                  by norm_num [M], by norm_num [M], fun i => by norm_num [M], by norm_num [M],
                  by norm_num [M], by norm_num [M], by norm_num [M], by norm_num [M],
                  fun i hi => by simp [M] at hi, fun i _ j => by simp [M, hαpos i j]⟩
              have hA2 : M.Assumption2 := by
                refine ⟨by rw [hlamMax]; norm_num [M], fun i => by rw [hlamMax]; norm_num [M],
                  ⟨0, by norm_num [M]⟩, ⟨⟨0, by norm_num [M]⟩, fun i _ => by simp [M, hθpos i]; norm_num⟩, ?_⟩
                intro i j _
                exact Relation.TransGen.single (by simp [M])
              have hceil : ∀ t : ℝ, 0 < t → t ≤ 1/2 → ⌈t⌉₊ = 1 := by
                intro t h1 h2
                rw [Nat.ceil_eq_iff (by norm_num)]
                constructor <;> push_cast <;> linarith
              have hOp : AOperational M (1/2) R := by
                refine ⟨fun t _ i => ⟨measurable_const, measurable_const⟩, ?_, ?_, ?_⟩
                · intro h t ht i
                  by_cases h0 : t = 0
                  · subst h0; simp [R, priorOf, M]; norm_num
                  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
                    simp [R, M, h0, hceil t htpos ht.2, rawBU]
                · intro h H hH t ht i
                  have h0' : ∀ j, H 0 j = 1/2 := by
                    intro j
                    have := hH 0 ⟨le_refl _, by norm_num⟩ j
                    rw [this]; simp [priorOf, M]; norm_num
                  by_cases h0 : t = 0
                  · subst h0; simp [R, h0']
                  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
                    rw [hH t ht i]
                    simp [R, M, h0, hceil t htpos ht.2, rawBU, h0']
                · intro t ht
                  refine ⟨fun g s i => if (s:ℝ) = 0 then 1/2 else
                    θ i * (1 - BUS (4/5) (1/2) (g s i).1 (g s i).2) + ∑ j, α i j * (1/2), ?_, fun h s i => rfl⟩
                  refine measurable_pi_lambda _ (fun s => measurable_pi_lambda _ (fun i => ?_))
                  have hm : Measurable (fun g : RawPrefix 2 t => g s i) :=
                    (measurable_pi_apply i).comp (measurable_pi_apply s)
                  exact (Measurable.of_discrete (f := fun v : ℕ × ℕ => if (s:ℝ) = 0 then (1/2:ℝ) else
                    θ i * (1 - BUS (4/5) (1/2) v.1 v.2) + ∑ j, α i j * (1/2))).comp hm
              have hopt : ∀ y (a' : AAction 2), a'.Admissible M →
                  principalPayoffA M (1/2) R σA y a' ≤ principalPayoffA M (1/2) R σA y astar := by
                intro y a' ha'
                haveI hbase : IsProbabilityMeasure (baseMeasure 2) := by unfold baseMeasure; infer_instance
                have hBUS : ∀ a b : ℕ, BUS (4/5) (1/2) a b < 1/2 ↔ a < b := by
                  intro a b
                  have key : ∀ a b : ℕ, (4/5:ℝ)^a * (1-4/5)^b = 4^a / (5^a * 5^b) := by
                    intro a b
                    rw [div_pow, show (1:ℝ)-4/5 = 1/5 by norm_num, div_pow, one_pow]
                    field_simp
                  unfold BUS
                  rw [key, key]
                  have h4a : (0:ℝ) < 4^a := by positivity
                  have h4b : (0:ℝ) < 4^b := by positivity
                  have h5 : (0:ℝ) < 5^a * 5^b := by positivity
                  rw [div_lt_iff₀ (by positivity), ← pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 4)]
                  rw [mul_comm ((5:ℝ)^b) (5^a)]
                  constructor
                  · intro h
                    by_contra hc; push Not at hc
                    have : 4^b / (5^a*5^b) * (1/2:ℝ) ≤ 4^a / (5^a*5^b) * (1/2) := by gcongr
                    nlinarith
                  · intro h
                    have : 4^a / (5^a*5^b) * (1/2:ℝ) < 4^b / (5^a*5^b) * (1/2) := by gcongr
                    nlinarith
                have hscore : ∀ i (a b : ℕ), σD i (θ i * (1 - BUS (4/5) (1/2) a b) + ∑ j, α i j * (1/2)) =
                    if a < b then 1 else 0 := by
                  intro i a b
                  have : (1/2 < θ i * (1 - BUS (4/5) (1/2) a b) + ∑ j, α i j * (1/2)) ↔
                      BUS (4/5) (1/2) a b < 1/2 := by
                    rw [hsoc i]
                    constructor <;> intro h <;> nlinarith [hθpos i]
                  simp only [σD, this, hBUS]
                let sc : AAction 2 → Base 2 → Fin 2 → ℝ := fun a ω i =>
                  if countA M ((y, false, a, M.lam), ω) i (1/2) State.S <
                    countA M ((y, false, a, M.lam), ω) i (1/2) State.R then 1 else 0
                have hpay : ∀ a : AAction 2, principalPayoffA M (1/2) R σA y a =
                    ∫ ω, ∑ i, sc a ω i ∂(baseMeasure 2) -
                      1/10 * ((Finset.univ.filter fun i => a.2.1 i = true).card : ℝ) := by
                  intro a
                  unfold principalPayoffA trueLaw
                  rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left _).integral_map]
                  congr 2
                  funext ω
                  refine Finset.sum_congr rfl fun i _ => ?_
                  simp only [actionProbA, beliefA, receivedPath, sc]
                  have hB : i ∉ M.B := by simp [M]
                  rw [if_neg hB]
                  show σD i (if (1/2:ℝ) = 0 then _ else _) = _
                  rw [if_neg (by norm_num)]
                  exact hscore i _ _
                have hnc : ∀ (A : ℕ → Set (Base 2)), (∀ k, MeasurableSet (A k)) →
                    Measurable (fun ω => {k | ω ∈ A k}.ncard) := by
                  classical
                  intro A hA
                  refine measurable_to_countable' (fun n => ?_)
                  have : (fun ω => {k | ω ∈ A k}.ncard) ⁻¹' {n} =
                      (⋃ F : Finset ℕ, if F.card = n then ⋂ k, (if k ∈ F then A k else (A k)ᶜ) else ∅) ∪
                      (if n = 0 then ⋂ N : ℕ, ⋃ k, ⋃ (_ : N < k), A k else ∅) := by
                    ext ω
                    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion]
                    constructor
                    · intro h
                      by_cases hfin : {k | ω ∈ A k}.Finite
                      · left
                        obtain ⟨F, hF⟩ := hfin.exists_finset_coe
                        refine ⟨F, ?_⟩
                        rw [if_pos (by rw [← h, ← hF, Set.ncard_coe_finset])]
                        simp only [Set.mem_iInter]
                        intro k
                        split_ifs with hk
                        · have : k ∈ (F : Set ℕ) := hk
                          rw [hF] at this; exact this
                        · intro hk'
                          apply hk
                          have : k ∈ {k | ω ∈ A k} := hk'
                          rw [← hF] at this; exact this
                      · right
                        have hn : n = 0 := by rw [← h]; exact Set.Infinite.ncard hfin
                        rw [if_pos hn]
                        simp only [Set.mem_iInter, Set.mem_iUnion]
                        intro N
                        obtain ⟨b, hb, hNb⟩ := (Set.infinite_iff_exists_gt.mp hfin) N
                        exact ⟨b, hNb, hb⟩
                    · rintro (⟨F, hF⟩ | h)
                      · split_ifs at hF with hc
                        · simp only [Set.mem_iInter] at hF
                          have : {k | ω ∈ A k} = ↑F := by
                            ext k
                            have := hF k
                            by_cases hk : k ∈ F
                            · rw [if_pos hk] at this
                              simp only [Set.mem_setOf_eq, Finset.mem_coe, hk, iff_true]; exact this
                            · rw [if_neg hk] at this
                              simp only [Set.mem_setOf_eq, Finset.mem_coe, hk, iff_false]; exact this
                          rw [this, Set.ncard_coe_finset, hc]
                        · exact absurd hF (Set.notMem_empty _)
                      · split_ifs at h with hn
                        · subst hn
                          apply Set.Infinite.ncard
                          rw [Set.infinite_iff_exists_gt]
                          intro N
                          simp only [Set.mem_iInter, Set.mem_iUnion] at h
                          obtain ⟨k, hk1, hk2⟩ := h N
                          exact ⟨k, hk2, hk1⟩
                        · exact absurd h (Set.notMem_empty _)
                  rw [this]
                  refine MeasurableSet.union (MeasurableSet.iUnion fun F => ?_) ?_
                  · split_ifs
                    · exact MeasurableSet.iInter fun k => by split_ifs; exacts [hA k, (hA k).compl]
                    · exact MeasurableSet.empty
                  · split_ifs
                    · exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun k =>
                        MeasurableSet.iUnion fun _ => hA k
                    · exact MeasurableSet.empty
                have hmeasc : ∀ a i s, Measurable (fun ω : Base 2 => countA M ((y, false, a, M.lam), ω) i (1/2) s) := by
                  intro a i s
                  unfold countA
                  refine Measurable.add (M := ℕ) ?_ ?_
                  · refine hnc (fun k => {ω : Base 2 | orgArrival ((y, false, a, M.lam), ω) i k ≤ 1/2 ∧
                      orgSignal M ((y, false, a, M.lam), ω) i k = s}) (fun k => ?_)
                    refine MeasurableSet.inter ?_ ?_
                    · show MeasurableSet {ω : Base 2 | orgArrival ((y, false, a, M.lam), ω) i k ≤ 1/2}
                      refine measurableSet_le ?_ measurable_const
                      unfold orgArrival
                      refine Measurable.div_const (Finset.measurable_sum (M := ℝ) _ fun l _ => ?_) _
                      exact (measurable_pi_apply _).comp measurable_fst
                    · have : Measurable (fun ω : Base 2 => orgSignal M ((y, false, a, M.lam), ω) i k) := by
                        unfold orgSignal
                        refine Measurable.ite (measurableSet_lt ?_ (by dsimp only; exact measurable_const)) measurable_const measurable_const
                        exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))
                      exact this (MeasurableSet.singleton s)
                  · dsimp only
                    by_cases hc : a.2.1 i = true ∧ 0 < a.2.2 i ∧ a.1 = s
                    · simp only [if_pos hc]
                      refine hnc _ (fun k => ?_)
                      show MeasurableSet {ω : Base 2 | prinArrival ((y, false, a, M.lam), ω) i k ≤ 1/2}
                      refine measurableSet_le ?_ measurable_const
                      unfold prinArrival
                      dsimp only
                      refine Measurable.div_const (Finset.measurable_sum (M := ℝ) _ fun l _ => ?_) _
                      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
                    · simp only [if_neg hc]; exact measurable_const
                have hmsc : ∀ a i, Measurable (fun ω => sc a ω i) := by
                  intro a i
                  refine Measurable.ite (measurableSet_lt (hmeasc a i _) (hmeasc a i _)) measurable_const measurable_const
                have hint : ∀ a i, Integrable (fun ω => sc a ω i) (baseMeasure 2) := by
                  intro a i
                  refine Integrable.of_bound (hmsc a i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
                  simp only [sc]; split_ifs <;> norm_num
                let Eind : Fin 2 → Base 2 → ℝ := fun i ω =>
                  if 1/2 < ω.1 (i,0) ∧ ω.2.1 (i,0) ≤ 1 then 1 else 0
                have hEm : ∀ i, Measurable (Eind i) := by
                  intro i
                  refine Measurable.ite (MeasurableSet.inter ?_ ?_) measurable_const measurable_const
                  · exact measurableSet_lt measurable_const ((measurable_pi_apply _).comp measurable_fst)
                  · exact measurableSet_le ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)) measurable_const
                have hEint : ∀ i, Integrable (Eind i) (baseMeasure 2) := by
                  intro i
                  refine Integrable.of_bound (hEm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
                  simp only [Eind]; split_ifs <;> norm_num
                haveI hE : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) := ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
                have hIic : ∀ x : ℝ, 0 ≤ x → ProbabilityTheory.expMeasure 1 (Set.Iic x) = ENNReal.ofReal (1 - Real.exp (-x)) := by
                  intro x hx
                  rw [← ProbabilityTheory.ofReal_cdf, ProbabilityTheory.cdf_expMeasure_eq one_pos, if_pos hx, one_mul]
                have hneg : ProbabilityTheory.expMeasure 1 (Set.Iio 0) = 0 := by
                  refine le_antisymm (le_trans (measure_mono Set.Iio_subset_Iic_self) ?_) bot_le
                  rw [hIic 0 le_rfl]; simp
                have hPi : ∀ (j : Fin 2 × ℕ) (A : Set ℝ), MeasurableSet A →
                    (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1) ((fun x => x j) ⁻¹' A) = ProbabilityTheory.expMeasure 1 A := by
                  intro j A hA
                  exact (measurePreserving_eval_infinitePi (fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1) j).measure_preimage hA.nullMeasurableSet
                have hall : ∀ i : Fin 2, (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1)
                    {x | ∀ l, x (i,l) ≤ 1} = 0 := by
                  intro i
                  set c := ProbabilityTheory.expMeasure 1 (Set.Iic 1) with hc
                  have hc1 : c < 1 := by
                    rw [hc, hIic 1 zero_le_one]
                    rw [ENNReal.ofReal_lt_one]; linarith [Real.exp_pos (-1)]
                  have hle : ∀ N : ℕ, (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1)
                      {x | ∀ l, x (i,l) ≤ 1} ≤ c ^ N := by
                    intro N
                    calc _ ≤ (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1)
                          (Set.pi ↑(({i} : Finset (Fin 2)) ×ˢ Finset.range N) fun _ => Set.Iic 1) := by
                          refine measure_mono fun x hx => ?_
                          intro j hj
                          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_singleton,
                            Set.mem_singleton_iff] at hj
                          obtain ⟨j1, j2⟩ := j
                          simp only at hj
                          rw [hj.1]
                          exact hx j2
                      _ = c ^ N := by
                          rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic), Finset.prod_const,
                            Finset.card_product]
                          simp [hc]
                  refine le_antisymm ?_ bot_le
                  exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1) hle
                have hbm : baseMeasure 2 = (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1).prod
                  ((Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1).prod
                    (Measure.infinitePi fun _ : Fin 2 × ℕ => (volume : Measure unitInterval))) := rfl
                haveI : IsProbabilityMeasure (Measure.infinitePi fun _ : Fin 2 × ℕ => ProbabilityTheory.expMeasure 1) := inferInstance
                have hn1 : ∀ i l, baseMeasure 2 {ω | ¬ 0 ≤ ω.1 (i,l)} = 0 := by
                  intro i l
                  have : {ω : Base 2 | ¬ 0 ≤ ω.1 (i,l)} = ((fun x => x (i,l)) ⁻¹' Set.Iio 0) ×ˢ Set.univ := by
                    ext ω; simp
                  rw [this, hbm, Measure.prod_prod, hPi _ _ measurableSet_Iio, hneg, zero_mul]
                have hn2 : ∀ i l, baseMeasure 2 {ω | ¬ 0 ≤ ω.2.1 (i,l)} = 0 := by
                  intro i l
                  have : {ω : Base 2 | ¬ 0 ≤ ω.2.1 (i,l)} =
                      Set.univ ×ˢ (((fun x => x (i,l)) ⁻¹' Set.Iio 0) ×ˢ Set.univ) := by
                    ext ω; simp
                  rw [this, hbm, Measure.prod_prod, Measure.prod_prod, hPi _ _ measurableSet_Iio, hneg]
                  simp
                have hn3 : ∀ i, baseMeasure 2 {ω | ¬ ¬ ∀ l, ω.2.1 (i,l) ≤ 1} = 0 := by
                  intro i
                  have : {ω : Base 2 | ¬ ¬ ∀ l, ω.2.1 (i,l) ≤ 1} =
                      Set.univ ×ˢ ({x : Fin 2 × ℕ → ℝ | ∀ l, x (i,l) ≤ 1} ×ˢ Set.univ) := by
                    ext ω; simp
                  rw [this, hbm, Measure.prod_prod, Measure.prod_prod, hall i]
                  simp
                have hgood : ∀ᵐ ω ∂(baseMeasure 2), ∀ i, (∀ l, 0 ≤ ω.1 (i,l)) ∧
                    {k | (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2}.Finite := by
                  rw [ae_all_iff]
                  intro i
                  have h1 : ∀ᵐ ω ∂(baseMeasure 2), ∀ l, 0 ≤ ω.1 (i,l) :=
                    ae_all_iff.2 fun l => ae_iff.2 (hn1 i l)
                  have h2 : ∀ᵐ ω ∂(baseMeasure 2), ∀ l, 0 ≤ ω.2.1 (i,l) :=
                    ae_all_iff.2 fun l => ae_iff.2 (hn2 i l)
                  have h3 : ∀ᵐ ω ∂(baseMeasure 2), ¬ ∀ l, ω.2.1 (i,l) ≤ 1 := ae_iff.2 (hn3 i)
                  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
                  refine ⟨hω1, ?_⟩
                  push Not at hω3
                  obtain ⟨l0, hl0⟩ := hω3
                  refine (Finset.range l0).finite_toSet.subset fun k hk => ?_
                  simp only [Finset.coe_range, Set.mem_Iio]
                  by_contra hkl
                  push Not at hkl
                  have : ω.2.1 (i,l0) ≤ ∑ l ∈ Finset.range (k+1), ω.2.1 (i,l) :=
                    Finset.single_le_sum (f := fun l => ω.2.1 (i,l)) (fun l _ => hω2 l)
                      (Finset.mem_range.2 (by omega))
                  have hk' : (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2 := hk
                  linarith
                have hpt : ∀ ω : Base 2, (∀ i, (∀ l, 0 ≤ ω.1 (i,l)) ∧
                    {k | (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2}.Finite) →
                    ∀ i, sc a' ω i + (if a'.2.1 i = true then 0 else Eind i ω) ≤ sc astar ω i := by
                  intro ω hω i
                  obtain ⟨hnn, hfin⟩ := hω i
                  have hcnt : ∀ (a : AAction 2) s, countA M ((y, false, a, M.lam), ω) i (1/2) s =
                      {k | orgArrival ((y, false, astar, M.lam), ω) i k ≤ 1/2 ∧
                        orgSignal M ((y, false, astar, M.lam), ω) i k = s}.ncard +
                      (if a.2.1 i = true ∧ 0 < a.2.2 i ∧ a.1 = s then
                        {k | (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / a.2.2 i ≤ 1/2}.ncard else 0) := by
                    intro a s; rfl
                  have hsc : ∀ a : AAction 2, sc a ω i = if countA M ((y, false, a, M.lam), ω) i (1/2) State.S <
                      countA M ((y, false, a, M.lam), ω) i (1/2) State.R then 1 else 0 := fun a => rfl
                  have hmono : ∀ (p q p' q' : ℕ), p ≤ p' → q' ≤ q →
                      ((if p' < q' then 1 else 0 : ℝ)) ≤ (if p < q then 1 else 0) := by
                    intro p q p' q' h1 h2
                    by_cases hc : p' < q'
                    · rw [if_pos hc, if_pos (by omega)]
                    · rw [if_neg hc]; split_ifs <;> norm_num
                  have hA_S : countA M ((y, false, astar, M.lam), ω) i (1/2) State.S =
                      {k | orgArrival ((y, false, astar, M.lam), ω) i k ≤ 1/2 ∧
                        orgSignal M ((y, false, astar, M.lam), ω) i k = State.S}.ncard := by
                    rw [hcnt]; simp [astar]
                  have hA_R : countA M ((y, false, astar, M.lam), ω) i (1/2) State.R =
                      {k | orgArrival ((y, false, astar, M.lam), ω) i k ≤ 1/2 ∧
                        orgSignal M ((y, false, astar, M.lam), ω) i k = State.R}.ncard +
                      {k | (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2}.ncard := by
                    rw [hcnt]; simp [astar]
                  rw [hsc a', hsc astar, hA_S, hA_R, hcnt a' State.S, hcnt a' State.R]
                  cases hb : a'.2.1 i
                  · simp only [Bool.false_eq_true, false_and, if_false, add_zero]
                    by_cases hE : 1/2 < ω.1 (i,0) ∧ ω.2.1 (i,0) ≤ 1
                    · have hemp : ∀ s, {k | orgArrival ((y, false, astar, M.lam), ω) i k ≤ 1/2 ∧
                          orgSignal M ((y, false, astar, M.lam), ω) i k = s} = ∅ := by
                        intro s; ext k
                        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
                        intro hk; exfalso
                        have : ω.1 (i,0) ≤ ∑ l ∈ Finset.range (k+1), ω.1 (i,l) :=
                          Finset.single_le_sum (f := fun l => ω.1 (i,l)) (fun l _ => hnn l)
                            (Finset.mem_range.2 (by omega))
                        have hk' : (∑ l ∈ Finset.range (k+1), ω.1 (i,l)) / 1 ≤ 1/2 := hk
                        rw [div_one] at hk'; linarith [hE.1]
                      have hpos : 0 < {k | (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2}.ncard :=
                        (Set.ncard_pos hfin).2 ⟨0, by
                          show (∑ l ∈ Finset.range 1, ω.2.1 (i,l)) / 2 ≤ 1/2
                          simp only [Finset.sum_range_one]; linarith [hE.2]⟩
                      have hEi : Eind i ω = 1 := if_pos hE
                      rw [hemp, hemp, hEi, Set.ncard_empty, if_neg (lt_irrefl 0), if_pos (by omega)]
                      norm_num
                    · have hEi : Eind i ω = 0 := if_neg hE
                      rw [hEi, add_zero]
                      exact hmono _ _ _ _ le_rfl (Nat.le_add_right _ _)
                  · simp only [if_true, add_zero]
                    have hadm := ha' i hb
                    refine hmono _ _ _ _ (Nat.le_add_right _ _) ?_
                    split_ifs with hc
                    · refine Nat.add_le_add_left (Set.ncard_le_ncard (fun k hk => ?_) hfin) _
                      have hr : 0 < a'.2.2 i := hc.2.1
                      have hr2 : a'.2.2 i ≤ 2 := hadm.2
                      have hk' : (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / a'.2.2 i ≤ 1/2 := hk
                      show (∑ l ∈ Finset.range (k+1), ω.2.1 (i,l)) / 2 ≤ 1/2
                      rw [div_le_iff₀ hr] at hk'
                      rw [div_le_iff₀ (by norm_num)]
                      nlinarith
                    · omega
                have hPE : ∀ i, 1/10 ≤ ∫ ω, Eind i ω ∂(baseMeasure 2) := by
                  intro i
                  have hS : MeasurableSet {ω : Base 2 | 1/2 < ω.1 (i,0) ∧ ω.2.1 (i,0) ≤ 1} := by
                    refine MeasurableSet.inter ?_ ?_
                    · exact measurableSet_lt measurable_const ((measurable_pi_apply _).comp measurable_fst)
                    · exact measurableSet_le ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)) measurable_const
                  have heq : Eind i = Set.indicator {ω : Base 2 | 1/2 < ω.1 (i,0) ∧ ω.2.1 (i,0) ≤ 1} 1 := by
                    funext ω; simp only [Eind, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
                  rw [heq, integral_indicator_one hS]
                  have hset : {ω : Base 2 | 1/2 < ω.1 (i,0) ∧ ω.2.1 (i,0) ≤ 1} =
                      ((fun x => x (i,0)) ⁻¹' Set.Ioi (1/2)) ×ˢ (((fun x => x (i,0)) ⁻¹' Set.Iic 1) ×ˢ Set.univ) := by
                    ext ω; simp
                  have hIoi : ProbabilityTheory.expMeasure 1 (Set.Ioi (1/2)) = ENNReal.ofReal (Real.exp (-(1/2))) := by
                    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic _ (by norm_num),
                      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith [Real.exp_le_one_iff.2 (show -(1/2:ℝ) ≤ 0 by norm_num)])]
                    congr 1; ring
                  rw [Measure.real, hset, hbm, Measure.prod_prod, Measure.prod_prod, hPi _ _ measurableSet_Ioi,
                    hPi _ _ measurableSet_Iic, hIoi, hIic 1 zero_le_one]
                  simp only [measure_univ, mul_one]
                  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
                    ENNReal.toReal_ofReal (by linarith [Real.exp_le_one_iff.2 (show -(1:ℝ) ≤ 0 by norm_num)])]
                  have e1 : -(1/2:ℝ) + 1 ≤ Real.exp (-(1/2)) := Real.add_one_le_exp _
                  have e2 : (1:ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp _
                  have e3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
                  have e4 : 0 < Real.exp (-1) := Real.exp_pos _
                  have e5 : Real.exp (-1) ≤ 1/2 := by nlinarith
                  nlinarith
                have hcmp : ∀ i, ∫ ω, sc a' ω i ∂(baseMeasure 2) +
                    (if a'.2.1 i = true then 0 else ∫ ω, Eind i ω ∂(baseMeasure 2)) ≤
                    ∫ ω, sc astar ω i ∂(baseMeasure 2) := by
                  intro i
                  have h1 : ∫ ω, sc a' ω i + (if a'.2.1 i = true then 0 else Eind i ω) ∂(baseMeasure 2) ≤
                      ∫ ω, sc astar ω i ∂(baseMeasure 2) := by
                    refine integral_mono_ae ?_ (hint astar i) (hgood.mono fun ω hω => hpt ω hω i)
                    split_ifs
                    · simpa using hint a' i
                    · exact (hint a' i).add (hEint i)
                  refine le_trans (le_of_eq ?_) h1
                  split_ifs
                  · simp
                  · rw [integral_add (hint a' i) (hEint i)]
                rw [hpay, hpay]
                rw [integral_finsetSum _ (fun i _ => hint a' i), integral_finsetSum _ (fun i _ => hint astar i)]
                simp only [Finset.card_filter, Fin.sum_univ_two] at hcmp ⊢
                have h0 := hcmp 0
                have h1 := hcmp 1
                have e0 := hPE 0
                have e1 := hPE 1
                have hst : ∀ i, astar.2.1 i = true := fun _ => rfl
                cases hb0 : a'.2.1 0 <;> cases hb1 : a'.2.1 1 <;>
                  simp only [hb0, hb1, hst, if_true, Bool.false_eq_true, if_false] at h0 h1 ⊢ <;>
                  norm_num at h0 h1 ⊢ <;> linarith
              have hEq : AIsEquilibrium M (1 / 2) σP R σA := by
                refine ⟨⟨hOp, fun t _ i hi => by simp [M] at hi⟩, ?_, fun i hi => by simp [M] at hi,
                  fun y => ⟨?_, ?_, ?_⟩⟩
                · intro i _ π
                  dsimp only [σA, σD]
                  refine ⟨⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩,
                    fun h => if_pos (by norm_num [M] at h; linarith),
                    fun h => if_neg (by norm_num [M] at h; linarith)⟩
                · show IsProbabilityMeasure (Measure.dirac astar); infer_instance
                · show Measure.dirac astar _ = 0
                  rw [Measure.dirac_apply]
                  simp [Set.indicator, AAction.Admissible, astar, M]
                · show ∀ᵐ a ∂(Measure.dirac astar), _
                  rw [ae_dirac_eq]
                  exact Filter.eventually_pure.mpr (hopt y)
              refine ⟨M, hStanding, hA2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
                hαpos, hθpos, ?_, σP, R, σA, hEq, ?_⟩
              · exact hfZ
              · simp [σP, astar]
