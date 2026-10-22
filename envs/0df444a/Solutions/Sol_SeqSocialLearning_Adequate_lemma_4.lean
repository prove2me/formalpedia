-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:51:15.718735+00:00
-- url     : https://prove2.me/submissions/63994082-ae3e-4395-81bc-6da63f757076

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Beliefs

open MeasureTheory ProbabilityTheory Filter Topology
open scoped symmDiff

namespace SSLLem4Aux

variable {T S : Type*} [MeasurableSpace T] [MeasurableSpace S]

/-- Sets of `T × S` measurable with respect to some finite measurable product partition. -/
def PSet : Set (Set (T × S)) :=
  {s | ∃ (n₁ n₂ : ℕ) (i : T → Fin n₁) (j : S → Fin n₂), Measurable i ∧ Measurable j ∧
    ∃ W : Set (Fin n₁ × Fin n₂), s = (fun z => (i z.1, j z.2)) ⁻¹' W}

lemma mem_PSet_of {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (i : T → α) (j : S → β) (hi : Measurable i) (hj : Measurable j)
    (W : Set (α × β)) : (fun z : T × S => (i z.1, j z.2)) ⁻¹' W ∈ (PSet : Set (Set (T × S))) := by
  classical
  let e₁ := Fintype.equivFin α
  let e₂ := Fintype.equivFin β
  refine ⟨Fintype.card α, Fintype.card β, e₁ ∘ i, e₂ ∘ j, ?_, ?_,
    {p | (e₁.symm p.1, e₂.symm p.2) ∈ W}, ?_⟩
  · exact (measurable_of_countable _).comp hi
  · exact (measurable_of_countable _).comp hj
  · ext z; simp

lemma PSet_measurable {s : Set (T × S)} (hs : s ∈ (PSet : Set (Set (T × S)))) :
    MeasurableSet s := by
  obtain ⟨n₁, n₂, i, j, hi, hj, W, rfl⟩ := hs
  exact ((hi.comp measurable_fst).prodMk (hj.comp measurable_snd)) (Set.toFinite W).measurableSet

lemma PSet_combine {s t : Set (T × S)} (hs : s ∈ (PSet : Set (Set (T × S))))
    (ht : t ∈ (PSet : Set (Set (T × S)))) (op : Prop → Prop → Prop) :
    {z | op (z ∈ s) (z ∈ t)} ∈ (PSet : Set (Set (T × S))) := by
  classical
  obtain ⟨n₁, n₂, i, j, hi, hj, W, rfl⟩ := hs
  obtain ⟨m₁, m₂, i', j', hi', hj', W', rfl⟩ := ht
  have := mem_PSet_of (T := T) (S := S) (fun x => (i x, i' x)) (fun y => (j y, j' y))
    (hi.prodMk hi') (hj.prodMk hj')
    {p | op ((p.1.1, p.2.1) ∈ W) ((p.1.2, p.2.2) ∈ W')}
  convert this using 1
  ext z; rfl

lemma isSetRing_PSet : IsSetRing (PSet : Set (Set (T × S))) where
  empty_mem := by
    have := mem_PSet_of (T := T) (S := S) (fun _ => ()) (fun _ => ()) measurable_const
      measurable_const ∅
    simpa using this
  union_mem := fun s t hs ht => PSet_combine hs ht (· ∨ ·)
  sdiff_mem := fun s t hs ht => PSet_combine hs ht (fun a b => a ∧ ¬ b)

lemma univ_mem_PSet : (Set.univ : Set (T × S)) ∈ (PSet : Set (Set (T × S))) := by
  have := mem_PSet_of (T := T) (S := S) (fun _ => ()) (fun _ => ()) measurable_const
    measurable_const Set.univ
  simpa using this

open Classical in
lemma measurable_decide_mem {X : Type*} [MeasurableSpace X] {s : Set X} (hs : MeasurableSet s) :
    Measurable (fun x => decide (x ∈ s)) := by
  classical
  refine measurable_to_countable' fun b => ?_
  cases b
  · convert hs.compl using 1; ext x; simp
  · convert hs using 1; ext x; simp

lemma generate_PSet :
    (Prod.instMeasurableSpace : MeasurableSpace (T × S)) =
      MeasurableSpace.generateFrom (PSet : Set (Set (T × S))) := by
  classical
  apply le_antisymm
  · rw [← generateFrom_prod]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨s, hs, t, ht, rfl⟩
    have := mem_PSet_of (T := T) (S := S) (fun x => decide (x ∈ s)) (fun y => decide (y ∈ t))
      (measurable_decide_mem hs) (measurable_decide_mem ht) {(true, true)}
    convert this using 1
    ext z; simp [Set.mem_prod]
  · exact MeasurableSpace.generateFrom_le fun s hs => PSet_measurable hs

lemma approx_PSet (ν : Measure (T × S)) [IsFiniteMeasure ν] {C : Set (T × S)}
    (hC : MeasurableSet C) {δ : ENNReal} (hδ : 0 < δ) :
    ∃ R ∈ (PSet : Set (Set (T × S))), ν (R ∆ C) < δ :=
  exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_PSet
    ⟨{Set.univ}, Set.countable_singleton _, by simpa using univ_mem_PSet, by simp⟩
    generate_PSet hC hδ

lemma simple_to_partition {A : Type*} [MeasurableSpace A] [Nonempty A]
    (ν : Measure (T × S)) [IsFiniteMeasure ν]
    (f : SimpleFunc (T × S) A) {δ : ENNReal} (hδ : 0 < δ) :
    ∃ (n₁ n₂ : ℕ) (i : T → Fin n₁) (j : S → Fin n₂) (g : Fin n₁ → Fin n₂ → A),
      Measurable i ∧ Measurable j ∧ ν {z | g (i z.1) (j z.2) ≠ f z} ≤ δ := by
  classical
  set R := f.range with hR
  set N := R.card with hN
  have hδ' : 0 < δ / (N + 1) := ENNReal.div_pos hδ.ne' (by simp)
  have hC : ∀ b : R, MeasurableSet (f ⁻¹' {(b : A)}) := fun b => f.measurableSet_fiber _
  choose Rb hRb hRbν using fun b : R => approx_PSet ν (hC b) hδ'
  choose n₁ n₂ i j hi hj W hW using hRb
  let I : T → (Π b : R, Fin (n₁ b)) := fun t b => i b t
  let J : S → (Π b : R, Fin (n₂ b)) := fun s b => j b s
  have hI : Measurable I := measurable_pi_lambda _ fun b => hi b
  have hJ : Measurable J := measurable_pi_lambda _ fun b => hj b
  let G : (Π b : R, Fin (n₁ b)) → (Π b : R, Fin (n₂ b)) → A := fun x y =>
    if h : ∃ b : R, (x b, y b) ∈ W b then (h.choose : A) else Classical.arbitrary A
  let e₁ := Fintype.equivFin (Π b : R, Fin (n₁ b))
  let e₂ := Fintype.equivFin (Π b : R, Fin (n₂ b))
  refine ⟨_, _, e₁ ∘ I, e₂ ∘ J, fun k l => G (e₁.symm k) (e₂.symm l),
    (measurable_of_countable _).comp hI, (measurable_of_countable _).comp hJ, ?_⟩
  have hsub : {z : T × S | (fun k l => G (e₁.symm k) (e₂.symm l)) ((e₁ ∘ I) z.1) ((e₂ ∘ J) z.2)
      ≠ f z} ⊆ ⋃ b : R, Rb b ∆ (f ⁻¹' {(b : A)}) := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have key : ∀ b : R, z ∈ Rb b ↔ f z = b := by
      intro b
      have h1 := hcon b
      rw [Set.mem_symmDiff] at h1
      push Not at h1
      constructor
      · intro h; exact h1.1 h
      · intro h; exact h1.2 (by simp [h])
    let b0 : R := ⟨f z, f.mem_range_self z⟩
    have hex : ∃ b : R, (I z.1 b, J z.2 b) ∈ W b := by
      refine ⟨b0, ?_⟩
      have : z ∈ Rb b0 := (key b0).2 rfl
      rw [hW b0] at this
      exact this
    simp only [Function.comp_apply, Equiv.symm_apply_apply, G, Set.mem_ofPred_eq] at hz
    rw [dif_pos hex] at hz
    apply hz
    have hm : z ∈ Rb hex.choose := by rw [hW]; exact hex.choose_spec
    exact ((key _).1 hm).symm
  calc _ ≤ ν (⋃ b : R, Rb b ∆ (f ⁻¹' {(b : A)})) := measure_mono hsub
    _ ≤ ∑ b : R, ν (Rb b ∆ (f ⁻¹' {(b : A)})) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _b : R, δ / (N + 1) := Finset.sum_le_sum fun b _ => (hRbν b).le
    _ = N * (δ / (N + 1)) := by simp [hN]
    _ ≤ (N + 1) * (δ / (N + 1)) := by gcongr; exact le_self_add
    _ = δ := ENNReal.mul_div_cancel (by simp) (by simp)

end SSLLem4Aux

open SeqSocialLearning.Adequate SSLLem4Aux

theorem solution {Ω A S T : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [StandardBorelSpace T]
    (lam : Measure (Ω × T × S)) [IsProbabilityMeasure lam]
    (u : A → Ω → ℝ) (hu : InU u) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n₁ n₂ : ℕ) (i : T → Fin n₁) (j : S → Fin n₂) (g : Fin n₁ → Fin n₂ → A),
      Measurable i ∧ Measurable j ∧
        decisionValue lam u - ε ≤ ∫ z, u (g (i z.2.1) (j z.2.2)) z.1 ∂lam := by
  classical
  obtain ⟨hmeas, ⟨M, hM⟩, hcont⟩ := hu
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary A) (Classical.arbitrary Ω))
  -- integrability of payoffs of measurable strategies
  have hint : ∀ f : Ω × T × S → A, Measurable f →
      Integrable (fun z => u (f z) z.1) lam := fun f hf =>
    Integrable.of_bound (hmeas.comp (hf.prodMk measurable_fst)).aestronglyMeasurable M
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _ _)
  have hle : ∀ f : Ω × T × S → A, Measurable f → ∫ z, u (f z) z.1 ∂lam ≤ M := by
    intro f hf
    calc ∫ z, u (f z) z.1 ∂lam ≤ ∫ _z, M ∂lam :=
          integral_mono (hint f hf) (integrable_const M) fun z => (le_abs_self _).trans (hM _ _)
      _ = M := by simp
  set V : {τ : T × S → A // Measurable τ} → ℝ :=
    fun τ => ∫ z, u (τ.1 (z.2.1, z.2.2)) z.1 ∂lam with hV
  have hbdd : BddAbove (Set.range V) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨τ, rfl⟩
    exact hle _ (τ.2.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd)))
  have : Nonempty {τ : T × S → A // Measurable τ} :=
    ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩
  obtain ⟨τ, hτ⟩ := exists_lt_of_lt_ciSup (f := V)
    (show decisionValue lam u - ε / 3 < decisionValue lam u by linarith)
  -- step 2: approximate `τ` by simple functions
  have hsm : StronglyMeasurable τ.1 := τ.2.stronglyMeasurable
  set fs := hsm.approx
  have hmz : Measurable (fun z : Ω × T × S => (z.2.1, z.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  have hlim : Tendsto (fun n => ∫ z, u (fs n (z.2.1, z.2.2)) z.1 ∂lam) atTop (𝓝 (V τ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n =>
      (hmeas.comp (((fs n).measurable.comp hmz).prodMk measurable_fst)).aestronglyMeasurable)
      (integrable_const M) (fun n => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact hM _ _) (ae_of_all _ fun z => ?_)
    exact ((hcont z.1).tendsto _).comp (hsm.tendsto_approx _)
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds
    (show decisionValue lam u - 2 * ε / 3 < V τ by linarith))).exists
  -- step 3: replace the simple function by a product-partition strategy
  set ν : Measure (T × S) := lam.map (fun z => (z.2.1, z.2.2))
  have hδ : 0 < ENNReal.ofReal (ε / (3 * (2 * M + 1))) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨n₁, n₂, i, j, g, hi, hj, hbad⟩ := simple_to_partition ν (fs n) hδ
  refine ⟨n₁, n₂, i, j, g, hi, hj, ?_⟩
  have hgm : Measurable (fun w : T × S => g (i w.1) (j w.2)) :=
    measurable_of_countable (fun p : Fin n₁ × Fin n₂ => g p.1 p.2) |>.comp
      ((hi.comp measurable_fst).prodMk (hj.comp measurable_snd))
  set bad : Set (T × S) := {w | g (i w.1) (j w.2) ≠ fs n w}
  have hbadm : MeasurableSet bad := (measurableSet_eq_fun hgm (fs n).measurable).compl
  set bad' := (fun z : Ω × T × S => (z.2.1, z.2.2)) ⁻¹' bad
  have hbad'm : MeasurableSet bad' := hmz hbadm
  have hlam : lam.real bad' ≤ ε / (3 * (2 * M + 1)) := by
    have h1 : lam bad' = ν bad := (Measure.map_apply hmz hbadm).symm
    rw [measureReal_def, h1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hdiff : ∫ z, u (fs n (z.2.1, z.2.2)) z.1 ∂lam - ∫ z, u (g (i z.2.1) (j z.2.2)) z.1 ∂lam
      ≤ 2 * M * lam.real bad' := by
    have hI1 : Integrable (fun z : Ω × T × S => u (fs n (z.2.1, z.2.2)) z.1) lam :=
      hint _ ((fs n).measurable.comp hmz)
    have hI2 : Integrable (fun z : Ω × T × S => u (g (i z.2.1) (j z.2.2)) z.1) lam :=
      hint _ (hgm.comp hmz)
    rw [← integral_sub hI1 hI2]
    calc _ ≤ ∫ z, bad'.indicator (fun _ => 2 * M) z ∂lam := by
          refine integral_mono (hI1.sub hI2) ((integrable_const _).indicator hbad'm) fun z => ?_
          by_cases hz : z ∈ bad'
          · rw [Set.indicator_of_mem hz]
            have h1 := hM (fs n (z.2.1, z.2.2)) z.1
            have h2 := hM (g (i z.2.1) (j z.2.2)) z.1
            rw [abs_le] at h1 h2
            linarith
          · rw [Set.indicator_of_notMem hz]
            have : g (i z.2.1) (j z.2.2) = fs n (z.2.1, z.2.2) := by
              by_contra h; exact hz h
            simp [this]
      _ = 2 * M * lam.real bad' := by
          rw [integral_indicator_const _ hbad'm, smul_eq_mul, mul_comm]
  have hfin : 2 * M * lam.real bad' ≤ ε / 3 := by
    calc 2 * M * lam.real bad' ≤ 2 * M * (ε / (3 * (2 * M + 1))) := by gcongr
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  linarith
