-- Prove2me | solution 1 for RapidRatePoisson.WeakConv.thinned_compensator
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:11:21.624595+00:00
-- url     : https://prove2.me/submissions/465210cb-c2d1-4285-9c1d-e29330e9527e

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open RapidRatePoisson.WeakConv

namespace RRPComp

/-- The trace σ-algebra trick: sets `C` with `E ∩ C ∈ H`. -/
def restrictMS {Ω : Type*} (H : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet[H] E) :
    MeasurableSpace Ω where
  MeasurableSet' C := MeasurableSet[H] (E ∩ C)
  measurableSet_empty := by simp
  measurableSet_compl C hC := by
    have : E ∩ Cᶜ = E \ (E ∩ C) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    show MeasurableSet[H] (E ∩ Cᶜ)
    rw [this]; exact hE.diff hC
  measurableSet_iUnion f hf := by
    show MeasurableSet[H] (E ∩ ⋃ i, f i)
    rw [Set.inter_iUnion]; exact MeasurableSet.iUnion hf

/-- Integral of an `m₁`-measurable function over a set of an independent σ-algebra. -/
lemma setIntegral_of_indep {Ω : Type*} {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[m₁] Y) (hYi : Integrable Y μ) (hind : Indep m₁ m₂ μ) {D : Set Ω}
    (hD : MeasurableSet[m₂] D) :
    ∫ x in D, Y x ∂μ = μ.real D * ∫ x, Y x ∂μ := by
  rw [← setIntegral_condExp hle₂ hYi hD]
  rw [setIntegral_congr_ae (hle₂ _ hD)
    ((condExp_indep_eq hle₁ hle₂ hY hind).mono fun x hx _ => hx)]
  rw [setIntegral_const, smul_eq_mul]

/-- A family of σ-algebras indexed by `Option ℕ`: `none ↦ m0`, `some j ↦ mj j`, is independent
when `mj` is independent and `⨆ j, mj j`-type information `mβ` is independent of `m0`. -/
lemma iIndep_option {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m0 mβ : MeasurableSpace Ω) (mj : ℕ → MeasurableSpace Ω) (hj : ∀ j, mj j ≤ mβ)
    (hind : iIndep mj μ) (h0 : Indep mβ m0 μ) :
    iIndep (fun k : Option ℕ => Option.elim k m0 mj) μ := by
  classical
  rw [iIndep_iff]
  intro s f hf
  have hD : MeasurableSet[mβ] (⋂ j ∈ s.eraseNone, f (some j)) := by
    refine Finset.measurableSet_biInter _ fun j hjs => ?_
    exact hj j _ (hf (some j) (Finset.mem_eraseNone.mp hjs))
  have hDμ : μ (⋂ j ∈ s.eraseNone, f (some j)) = ∏ j ∈ s.eraseNone, μ (f (some j)) := by
    rw [iIndep_iff] at hind
    exact hind _ fun j hj => hf (some j) (Finset.mem_eraseNone.mp hj)
  by_cases hn : none ∈ s
  · have hset : (⋂ i ∈ s, f i) = (⋂ j ∈ s.eraseNone, f (some j)) ∩ f none := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_eraseNone]
      constructor
      · intro h; exact ⟨fun j hj => h _ hj, h _ hn⟩
      · rintro ⟨h1, h2⟩ (_ | j) hi
        · exact h2
        · exact h1 j hi
    have hs : s = Finset.insertNone s.eraseNone := by
      rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hn]
    rw [hset, (Indep_iff _ _ _).mp h0 _ _ hD (hf none hn), hDμ]
    conv_rhs => rw [hs, Finset.prod_insertNone]
    ring
  · have hset : (⋂ i ∈ s, f i) = (⋂ j ∈ s.eraseNone, f (some j)) := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_eraseNone]
      constructor
      · intro h j hj; exact h _ hj
      · rintro h (_ | j) hi
        · exact absurd hi hn
        · exact h j hi
    have hs : s = (s.eraseNone).map Function.Embedding.some := by
      rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hn]
    rw [hset, hDμ]
    conv_rhs => rw [hs, Finset.prod_map]
    rfl


lemma preimage_ite_meas {Ω : Type*} {H : MeasurableSpace Ω} (P : Ω → Prop) [DecidablePred P]
    (hp : MeasurableSet[H] {ω | P ω}) {f g : Ω → ℕ} (hf : ∀ S, MeasurableSet[H] (f ⁻¹' S))
    (hg : ∀ S, MeasurableSet[H] (g ⁻¹' S)) (S : Set ℕ) :
    MeasurableSet[H] ((fun ω => if P ω then f ω else g ω) ⁻¹' S) := by
  have : (fun ω => if P ω then f ω else g ω) ⁻¹' S =
      ({ω | P ω} ∩ f ⁻¹' S) ∪ ({ω | P ω}ᶜ ∩ g ⁻¹' S) := by
    ext ω; by_cases h : P ω <;> simp [h]
  rw [this]; exact (hp.inter (hf S)).union (hp.compl.inter (hg S))

lemma preimage_const_meas {Ω : Type*} {H : MeasurableSpace Ω} (c : ℕ) (S : Set ℕ) :
    MeasurableSet[H] ((fun _ : Ω => c) ⁻¹' S) := by
  by_cases h : c ∈ S
  · have : (fun _ : Ω => c) ⁻¹' S = Set.univ := by ext; simp [h]
    rw [this]; exact MeasurableSet.univ
  · have : (fun _ : Ω => c) ⁻¹' S = ∅ := by ext; simp [h]
    rw [this]; exact MeasurableSet.empty

lemma preimage_of_comap_le {Ω : Type*} {H : MeasurableSpace Ω} {f : Ω → ℕ}
    (h : MeasurableSpace.comap f ⊤ ≤ H) (S : Set ℕ) : MeasurableSet[H] (f ⁻¹' S) :=
  h _ ⟨S, MeasurableSpace.measurableSet_top, rfl⟩

lemma comap_le_of_preimage {Ω : Type*} {H : MeasurableSpace Ω} {f : Ω → ℕ}
    (h : ∀ S, MeasurableSet[H] (f ⁻¹' S)) : MeasurableSpace.comap f ⊤ ≤ H := by
  rintro _ ⟨S, -, rfl⟩; exact h S

/-- the observation code of mark `i` at time `t`. -/
noncomputable def code {Ω : Type*} (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε t : ℝ≥0) (i : ℕ)
    (ω : Ω) : ℕ :=
  if 1 ≤ i ∧ (i : ℝ) ≤ N (t / ε) ω then (if β i ω then 1 else 0) else 2

lemma gSigma_eq {Ω : Type*} {m : MeasurableSpace Ω} (F : Filtration ℝ≥0 m) (N : ℝ≥0 → Ω → ℝ)
    (β : ℕ → Ω → Bool) (ε t : ℝ≥0) :
    gSigma F N β ε t = F (t / ε) ⊔ ⨆ i : ℕ, MeasurableSpace.comap (code N β ε t i) ⊤ := rfl

lemma code_meas {Ω : Type*} {H : MeasurableSpace Ω} (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool)
    (ε t : ℝ≥0) (i : ℕ) (hN : MeasurableSet[H] {ω | (i : ℝ) ≤ N (t / ε) ω})
    (hβ : 1 ≤ i → MeasurableSet[H] {ω | β i ω = true}) (S : Set ℕ) :
    MeasurableSet[H] (code N β ε t i ⁻¹' S) := by
  classical
  by_cases hi : 1 ≤ i
  · have hc : code N β ε t i = fun ω => if (i : ℝ) ≤ N (t / ε) ω then
        (if β i ω = true then 1 else 0) else 2 := by
      funext ω; simp [code, hi]
    rw [hc]
    refine preimage_ite_meas _ hN ?_ (preimage_const_meas 2) S
    intro S'
    exact preimage_ite_meas _ (hβ hi) (preimage_const_meas 1) (preimage_const_meas 0) S'
  · have hc : code N β ε t i = fun _ => 2 := by funext ω; simp [code, hi]
    rw [hc]; exact preimage_const_meas 2 S

lemma gSigma_le_of {Ω : Type*} {m : MeasurableSpace Ω} (F : Filtration ℝ≥0 m) (N : ℝ≥0 → Ω → ℝ)
    (β : ℕ → Ω → Bool) (ε t : ℝ≥0) {X : MeasurableSpace Ω} (h1 : F (t / ε) ≤ X)
    (h2 : ∀ i S, MeasurableSet[X] (code N β ε t i ⁻¹' S)) : gSigma F N β ε t ≤ X := by
  rw [gSigma_eq]
  exact sup_le h1 (iSup_le fun i => comap_le_of_preimage (h2 i))


/-- Step B: a martingale increment integrates to zero over every set of `F a ⊔ mβ`, when `mβ` is
independent of `F ∞`. -/
lemma stepB {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (mβ : MeasurableSpace Ω)
    (hmβ : mβ ≤ m) (hind : Indep mβ (⨆ t, F t) P) (a b : ℝ≥0) (hab : a ≤ b) :
    ∀ C, MeasurableSet[F a ⊔ mβ] C → ∫ ω in C, (M b ω - M a ω) ∂P = 0 := by
  set X : Ω → ℝ := fun ω => M b ω - M a ω with hXdef
  have hXi : Integrable X P := (hM.integrable b).sub (hM.integrable a)
  have hle : F a ⊔ mβ ≤ m := sup_le (F.le a) hmβ
  have hBasic : ∀ B, MeasurableSet[F a] B → ∫ ω in B, X ω ∂P = 0 := by
    intro B hB
    have hB' : MeasurableSet[m] B := F.le a _ hB
    rw [integral_sub (hM.integrable b).integrableOn (hM.integrable a).integrableOn]
    rw [← setIntegral_condExp (F.le a) (hM.integrable b) hB]
    rw [setIntegral_congr_ae (μ := P) hB' ((hM.2 a b hab).mono fun x hx _ => hx)]
    simp
  have hXmeas : StronglyMeasurable[⨆ t, F t] X :=
    ((hM.1 b).mono (le_iSup (fun t => F t) b)).sub ((hM.1 a).mono (le_iSup (fun t => F t) a))
  have hBD : ∀ B D, MeasurableSet[F a] B → MeasurableSet[mβ] D → ∫ ω in B ∩ D, X ω ∂P = 0 := by
    intro B D hB hD
    have hB' : MeasurableSet[m] B := F.le a _ hB
    rw [Set.inter_comm, ← setIntegral_indicator hB']
    rw [setIntegral_of_indep (iSup_le fun t => F.le t) hmβ
      (hXmeas.indicator (le_iSup (fun t => F t) a _ hB)) (hXi.indicator hB') hind.symm hD]
    rw [integral_indicator hB', hBasic B hB, mul_zero]
  let S : Set (Set Ω) := {s | ∃ B D, MeasurableSet[F a] B ∧ MeasurableSet[mβ] D ∧ s = B ∩ D}
  have h_eq : F a ⊔ mβ = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · apply sup_le
      · intro B hB
        apply MeasurableSpace.measurableSet_generateFrom
        exact ⟨B, Set.univ, hB, MeasurableSet.univ, by simp⟩
      · intro D hD
        apply MeasurableSpace.measurableSet_generateFrom
        exact ⟨Set.univ, D, MeasurableSet.univ, hD, by simp⟩
    · apply MeasurableSpace.generateFrom_le
      rintro _ ⟨B, D, hB, hD, rfl⟩
      exact (le_sup_left (a := F a) (b := mβ) _ hB).inter (le_sup_right (a := F a) (b := mβ) _ hD)
  have h_pi : IsPiSystem S := by
    rintro _ ⟨B1, D1, hB1, hD1, rfl⟩ _ ⟨B2, D2, hB2, hD2, rfl⟩ _
    exact ⟨B1 ∩ B2, D1 ∩ D2, hB1.inter hB2, hD1.inter hD2, Set.inter_inter_inter_comm _ _ _ _⟩
  intro C hC
  refine MeasurableSpace.induction_on_inter (m := F a ⊔ mβ)
    (C := fun C _ => ∫ ω in C, X ω ∂P = 0) h_eq h_pi ?_ ?_ ?_ ?_ C hC
  · simp
  · rintro _ ⟨B, D, hB, hD, rfl⟩
    exact hBD B D hB hD
  · intro t htm ih
    have h1 := integral_add_compl (hle _ htm) hXi
    have h2 := hBasic Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at h2
    linarith
  · intro f hd hfm hf
    rw [integral_iUnion (fun i => hle _ (hfm i)) hd hXi.integrableOn]
    simp [hf]


/-- Step A, one term: the `i`-th mark is independent of everything observed in `G s`
on the event that it has not yet been observed. -/
lemma stepA_term {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε : ℝ≥0)
    (hNad : ∀ t, Measurable[F t] (N t)) (hβ : IsBernoulliSeq P ε β)
    (hβF : Indep (MeasurableSpace.comap (markSeq β) inferInstance) (⨆ t, F t) P)
    (s t : ℝ≥0) (i : ℕ) (hi : 1 ≤ i) (C : Set Ω)
    (hC : MeasurableSet[gSigma F N β ε s] C) :
    ∫ ω in C, ({ω | N (s / ε) ω < i} ∩ {ω | (i : ℝ) ≤ N (t / ε) ω}).indicator
        (fun ω => if β i ω = true then (1 : ℝ) else 0) ω ∂P
      = ε * P.real (C ∩ ({ω | N (s / ε) ω < i} ∩ {ω | (i : ℝ) ≤ N (t / ε) ω})) := by
  classical
  set a := s / ε
  set b := t / ε
  let mo : Option ℕ → MeasurableSpace Ω := fun k =>
    Option.elim k (⨆ u, F u) (fun j => MeasurableSpace.comap (β (j + 1)) inferInstance)
  have hj : ∀ j, MeasurableSpace.comap (β (j + 1)) inferInstance ≤
      MeasurableSpace.comap (markSeq β) inferInstance := by
    intro j
    have : β (j + 1) = (fun x : ℕ → Bool => x j) ∘ markSeq β := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply j).comap_le
  have hind : iIndep (fun j => MeasurableSpace.comap (β (j + 1)) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).mp hβ.2.1
  have hiI : iIndep mo P := iIndep_option _ _ _ hj hind hβF
  have hle_mo : ∀ k, mo k ≤ m := by
    rintro (_ | j)
    · exact iSup_le fun u => F.le u
    · exact (hβ.1 j).comap_le
  set T : Set (Option ℕ) := ({some (i - 1)} : Set (Option ℕ))ᶜ with hT
  set H : MeasurableSpace Ω := ⨆ k ∈ T, mo k with hH
  have hHle : H ≤ m := iSup₂_le fun k _ => hle_mo k
  have hindep : Indep (MeasurableSpace.comap (β i) inferInstance) H P := by
    have h := indep_iSup_of_disjoint hle_mo hiI (S := {some (i - 1)}) (T := T)
      disjoint_compl_right
    rw [iSup_singleton] at h
    have e : mo (some (i - 1)) = MeasurableSpace.comap (β i) inferInstance := by
      show MeasurableSpace.comap (β (i - 1 + 1)) inferInstance = _
      rw [Nat.sub_add_cancel hi]
    rw [e] at h; exact h
  have hFH : ∀ u, F u ≤ H := by
    intro u
    refine (le_iSup (fun u => F u) u).trans ?_
    exact le_iSup₂ (f := fun k (_ : k ∈ T) => mo k) none (by simp [T])
  have hβH : ∀ j, 1 ≤ j → j ≠ i → MeasurableSet[H] {ω | β j ω = true} := by
    intro j hj1 hji
    have hmem : some (j - 1) ∈ T := by simp [T]; omega
    have hle : mo (some (j - 1)) ≤ H := le_iSup₂ (f := fun k (_ : k ∈ T) => mo k) _ hmem
    apply hle
    show MeasurableSet[MeasurableSpace.comap (β (j - 1 + 1)) inferInstance] _
    rw [Nat.sub_add_cancel hj1]
    exact ⟨{true}, measurableSet_singleton true, rfl⟩
  set E : Set Ω := {ω | N a ω < i} with hEdef
  have hE : MeasurableSet[H] E := hFH a _ (measurableSet_lt (hNad a) measurable_const)
  have hGR : gSigma F N β ε s ≤ restrictMS H E hE := by
    apply gSigma_le_of
    · intro B hB
      show MeasurableSet[H] (E ∩ B)
      exact hE.inter (hFH a _ hB)
    · intro j S
      show MeasurableSet[H] (E ∩ code N β ε s j ⁻¹' S)
      by_cases hji : j = i
      · subst hji
        have : E ∩ code N β ε s j ⁻¹' S = E ∩ ((fun _ : Ω => 2) ⁻¹' S) := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage, hEdef, Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            have : ¬ (1 ≤ j ∧ (j : ℝ) ≤ N (s / ε) ω) := fun h => absurd h.2 (not_le.mpr h1)
            simpa [code, this] using h2
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            have : ¬ (1 ≤ j ∧ (j : ℝ) ≤ N (s / ε) ω) := fun h => absurd h.2 (not_le.mpr h1)
            simpa [code, this] using h2
        rw [this]; exact hE.inter (preimage_const_meas 2 S)
      · exact hE.inter (code_meas N β ε s j (hFH a _ (measurableSet_le measurable_const (hNad a)))
          (fun hj => hβH j hj hji) S)
  have hCH : MeasurableSet[H] (E ∩ C) := hGR C hC
  have hD : MeasurableSet[H] (C ∩ (E ∩ {ω | (i : ℝ) ≤ N b ω})) := by
    have : C ∩ (E ∩ {ω | (i : ℝ) ≤ N b ω}) = (E ∩ C) ∩ {ω | (i : ℝ) ≤ N b ω} := by
      ext; simp only [Set.mem_inter_iff]; tauto
    rw [this]
    exact hCH.inter (hFH b _ (measurableSet_le measurable_const (hNad b)))
  have hDm : MeasurableSet[m] (E ∩ {ω | (i : ℝ) ≤ N b ω}) :=
    (F.le a _ (measurableSet_lt (hNad a) measurable_const)).inter
      (F.le b _ (measurableSet_le measurable_const (hNad b)))
  have hβi : Measurable[m] (β i) := by
    have := hβ.1 (i - 1); rwa [Nat.sub_add_cancel hi] at this
  have hβis : MeasurableSet[m] {ω | β i ω = true} := hβi (measurableSet_singleton true)
  have hYeq : (fun ω => if β i ω = true then (1 : ℝ) else 0) =
      {ω | β i ω = true}.indicator 1 := by
    funext ω; by_cases h : β i ω = true <;> simp [h]
  have hYm : StronglyMeasurable[MeasurableSpace.comap (β i) inferInstance]
      (fun ω => if β i ω = true then (1 : ℝ) else 0) := by
    have hg : Measurable (fun x : Bool => if x = true then (1 : ℝ) else 0) := measurable_from_top
    exact (hg.comp (comap_measurable (β i))).stronglyMeasurable
  have hYi : Integrable (fun ω => if β i ω = true then (1 : ℝ) else 0) P := by
    rw [hYeq]
    exact (integrable_const (1 : ℝ)).indicator hβis
  rw [setIntegral_indicator hDm]
  rw [setIntegral_of_indep (hβi.comap_le) hHle hYm hYi hindep hD]
  rw [hYeq, integral_indicator_one hβis]
  have hP : P {ω | β i ω = true} = (ε : ℝ≥0∞) := by
    have := hβ.2.2 (i - 1); rwa [Nat.sub_add_cancel hi] at this
  rw [measureReal_def P {ω | β i ω = true}, hP]
  simp [mul_comm]


lemma window_sum (g : ℕ → ℝ) (p q K : ℕ) (hpq : p ≤ q) (hqK : q ≤ K) :
    ∑ i ∈ Finset.Icc 1 K, (if p < i ∧ i ≤ q then g i else 0) =
      ∑ i ∈ Finset.Icc 1 q, g i - ∑ i ∈ Finset.Icc 1 p, g i := by
  rw [← Finset.sum_filter]
  have h1 : (Finset.Icc 1 K).filter (fun i => p < i ∧ i ≤ q) = Finset.Ioc p q := by
    ext i; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have h2 : Finset.Icc 1 q = Finset.Icc 1 p ∪ Finset.Ioc p q := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have h3 : Disjoint (Finset.Icc 1 p) (Finset.Ioc p q) := by
    rw [Finset.disjoint_left]; intro i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h2, Finset.sum_union h3]
  ring

lemma thinned_eq_sum {Ω : Type*} (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε t : ℝ≥0) (ω : Ω) :
    thinned N β ε t ω =
      ∑ i ∈ Finset.Icc 1 ⌊N (t / ε) ω⌋₊, (if β i ω = true then (1 : ℝ) else 0) := by
  simp only [thinned, Finset.card_filter]
  push_cast
  rfl

/-- Step A: summing over the marks. -/
lemma stepA {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε : ℝ≥0)
    (hNad : ∀ t, Measurable[F t] (N t)) (hβ : IsBernoulliSeq P ε β)
    (hβF : Indep (MeasurableSpace.comap (markSeq β) inferInstance) (⨆ t, F t) P)
    (hNnat : ∀ t ω, ∃ k : ℕ, N t ω = k) (hNmono : ∀ ω, Monotone fun t => N t ω)
    (hNint : ∀ t, Integrable (N t) P) (hε : 0 < ε)
    (s t : ℝ≥0) (hst : s ≤ t) (C : Set Ω)
    (hC : MeasurableSet[gSigma F N β ε s] C) :
    ∫ ω in C, (thinned N β ε t ω - thinned N β ε s ω) ∂P =
      ε * ∫ ω in C, (N (t / ε) ω - N (s / ε) ω) ∂P := by
  classical
  set a := s / ε with ha
  set b := t / ε with hb
  have hab : a ≤ b := div_le_div_of_nonneg_right hst (le_of_lt hε)
  let D : ℕ → Set Ω := fun i => {ω | N a ω < i} ∩ {ω | (i : ℝ) ≤ N b ω}
  let Y : ℕ → Ω → ℝ := fun i ω => if β i ω = true then (1 : ℝ) else 0
  have hDm : ∀ i, MeasurableSet[m] (D i) := fun i =>
    (F.le a _ (measurableSet_lt (hNad a) measurable_const)).inter
      (F.le b _ (measurableSet_le measurable_const (hNad b)))
  have hYm : ∀ i, 1 ≤ i → Measurable[m] (Y i) := by
    intro i hi
    have hβi : Measurable[m] (β i) := by
      have := hβ.1 (i - 1); rwa [Nat.sub_add_cancel hi] at this
    have hg : Measurable (fun x : Bool => if x = true then (1 : ℝ) else 0) := measurable_from_top
    exact hg.comp hβi
  have hYb : ∀ i ω, ‖Y i ω‖ ≤ 1 := by
    intro i ω; by_cases h : β i ω = true <;> simp [Y, h]
  have hYi : ∀ i, 1 ≤ i → Integrable (Y i) P := fun i hi =>
    Integrable.of_bound (hYm i hi).aestronglyMeasurable 1 (Eventually.of_forall (hYb i))
  let T : ℕ → Ω → ℝ := fun K ω => ∑ i ∈ Finset.Icc 1 K, (D i).indicator (Y i) ω
  let U : ℕ → Ω → ℝ := fun K ω => ∑ i ∈ Finset.Icc 1 K, (D i).indicator (fun _ => (1 : ℝ)) ω
  have hTint : ∀ K, Integrable (T K) P := fun K =>
    integrable_finset_sum _ fun i hi =>
      (hYi i (Finset.mem_Icc.mp hi).1).indicator (hDm i)
  have hUint : ∀ K, Integrable (U K) P := fun K =>
    integrable_finset_sum _ fun i _ => (integrable_const (1 : ℝ)).indicator (hDm i)
  have hTU : ∀ K, ∫ ω in C, T K ω ∂P = ε * ∫ ω in C, U K ω ∂P := by
    intro K
    simp only [T, U]
    rw [integral_finset_sum _ fun i hi => ((hYi i (Finset.mem_Icc.mp hi).1).indicator
      (hDm i)).restrict]
    rw [integral_finset_sum _ fun i _ => ((integrable_const (1 : ℝ)).indicator
      (hDm i)).restrict]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := stepA_term (P := P) F N β ε hNad hβ hβF s t i (Finset.mem_Icc.mp hi).1 C hC
    rw [h1, setIntegral_indicator (hDm i), setIntegral_const, smul_eq_mul, mul_one]
  -- pointwise identification of the limits
  have hpt : ∀ ω, ∀ K, ⌊N b ω⌋₊ ≤ K →
      T K ω = thinned N β ε t ω - thinned N β ε s ω ∧ U K ω = N b ω - N a ω := by
    intro ω K hK
    obtain ⟨p, hp⟩ := hNnat a ω
    obtain ⟨q, hq⟩ := hNnat b ω
    have hpq : p ≤ q := by
      have : N a ω ≤ N b ω := hNmono ω hab
      rw [hp, hq] at this; exact_mod_cast this
    have hq' : ⌊N b ω⌋₊ = q := by rw [hq, Nat.floor_natCast]
    have hp' : ⌊N a ω⌋₊ = p := by rw [hp, Nat.floor_natCast]
    rw [hq'] at hK
    have hind : ∀ (f : Ω → ℝ) (i : ℕ), (D i).indicator f ω =
        if p < i ∧ i ≤ q then f ω else 0 := by
      intro f i
      simp only [D, Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq, hp, hq,
        Nat.cast_lt, Nat.cast_le]
    constructor
    · simp only [T, hind]
      rw [window_sum (fun i => Y i ω) p q K hpq hK, thinned_eq_sum, thinned_eq_sum]
      rw [← ha, ← hb, hp', hq']
    · simp only [U, hind]
      rw [window_sum (fun _ => (1 : ℝ)) p q K hpq hK]
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, hp, hq]
      push_cast; ring
  have hTmono : ∀ ω, Monotone fun K => T K ω := by
    intro ω K K' hKK'
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hKK')
    intro i _ _
    apply Set.indicator_nonneg
    intro x _; by_cases h : β i x = true <;> simp [Y, h]
  have hUmono : ∀ ω, Monotone fun K => U K ω := by
    intro ω K K' hKK'
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hKK')
    intro i _ _
    apply Set.indicator_nonneg
    intro x _; norm_num
  have hthin_int : ∀ u, Integrable (thinned N β ε u) P := by
    intro u
    refine Integrable.mono' (hNint (u / ε)) ?_ (Eventually.of_forall fun ω => ?_)
    · have hmeas : ∀ k : ℕ, Measurable[m] fun ω =>
          ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0) := fun k =>
        Finset.measurable_sum _ fun i hi => hYm i (Finset.mem_Icc.mp hi).1
      have hF : Measurable fun p : Ω × ℕ =>
          ∑ i ∈ Finset.Icc 1 p.2, (if β i p.1 = true then (1 : ℝ) else 0) :=
        measurable_from_prod_countable_left (fun k => hmeas k)
      have hn : Measurable[m] fun ω => ⌊N (u / ε) ω⌋₊ :=
        ((hNad (u / ε)).mono (F.le _) le_rfl).nat_floor
      have heq : thinned N β ε u = (fun p : Ω × ℕ =>
          ∑ i ∈ Finset.Icc 1 p.2, (if β i p.1 = true then (1 : ℝ) else 0)) ∘
          (fun ω => (ω, ⌊N (u / ε) ω⌋₊)) := by
        funext ω; exact thinned_eq_sum N β ε u ω
      rw [heq]
      exact (hF.comp (measurable_id.prodMk hn)).aestronglyMeasurable
    · obtain ⟨k, hk⟩ := hNnat (u / ε) ω
      rw [thinned_eq_sum, hk, Nat.floor_natCast, Real.norm_eq_abs]
      have h0 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun i _ => by by_cases h : β i ω = true <;> simp [h]
      rw [abs_of_nonneg h0]
      calc ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0)
          ≤ ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by by_cases h : β i ω = true <;> simp [h]
        _ = k := by simp
  have hlimT := integral_tendsto_of_tendsto_of_monotone (μ := P.restrict C)
    (fun K => (hTint K).restrict) (((hthin_int t).sub (hthin_int s)).restrict)
    (Eventually.of_forall hTmono)
    (Eventually.of_forall fun ω => tendsto_atTop_of_eventually_const
      (fun K hK => (hpt ω K hK).1))
  have hlimU := integral_tendsto_of_tendsto_of_monotone (μ := P.restrict C)
    (fun K => (hUint K).restrict) (((hNint b).sub (hNint a)).restrict)
    (Eventually.of_forall hUmono)
    (Eventually.of_forall fun ω => tendsto_atTop_of_eventually_const
      (fun K hK => (hpt ω K hK).2))
  have hlimU' := hlimU.const_mul (ε : ℝ)
  have : (fun K => ∫ ω in C, T K ω ∂P) = fun K => (ε : ℝ) * ∫ ω in C, U K ω ∂P :=
    funext hTU
  rw [this] at hlimT
  exact tendsto_nhds_unique hlimT hlimU'


lemma thinned_meas_of {Ω : Type*} [H : MeasurableSpace Ω] (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool)
    (ε t : ℝ≥0) (hNnn : ∀ ω, 0 ≤ N (t / ε) ω) (hn : Measurable fun ω => ⌊N (t / ε) ω⌋₊)
    (hc : ∀ i S, MeasurableSet (code N β ε t i ⁻¹' S)) : Measurable (thinned N β ε t) := by
  classical
  have hk : ∀ k : ℕ, Measurable fun ω =>
      ∑ i ∈ Finset.Icc 1 k, (if code N β ε t i ω = 1 then (1 : ℝ) else 0) := by
    intro k
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite (hc i {1}) measurable_const measurable_const
  have hF : Measurable fun p : Ω × ℕ =>
      ∑ i ∈ Finset.Icc 1 p.2, (if code N β ε t i p.1 = 1 then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left (fun k => hk k)
  have heq : thinned N β ε t = (fun p : Ω × ℕ =>
      ∑ i ∈ Finset.Icc 1 p.2, (if code N β ε t i p.1 = 1 then (1 : ℝ) else 0)) ∘
      (fun ω => (ω, ⌊N (t / ε) ω⌋₊)) := by
    funext ω
    rw [thinned_eq_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi2 : (i : ℝ) ≤ N (t / ε) ω := by
      have h1 : (i : ℝ) ≤ (⌊N (t / ε) ω⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).2
      exact h1.trans (Nat.floor_le (hNnn ω))
    simp only [Function.comp, code, hi1, hi2, and_self, if_true]
    by_cases h : β i ω = true <;> simp [h]
  rw [heq]
  exact hF.comp (measurable_id.prodMk hn)

lemma thinned_integrable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε u : ℝ≥0)
    (hNm : Measurable (N (u / ε))) (hβm : ∀ i, 1 ≤ i → Measurable (β i))
    (hNnat : ∀ ω, ∃ k : ℕ, N (u / ε) ω = k) (hNint : Integrable (N (u / ε)) P) :
    Integrable (thinned N β ε u) P := by
  classical
  refine Integrable.mono' hNint ?_ (Eventually.of_forall fun ω => ?_)
  · have hmeas : ∀ k : ℕ, Measurable fun ω =>
        ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0) := fun k =>
      Finset.measurable_sum _ fun i hi =>
        Measurable.ite (hβm i (Finset.mem_Icc.mp hi).1 (measurableSet_singleton true))
          measurable_const measurable_const
    have hF : Measurable fun p : Ω × ℕ =>
        ∑ i ∈ Finset.Icc 1 p.2, (if β i p.1 = true then (1 : ℝ) else 0) :=
      measurable_from_prod_countable_left (fun k => hmeas k)
    have heq : thinned N β ε u = (fun p : Ω × ℕ =>
        ∑ i ∈ Finset.Icc 1 p.2, (if β i p.1 = true then (1 : ℝ) else 0)) ∘
        (fun ω => (ω, ⌊N (u / ε) ω⌋₊)) := by
      funext ω; exact thinned_eq_sum N β ε u ω
    rw [heq]
    exact (hF.comp (measurable_id.prodMk hNm.nat_floor)).aestronglyMeasurable
  · obtain ⟨k, hk⟩ := hNnat ω
    rw [thinned_eq_sum, hk, Nat.floor_natCast, Real.norm_eq_abs]
    have h0 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun i _ => by by_cases h : β i ω = true <;> simp [h]
    rw [abs_of_nonneg h0]
    calc ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0)
        ≤ ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by by_cases h : β i ω = true <;> simp [h]
      _ = k := by simp

end RRPComp

open RRPComp in
theorem solution {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ)
    (hN : ∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω))
    (hA : IsCompensator F P N A) (hNint : ∀ t, Integrable (N t) P)
    (ε : ℝ≥0) (hε : 0 < ε) (hε1 : ε ≤ 1) (β : ℕ → Ω → Bool) (hβ : IsBernoulliSeq P ε β)
    (hβF : Indep (MeasurableSpace.comap (markSeq β) inferInstance) (⨆ t, F t) P) :
    ∃ G : Filtration ℝ≥0 m, (∀ t, G t = gSigma F N β ε t) ∧
      IsCompensator G P (thinned N β ε) (scaledComp A ε) := by
  classical
  obtain ⟨hA0, hAmono, hArc, hApred, hMart⟩ := hA
  have hAad : ∀ t, StronglyMeasurable[F t] (A t) := hApred.stronglyAdapted
  have hMad : ∀ t, StronglyMeasurable[F t] (fun ω => N t ω - A t ω) := hMart.1
  have hNad : ∀ t, Measurable[F t] (N t) := by
    intro t
    have : N t = (fun ω => N t ω - A t ω) + A t := by funext ω; simp
    rw [this]; exact ((hMad t).add (hAad t)).measurable
  have hNnat : ∀ t ω, ∃ k : ℕ, N t ω = k := fun t ω => (hN ω).2.1 t
  have hNmono : ∀ ω, Monotone (fun t => N t ω) := fun ω => (hN ω).2.2.1
  have hNnn : ∀ t ω, 0 ≤ N t ω := by
    intro t ω; obtain ⟨k, hk⟩ := hNnat t ω; rw [hk]; positivity
  have hβm : ∀ i, 1 ≤ i → Measurable (β i) := by
    intro i hi
    have := hβ.1 (i - 1)
    rwa [Nat.sub_add_cancel hi] at this
  have hβset : ∀ i, 1 ≤ i → MeasurableSet {ω | β i ω = true} :=
    fun i hi => hβm i hi (measurableSet_singleton true)
  have hNset : ∀ (H : MeasurableSpace Ω) (u : ℝ≥0) (x : ℝ), F u ≤ H →
      MeasurableSet[H] {ω | x ≤ N u ω} :=
    fun H u x h => h _ (measurableSet_le measurable_const (hNad u))
  -- the codes at time `t` are `gSigma t`-measurable
  have hcodeG : ∀ t i S, MeasurableSet[gSigma F N β ε t] (code N β ε t i ⁻¹' S) := by
    intro t i S
    apply preimage_of_comap_le
    rw [gSigma_eq]
    exact le_sup_of_le_right (le_iSup (fun i => MeasurableSpace.comap (code N β ε t i) ⊤) i)
  have hFG : ∀ t, F (t / ε) ≤ gSigma F N β ε t := fun t => by rw [gSigma_eq]; exact le_sup_left
  have hmonoG : Monotone (gSigma F N β ε) := by
    intro s t hst
    have hst' : s / ε ≤ t / ε := div_le_div_of_nonneg_right hst (le_of_lt hε)
    apply gSigma_le_of
    · exact (F.mono hst').trans (hFG t)
    · intro i S
      have hc : code N β ε s i = fun ω => if 1 ≤ i ∧ (i : ℝ) ≤ N (s / ε) ω then
          code N β ε t i ω else 2 := by
        funext ω
        by_cases h : 1 ≤ i ∧ (i : ℝ) ≤ N (s / ε) ω
        · have h' : 1 ≤ i ∧ (i : ℝ) ≤ N (t / ε) ω := ⟨h.1, h.2.trans (hNmono ω hst')⟩
          simp [code, h, h']
        · simp [code, h]
      rw [hc]
      refine preimage_ite_meas _ ?_ (hcodeG t i) (preimage_const_meas 2) S
      by_cases hi : 1 ≤ i
      · simp only [hi, true_and]
        exact hNset _ _ _ ((F.mono hst').trans (hFG t))
      · simp [hi]
  have hleG : ∀ t, gSigma F N β ε t ≤ m := by
    intro t
    apply gSigma_le_of
    · exact F.le _
    · intro i S
      exact code_meas N β ε t i (hNset m _ _ (F.le _)) (hβset i) S
  let G : Filtration ℝ≥0 m := ⟨gSigma F N β ε, hmonoG, hleG⟩
  have hpredG : IsStronglyPredictable G (scaledComp A ε) := by
    have hφ : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) G.predictable F.predictable
        (fun p => (p.1 / ε, p.2)) := by
      rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
      refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
      · intro B hB
        show MeasurableSet[G.predictable] ((fun p : ℝ≥0 × Ω => (p.1 / ε, p.2)) ⁻¹' ({⊥} ×ˢ B))
        have : (fun p : ℝ≥0 × Ω => (p.1 / ε, p.2)) ⁻¹' ({⊥} ×ˢ B) = {⊥} ×ˢ B := by
          ext ⟨u, ω⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, bot_eq_zero',
            div_eq_zero_iff, hε.ne', or_false]
        rw [this]
        apply measurableSet_predictable_singleton_bot_prod
        have : (⊥ : ℝ≥0) = ⊥ / ε := by simp
        exact hFG ⊥ _ (by rw [← this]; exact hB)
      · intro i B hB
        show MeasurableSet[G.predictable] ((fun p : ℝ≥0 × Ω => (p.1 / ε, p.2)) ⁻¹'
          (Set.Ioi i ×ˢ B))
        have : (fun p : ℝ≥0 × Ω => (p.1 / ε, p.2)) ⁻¹' (Set.Ioi i ×ˢ B) =
            Set.Ioi (i * ε) ×ˢ B := by
          ext ⟨u, ω⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
          rw [lt_div_iff₀ hε]
        rw [this]
        apply measurableSet_predictable_Ioi_prod
        have : i * ε / ε = i := by field_simp
        exact hFG (i * ε) _ (by rw [this]; exact hB)
    have h1 := hApred.comp_measurable hφ
    have h2 := h1.const_mul (ε : ℝ)
    exact h2
  have hAint : ∀ u, Integrable (A u) P := by
    intro u
    have := (hNint u).sub (hMart.integrable u)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  have hthin : ∀ u, Integrable (thinned N β ε u) P := fun u =>
    thinned_integrable N β ε u ((hNad (u / ε)).mono (F.le _) le_rfl) hβm (hNnat (u / ε))
      (hNint (u / ε))
  have hXint : ∀ u, Integrable (fun ω => thinned N β ε u ω - scaledComp A ε u ω) P := by
    intro u
    exact (hthin u).sub ((hAint (u / ε)).const_mul (ε : ℝ))
  have hXad : ∀ u, StronglyMeasurable[G u] (fun ω => thinned N β ε u ω - scaledComp A ε u ω) := by
    intro u
    have h1 : Measurable[G u] (thinned N β ε u) := by
      apply @thinned_meas_of Ω (G u) N β ε u (fun ω => hNnn _ ω)
      · exact (Nat.measurable_floor (R := ℝ)).comp ((hNad (u / ε)).mono (hFG u) le_rfl)
      · exact hcodeG u
    exact h1.stronglyMeasurable.sub (hpredG.stronglyAdapted u)
  have hmβ : MeasurableSpace.comap (markSeq β) inferInstance ≤ m := by
    apply Measurable.comap_le
    rw [measurable_pi_iff]; intro j; exact hβ.1 j
  have hGK : ∀ u, gSigma F N β ε u ≤ F (u / ε) ⊔ MeasurableSpace.comap (markSeq β) inferInstance := by
    intro u
    apply gSigma_le_of
    · exact le_sup_left
    · intro i S
      refine code_meas (H := F (u / ε) ⊔ MeasurableSpace.comap (markSeq β) inferInstance)
        N β ε u i (le_sup_left (a := F (u / ε))
          (b := MeasurableSpace.comap (markSeq β) inferInstance) _
        (measurableSet_le measurable_const (hNad _))) ?_ S
      intro hi
      apply le_sup_right (a := F (u / ε)) (b := MeasurableSpace.comap (markSeq β) inferInstance)
      refine ⟨{x | x (i - 1) = true}, ?_, ?_⟩
      · exact (measurable_pi_apply (X := fun _ : ℕ => Bool) (i - 1)) (measurableSet_singleton true)
      · ext ω; simp [markSeq, Nat.sub_add_cancel hi]
  refine ⟨G, fun t => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; simp [scaledComp, hA0]
  · intro ω a b hab
    simp only [scaledComp]
    exact mul_le_mul_of_nonneg_left (hAmono ω (div_le_div_of_nonneg_right hab (le_of_lt hε)))
      (by positivity)
  · intro ω t
    have hcont : Continuous fun s : ℝ≥0 => s / ε := by
      simp_rw [div_eq_mul_inv]; exact continuous_id.mul continuous_const
    have hT : Tendsto (fun s : ℝ≥0 => s / ε) (𝓝[≥] t) (𝓝[≥] (t / ε)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (hcont.tendsto t).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact div_le_div_of_nonneg_right hs (le_of_lt hε)
    have := ((hArc ω (t / ε)).tendsto.comp hT).const_mul (ε : ℝ)
    exact this
  · exact hpredG
  · refine ⟨hXad, ?_⟩
    intro s t hst
    refine (ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hXint t)
      (fun C _ _ => (hXint s).integrableOn) ?_ (hXad s).aestronglyMeasurable).symm
    intro C hC _
    have hCm : MeasurableSet[m] C := G.le s _ hC
    have hab : s / ε ≤ t / ε := div_le_div_of_nonneg_right hst (le_of_lt hε)
    have hAs := stepA (P := P) F N β ε hNad hβ hβF hNnat hNmono hNint hε s t hst C hC
    have hBs := stepB (P := P) F (fun u ω => N u ω - A u ω) hMart _ hmβ hβF (s / ε) (t / ε) hab C
      (hGK s C hC)
    simp only [scaledComp]
    rw [integral_sub (hthin s).integrableOn ((hAint _).const_mul (ε : ℝ)).integrableOn,
      integral_sub (hthin t).integrableOn ((hAint _).const_mul (ε : ℝ)).integrableOn,
      integral_const_mul, integral_const_mul]
    rw [integral_sub (hthin t).integrableOn (hthin s).integrableOn,
      integral_sub (hNint _).integrableOn (hNint _).integrableOn] at hAs
    have hMi : ∀ u, Integrable (fun ω => N u ω - A u ω) P := fun u => (hNint u).sub (hAint u)
    rw [integral_sub (hMi _).integrableOn (hMi _).integrableOn,
      integral_sub (hNint _).integrableOn (hAint _).integrableOn,
      integral_sub (hNint _).integrableOn (hAint _).integrableOn] at hBs
    linear_combination (-1 : ℝ) * hAs + (-(ε : ℝ)) * hBs
