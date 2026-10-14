-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.hanneke_learner_pac
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:58:40.560501+00:00
-- url     : https://prove2.me/submissions/bdb63538-2e8e-4600-9f7e-057e3214fb84

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm
import Theorems.Thm_OptimalPAC_SampleComplexity_consistent_error_bound

set_option autoImplicit false

-- ##### from b1bc7e99_infra.lean #####


open MeasureTheory

namespace OptimalPAC.SampleComplexity

open scoped ENNReal

/-- (C) block split of the i.i.d. sample. -/
theorem b1_split_mp {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (a b : ℕ) :
    MeasurePreserving (fun x : Fin (a + b) → X =>
        ((fun i : Fin a => x (Fin.castAdd b i)), (fun j : Fin b => x (Fin.natAdd a j))))
      (Measure.pi fun _ : Fin (a + b) => P)
      ((Measure.pi fun _ : Fin a => P).prod (Measure.pi fun _ : Fin b => P)) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (a + b) => P)
    (finSumFinEquiv (m := a) (n := b))).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Fin a ⊕ Fin b => X) (fun _ => P)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft]

/-- Fubini upper bound: if every section has measure `≤ η` then so does the set. -/
theorem b1_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν]
    (s : Set (α × β)) (hs : MeasurableSet s) (η : ℝ≥0∞)
    (h : ∀ a, ν (Prod.mk a ⁻¹' s) ≤ η) : (μ.prod ν) s ≤ η := by
  rw [Measure.prod_apply hs]
  calc ∫⁻ a, ν (Prod.mk a ⁻¹' s) ∂μ ≤ ∫⁻ _, η ∂μ := lintegral_mono h
    _ = η := by simp

/-- Fubini upper bound, sections in the first coordinate. -/
theorem b1_prod_le' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    (s : Set (α × β)) (hs : MeasurableSet s) (η : ℝ≥0∞)
    (h : ∀ b, μ ((fun a => (a, b)) ⁻¹' s) ≤ η) : (μ.prod ν) s ≤ η := by
  rw [Measure.prod_apply_symm hs]
  calc ∫⁻ b, μ ((fun a => (a, b)) ⁻¹' s) ∂ν ≤ ∫⁻ _, η ∂ν := lintegral_mono h
    _ = η := by simp

/-! ### Measurability of the learner as a function of the sample -/

/-- A list-valued map of constant length `n` with measurable entries. -/
def LMeasN {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (n : ℕ)
    (F : Y → List (X × Bool)) : Prop :=
  ∃ g : Y → Fin n → X × Bool, Measurable g ∧ ∀ y, F y = List.ofFn (g y)

theorem lm_length {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    {F : Y → List (X × Bool)} (h : LMeasN n F) (y : Y) : (F y).length = n := by
  obtain ⟨g, -, e⟩ := h; simp [e]

theorem lm_const {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (T : List (X × Bool)) :
    LMeasN (Y := Y) T.length (fun _ => T) :=
  ⟨fun _ => T.get, measurable_const, fun _ => by simp⟩

theorem lm_comp {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {n : ℕ} {F : Y → List (X × Bool)} (h : LMeasN n F) {φ : Z → Y} (hφ : Measurable φ) :
    LMeasN n (fun z => F (φ z)) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun z => g (φ z), hg.comp hφ, fun z => e (φ z)⟩

theorem lm_append {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n₁ n₂ : ℕ}
    {F G : Y → List (X × Bool)} (h₁ : LMeasN n₁ F) (h₂ : LMeasN n₂ G) :
    LMeasN (n₁ + n₂) (fun y => F y ++ G y) := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨fun y => Fin.append (g₁ y) (g₂ y), ?_, fun y => ?_⟩
  · rw [measurable_pi_iff]
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]; exact (measurable_pi_apply j).comp hg₁
    · simp only [Fin.append_right]; exact (measurable_pi_apply j).comp hg₂
  · dsimp only
    rw [e₁, e₂, List.ofFn_add]
    simp [Fin.append_left, Fin.append_right]

theorem lm_take {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    {F : Y → List (X × Bool)} (h : LMeasN n F) (k : ℕ) :
    LMeasN (min k n) (fun y => (F y).take k) := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun y i => g y (Fin.castLE (min_le_right k n) i),
    measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp hg), fun y => ?_⟩
  dsimp only
  rw [e]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem lm_drop {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    {F : Y → List (X × Bool)} (h : LMeasN n F) (k : ℕ) :
    LMeasN (n - k) (fun y => (F y).drop k) := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun y i => g y ⟨k + i, by omega⟩,
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (⟨k + i, by omega⟩ : Fin n)).comp hg),
    fun y => ?_⟩
  dsimp only
  rw [e]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem lm_labeled {X : Type*} [MeasurableSpace X] (f : X → Bool) (hf : Measurable f) (m : ℕ) :
    LMeasN m (fun x : Fin m → X => labeled f x) :=
  ⟨fun x i => (x i, f (x i)),
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).prodMk (hf.comp (measurable_pi_apply i))),
    fun _ => rfl⟩

/-- A list of lists of constant length whose members are `LMeasN`. -/
def LLMeas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (R : Y → List (List (X × Bool))) : Prop :=
  ∃ k, ∃ R' : Fin k → Y → List (X × Bool), (∀ i, ∃ n, LMeasN n (R' i)) ∧
    ∀ y, R y = List.ofFn (fun i => R' i y)

theorem llm_single {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    {F : Y → List (X × Bool)} (h : LMeasN n F) : LLMeas (fun y => [F y]) :=
  ⟨1, fun _ => F, fun _ => ⟨n, h⟩, fun y => by simp⟩

theorem llm_append {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {R₁ R₂ : Y → List (List (X × Bool))} (h₁ : LLMeas R₁) (h₂ : LLMeas R₂) :
    LLMeas (fun y => R₁ y ++ R₂ y) := by
  obtain ⟨k₁, R₁', h₁', e₁⟩ := h₁
  obtain ⟨k₂, R₂', h₂', e₂⟩ := h₂
  refine ⟨k₁ + k₂, Fin.append R₁' R₂', fun i => ?_, fun y => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using h₁' j
    · simpa only [Fin.append_right] using h₂' j
  · dsimp only
    rw [e₁, e₂, List.ofFn_add]
    simp [Fin.append_left, Fin.append_right]

theorem llm_subsamples {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    ∀ n : ℕ, ∀ (F G : Y → List (X × Bool)), LMeasN n F → (∃ n', LMeasN n' G) →
      LLMeas (fun y => subsamples (F y) (G y)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F G hF hG
  obtain ⟨n', hG⟩ := hG
  by_cases hn : n ≤ 3
  · have key : (fun y => subsamples (F y) (G y)) = fun y => [F y ++ G y] := by
      funext y
      rw [subsamples.eq_1]
      simp [lm_length hF y, hn]
    rw [key]
    exact llm_single (lm_append hF hG)
  · set q := n / 4 with hq
    have key : (fun y => subsamples (F y) (G y)) = fun y =>
        subsamples ((F y).take (n - 3 * q))
            (((F y).drop (n - 2 * q)).take q ++ (F y).drop (n - q) ++ G y) ++
          subsamples ((F y).take (n - 3 * q))
            (((F y).drop (n - 3 * q)).take q ++ (F y).drop (n - q) ++ G y) ++
          subsamples ((F y).take (n - 3 * q))
            (((F y).drop (n - 3 * q)).take q ++ ((F y).drop (n - 2 * q)).take q ++ G y) := by
      funext y
      rw [subsamples.eq_1]
      simp only [lm_length hF y, hn, if_false, hq]
    rw [key]
    have hlt : min (n - 3 * q) n < n := by omega
    have h0 := lm_take hF (n - 3 * q)
    have hrec : ∀ G' : Y → List (X × Bool), (∃ n'', LMeasN n'' G') →
        LLMeas (fun y => subsamples ((F y).take (n - 3 * q)) (G' y)) :=
      fun G' hG' => ih _ hlt _ G' h0 hG'
    exact llm_append (llm_append
      (hrec _ ⟨_, lm_append (lm_append (lm_take (lm_drop hF _) _) (lm_drop hF _)) hG⟩)
      (hrec _ ⟨_, lm_append (lm_append (lm_take (lm_drop hF _) _) (lm_drop hF _)) hG⟩))
      (hrec _ ⟨_, lm_append (lm_append (lm_take (lm_drop hF _) _) (lm_take (lm_drop hF _) _)) hG⟩)

theorem majority_eq_vals {X : Type*} (hs : List (X → Bool)) (x : X) :
    majority hs x = decide ((hs.map (fun h => h x)).countP (fun c => c = false) ≤
      (hs.map (fun h => h x)).countP (fun c => c = true)) := by
  simp [majority, List.countP_map, Function.comp_def]

theorem llm_majority {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (L : List (X × Bool) → X → Bool) (hLm : LearnerMeasurable L)
    {R : Y → List (List (X × Bool))} (hR : LLMeas R) :
    Measurable (fun p : Y × X => majority ((R p.1).map L) p.2) := by
  obtain ⟨k, R', hR', e⟩ := hR
  have hi : ∀ i, Measurable (fun p : Y × X => L (R' i p.1) p.2) := by
    intro i
    obtain ⟨n, g, hg, eg⟩ := hR' i
    have := (hLm n).comp ((hg.comp measurable_fst).prodMk measurable_snd)
    convert this using 1
    funext p
    simp [eg]
  have hV : Measurable (fun p : Y × X => fun i : Fin k => L (R' i p.1) p.2) :=
    measurable_pi_lambda _ hi
  let Φ : (Fin k → Bool) → Bool := fun v =>
    decide ((List.ofFn v).countP (fun c => c = false) ≤ (List.ofFn v).countP (fun c => c = true))
  have hΦ : Measurable Φ := measurable_of_countable Φ
  convert hΦ.comp hV using 1
  funext p
  simp only [Function.comp_apply, Φ, e, majority_eq_vals, List.map_ofFn, Function.comp_def]

theorem meas_er {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (P : Measure X)
    [IsProbabilityMeasure P] (f : X → Bool) (hf : Measurable f) (h : Y → X → Bool)
    (hh : Measurable (fun p : Y × X => h p.1 p.2)) :
    Measurable (fun y => er P (h y) f) := by
  have hs : MeasurableSet {p : Y × X | h p.1 p.2 ≠ f p.2} := by
    have hc : MeasurableSet {q : Bool × Bool | q.1 ≠ q.2} := (Set.to_countable _).measurableSet
    exact (hh.prodMk (hf.comp measurable_snd)) hc
  exact (measurable_measure_prodMk_left (ν := P) hs).ennreal_toReal

/-- The learner `hannekeLearner L (labeled f x) T` is jointly measurable in `(sample, point)`. -/
theorem meas_hanneke {X : Type*} [MeasurableSpace X]
    (L : List (X × Bool) → X → Bool) (hLm : LearnerMeasurable L) (f : X → Bool) (hf : Measurable f)
    (m : ℕ) (T : List (X × Bool)) :
    Measurable (fun p : (Fin m → X) × X => hannekeLearner L (labeled f p.1) T p.2) :=
  llm_majority L hLm (llm_subsamples m _ _ (lm_labeled f hf m) ⟨_, lm_const T⟩)

end OptimalPAC.SampleComplexity

-- ##### from b1bc7e99_struct.lean #####


open MeasureTheory

namespace OptimalPAC.SampleComplexity

theorem b1_subsamples_split {X : Type*} (S0 S1 S2 S3 T : List (X × Bool)) (q : ℕ)
    (h1 : S1.length = q) (h2 : S2.length = q) (h3 : S3.length = q)
    (hq : (S0.length + q + q + q) / 4 = q) (hbig : 3 < S0.length + q + q + q) :
    subsamples (S0 ++ S1 ++ S2 ++ S3) T =
      subsamples S0 (S2 ++ S3 ++ T) ++ subsamples S0 (S1 ++ S3 ++ T) ++
        subsamples S0 (S1 ++ S2 ++ T) := by
  have hlen : (S0 ++ S1 ++ S2 ++ S3).length = S0.length + q + q + q := by
    simp [h1, h2, h3]; omega
  rw [subsamples, if_neg (by omega), hlen, hq]
  have e0 : S0.length + q + q + q - 3 * q = S0.length := by omega
  have e2 : S0.length + q + q + q - 2 * q = S0.length + q := by omega
  have e3 : S0.length + q + q + q - q = S0.length + q + q := by omega
  rw [e0, e2, e3]
  have t0 : (S0 ++ S1 ++ S2 ++ S3).take S0.length = S0 := by
    rw [List.append_assoc, List.append_assoc]; exact List.take_left' rfl
  have d1 : (S0 ++ S1 ++ S2 ++ S3).drop S0.length = S1 ++ S2 ++ S3 := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc]; exact List.drop_left' rfl
  have d2 : (S0 ++ S1 ++ S2 ++ S3).drop (S0.length + q) = S2 ++ S3 := by
    rw [List.append_assoc (S0 ++ S1)]; exact List.drop_left' (by simp [h1])
  have d3 : (S0 ++ S1 ++ S2 ++ S3).drop (S0.length + q + q) = S3 :=
    List.drop_left' (by simp [h1, h2]; omega)
  have tk1 : (S1 ++ S2 ++ S3).take q = S1 := by
    rw [List.append_assoc]; exact List.take_left' h1
  have tk2 : (S2 ++ S3).take q = S2 := List.take_left' h2
  rw [t0, d1, d2, d3, tk1, tk2]

/-- Every subsample is consistent with `f` when `S` and `T` are, and contains `T`. -/
theorem b1_subsamples_mem_aux {X : Type*} (n : ℕ) : ∀ (S T : List (X × Bool)), S.length = n →
    (∀ Ŝ ∈ subsamples S T, (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ)) ∧
      (∀ T' : List (X × Bool), (subsamples S T).length = (subsamples S T').length) ∧
      1 ≤ (subsamples S T).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S T hS
  by_cases h : S.length ≤ 3
  · have e : ∀ T'' : List (X × Bool), subsamples S T'' = [S ++ T''] := fun T'' => by
      rw [subsamples, if_pos h]
    refine ⟨?_, ?_, ?_⟩
    · intro Ŝ hŜ
      rw [e, List.mem_singleton] at hŜ
      subst hŜ
      exact ⟨fun z hz => hz, fun z hz => List.mem_append_right _ hz⟩
    · intro T'
      rw [e, e]; rfl
    · rw [e]; simp
  · obtain ⟨S0, hS0⟩ : ∃ S0, S0 = S.take (S.length - 3 * (S.length / 4)) := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, A = (S.drop (S.length - 2 * (S.length / 4))).take (S.length / 4) :=
      ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = S.drop (S.length - S.length / 4) := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = (S.drop (S.length - 3 * (S.length / 4))).take (S.length / 4) :=
      ⟨_, rfl⟩
    have e : ∀ T'' : List (X × Bool), subsamples S T'' =
        subsamples S0 (A ++ B ++ T'') ++ subsamples S0 (C ++ B ++ T'') ++
          subsamples S0 (C ++ A ++ T'') := fun T'' => by
      rw [subsamples, if_neg h, hS0, hA, hB, hC]
    have hlt : S0.length < n := by
      rw [hS0, List.length_take]; omega
    have IH := fun T'' => ih S0.length hlt S0 T'' rfl
    have h0 : ∀ z ∈ S0, z ∈ S := fun z hz => by
      rw [hS0] at hz; exact List.mem_of_mem_take hz
    have hA' : ∀ z ∈ A, z ∈ S := fun z hz => by
      rw [hA] at hz; exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have hB' : ∀ z ∈ B, z ∈ S := fun z hz => by
      rw [hB] at hz; exact List.mem_of_mem_drop hz
    have hC' : ∀ z ∈ C, z ∈ S := fun z hz => by
      rw [hC] at hz; exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have key : ∀ U V : List (X × Bool), (∀ z ∈ U, z ∈ S) → (∀ z ∈ V, z ∈ S) →
        ∀ Ŝ ∈ subsamples S0 (U ++ V ++ T), (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ) := by
      intro U V hU hV Ŝ hŜ
      obtain ⟨h1, h2⟩ := (IH (U ++ V ++ T)).1 Ŝ hŜ
      refine ⟨fun z hz => ?_, fun z hz => h2 z (List.mem_append_right _ hz)⟩
      have := h1 z hz
      simp only [List.mem_append] at this ⊢
      rcases this with h | (h | h) | h
      · exact Or.inl (h0 z h)
      · exact Or.inl (hU z h)
      · exact Or.inl (hV z h)
      · exact Or.inr h
    refine ⟨?_, ?_, ?_⟩
    · intro Ŝ hŜ
      rw [e] at hŜ
      simp only [List.mem_append] at hŜ
      rcases hŜ with (h | h) | h
      · exact key A B hA' hB' Ŝ h
      · exact key C B hC' hB' Ŝ h
      · exact key C A hC' hA' Ŝ h
    · intro T'
      rw [e, e]
      simp only [List.length_append]
      rw [(IH (A ++ B ++ T)).2.1 (A ++ B ++ T'), (IH (C ++ B ++ T)).2.1 (C ++ B ++ T'),
        (IH (C ++ A ++ T)).2.1 (C ++ A ++ T')]
    · rw [e]
      simp only [List.length_append]
      have := (IH (A ++ B ++ T)).2.2
      omega

/-- A classifier trained by a consistent learner on a subsample of `𝔸(S; T)` (all labels given
by `f ∈ C`) lies in `C` and agrees with `f` on `T`. -/
theorem b1_learner_consistent {X : Type*} (C : Set (X → Bool)) (L : List (X × Bool) → X → Bool)
    (hL : IsConsistentLearner C L) (f : X → Bool) (hf : f ∈ C) (S T : List (X × Bool))
    (hS : ∀ p ∈ S, f p.1 = p.2) (hT : ∀ p ∈ T, f p.1 = p.2) (Ŝ : List (X × Bool))
    (hŜ : Ŝ ∈ subsamples S T) : L Ŝ ∈ C ∧ ∀ p ∈ T, L Ŝ p.1 = p.2 := by
  obtain ⟨h1, h2⟩ := (b1_subsamples_mem_aux S.length S T rfl).1 Ŝ hŜ
  have hne : (consistent C Ŝ).Nonempty := ⟨f, hf, fun p hp => by
    rcases List.mem_append.mp (h1 p hp) with h | h
    · exact hS p h
    · exact hT p h⟩
  obtain ⟨hC, hcons⟩ := hL Ŝ hne
  exact ⟨hC, fun p hp => hcons p (h2 p hp)⟩

end OptimalPAC.SampleComplexity

-- ##### from b1bc7e99_cond.lean #####


open MeasureTheory

namespace B1Cond

open scoped ENNReal
open Classical

universe u

theorem meas_cons {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] {N : ℕ} (g : Z → X)
    (hg : Measurable g) (h : Z → Fin N → X) (hh : Measurable h) :
    Measurable (fun z => (Fin.cons (g z) (h z) : Fin (N + 1) → X)) := by
  rw [measurable_pi_iff]
  intro i
  induction i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact hg
  | succ j => simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp hh

theorem ofFn_cons' {X : Type*} {N : ℕ} (x : X) (v : Fin N → X) :
    List.ofFn (Fin.cons x v : Fin (N + 1) → X) = x :: List.ofFn v := by
  rw [List.ofFn_succ]; simp

/-- Measurability of `{(y, z) | (y, filter_E (z)) ∈ B}` from measurability of the slices of `B`. -/
theorem cs_meas {X : Type u} [MeasurableSpace X] (E : Set X) (hE : MeasurableSet E) :
    ∀ (n : ℕ) {Y : Type u} [MeasurableSpace Y] (B : Set (Y × List X)),
      (∀ N, MeasurableSet {p : Y × (Fin N → X) | (p.1, List.ofFn p.2) ∈ B}) →
      MeasurableSet {p : Y × (Fin n → X) |
        (p.1, (List.ofFn p.2).filter (fun x => decide (x ∈ E))) ∈ B} := by
  intro n
  induction n with
  | zero =>
    intro Y _ B hB
    convert hB 0 using 2
    simp
  | succ n ih =>
    intro Y _ B hB
    set B₃ : Set ((Y × X) × List X) :=
      {q | (q.1.1, if q.1.2 ∈ E then q.1.2 :: q.2 else q.2) ∈ B} with hB₃
    have hB₃m : ∀ N, MeasurableSet {q : (Y × X) × (Fin N → X) | (q.1, List.ofFn q.2) ∈ B₃} := by
      intro N
      have e : {q : (Y × X) × (Fin N → X) | (q.1, List.ofFn q.2) ∈ B₃} =
          ({q | q.1.2 ∈ E} ∩ (fun q : (Y × X) × (Fin N → X) =>
              ((q.1.1, (Fin.cons q.1.2 q.2 : Fin (N + 1) → X)) : Y × (Fin (N + 1) → X))) ⁻¹'
              {p : Y × (Fin (N + 1) → X) | (p.1, List.ofFn p.2) ∈ B}) ∪
          ({q | q.1.2 ∉ E} ∩ (fun q : (Y × X) × (Fin N → X) => ((q.1.1, q.2) : Y × (Fin N → X))) ⁻¹'
              {p : Y × (Fin N → X) | (p.1, List.ofFn p.2) ∈ B}) := by
        ext ⟨⟨y, x⟩, v⟩
        by_cases hx : x ∈ E <;> simp [hB₃, hx, ofFn_cons']
      rw [e]
      have hq : MeasurableSet {q : (Y × X) × (Fin N → X) | q.1.2 ∈ E} :=
        (measurable_snd.comp measurable_fst) hE
      refine (hq.inter ?_).union (hq.compl.inter ?_)
      · exact ((measurable_fst.comp measurable_fst).prodMk
          (meas_cons _ (measurable_snd.comp measurable_fst) _ measurable_snd)) (hB (N + 1))
      · exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd) (hB N)
    have hS := ih B₃ hB₃m
    have e : {p : Y × (Fin (n + 1) → X) |
          (p.1, (List.ofFn p.2).filter (fun x => decide (x ∈ E))) ∈ B} =
        (fun p : Y × (Fin (n + 1) → X) => (((p.1, p.2 0), Fin.tail p.2) : (Y × X) × (Fin n → X))) ⁻¹'
          {q : (Y × X) × (Fin n → X) |
            (q.1, (List.ofFn q.2).filter (fun x => decide (x ∈ E))) ∈ B₃} := by
      ext ⟨y, z⟩
      by_cases hz : z 0 ∈ E <;> simp [hB₃, hz, List.ofFn_succ, List.filter_cons] <;> exact Iff.rfl
    rw [e]
    have hΦ : Measurable (fun p : Y × (Fin (n + 1) → X) =>
        (((p.1, p.2 0), Fin.tail p.2) : (Y × X) × (Fin n → X))) :=
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_pi_lambda _ (fun j => (measurable_pi_apply j.succ).comp measurable_snd))
    exact hΦ hS

/-- `aC p pc n N` = probability that exactly `N` of `n` i.i.d. points fall in `E`. -/
noncomputable def aC (p pc : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => pc * aC p pc n 0
  | n + 1, N + 1 => p * aC p pc n N + pc * aC p pc n (N + 1)

theorem aC_shift (p pc : ℝ≥0∞) (n : ℕ) (η : ℕ → ℝ≥0∞) :
    ∑' N, aC p pc (n + 1) N * η N =
      p * ∑' N, aC p pc n N * η (N + 1) + pc * ∑' N, aC p pc n N * η N := by
  rw [tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' (f := fun N => aC p pc n N * η N) ENNReal.summable]
  simp only [aC]
  simp_rw [add_mul, ENNReal.tsum_add, mul_assoc, ENNReal.tsum_mul_left]
  ring

theorem aC_sum (p pc : ℝ≥0∞) (h : p + pc = 1) : ∀ n, ∑' N, aC p pc n N = 1 := by
  intro n
  induction n with
  | zero =>
    rw [tsum_eq_single 0 (fun N hN => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN; simp [aC])]
    simp [aC]
  | succ n ih =>
    have := aC_shift p pc n (fun _ => 1)
    simp only [mul_one] at this
    rw [this, ih, mul_one, mul_one, h]

/-- Slices of `{(x,l) | (if x ∈ E then x :: l else l) ∈ B}` are measurable. -/
theorem step_slices {X : Type u} [MeasurableSpace X] (E : Set X) (hE : MeasurableSet E)
    (B : Set (List X)) (hB : ∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B}) (N : ℕ) :
    MeasurableSet {p : X × (Fin N → X) |
      (p.1, List.ofFn p.2) ∈ {q : X × List X | (if q.1 ∈ E then q.1 :: q.2 else q.2) ∈ B}} := by
  have e : {p : X × (Fin N → X) |
      (p.1, List.ofFn p.2) ∈ {q : X × List X | (if q.1 ∈ E then q.1 :: q.2 else q.2) ∈ B}} =
      ({p | p.1 ∈ E} ∩ (fun p : X × (Fin N → X) => (Fin.cons p.1 p.2 : Fin (N + 1) → X)) ⁻¹'
          {v | List.ofFn v ∈ B}) ∪
        ({p | p.1 ∉ E} ∩ (fun p : X × (Fin N → X) => p.2) ⁻¹' {v | List.ofFn v ∈ B}) := by
    ext ⟨x, v⟩
    by_cases hx : x ∈ E <;> simp [hx, ofFn_cons']
  rw [e]
  have hq : MeasurableSet {p : X × (Fin N → X) | p.1 ∈ E} := measurable_fst hE
  exact (hq.inter ((meas_cons _ measurable_fst _ measurable_snd) (hB (N + 1)))).union
    (hq.compl.inter (measurable_snd (hB N)))

theorem cons_slices {X : Type u} [MeasurableSpace X] (B : Set (List X))
    (hB : ∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B}) (x : X) (N : ℕ) :
    MeasurableSet {v : Fin N → X | List.ofFn v ∈ {l | x :: l ∈ B}} := by
  have := (meas_cons (fun _ : Fin N → X => x) measurable_const id measurable_id) (hB (N + 1))
  convert this using 1
  ext v; simp [ofFn_cons']

theorem split_first {X : Type u} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (N : ℕ) (A : Set (Fin (N + 1) → X)) (hA : MeasurableSet A) :
    Measure.pi (fun _ : Fin (N + 1) => Q) A =
      (Q.prod (Measure.pi fun _ : Fin N => Q))
        ((fun p : X × (Fin N → X) => (Fin.cons p.1 p.2 : Fin (N + 1) → X)) ⁻¹' A) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => Q) 0).symm
  have e : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => X) 0).symm :
      X × (Fin N → X) → (Fin (N + 1) → X)) =
      (fun p : X × (Fin N → X) => (Fin.cons p.1 p.2 : Fin (N + 1) → X)) := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  rw [← hmp.measure_preimage hA.nullMeasurableSet]
  rw [e]

theorem cons_integral {X : Type u} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (B : Set (List X)) (hB : ∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B}) (N : ℕ) :
    ∫⁻ x, Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ {l | x :: l ∈ B}} ∂Q =
      Measure.pi (fun _ : Fin (N + 1) => Q) {v | List.ofFn v ∈ B} := by
  rw [split_first Q N _ (hB (N + 1))]
  have hT : MeasurableSet ((fun p : X × (Fin N → X) => (Fin.cons p.1 p.2 : Fin (N + 1) → X)) ⁻¹'
      {v | List.ofFn v ∈ B}) := (meas_cons _ measurable_fst _ measurable_snd) (hB (N + 1))
  rw [Measure.prod_apply hT]
  congr 1
  funext x
  congr 1
  ext v
  simp [ofFn_cons']

theorem cons_integral_meas {X : Type u} [MeasurableSpace X] (Q : Measure X)
    [IsProbabilityMeasure Q]
    (B : Set (List X)) (hB : ∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B}) (N : ℕ) :
    Measurable (fun x => Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ {l | x :: l ∈ B}}) := by
  have hT : MeasurableSet ((fun p : X × (Fin N → X) => (Fin.cons p.1 p.2 : Fin (N + 1) → X)) ⁻¹'
      {v | List.ofFn v ∈ B}) := (meas_cons _ measurable_fst _ measurable_snd) (hB (N + 1))
  convert measurable_measure_prodMk_left (ν := Measure.pi fun _ : Fin N => Q) hT using 1
  funext x
  congr 1
  ext v
  simp [ofFn_cons']

/-- The law of the `E`-points of an i.i.d. `P`-sample: a binomial mixture of i.i.d. `Q`-samples. -/
theorem cs_formula {X : Type u} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E)
    (hQ : ∀ h : X → ℝ≥0∞, Measurable h → ∫⁻ x in E, h x ∂P = P E * ∫⁻ x, h x ∂Q) :
    ∀ (n : ℕ) (B : Set (List X)), (∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B}) →
      Measure.pi (fun _ : Fin n => P)
          {z | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} =
        ∑' N, aC (P E) (P Eᶜ) n N * Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ B} := by
  intro n
  induction n with
  | zero =>
    intro B hB
    rw [tsum_eq_single 0 (fun N hN => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN; simp [aC])]
    simp only [aC, one_mul]
    by_cases h : ([] : List X) ∈ B
    · have e1 : {z : Fin 0 → X | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} = Set.univ := by
        ext z; simp [h]
      have e2 : {v : Fin 0 → X | List.ofFn v ∈ B} = Set.univ := by ext z; simp [h]
      rw [e1, e2]; simp
    · have e1 : {z : Fin 0 → X | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} = ∅ := by
        ext z; simp [h]
      have e2 : {v : Fin 0 → X | List.ofFn v ∈ B} = ∅ := by ext z; simp [h]
      rw [e1, e2]; simp
  | succ n ih =>
    intro B hB
    set B₃ : Set (X × List X) := {q | (if q.1 ∈ E then q.1 :: q.2 else q.2) ∈ B} with hB₃
    have hS := cs_meas E hE n B₃ (step_slices E hE B hB)
    have hSeq : (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) ⁻¹'
          {z | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} =
        {q : X × (Fin n → X) | (q.1, (List.ofFn q.2).filter (fun x => decide (x ∈ E))) ∈ B₃} := by
      ext ⟨x, v⟩
      by_cases hx : x ∈ E <;> simp [hB₃, hx, ofFn_cons', List.filter_cons]
    have hmeasZ : MeasurableSet {z : Fin (n + 1) → X |
        (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} := by
      have := cs_meas E hE (n + 1) (Y := PUnit.{u+1}) {q : PUnit.{u+1} × List X | q.2 ∈ B}
        (fun N => measurable_snd (hB N))
      exact (measurable_const.prodMk measurable_id :
        Measurable (fun z : Fin (n + 1) → X => (PUnit.unit, z))) this
    rw [split_first P n _ hmeasZ, hSeq, Measure.prod_apply hS]
    -- the sections
    set η : ℕ → ℝ≥0∞ := fun N => Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ B} with hη
    set g : X → ℝ≥0∞ := fun x => if x ∈ E then
        ∑' N, aC (P E) (P Eᶜ) n N *
          Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ {l | x :: l ∈ B}}
      else ∑' N, aC (P E) (P Eᶜ) n N * η N with hg
    have hsec : ∀ x, Measure.pi (fun _ : Fin n => P)
        (Prod.mk x ⁻¹' {q : X × (Fin n → X) |
          (q.1, (List.ofFn q.2).filter (fun x => decide (x ∈ E))) ∈ B₃}) = g x := by
      intro x
      by_cases hx : x ∈ E
      · rw [hg]; simp only [hx, if_true]
        rw [← ih {l | x :: l ∈ B} (cons_slices B hB x)]
        congr 1; ext w; simp [hB₃, hx]
      · rw [hg]; simp only [hx, if_false]
        rw [← ih B hB]
        congr 1; ext w; simp [hB₃, hx]
    simp_rw [hsec]
    rw [← lintegral_add_compl g hE]
    have hgE : ∫⁻ x in E, g x ∂P = ∑' N, aC (P E) (P Eᶜ) n N * (P E * η (N + 1)) := by
      rw [setLIntegral_congr_fun hE (g := fun x => ∑' N, aC (P E) (P Eᶜ) n N *
          Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ {l | x :: l ∈ B}})
        (fun x hx => by rw [hg]; simp [hx])]
      rw [lintegral_tsum (fun N => ((cons_integral_meas Q B hB N).const_mul _).aemeasurable)]
      congr 1; funext N
      rw [lintegral_const_mul _ (cons_integral_meas Q B hB N), hQ _ (cons_integral_meas Q B hB N),
        cons_integral Q B hB N]
    have hgEc : ∫⁻ x in Eᶜ, g x ∂P = (∑' N, aC (P E) (P Eᶜ) n N * η N) * P Eᶜ := by
      rw [setLIntegral_congr_fun hE.compl (g := fun _ => ∑' N, aC (P E) (P Eᶜ) n N * η N)
        (fun x hx => by rw [hg]; simp [show x ∉ E from hx])]
      rw [setLIntegral_const]
    rw [hgE, hgEc, aC_shift]
    simp_rw [mul_left_comm _ (P E), ENNReal.tsum_mul_left]
    ring

/-- **Conditional sampling bound.** If every i.i.d. `P[·|E]`-sample of any size `N ≥ 1` lies in
`B` with (outer) probability `≤ η`, then the subsequence of `E`-points of an i.i.d. `P`-sample
lies in `B` (and is nonempty) with (outer) probability `≤ η`. -/
theorem cs_bound {X : Type u} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (E : Set X) (hE : MeasurableSet E) (hPE : P E ≠ 0) (n : ℕ) (B : Set (List X))
    (hB0 : ([] : List X) ∉ B) (η : ℝ≥0∞)
    (hη : ∀ N, 1 ≤ N →
      Measure.pi (fun _ : Fin N => ProbabilityTheory.cond P E) {v | List.ofFn v ∈ B} ≤ η) :
    Measure.pi (fun _ : Fin n => P)
      {z | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B} ≤ η := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond P E) :=
    ProbabilityTheory.cond_isProbabilityMeasure hPE
  set Q := ProbabilityTheory.cond P E with hQdef
  let M : ∀ N, Set (Fin N → X) := fun N =>
    toMeasurable (Measure.pi fun _ : Fin N => Q) {v | List.ofFn v ∈ B}
  let B' : Set (List X) := {l | ∃ N, ∃ v : Fin N → X, 1 ≤ N ∧ v ∈ M N ∧ l = List.ofFn v}
  have hsl : ∀ N, {v : Fin N → X | List.ofFn v ∈ B'} = if 1 ≤ N then M N else ∅ := by
    intro N
    ext v
    constructor
    · rintro ⟨N', v', h1, h2, e⟩
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp e)
      have := eq_of_heq hv
      subst this
      simp [h1, h2]
    · intro h
      split_ifs at h with h1
      · exact ⟨N, v, h1, h, rfl⟩
      · exact h.elim
  have hBm : ∀ N, MeasurableSet {v : Fin N → X | List.ofFn v ∈ B'} := by
    intro N
    rw [hsl]
    split_ifs
    · exact measurableSet_toMeasurable _ _
    · exact MeasurableSet.empty
  have hsub : B ⊆ B' := by
    intro l hl
    refine ⟨l.length, l.get, ?_, subset_toMeasurable _ _ (by simpa using hl), by simp⟩
    rcases l with _ | ⟨a, l⟩
    · exact absurd hl hB0
    · simp
  have hQint : ∀ h : X → ℝ≥0∞, Measurable h → ∫⁻ x in E, h x ∂P = P E * ∫⁻ x, h x ∂Q := by
    intro h _
    rw [hQdef, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hPE (measure_ne_top P E), one_mul]
  calc Measure.pi (fun _ : Fin n => P)
        {z | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B}
      ≤ Measure.pi (fun _ : Fin n => P)
        {z | (List.ofFn z).filter (fun x => decide (x ∈ E)) ∈ B'} :=
        measure_mono (fun z hz => hsub hz)
    _ = ∑' N, aC (P E) (P Eᶜ) n N * Measure.pi (fun _ : Fin N => Q) {v | List.ofFn v ∈ B'} :=
        cs_formula P Q E hE hQint n B' hBm
    _ ≤ ∑' N, aC (P E) (P Eᶜ) n N * η := by
        refine ENNReal.tsum_le_tsum (fun N => ?_)
        gcongr
        rw [hsl]
        split_ifs with h1
        · rw [measure_toMeasurable]; exact hη N h1
        · simp
    _ = η := by
        rw [ENNReal.tsum_mul_right, aC_sum (P E) (P Eᶜ)
          (by rw [measure_add_measure_compl hE, measure_univ]), one_mul]

end B1Cond

-- ##### from b1bc7e99_fub.lean #####


open MeasureTheory

namespace B1Fub

open scoped ENNReal

/-- Fubini upper bound, sections in the first coordinate. -/
theorem prod_le' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    (s : Set (α × β)) (hs : MeasurableSet s) (η : ℝ≥0∞)
    (h : ∀ b, μ ((fun a => (a, b)) ⁻¹' s) ≤ η) : (μ.prod ν) s ≤ η := by
  rw [Measure.prod_apply_symm hs]
  calc ∫⁻ b, μ ((fun a => (a, b)) ⁻¹' s) ∂ν ≤ ∫⁻ _, η ∂ν := lintegral_mono h
    _ = η := by simp

/-- **Fubini over a block of coordinates.** If, whatever the coordinates outside the image of
the injection `e`, resampling the coordinates `e k` i.i.d. lands in `A` with probability `≤ η`,
then `P^m(A) ≤ η`. -/
theorem fubini_extend {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {q m : ℕ} (e : Fin q → Fin m) (he : Function.Injective e) (A : Set (Fin m → X))
    (hA : MeasurableSet A) (η : ℝ≥0∞)
    (h : ∀ x : Fin m → X,
      Measure.pi (fun _ : Fin q => P) {u | Function.extend e u x ∈ A} ≤ η) :
    Measure.pi (fun _ : Fin m => P) A ≤ η := by
  classical
  let p : Fin m → Prop := fun j => j ∈ Set.range e
  let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => X) p
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => P) p
  rw [← (hmp.symm Φ).measure_preimage hA.nullMeasurableSet]
  refine prod_le' _ _ _ (Φ.symm.measurable hA) η (fun w => ?_)
  by_cases hne : Nonempty (Subtype p → X)
  · obtain ⟨v0⟩ := hne
    set x : Fin m → X := Φ.symm (v0, w) with hx
    let σ : Fin q ≃ Subtype p := Equiv.ofInjective e he
    have hσ := measurePreserving_piCongrLeft (fun _ : Subtype p => P) σ
    have hT : MeasurableSet ((fun a => (a, w)) ⁻¹' (Φ.symm ⁻¹' A)) :=
      measurable_prodMk_right (Φ.symm.measurable hA)
    refine le_trans (le_of_eq (?_ : _ = (Measure.pi fun _ : Fin q => P)
      ((MeasurableEquiv.piCongrLeft (fun _ => X) σ) ⁻¹'
        ((fun a => (a, w)) ⁻¹' (Φ.symm ⁻¹' A))))) ?_
    · convert (hσ.measure_preimage hT.nullMeasurableSet).symm
    refine le_trans (le_of_eq ?_) (h x)
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have key : Φ.symm (MeasurableEquiv.piCongrLeft (fun _ => X) σ u, w) =
        Function.extend e u x := by
      funext j
      by_cases hj : p j
      · obtain ⟨k, rfl⟩ := hj
        rw [he.extend_apply]
        have h1 : Φ.symm (MeasurableEquiv.piCongrLeft (fun _ => X) σ u, w) (e k) =
            MeasurableEquiv.piCongrLeft (fun _ => X) σ u ⟨e k, k, rfl⟩ := by
          simp only [Φ, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
          simp
          exact dif_pos (Set.mem_range_self k)
        rw [h1]
        have h2 : (⟨e k, k, rfl⟩ : Subtype p) = σ k := rfl
        rw [h2, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
      · have hj' : ¬ ∃ k, e k = j := hj
        rw [Function.extend_apply' _ _ _ hj', hx]
        simp [Φ, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
    rw [key]
  · have : {v : Subtype p → X | (v, w) ∈ Φ.symm ⁻¹' A} = ∅ := by
      ext v; exact absurd ⟨v⟩ hne
    simp only [Set.preimage] at this ⊢
    rw [this]; simp

end B1Fub

-- ##### from b1bc7e99_sibs.lean #####


-- ===== copied from Solutions/Sol_pv_6edfc126.lean (majority_error_le_twelve) =====


open MeasureTheory

namespace OptimalPAC.SampleComplexity

open scoped ENNReal

theorem p6e_measSet_ER {X : Type*} [MeasurableSpace X] {h f : X → Bool} (hh : Measurable h)
    (hf : Measurable f) : MeasurableSet (ER h f) :=
  (measurableSet_eq_fun hh hf).compl

theorem p6e_meas_count {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (p : (X → Bool) → X → Bool) (hp : ∀ h ∈ L, MeasurableSet {x | p h x = true}) :
    Measurable (fun x => ((L.countP (fun h => p h x) : ℕ) : ℝ≥0∞)) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hp h (List.mem_cons_of_mem a hh))
    have ha := hp a List.mem_cons_self
    simp only [List.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact ih'.add (Measurable.ite ha measurable_const measurable_const)

theorem p6e_meas_majority {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) : Measurable (majority L) := by
  apply measurable_to_bool
  have h1 := p6e_meas_count L (fun h x => decide (h x = false))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton false) using 1
      ext x; simp)
  have h2 := p6e_meas_count L (fun h x => decide (h x = true))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton true) using 1
      ext x; simp)
  have : majority L ⁻¹' {true} =
      {x | ((L.countP (fun h => decide (h x = false)) : ℕ) : ℝ≥0∞) ≤
        ((L.countP (fun h => decide (h x = true)) : ℕ) : ℝ≥0∞)} := by
    ext x; simp [majority]
  rw [this]
  exact measurableSet_le h1 h2

theorem p6e_lint_eq {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → Bool)
    (hf : Measurable f) (A : Set X) (hA : MeasurableSet A) (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) :
    ∫⁻ x, A.indicator (fun x => ((L.countP (fun h => decide (h x ≠ f x)) : ℕ) : ℝ≥0∞)) x ∂P =
      (L.map (fun h => P (A ∩ ER h f))).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hL h (List.mem_cons_of_mem a hh))
    have ha := hL a List.mem_cons_self
    have hE : MeasurableSet (ER a f) := p6e_measSet_ER ha hf
    have hfun : (fun x => A.indicator
        (fun x => ((List.countP (fun h => decide (h x ≠ f x)) (a :: l) : ℕ) : ℝ≥0∞)) x) =
        fun x => (A ∩ ER a f).indicator 1 x +
          A.indicator (fun x => ((l.countP (fun h => decide (h x ≠ f x)) : ℕ) : ℝ≥0∞)) x := by
      funext x
      by_cases hxA : x ∈ A
      · by_cases hxE : x ∈ ER a f
        · have hxE' : a x ≠ f x := hxE
          simp [Set.indicator_of_mem hxA, Set.indicator_of_mem (Set.mem_inter hxA hxE),
            List.countP_cons, hxE', add_comm]
        · have hxE' : a x = f x := by simpa [ER] using hxE
          have : x ∉ A ∩ ER a f := fun h => hxE h.2
          simp [Set.indicator_of_mem hxA, Set.indicator_of_notMem this, List.countP_cons, hxE']
      · have : x ∉ A ∩ ER a f := fun h => hxA h.1
        simp [Set.indicator_of_notMem hxA, Set.indicator_of_notMem this]
    rw [hfun, lintegral_add_left (f := (A ∩ ER a f).indicator 1)
      (measurable_one.indicator (hA.inter hE)),
      lintegral_indicator_one (hA.inter hE), ih']
    simp

theorem p6e_sum_toReal {X : Type*} [MeasurableSpace X] (P : Measure X) [IsFiniteMeasure P]
    (g : (X → Bool) → Set X) (L : List (X → Bool)) :
    (L.map (fun h => P (g h))).sum ≠ ⊤ ∧
      (L.map (fun h => (P (g h)).toReal)).sum = ((L.map (fun h => P (g h))).sum).toReal := by
  induction L with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    refine ⟨ENNReal.add_ne_top.2 ⟨measure_ne_top P _, h1⟩, ?_⟩
    rw [ENNReal.toReal_add (measure_ne_top P _) h1, h2]

theorem p6e_countP_tf {X : Type*} (L : List (X → Bool)) (x : X) :
    L.countP (fun h => decide (h x = true)) + L.countP (fun h => decide (h x = false)) =
      L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    have : (if decide (a x = true) = true then 1 else 0) +
        (if decide (a x = false) = true then 1 else 0) = 1 := by
      cases a x <;> rfl
    omega

theorem p6e_key {X : Type*} (f : X → Bool) (G : Fin 3 → List (X → Bool)) (n : ℕ)
    (hG : ∀ i, (G i).length = n) (x : X)
    (hx : x ∈ ER (majority (G 0 ++ G 1 ++ G 2)) f) :
    ∃ i : Fin 3, x ∈ ER (majority (G i)) f ∧
      n ≤ 2 * ∑ j ∈ Finset.univ.erase i, (G j).countP (fun h => decide (h x ≠ f x)) := by
  have e : ∀ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (G j).countP (fun h => decide (h x ≠ f x))
      + (G i).countP (fun h => decide (h x ≠ f x)) =
      ∑ j, (G j).countP (fun h => decide (h x ≠ f x)) := fun i =>
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  simp only [Fin.sum_univ_three] at e
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have t : ∀ j, (G j).countP (fun h => decide (h x = true)) +
      (G j).countP (fun h => decide (h x = false)) = n := fun j =>
    (p6e_countP_tf (G j) x).trans (hG j)
  have t0 := t 0
  have t1 := t 1
  have t2 := t 2
  have hx' : decide ((G 0 ++ G 1 ++ G 2).countP (fun h => decide (h x = false)) ≤
      (G 0 ++ G 1 ++ G 2).countP (fun h => decide (h x = true))) ≠ f x := hx
  rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append] at hx'
  have mem : ∀ i, x ∈ ER (majority (G i)) f ↔
      decide ((G i).countP (fun h => decide (h x = false)) ≤
        (G i).countP (fun h => decide (h x = true))) ≠ f x := fun i => Iff.rfl
  by_cases hfx : f x = true
  · have hw : ∀ j, (G j).countP (fun h => decide (h x ≠ f x)) =
        (G j).countP (fun h => decide (h x = false)) := fun j =>
      List.countP_congr (fun h _ => by rw [hfx]; cases hh : h x <;> simp)
    rw [hfx] at hx'
    have hx2 : (G 0).countP (fun h => decide (h x = true)) +
        (G 1).countP (fun h => decide (h x = true)) +
        (G 2).countP (fun h => decide (h x = true)) <
        (G 0).countP (fun h => decide (h x = false)) +
        (G 1).countP (fun h => decide (h x = false)) +
        (G 2).countP (fun h => decide (h x = false)) := by simpa using hx'
    simp only [hw] at e0 e1 e2 ⊢
    by_cases c0 : (G 0).countP (fun h => decide (h x = true)) <
        (G 0).countP (fun h => decide (h x = false))
    · exact ⟨0, (mem 0).2 (by rw [hfx]; simpa using c0), by omega⟩
    by_cases c1 : (G 1).countP (fun h => decide (h x = true)) <
        (G 1).countP (fun h => decide (h x = false))
    · exact ⟨1, (mem 1).2 (by rw [hfx]; simpa using c1), by omega⟩
    by_cases c2 : (G 2).countP (fun h => decide (h x = true)) <
        (G 2).countP (fun h => decide (h x = false))
    · exact ⟨2, (mem 2).2 (by rw [hfx]; simpa using c2), by omega⟩
    omega
  · have hfx' : f x = false := by simpa using hfx
    have hw : ∀ j, (G j).countP (fun h => decide (h x ≠ f x)) =
        (G j).countP (fun h => decide (h x = true)) := fun j =>
      List.countP_congr (fun h _ => by rw [hfx']; cases hh : h x <;> simp)
    rw [hfx'] at hx'
    have hx2 : (G 0).countP (fun h => decide (h x = false)) +
        (G 1).countP (fun h => decide (h x = false)) +
        (G 2).countP (fun h => decide (h x = false)) ≤
        (G 0).countP (fun h => decide (h x = true)) +
        (G 1).countP (fun h => decide (h x = true)) +
        (G 2).countP (fun h => decide (h x = true)) := by simpa using hx'
    simp only [hw] at e0 e1 e2 ⊢
    by_cases c0 : (G 0).countP (fun h => decide (h x = false)) ≤
        (G 0).countP (fun h => decide (h x = true))
    · exact ⟨0, (mem 0).2 (by rw [hfx']; simpa using c0), by omega⟩
    by_cases c1 : (G 1).countP (fun h => decide (h x = false)) ≤
        (G 1).countP (fun h => decide (h x = true))
    · exact ⟨1, (mem 1).2 (by rw [hfx']; simpa using c1), by omega⟩
    by_cases c2 : (G 2).countP (fun h => decide (h x = false)) ≤
        (G 2).countP (fun h => decide (h x = true))
    · exact ⟨2, (mem 2).2 (by rw [hfx']; simpa using c2), by omega⟩
    omega

end OptimalPAC.SampleComplexity

open MeasureTheory OptimalPAC.SampleComplexity in
theorem sib_majority_error_le_twelve {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (f : X → Bool) (hf : Measurable f)
    (G : Fin 3 → List (X → Bool)) (n : ℕ) (hn : 1 ≤ n) (hG : ∀ i, (G i).length = n)
    (hGm : ∀ i, ∀ h ∈ G i, Measurable h) :
    er P (majority (G 0 ++ G 1 ++ G 2)) f ≤
        12 * ((1 / 3 : ℝ) * ∑ i : Fin 3, (1 / (2 * (n : ℝ))) *
          ∑ j ∈ Finset.univ.erase i,
            ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)).sum) ∧
      ∀ B : ℝ, (∀ i j : Fin 3, j ≠ i → ∀ h ∈ G j,
          (P (ER (majority (G i)) f ∩ ER h f)).toReal ≤ B) →
        er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 12 * B := by
  -- measurability
  have hall : ∀ h ∈ G 0 ++ G 1 ++ G 2, Measurable h := by
    intro h hh
    simp only [List.mem_append] at hh
    rcases hh with (h0 | h1) | h2
    · exact hGm 0 h h0
    · exact hGm 1 h h1
    · exact hGm 2 h h2
  have hE : MeasurableSet (ER (majority (G 0 ++ G 1 ++ G 2)) f) :=
    p6e_measSet_ER (p6e_meas_majority _ hall) hf
  have hEi : ∀ i, MeasurableSet (ER (majority (G i)) f) := fun i =>
    p6e_measSet_ER (p6e_meas_majority _ (hGm i)) hf
  set E := ER (majority (G 0 ++ G 1 ++ G 2)) f with hEdef
  set W : Fin 3 → X → ENNReal := fun j x =>
    (((G j).countP (fun h => decide (h x ≠ f x)) : ℕ) : ENNReal) with hW
  have hWm : ∀ j, Measurable (W j) := fun j =>
    p6e_meas_count (G j) (fun h x => decide (h x ≠ f x))
      (fun h hh => by simpa [ER] using p6e_measSet_ER (hGm j h hh) hf)
  -- pointwise
  have hpt : ∀ x, (n : ENNReal) * E.indicator 1 x ≤
      2 * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x := by
    intro x
    by_cases hx : x ∈ E
    · obtain ⟨i, hxi, hle⟩ := p6e_key f G n hG x hx
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      calc (n : ENNReal) ≤ 2 * ∑ j ∈ Finset.univ.erase i, W j x := by
              simp only [hW]
              exact_mod_cast hle
        _ = 2 * ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x := by
              simp [Set.indicator_of_mem hxi]
        _ ≤ _ := by
              gcongr
              exact Finset.single_le_sum
                (f := fun i => ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x)
                (fun _ _ => zero_le) (Finset.mem_univ i)
    · simp [Set.indicator_of_notMem hx]
  have hint := lintegral_mono (μ := P) hpt
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), lintegral_indicator_one hE] at hint
  rw [lintegral_const_mul' _ _ (by simp)] at hint
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _
    fun j _ => (hWm j).indicator (hEi i))] at hint
  simp_rw [lintegral_finsetSum _ (fun j _ => (hWm j).indicator (hEi _))] at hint
  simp_rw [hW, p6e_lint_eq P f hf _ (hEi _) _ (hGm _)] at hint
  -- convert to reals
  set R : Fin 3 → Fin 3 → ℝ := fun i j =>
    ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)).sum with hR
  have hRe : ∀ i j, R i j =
      (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum).toReal := fun i j =>
    (p6e_sum_toReal P (fun h => ER (majority (G i)) f ∩ ER h f) (G j)).2
  have hfin : ∀ i j,
      (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum) ≠ ⊤ := fun i j =>
    (p6e_sum_toReal P (fun h => ER (majority (G i)) f ∩ ER h f) (G j)).1
  have hreal : (n : ℝ) * er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    have hne : (2 : ENNReal) * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i,
        (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum) ≠ ⊤ := by
      apply ENNReal.mul_ne_top (by simp)
      exact (ENNReal.sum_ne_top).2 fun i _ => (ENNReal.sum_ne_top).2 fun j _ => hfin i j
    have := ENNReal.toReal_mono hne hint
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum
      (fun i _ => (ENNReal.sum_ne_top).2 fun j _ => hfin i j)] at this
    simp_rw [ENNReal.toReal_sum (fun j _ => hfin _ j), ← hRe] at this
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at this
    exact this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain : er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
    linarith
  have hrhs : 12 * ((1 / 3 : ℝ) * ∑ i : Fin 3, (1 / (2 * (n : ℝ))) *
          ∑ j ∈ Finset.univ.erase i, R i j) =
      2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    rw [← Finset.mul_sum]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hrhs]; exact hmain
  · intro B hB
    have hRB : ∀ i j, j ≠ i → R i j ≤ n * B := by
      intro i j hji
      have := List.sum_le_card_nsmul
        ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)) B (by
          intro y hy
          obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hy
          exact hB i j hji h hh)
      simpa [hR, hG, nsmul_eq_mul] using this
    have hQ : ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j ≤ 6 * (n * B) := by
      calc ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j
          ≤ ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (n * B : ℝ) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j hj
            exact hRB i j (Finset.ne_of_mem_erase hj)
        _ = 6 * (n * B) := by
            simp [Finset.sum_const, Finset.card_erase_of_mem]
            ring
    calc er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := hmain
      _ ≤ 2 / n * (6 * (n * B)) := by gcongr
      _ = 12 * B := by field_simp; ring

-- ===== copied from Solutions/Sol_pv_5ec3b2ae.lean (chernoff_count_lower) =====


namespace Chernoff5ec3b2ae

/-- `exp (-0.363) ≤ 7/10`. -/
lemma exp_neg_le : Real.exp (-(363 / 1000 : ℝ)) ≤ 7 / 10 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := (363 / 1000 : ℝ)) (by norm_num)
  have h1 : Real.exp (-(363 / 1000 : ℝ)) * Real.exp (363 / 1000) = 1 := by
    rw [← Real.exp_add]; simp
  have hc0 := Real.exp_pos (-(363 / 1000 : ℝ))
  have he0 := Real.exp_pos (363 / 1000 : ℝ)
  nlinarith

/-- The final real inequality. -/
lemma final_real (c q L δ : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 7 / 10)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL0 : 0 < L) (hL : Real.exp (-L) = δ / 9)
    (hqn : 23 * L ≤ q * n) :
    (c * q + (1 - q)) ^ n ≤
      Real.exp (-(363 / 1000 : ℝ) * (7 / 10 * q * n)) * (δ / 9) := by
  have hb0 : 0 ≤ c * q + (1 - q) := by nlinarith
  have hb1 : c * q + (1 - q) ≤ Real.exp (-(3 / 10) * q) := by
    have := Real.add_one_le_exp (-(3 / 10) * q)
    nlinarith
  have hpow : (c * q + (1 - q)) ^ n ≤ Real.exp (n * (-(3 / 10) * q)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hb0 hb1 n
  refine hpow.trans ?_
  rw [← hL, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end Chernoff5ec3b2ae

open MeasureTheory in
theorem sib_chernoff_count_lower {X : Type*} [MeasurableSpace X] (Q : Measure X)
    [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hQE : 23 / (n : ℝ) * Real.log (9 / δ) ≤ (Q E).toReal) :
    Measure.pi (fun _ : Fin n => Q)
      {z | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * (Q E).toReal * n}
      ≤ ENNReal.ofReal (δ / 9) := by
  classical
  set q : ℝ := (Q E).toReal with hq
  set P : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => Q) with hP
  set c : ℝ := Real.exp (-(363 / 1000 : ℝ)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 7 / 10 := Chernoff5ec3b2ae.exp_neg_le
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := by
    rw [hq]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  let f : X → ℝ := fun x => if x ∈ E then c else 1
  have hfm : Measurable f := Measurable.ite hE measurable_const measurable_const
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [f]; split_ifs <;> linarith
  have hf1 : ∀ x, f x ≤ 1 := fun x => by
    simp only [f]; split_ifs <;> linarith
  let g : (Fin n → X) → ℝ := fun z => ∏ t, f (z t)
  have hgm : Measurable g :=
    Finset.measurable_prod _ (fun t _ => hfm.comp (measurable_pi_apply t))
  have hg0 : ∀ z, 0 ≤ g z := fun z => Finset.prod_nonneg (fun t _ => hf0 _)
  have hg1 : ∀ z, g z ≤ 1 := fun z =>
    Finset.prod_le_one (fun t _ => hf0 _) (fun t _ => hf1 _)
  have hgint : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hg1 z)
  have hfint : ∫ x, f x ∂Q = c * q + (1 - q) := by
    have hfe : f = E.piecewise (fun _ => c) (fun _ => 1) := by
      ext x; simp [f, Set.piecewise]
    rw [hfe, integral_piecewise hE (integrable_const _).integrableOn
      (integrable_const _).integrableOn, setIntegral_const, setIntegral_const,
      probReal_compl_eq_one_sub hE]
    simp [q, measureReal_def]
    ring
  have hgI : ∫ z, g z ∂P = (c * q + (1 - q)) ^ n := by
    rw [← hfint]
    have := integral_fintype_prod_eq_pow (ι := Fin n) (μ := Q) f
    simpa [g, P, Fintype.card_fin] using this
  -- g z = c ^ N z
  have hgN : ∀ z : Fin n → X, g z = c ^ ({t : Fin n | z t ∈ E}.ncard) := by
    intro z
    have hcard : ({t : Fin n | z t ∈ E}.ncard) =
        (Finset.univ.filter (fun t => z t ∈ E)).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext t; simp
    simp only [g, f]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  set k : ℝ := Real.exp (-(363 / 1000 : ℝ) * (7 / 10 * q * n)) with hk
  have hk0 : 0 < k := Real.exp_pos _
  have hsub : {z : Fin n → X | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * q * n}
      ⊆ {z | k ≤ g z} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [hgN, hc, ← Real.exp_nat_mul, hk]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hg0) hgint k
  rw [hgI] at hmk
  -- the real bound
  set L : ℝ := Real.log (9 / δ) with hLdef
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hL : Real.exp (-L) = δ / 9 := by
    rw [Real.exp_neg, hLdef, Real.exp_log (by positivity)]; field_simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqn : 23 * L ≤ q * n := by
    have := mul_le_mul_of_nonneg_right hQE hnpos.le
    have e : 23 / (n : ℝ) * L * n = 23 * L := by field_simp
    have e2 : 23 * (L / (n : ℝ)) * n = 23 * L := by field_simp
    linarith
  have hfin := Chernoff5ec3b2ae.final_real c q L δ n hc0 hc1 hq0 hq1 hL0 hL hqn
  have hreal : P.real {z | k ≤ g z} ≤ δ / 9 := by
    have h1 : k * P.real {z | k ≤ g z} ≤ k * (δ / 9) := by
      calc k * P.real {z | k ≤ g z} ≤ (c * q + (1 - q)) ^ n := hmk
        _ ≤ k * (δ / 9) := hfin
    exact le_of_mul_le_mul_left h1 hk0
  calc P {z | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * q * n}
      ≤ P {z | k ≤ g z} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {z | k ≤ g z}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (δ / 9) := ENNReal.ofReal_le_ofReal hreal

-- ===== copied from Solutions/Sol_pv_70b97ce2.lean (ratio_bound_numeric) =====


/-- `log (max (K N) 2) / N ≤ max (log (K N₀)) 1 / N₀` for `N ≥ N₀ > 0`. -/
lemma rbn70_key (K N N0 : ℝ) (hK : 0 < K) (hN0 : 0 < N0) (hN : N0 ≤ N) :
    Real.log (max (K * N) 2) * N0 ≤ max (Real.log (K * N0)) 1 * N := by
  have hNpos : 0 < N := lt_of_lt_of_le hN0 hN
  have hM1 : 1 ≤ max (Real.log (K * N0)) 1 := le_max_right _ _
  have hMl : Real.log (K * N0) ≤ max (Real.log (K * N0)) 1 := le_max_left _ _
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hratio : 1 ≤ N / N0 := by rw [le_div_iff₀ hN0]; linarith
  have hbound : Real.log (max (K * N) 2) ≤ max (Real.log (K * N0)) 1 + N / N0 - 1 := by
    rcases le_total (K * N) 2 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]
      have hKN0 : 0 < K * N0 := mul_pos hK hN0
      have e1 : K * N = (K * N0) * (N / N0) := by field_simp
      rw [e1, Real.log_mul hKN0.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < N / N0 by positivity)
      linarith
  have h1 := mul_le_mul_of_nonneg_right hbound hN0.le
  have h2 : N / N0 * N0 = N := div_mul_cancel₀ N hN0.ne'
  have h3 := mul_le_mul_of_nonneg_left hN (show 0 ≤ max (Real.log (K * N0)) 1 - 1 by linarith)
  have h4 : (max (Real.log (K * N0)) 1 + N / N0 - 1) * N0
      = (max (Real.log (K * N0)) 1 - 1) * N0 + N := by
    linear_combination h2
  linarith

lemma rbn70_final (l2 d u L9 q m : ℝ) (hl2 : 69 / 100 < l2) (hd : 1 ≤ d) (hu : 4 * l2 ≤ u)
    (hL9 : L9 ≤ 4 * l2) (hm : 1800 ≤ m) (hq : m - 3 ≤ 4 * q) :
    20 / 7 * (13 * l2 * d + (L9 + u) + u) * (m + 1) < 150 * (d + u) * l2 * q := by
  have hl2p : 0 < l2 := by linarith
  have hup : 0 < u := by linarith
  have a1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 525 / 2 * (d + u) * l2 by positivity)
  have a2 : 0 ≤ l2 * d * (5 / 2 * m - 2095 / 2) :=
    mul_nonneg (by positivity) (by linarith)
  have a3' := mul_le_mul_of_nonneg_right hl2.le (show 0 ≤ m - 3 by linarith)
  have a3 : 0 < 525 / 2 * l2 * (m - 3) - 60 * (m + 1) := by nlinarith
  have a3'' : 0 ≤ 525 / 2 * l2 * (m - 3) - 40 * (m + 1) := by linarith
  have a4 : 0 ≤ (u - 4 * l2) * (525 / 2 * l2 * (m - 3) - 40 * (m + 1)) :=
    mul_nonneg (by linarith) a3''
  have a5 := mul_le_mul_of_nonneg_right hL9 (show 0 ≤ m + 1 by linarith)
  have a6 : 0 < l2 * (525 / 2 * l2 * (m - 3) - 60 * (m + 1)) := mul_pos hl2p a3
  nlinarith

lemma rbn70_b (L u d q m : ℝ) (hL : L ≤ u) (hu : 0 < u) (hd : 1 ≤ d) (hm : 1800 ≤ m)
    (hq : m - 3 ≤ 4 * q) :
    23 * L * (m + 1) < 150 * (d + u) * q := by
  have b1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 75 / 2 * (d + u) by positivity)
  have b2 := mul_le_mul_of_nonneg_right hL (show 0 ≤ m + 1 by linarith)
  have b3 : 0 < d * (m - 3) := mul_pos (by linarith) (by linarith)
  have b4 : 0 ≤ u * (29 / 2 * m - 271 / 2) := mul_nonneg hu.le (by linarith)
  nlinarith

set_option maxHeartbeats 1000000 in
open OptimalPAC.SampleComplexity in
theorem sib_ratio_bound_numeric (m d : ℕ) (hm : 1800 * Real.log (18 * Real.exp 1) - 1 < m)
    (hd : 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ (p : ℝ) (N : ℕ),
      23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) ≤ p →
      p ≤ 4 * 1800 / (m : ℝ) * (d + Real.log (9 * 18 / δ)) →
      7 / 10 * p * ((m / 4 : ℕ) : ℝ) ≤ N →
      p * (2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (18 / δ))) <
        150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ))) ∧
    23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) <
      150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  -- m ≥ 1800
  have hm1800 : (1800 : ℝ) ≤ m := by
    have h1 : 1 ≤ Real.log (18 * Real.exp 1) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
      have : 0 < Real.log 18 := Real.log_pos (by norm_num)
      linarith
    have h2 : (1799 : ℝ) < m := by linarith
    have h3 : (1799 : ℕ) < m := by exact_mod_cast h2
    exact_mod_cast (show 1800 ≤ m by omega)
  have hmpos : (0 : ℝ) < m := by linarith
  -- q
  have hq4 : (m : ℝ) - 3 ≤ 4 * ((m / 4 : ℕ) : ℝ) := by
    have h : m ≤ 4 * (m / 4) + 3 := by omega
    have h' : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast h
    linarith
  have hq4' : 4 * ((m / 4 : ℕ) : ℝ) ≤ m := by
    have h : 4 * (m / 4) ≤ m := by omega
    exact_mod_cast h
  set q : ℝ := ((m / 4 : ℕ) : ℝ) with hqdef
  have hqpos : 0 < q := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  -- logs
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hu4 : 4 * Real.log 2 ≤ Real.log (18 / δ) := by
    rw [← hlog16]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hδ0]; linarith
  have hL9 : Real.log 9 ≤ 4 * Real.log 2 := by
    rw [← hlog16]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hL9pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hw : Real.log (9 * 18 / δ) = Real.log 9 + Real.log (18 / δ) := by
    rw [show (9 : ℝ) * 18 / δ = 9 * (18 / δ) by ring]
    exact Real.log_mul (by norm_num) (by positivity)
  have h9le : Real.log (9 / δ) ≤ Real.log (18 / δ) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by norm_num) hδ0.le
  have h9pos : 0 < Real.log (9 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ0]; linarith
  set u := Real.log (18 / δ) with hudef
  have hup : 0 < u := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro p N hp1 hp2 hN
    rw [hw] at hp2
    set w := Real.log 9 + u with hwdef
    have hwpos : 0 < w := by linarith
    have hp : 0 < p := lt_of_lt_of_le (by positivity) hp1
    set N0 := 7 / 10 * p * q with hN0def
    have hN0 : 0 < N0 := by positivity
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hN0 hN
    -- p q ≤ 1800 (d + w)
    have hpm : p * m ≤ 7200 * (d + w) := by
      have e : 4 * 1800 / (m : ℝ) * (d + w) * m = 7200 * (d + w) := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_right hp2 hmpos.le
      linarith
    have hpq : p * q ≤ 1800 * (d + w) := by
      have := mul_le_mul_of_nonneg_left hq4' hp.le
      nlinarith
    -- K
    set K := 2 * Real.exp 1 / d with hKdef
    have hK : 0 < K := by positivity
    have hkey := rbn70_key K N N0 hK hN0 hN
    set M := max (Real.log (K * N0)) 1 with hMdef
    -- bound M
    have hKN0 : K * N0 ≤ 2520 * Real.exp 1 * ((d + w) / d) := by
      rw [hKdef, hN0def]
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
      have : 2520 * Real.exp 1 * ((d + w) / d) * d = 2520 * Real.exp 1 * (d + w) := by
        field_simp
      rw [this]
      nlinarith
    have hlog2520 : Real.log (2520 * Real.exp 1) ≤ 13 * Real.log 2 := by
      have : Real.log ((2 : ℝ) ^ 13) = 13 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      rw [← this]
      apply Real.log_le_log (by positivity)
      have := Real.exp_one_lt_d9
      norm_num; linarith
    have hMb : M ≤ 13 * Real.log 2 + w / d := by
      have hwd : 0 ≤ w / d := by positivity
      apply max_le
      · have hpos : 0 < K * N0 := mul_pos hK hN0
        have h1 := Real.log_le_log hpos hKN0
        have h1' : Real.log (2520 * Real.exp 1 * ((d + w) / d))
            = Real.log (2520 * Real.exp 1) + Real.log ((d + w) / d) :=
          Real.log_mul (by positivity) (by positivity)
        have h2 := Real.log_le_sub_one_of_pos (show 0 < (d + w) / d by positivity)
        have h3 : (d + w) / d - 1 = w / d := by field_simp; ring
        linarith
      · linarith
    have hdM : d * M ≤ 13 * Real.log 2 * d + w := by
      have := mul_le_mul_of_nonneg_left hMb hdpos.le
      have e : d * (w / d) = w := by field_simp
      nlinarith
    -- the main quantity
    set A := Real.log (max (K * N) 2) with hAdef
    have hS : p * q * (d * A + u) ≤ 10 / 7 * (13 * Real.log 2 * d + w + u) * N := by
      have s1 := mul_le_mul_of_nonneg_left hkey hdpos.le
      have s2 := mul_le_mul_of_nonneg_right hdM hNpos.le
      have s3 := mul_le_mul_of_nonneg_left hN hup.le
      rw [hN0def] at s1 s3
      linarith
    have hF := rbn70_final (Real.log 2) d u (Real.log 9) q m (by linarith) hd' hu4 hL9 hm1800
      hq4
    -- rewrite the goal
    have h18 : max (18 / δ) 2 = 18 / δ := by
      apply max_eq_left
      rw [le_div_iff₀ hδ0]; linarith
    have hKN : 2 * Real.exp 1 * (N : ℝ) / d = K * N := by rw [hKdef]; ring
    have hgoal : p * (2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (18 / δ)))
        = 2 * p * (d * A + u) / (N * Real.log 2) := by
      simp only [Log2, Real.logb]
      rw [hKN, h18]
      field_simp
      rw [hAdef, hudef, mul_comm (N : ℝ) K]
    rw [hgoal, div_lt_iff₀ (by positivity)]
    have t1 := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ 2 * (m + 1) by positivity)
    have t2 := mul_lt_mul_of_pos_left hF hNpos
    have t3 : q * (2 * p * (d * A + u)) < q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) := by
      have e : 150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2) * (m + 1)
          = 150 * (d + u) * Real.log 2 * N := by field_simp
      have t4 : q * (2 * p * (d * A + u)) * (m + 1) <
          q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) * (m + 1) := by
        have e2 : q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) * (m + 1)
            = q * (150 * (d + u) * Real.log 2 * N) := by rw [mul_assoc, e]
        rw [e2]
        linarith
      exact lt_of_mul_lt_mul_right t4 hm1.le
    exact lt_of_mul_lt_mul_left t3 hqpos.le
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff₀ hqpos hm1]
    exact rbn70_b (Real.log (9 / δ)) u d q m h9le hup hd' hm1800 hq4


-- ##### ASSEMBLY: Claim (9) from Lemma 4 #####
namespace OptimalPAC.SampleComplexity

open scoped ENNReal

/-- Lemma 4 (39b66463) as a hypothesis, for every probability measure. -/
def L4Hyp {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (d : ℕ) (f : X → Bool) : Prop :=
  ∀ (Q : Measure X), IsProbabilityMeasure Q → ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ (N : ℕ), 1 ≤ N →
    Measure.pi (fun _ : Fin N => Q)
      {z | ∃ h ∈ consistent C (labeled f z),
        2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (2 / δ)) < er Q h f}
      ≤ ENNReal.ofReal δ

theorem er_le_one {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (h f : X → Bool) : er P h f ≤ 1 := by
  unfold er
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem one_le_d {X : Type*} (C : Set (X → Bool)) (hC3 : 3 ≤ C.encard) (d : ℕ)
    (hd : vcDim C = d) : 1 ≤ d := by
  have h1 : 1 < C.encard := lt_of_lt_of_le (by norm_num) hC3
  obtain ⟨g1, g2, hg1, hg2, hne⟩ := Set.one_lt_encard_iff.mp h1
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  have hsh : Shatters C (fun _ : Fin 1 => y) := by
    intro lab
    by_cases hl : lab 0 = g1 y
    · exact ⟨g1, hg1, fun i => by fin_cases i; simpa using hl.symm⟩
    · have h2 : g2 y = lab 0 := by
        revert hl hy; cases lab 0 <;> cases g1 y <;> cases g2 y <;> simp
      exact ⟨g2, hg2, fun i => by fin_cases i; simpa using h2⟩
  have : (1 : ℕ∞) ≤ vcDim C := by
    unfold vcDim
    exact le_iSup₂_of_le (f := fun (k : ℕ) (_ : ∃ x : Fin k → _, Shatters C x) => (k : ℕ∞)) 1
      ⟨_, hsh⟩ (by simp)
  rw [hd] at this
  exact_mod_cast this

/-- A segment of the labelled sample. -/
def seg {X : Type*} (f : X → Bool) {m : ℕ} (x : Fin m → X) (s len : ℕ) : List (X × Bool) :=
  ((labeled f x).drop s).take len

theorem seg_consistent {X : Type*} (f : X → Bool) {m : ℕ} (x : Fin m → X) (s len : ℕ) :
    ∀ pr ∈ seg f x s len, f pr.1 = pr.2 := by
  intro pr hpr
  have h := List.mem_of_mem_drop (List.mem_of_mem_take hpr)
  simp only [labeled, List.mem_ofFn] at h
  obtain ⟨i, rfl⟩ := h
  rfl

theorem labeled_eq_segs {X : Type*} (f : X → Bool) {m : ℕ} (x : Fin m → X) (a q : ℕ)
    (hm : m = a + q + q + q) :
    labeled f x = seg f x 0 a ++ seg f x a q ++ seg f x (a + q) q ++ seg f x (a + q + q) q := by
  set l := labeled f x with hl0
  have hl : l.length = a + q + q + q := by simp [hl0, labeled, hm]
  simp only [seg, List.drop_zero, List.append_assoc]
  have e3 : (l.drop (a + q + q)).take q = l.drop (a + q + q) :=
    List.take_of_length_le (by simp [hl])
  have d2 : l.drop (a + q + q) = (l.drop (a + q)).drop q := by
    rw [List.drop_drop]
  have d1 : l.drop (a + q) = (l.drop a).drop q := by
    rw [List.drop_drop]
  rw [e3, d2, List.take_append_drop, d1, List.take_append_drop, List.take_append_drop]

theorem seg_length {X : Type*} (f : X → Bool) {m : ℕ} (x : Fin m → X) (s len : ℕ)
    (h : s + len ≤ m) : (seg f x s len).length = len := by
  simp [seg, labeled]; omega

theorem seg_extend_out {X : Type*} (f : X → Bool) {q m : ℕ} (e : Fin q → Fin m)
    (u : Fin q → X) (x : Fin m → X) (s len : ℕ)
    (hdis : ∀ k, (e k : ℕ) < s ∨ s + len ≤ e k) :
    seg f (Function.extend e u x) s len = seg f x s len := by
  apply List.ext_getElem
  · simp [seg, labeled]
  · intro i h1 h2
    have hi : i < len := by simp [seg, labeled] at h1; omega
    simp only [seg, labeled, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    rw [Function.extend_apply']
    rintro ⟨k, hk⟩
    have := hdis k
    rw [hk] at this
    simp at this
    omega

theorem seg_extend_in {X : Type*} (f : X → Bool) {q m : ℕ} (off : ℕ) (h : off + q ≤ m)
    (u : Fin q → X) (x : Fin m → X) :
    seg f (Function.extend (fun k : Fin q => (⟨off + k, by omega⟩ : Fin m)) u x) off q =
      labeled f u := by
  have hinj : Function.Injective (fun k : Fin q => (⟨off + k, by omega⟩ : Fin m)) := by
    intro k1 k2 h12
    have := congrArg Fin.val h12
    simp at this
    exact Fin.ext this
  apply List.ext_getElem
  · simp [seg, labeled]; omega
  · intro i h1 h2
    have hi : i < q := by simpa [labeled] using h2
    have key : Function.extend (fun k : Fin q => (⟨off + k, by omega⟩ : Fin m)) u x
        ⟨off + i, by omega⟩ = u ⟨i, hi⟩ := hinj.extend_apply u x ⟨i, hi⟩
    simp only [seg, labeled, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    simp only [key]

theorem filter_len {X : Type*} (pr : X → Bool) : ∀ {q : ℕ} (u : Fin q → X),
    ((List.ofFn u).filter pr).length = ∑ k, (if pr (u k) = true then 1 else 0)
  | 0, u => by simp
  | q + 1, u => by
    rw [List.ofFn_succ, List.filter_cons, Fin.sum_univ_succ, ← filter_len pr (fun i => u i.succ)]
    by_cases h : pr (u 0) = true <;> simp [h] <;> omega

theorem b1_meas_learner {X : Type*} [MeasurableSpace X] (L : List (X × Bool) → X → Bool)
    (hLm : LearnerMeasurable L) (S : List (X × Bool)) : Measurable (L S) := by
  have h := (hLm S.length).comp (measurable_const.prodMk measurable_id :
    Measurable (fun x : X => ((fun i : Fin S.length => S.get i), x)))
  have e : (fun p : (Fin S.length → X × Bool) × X => L (List.ofFn p.1) p.2) ∘
      (fun x : X => ((fun i : Fin S.length => S.get i), x)) = L S := by
    funext x; simp
  rwa [e] at h

theorem claim9_step {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (L : List (X × Bool) → X → Bool) (hL : IsConsistentLearner C L) (hLm : LearnerMeasurable L)
    (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool) (hf : f ∈ C) (hL4 : L4Hyp C d f)
    (m : ℕ) (hm : 1800 * Real.log (18 * Real.exp 1) - 1 < m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (T : List (X × Bool)) (hT : ∀ p ∈ T, f p.1 = p.2)
    (IH : ∀ m' < m, 1 ≤ m' → ∀ δ' : ℝ, 0 < δ' → δ' < 1 → ∀ T' : List (X × Bool),
      (∀ p ∈ T', f p.1 = p.2) →
      Measure.pi (fun _ : Fin m' => P)
        {x | 1800 / ((m' : ℝ) + 1) * (d + Real.log (18 / δ')) <
          er P (hannekeLearner L (labeled f x) T') f} ≤ ENNReal.ofReal δ') :
    Measure.pi (fun _ : Fin m => P)
      {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (hannekeLearner L (labeled f x) T) f} ≤ ENNReal.ofReal δ := by
  classical
  have hfm : Measurable f := hCm f hf
  have hd1 : 1 ≤ d := one_le_d C hC3 d hd
  have hm7 : 4 ≤ m := by
    have h1 : (2 : ℝ) < Real.log (18 * Real.exp 1) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
      have : (1 : ℝ) < Real.log 18 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      linarith
    have : (4 : ℝ) < m := by linarith
    exact_mod_cast this.le
  set q := m / 4 with hq
  set a := m - 3 * q with ha
  have hq1 : 1 ≤ q := by omega
  have ha1 : 1 ≤ a := by omega
  have hmaq : m = a + q + q + q := by omega
  have ha4 : m ≤ 4 * a := by omega
  set μ := Measure.pi (fun _ : Fin m => P) with hμ
  -- segments, training sets, voters
  let S0 : (Fin m → X) → List (X × Bool) := fun x => seg f x 0 a
  let Sb : Fin 3 → (Fin m → X) → List (X × Bool) := fun i x => seg f x (a + i * q) q
  let Ti : Fin 3 → (Fin m → X) → List (X × Bool) := fun i x =>
    (![Sb 1 x ++ Sb 2 x, Sb 0 x ++ Sb 2 x, Sb 0 x ++ Sb 1 x] i) ++ T
  let G : Fin 3 → (Fin m → X) → List (X → Bool) := fun i x => (subsamples (S0 x) (Ti i x)).map L
  let hI : Fin 3 → (Fin m → X) → X → Bool := fun i x => hannekeLearner L (S0 x) (Ti i x)
  let ei : Fin 3 → Fin q → Fin m := fun i k => ⟨a + i * q + k, by
    have := i.isLt; have := k.isLt
    have : (i : ℕ) * q ≤ 2 * q := Nat.mul_le_mul_right q (by omega)
    omega⟩
  set thrA : ℝ := 4 * 1800 / (m : ℝ) * (d + Real.log (9 * 18 / δ)) with hthrA
  set thrC : ℝ := 23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) with hthrC
  set Bv : ℝ := 150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) with hBv
  let A : Fin 3 → Set (Fin m → X) := fun i => {x | thrA < er P (hI i x) f}
  let Bc : Fin 3 → Set (Fin m → X) := fun i => {x | thrC ≤ er P (hI i x) f ∧
    (({k : Fin q | x (ei i k) ∈ ER (hI i x) f}.ncard : ℕ) : ℝ) < 7 / 10 * er P (hI i x) f * q}
  let D : Fin 3 → Set (Fin m → X) := fun i => {x | ∃ j, j ≠ i ∧ ∃ h ∈ G j x,
    Bv < (P (ER (hI i x) f ∩ ER h f)).toReal}
  let Dp : Fin 3 → Set (Fin m → X) := fun i => D i \ (A i ∪ Bc i)
  -- facts about the training sets
  have hTi_sub : ∀ i x, ∀ p ∈ Ti i x, p ∈ Sb 0 x ∨ p ∈ Sb 1 x ∨ p ∈ Sb 2 x ∨ p ∈ T := by
    intro i x p hp
    fin_cases i <;> simp [Ti] at hp <;> tauto
  have hTi_cons : ∀ i x, ∀ p ∈ Ti i x, f p.1 = p.2 := by
    intro i x p hp
    rcases hTi_sub i x p hp with h | h | h | h
    · exact seg_consistent f x _ _ p h
    · exact seg_consistent f x _ _ p h
    · exact seg_consistent f x _ _ p h
    · exact hT p h
  have hTi_contains : ∀ i j, j ≠ i → ∀ x, ∀ p ∈ Sb i x, p ∈ Ti j x := by
    intro i j hij x p hp
    fin_cases i <;> fin_cases j <;> simp [Ti] at hij hp ⊢ <;> simp [hp]
  have hS0_cons : ∀ x, ∀ p ∈ S0 x, f p.1 = p.2 := fun x => seg_consistent f x _ _
  -- measurability
  have hS0m : LMeasN (min a (m - 0)) S0 := lm_take (lm_drop (lm_labeled f hfm m) 0) a
  have hSbm : ∀ j, ∃ n, LMeasN n (Sb j) := fun j => ⟨_, lm_take (lm_drop (lm_labeled f hfm m) _) q⟩
  have hTim : ∀ i, ∃ n, LMeasN n (Ti i) := by
    intro i
    obtain ⟨n0, h0⟩ := hSbm 0
    obtain ⟨n1, h1⟩ := hSbm 1
    obtain ⟨n2, h2⟩ := hSbm 2
    fin_cases i
    · exact ⟨_, lm_append (lm_append h1 h2) (lm_const T)⟩
    · exact ⟨_, lm_append (lm_append h0 h2) (lm_const T)⟩
    · exact ⟨_, lm_append (lm_append h0 h1) (lm_const T)⟩
  have hGll : ∀ i, LLMeas (fun x => subsamples (S0 x) (Ti i x)) :=
    fun i => llm_subsamples _ S0 (Ti i) hS0m (hTim i)
  have hIm : ∀ i, Measurable (fun p : (Fin m → X) × X => hI i p.1 p.2) :=
    fun i => llm_majority L hLm (hGll i)
  have herm : ∀ i, Measurable (fun x => er P (hI i x) f) :=
    fun i => meas_er P f hfm (hI i) (hIm i)
  have hδ9 : 0 < δ / 9 := by positivity
  have hδ9' : δ / 9 < 1 := by linarith
  have hlog9 : Real.log (18 / (δ / 9)) = Real.log (9 * 18 / δ) := by
    congr 1; field_simp
  have hthrIH : 1800 / ((a : ℝ) + 1) * (d + Real.log (18 / (δ / 9))) ≤ thrA := by
    rw [hlog9, hthrA]
    have hK : 0 ≤ (d : ℝ) + Real.log (9 * 18 / δ) := by
      have : 0 ≤ Real.log (9 * 18 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
      positivity
    apply mul_le_mul_of_nonneg_right _ hK
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [div_le_div_iff₀ (by positivity) hm0]
    have : (m : ℝ) ≤ 4 * a := by exact_mod_cast ha4
    nlinarith
  have hAb : ∀ i, μ (A i) ≤ ENNReal.ofReal (δ / 9) := by
    intro i
    have hAm : MeasurableSet (A i) := measurableSet_lt measurable_const (herm i)
    let e0 : Fin a → Fin m := fun k => ⟨0 + k, by omega⟩
    have he0 : Function.Injective e0 := by
      intro k1 k2 h12
      have := congrArg Fin.val h12
      simp [e0] at this
      exact Fin.ext this
    refine B1Fub.fubini_extend P e0 he0 (A i) hAm _ (fun x => ?_)
    have hS0' : ∀ u, S0 (Function.extend e0 u x) = labeled f u :=
      fun u => seg_extend_in f 0 (by omega) u x
    have hSb' : ∀ u j, Sb j (Function.extend e0 u x) = Sb j x := by
      intro u j
      exact seg_extend_out f e0 u x _ _ (fun k => Or.inl (by
        have := k.isLt; simp [e0]; nlinarith [Nat.zero_le ((j : ℕ) * q)]))
    have hTi' : ∀ u, Ti i (Function.extend e0 u x) = Ti i x := by
      intro u; simp only [Ti, hSb']
    have hsub : {u | Function.extend e0 u x ∈ A i} ⊆ {u : Fin a → X |
        1800 / ((a : ℝ) + 1) * (d + Real.log (18 / (δ / 9))) <
          er P (hannekeLearner L (labeled f u) (Ti i x)) f} := by
      intro u hu
      simp only [A, hI, Set.mem_setOf_eq] at hu ⊢
      rw [hS0', hTi'] at hu
      exact lt_of_le_of_lt hthrIH hu
    exact (measure_mono hsub).trans
      (IH a (by omega) ha1 (δ / 9) hδ9 hδ9' (Ti i x) (hTi_cons i x))
  -- block replacement facts
  have hei_inj : ∀ i, Function.Injective (ei i) := by
    intro i k1 k2 h12
    have := congrArg Fin.val h12
    simp [ei] at this
    exact Fin.ext this
  have hrepl : ∀ i x u, hI i (Function.extend (ei i) u x) = hI i x ∧
      (∀ k, Function.extend (ei i) u x (ei i k) = u k) ∧
      Sb i (Function.extend (ei i) u x) = labeled f u := by
    intro i x u
    have hS0' : S0 (Function.extend (ei i) u x) = S0 x :=
      seg_extend_out f (ei i) u x 0 a (fun k => Or.inr
        (show 0 + a ≤ a + (i : ℕ) * q + k by rw [Nat.zero_add, Nat.add_assoc]; exact Nat.le_add_right _ _))
    have hSb' : ∀ j, j ≠ i → Sb j (Function.extend (ei i) u x) = Sb j x := by
      intro j hji
      refine seg_extend_out f (ei i) u x _ _ (fun k => ?_)
      have hk := k.isLt
      have hne : (i : ℕ) ≠ j := fun h => hji (Fin.ext h.symm)
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · left
        have h' : (i : ℕ) * q + q ≤ (j : ℕ) * q := by
          have := Nat.mul_le_mul_right q (show (i : ℕ) + 1 ≤ j from h)
          rwa [Nat.add_mul, one_mul] at this
        simp only [ei]
        linarith
      · right
        have h' : (j : ℕ) * q + q ≤ (i : ℕ) * q := by
          have := Nat.mul_le_mul_right q (show (j : ℕ) + 1 ≤ i from h)
          rwa [Nat.add_mul, one_mul] at this
        simp only [ei]
        linarith
    have hTi' : Ti i (Function.extend (ei i) u x) = Ti i x := by
      fin_cases i <;> simp at hSb' ⊢ <;> simp [Ti, hSb']
    refine ⟨?_, fun k => (hei_inj i).extend_apply u x k, ?_⟩
    · simp only [hI]; rw [hS0', hTi']
    · exact seg_extend_in f (a + i * q) (by
        have hi := i.isLt
        have : (i : ℕ) * q ≤ 2 * q := Nat.mul_le_mul_right q (by omega)
        omega) u x
  have hERm : ∀ i x, MeasurableSet (ER (hI i x) f) := by
    intro i x
    have hh : Measurable (hI i x) := (hIm i).comp (measurable_const.prodMk measurable_id)
    have hc : MeasurableSet {q : Bool × Bool | q.1 ≠ q.2} := (Set.to_countable _).measurableSet
    exact (hh.prodMk hfm) hc
  have hBcm : ∀ i, MeasurableSet (Bc i) := by
    intro i
    have hcnt : ∀ x : Fin m → X, (({k : Fin q | x (ei i k) ∈ ER (hI i x) f}.ncard : ℕ) : ℝ) =
        ∑ k, (if x (ei i k) ∈ ER (hI i x) f then (1 : ℝ) else 0) := by
      intro x
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
      push_cast; rfl
    have hsetk : ∀ k, MeasurableSet {x : Fin m → X | x (ei i k) ∈ ER (hI i x) f} := by
      intro k
      have hc : MeasurableSet {q : Bool × Bool | q.1 ≠ q.2} := (Set.to_countable _).measurableSet
      have hφ : Measurable (fun x : Fin m → X => (hI i x (x (ei i k)), f (x (ei i k)))) :=
        ((hIm i).comp (measurable_id.prodMk (measurable_pi_apply (ei i k)))).prodMk
          (hfm.comp (measurable_pi_apply _))
      exact hφ hc
    have hcm : Measurable (fun x : Fin m → X =>
        (({k : Fin q | x (ei i k) ∈ ER (hI i x) f}.ncard : ℕ) : ℝ)) := by
      simp_rw [hcnt]
      exact Finset.measurable_sum _ (fun k _ => Measurable.ite (hsetk k) measurable_const
        measurable_const)
    exact
      (measurableSet_le measurable_const (herm i)).inter
        (measurableSet_lt hcm (((herm i).const_mul _).mul_const _))
  have hBb : ∀ i, μ (Bc i) ≤ ENNReal.ofReal (δ / 9) := by
    intro i
    refine B1Fub.fubini_extend P (ei i) (hei_inj i) (Bc i) (hBcm i) _ (fun x => ?_)
    by_cases hp : thrC ≤ er P (hI i x) f
    · have hsub : {u | Function.extend (ei i) u x ∈ Bc i} ⊆ {z : Fin q → X |
          (({t : Fin q | z t ∈ ER (hI i x) f}.ncard : ℕ) : ℝ) <
            7 / 10 * (P (ER (hI i x) f)).toReal * q} := by
        intro u hu
        obtain ⟨h1, h2, -⟩ := hrepl i x u
        simp only [Bc, Set.mem_setOf_eq, h1, h2] at hu
        exact hu.2
      exact (measure_mono hsub).trans
        (sib_chernoff_count_lower P (ER (hI i x) f) (hERm i x) q hq1 δ hδ0 hδ1 hp)
    · have : {u | Function.extend (ei i) u x ∈ Bc i} = ∅ := by
        ext u
        simp only [Bc, Set.mem_setOf_eq, (hrepl i x u).1]
        simp [hp]
      rw [this]; simp
  have hBvpos : 0 < Bv := by
    have hl : 0 < Real.log (18 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [hBv]; positivity
  have hDm : ∀ i, MeasurableSet (D i) := by
    intro i
    have e1 : D i = ⋃ j : Fin 3, ⋃ (_ : j ≠ i),
        {x | ∃ h ∈ G j x, Bv < (P (ER (hI i x) f ∩ ER h f)).toReal} := by
      ext x; simp [D]
    rw [e1]
    refine MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => ?_))
    obtain ⟨k, R', hR', e⟩ := hGll j
    have e2 : {x | ∃ h ∈ G j x, Bv < (P (ER (hI i x) f ∩ ER h f)).toReal} =
        ⋃ t : Fin k, {x | Bv < (P (ER (hI i x) f ∩ ER (L (R' t x)) f)).toReal} := by
      ext x
      simp only [G, e x, List.map_ofFn, List.mem_ofFn, Set.mem_range, Set.mem_setOf_eq,
        Set.mem_iUnion, Function.comp_apply]
      constructor
      · rintro ⟨h, ⟨t, rfl⟩, hlt⟩; exact ⟨t, hlt⟩
      · rintro ⟨t, hlt⟩; exact ⟨_, ⟨t, rfl⟩, hlt⟩
    rw [e2]
    refine MeasurableSet.iUnion (fun t => measurableSet_lt measurable_const ?_)
    have hRt : Measurable (fun p : (Fin m → X) × X => L (R' t p.1) p.2) := by
      obtain ⟨n, g, hg, eg⟩ := hR' t
      have := (hLm n).comp ((hg.comp measurable_fst).prodMk measurable_snd)
      convert this using 1
      funext p
      simp [eg]
    have hs : MeasurableSet {p : (Fin m → X) × X |
        hI i p.1 p.2 ≠ f p.2 ∧ L (R' t p.1) p.2 ≠ f p.2} := by
      have hc : MeasurableSet {q : Bool × Bool | q.1 ≠ q.2} := (Set.to_countable _).measurableSet
      exact (((hIm i).prodMk (hfm.comp measurable_snd)) hc).inter
        ((hRt.prodMk (hfm.comp measurable_snd)) hc)
    exact (measurable_measure_prodMk_left (ν := P) hs).ennreal_toReal
  have hDb : ∀ i, μ (Dp i) ≤ ENNReal.ofReal (δ / 9) := by
    intro i
    have hDpm : MeasurableSet (Dp i) :=
      (hDm i).diff ((measurableSet_lt measurable_const (herm i)).union (hBcm i))
    refine B1Fub.fubini_extend P (ei i) (hei_inj i) (Dp i) hDpm _ (fun x => ?_)
    by_cases hPE : P (ER (hI i x) f) = 0
    · have : {u | Function.extend (ei i) u x ∈ Dp i} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hu
        obtain ⟨⟨j, hji, h, hh, hlt⟩, -⟩ := hu
        rw [(hrepl i x u).1] at hlt
        have h0 : P (ER (hI i x) f ∩ ER h f) = 0 := measure_mono_null Set.inter_subset_left hPE
        rw [h0] at hlt
        simp at hlt
        linarith
      rw [this]; simp
    · haveI : IsProbabilityMeasure (ProbabilityTheory.cond P (ER (hI i x) f)) :=
        ProbabilityTheory.cond_isProbabilityMeasure hPE
      let Bset : Set (List X) := {l | l ≠ [] ∧ ∃ h ∈ C, (∀ y ∈ l, h y = f y) ∧
        2 / (l.length : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * l.length / d) +
          Log2 (2 / (δ / 9))) < er (ProbabilityTheory.cond P (ER (hI i x) f)) h f}
      have hB0 : ([] : List X) ∉ Bset := fun h => h.1 rfl
      have hη : ∀ N, 1 ≤ N → Measure.pi (fun _ : Fin N => ProbabilityTheory.cond P (ER (hI i x) f))
          {v | List.ofFn v ∈ Bset} ≤ ENNReal.ofReal (δ / 9) := by
        intro N hN
        refine (measure_mono ?_).trans (hL4 _ inferInstance (δ / 9) hδ9 hδ9' N hN)
        rintro v ⟨-, h, hC, hcons, hlt⟩
        refine ⟨h, ⟨hC, fun pr hpr => ?_⟩, by simpa using hlt⟩
        simp only [labeled, List.mem_ofFn, Set.mem_range] at hpr
        obtain ⟨k, rfl⟩ := hpr
        exact hcons _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
      refine (measure_mono ?_).trans
        (B1Cond.cs_bound P (ER (hI i x) f) (hERm i x) hPE q Bset hB0 _ hη)
      intro u hu
      obtain ⟨h1, h2, h3⟩ := hrepl i x u
      obtain ⟨⟨j, hji, h, hh, hlt⟩, hnAB⟩ := hu
      simp only [Set.mem_union, not_or] at hnAB
      obtain ⟨hnA, hnB⟩ := hnAB
      simp only [A, Bc, Set.mem_setOf_eq, h1, h2, not_lt, not_and] at hnA hnB
      rw [h1] at hlt
      have hle : (P (ER (hI i x) f ∩ ER h f)).toReal ≤ er P (hI i x) f :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
      have hBvp : Bv < er P (hI i x) f := lt_of_lt_of_le hlt hle
      have hrat := sib_ratio_bound_numeric m d hm hd1 δ hδ0 hδ1
      have hthrC : thrC < Bv := hrat.2
      have hpC : thrC ≤ er P (hI i x) f := by linarith
      have hN := hnB hpC
      have hp0 : 0 < er P (hI i x) f := by linarith
      -- the filtered list and its length
      have hlenP : ∀ pr : X → Bool, (∀ y, pr y = true ↔ y ∈ ER (hI i x) f) →
          ((((List.ofFn u).filter pr).length : ℕ) : ℝ) =
            (({k : Fin q | u k ∈ ER (hI i x) f}.ncard : ℕ) : ℝ) := by
        intro pr hpr
        rw [filter_len pr u, Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hk : u k ∈ ER (hI i x) f
        · have := (hpr (u k)).mpr hk; simp [hk, this]
        · have : pr (u k) = false := by
            cases hv : pr (u k)
            · rfl
            · exact absurd ((hpr (u k)).mp hv) hk
          simp [hk, this]
      have hLen := hlenP (fun y => decide (y ∈ ER (hI i x) f)) (fun y => decide_eq_true_iff)
      obtain ⟨Ŝ, hŜ, rfl⟩ := List.mem_map.mp hh
      obtain ⟨hCŜ, hTŜ⟩ := b1_learner_consistent C L hL f hf _ _ (hS0_cons _) (hTi_cons j _) Ŝ hŜ
      have hNpos : (0 : ℝ) < 7 / 10 * er P (hI i x) f * q := by
        have : (0 : ℝ) < q := by exact_mod_cast hq1
        positivity
      refine ⟨?_, L Ŝ, hCŜ, ?_, ?_⟩
      · intro hnil
        have := hLen
        rw [hnil] at this
        simp at this
        linarith
      · intro y hy
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_filter hy)
        have hmem : (u k, f (u k)) ∈ Sb i (Function.extend (ei i) u x) := by
          rw [h3]; exact List.mem_ofFn.mpr ⟨k, rfl⟩
        exact hTŜ _ (hTi_contains i j hji _ _ hmem)
      · set N := ((List.ofFn u).filter (fun y => decide (y ∈ ER (hI i x) f))).length with hNdef
        have hNq : 7 / 10 * er P (hI i x) f * ((m / 4 : ℕ) : ℝ) ≤ (N : ℝ) := by
          rw [hLen]; exact hN
        have hka := hrat.1 (er P (hI i x) f) N hpC hnA hNq
        have h29 : (2 : ℝ) / (δ / 9) = 18 / δ := by field_simp; ring
        rw [h29]
        have herQ : er (ProbabilityTheory.cond P (ER (hI i x) f)) (L Ŝ) f =
            (P (ER (hI i x) f ∩ ER (L Ŝ) f)).toReal / er P (hI i x) f := by
          unfold er
          rw [ProbabilityTheory.cond_apply (hERm i x), ENNReal.toReal_mul, ENNReal.toReal_inv]
          ring
        rw [herQ, lt_div_iff₀ hp0]
        nlinarith
  have hcover : {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
      er P (hannekeLearner L (labeled f x) T) f} ⊆ ⋃ i, (A i ∪ Bc i ∪ Dp i) := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have hnD : ∀ i, x ∉ D i := by
      intro i hD
      have h1 := hnot i
      simp only [Set.mem_union, not_or] at h1
      exact h1.2 ⟨hD, fun h => by rcases h with h | h; exact h1.1.1 h; exact h1.1.2 h⟩
    have hB : ∀ i j : Fin 3, j ≠ i → ∀ h ∈ G j x,
        (P (ER (majority (G i x)) f ∩ ER h f)).toReal ≤ Bv := by
      intro i j hij h hh
      by_contra hlt
      exact hnD i ⟨j, hij, h, hh, lt_of_not_ge hlt⟩
    have hlen : ∀ i, (G i x).length = (subsamples (S0 x) []).length := by
      intro i
      simp only [G, List.length_map]
      exact (b1_subsamples_mem_aux _ (S0 x) (Ti i x) rfl).2.1 []
    have hn1 : 1 ≤ (subsamples (S0 x) []).length :=
      (b1_subsamples_mem_aux _ (S0 x) [] rfl).2.2
    have hGm : ∀ i, ∀ h ∈ G i x, Measurable h := by
      intro i h hh
      obtain ⟨S', -, rfl⟩ := List.mem_map.mp hh
      exact b1_meas_learner L hLm S'
    have h12 := (sib_majority_error_le_twelve P f hfm (fun i => G i x) _ hn1 hlen hGm).2 Bv hB
    have hsplit : hannekeLearner L (labeled f x) T = majority (G 0 x ++ G 1 x ++ G 2 x) := by
      have e1 := labeled_eq_segs f x a q hmaq
      have hl0 : (seg f x 0 a).length = a := seg_length f x 0 a (by omega)
      have hl1 : (seg f x a q).length = q := seg_length f x a q (by omega)
      have hl2 : (seg f x (a + q) q).length = q := seg_length f x (a + q) q (by omega)
      have hl3 : (seg f x (a + q + q) q).length = q := seg_length f x (a + q + q) q (by omega)
      unfold hannekeLearner
      rw [e1, b1_subsamples_split _ _ _ _ T q hl1 hl2 hl3 (by rw [hl0]; omega) (by rw [hl0]; omega)]
      simp only [List.map_append, G, Ti, S0, Sb]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, two_mul, add_assoc]
    have hx' : 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (majority (G 0 x ++ G 1 x ++ G 2 x)) f := by
      rw [← hsplit]; exact hx
    have : 12 * Bv = 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) := by
      rw [hBv]; ring
    linarith
  have h9 : ENNReal.ofReal δ = 9 * ENNReal.ofReal (δ / 9) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  calc μ {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (hannekeLearner L (labeled f x) T) f}
      ≤ μ (⋃ i, (A i ∪ Bc i ∪ Dp i)) := measure_mono hcover
    _ ≤ ∑ i, μ (A i ∪ Bc i ∪ Dp i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 3, (ENNReal.ofReal (δ / 9) + ENNReal.ofReal (δ / 9) + ENNReal.ofReal (δ / 9)) :=
        Finset.sum_le_sum (fun i _ => (measure_union_le _ _).trans
          (add_le_add ((measure_union_le _ _).trans (add_le_add (hAb i) (hBb i))) (hDb i)))
    _ = ENNReal.ofReal δ := by
        rw [h9]; simp [Fin.sum_univ_three]; ring


/-- Claim (9) from Lemma 4 (taken as the hypothesis `hL4`), by strong induction on `m`. -/
theorem claim9_of_L4 {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (L : List (X × Bool) → X → Bool) (hL : IsConsistentLearner C L) (hLm : LearnerMeasurable L)
    (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool) (hf : f ∈ C) (hL4 : L4Hyp C d f) :
    ∀ m : ℕ, 1 ≤ m → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ T : List (X × Bool), (∀ p ∈ T, f p.1 = p.2) →
      Measure.pi (fun _ : Fin m => P)
        {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
          er P (hannekeLearner L (labeled f x) T) f} ≤ ENNReal.ofReal δ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm1 δ hδ0 hδ1 T hT
  by_cases hm : 1800 * Real.log (18 * Real.exp 1) - 1 < m
  · exact claim9_step C hCm hC3 d hd L hL hLm P f hf hL4 m hm δ hδ0 hδ1 T hT
      (fun m' hm' hm1' δ' h0 h1 T' hT' => ih m' hm' hm1' δ' h0 h1 T' hT')
  · have hd1 := one_le_d C hC3 d hd
    have hthr : 1 ≤ 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) := by
      push_neg at hm
      have hl : Real.log (18 * Real.exp 1) ≤ d + Real.log (18 / δ) := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
        have h18 : Real.log 18 ≤ Real.log (18 / δ) :=
          Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ0]; nlinarith)
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        linarith
      have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
      nlinarith
    have : {x : Fin m → X | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (hannekeLearner L (labeled f x) T) f} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (er_le_one P _ f).trans hthr
    rw [this]; simp

end OptimalPAC.SampleComplexity

-- ##### glue (from 1b0af15c_glue.lean) #####
open MeasureTheory
namespace OptimalPAC.SampleComplexity

open scoped ENNReal

theorem g1b_meas_count {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (p : (X → Bool) → X → Bool) (hp : ∀ h ∈ L, MeasurableSet {x | p h x = true}) :
    Measurable (fun x => ((L.countP (fun h => p h x) : ℕ) : ℝ≥0∞)) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hp h (List.mem_cons_of_mem a hh))
    have ha := hp a List.mem_cons_self
    simp only [List.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact ih'.add (Measurable.ite ha measurable_const measurable_const)

theorem g1b_meas_majority {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) : Measurable (majority L) := by
  apply measurable_to_bool
  have h1 := g1b_meas_count L (fun h x => decide (h x = false))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton false) using 1
      ext x; simp)
  have h2 := g1b_meas_count L (fun h x => decide (h x = true))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton true) using 1
      ext x; simp)
  have : majority L ⁻¹' {true} =
      {x | ((L.countP (fun h => decide (h x = false)) : ℕ) : ℝ≥0∞) ≤
        ((L.countP (fun h => decide (h x = true)) : ℕ) : ℝ≥0∞)} := by
    ext x; simp [majority]
  rw [this]
  exact measurableSet_le h1 h2

theorem g1b_meas_learner {X : Type*} [MeasurableSpace X] (L : List (X × Bool) → X → Bool)
    (hLm : LearnerMeasurable L) (S : List (X × Bool)) : Measurable (L S) := by
  have h := (hLm S.length).comp (measurable_const.prodMk measurable_id :
    Measurable (fun x : X => ((fun i : Fin S.length => S.get i), x)))
  have e : (fun p : (Fin S.length → X × Bool) × X => L (List.ofFn p.1) p.2) ∘
      (fun x : X => ((fun i : Fin S.length => S.get i), x)) = L S := by
    funext x; simp
  rwa [e] at h

/-- Glue: `hanneke_learner_pac` follows from Claim (9) (`majority_subsample_error_bound`, taken as a
hypothesis at `T = []`). -/
theorem g1b_pac_of_claim9 {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → Bool)
    (L : List (X × Bool) → X → Bool) (d : ℕ) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm : ⌊1800 / ε * (d + Real.log (18 / δ))⌋₊ ≤ m)
    (h9 : 1 ≤ m → Measure.pi (fun _ : Fin m => P)
      {x | 1800 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) <
        er P (hannekeLearner L (labeled f x) []) f} ≤ ENNReal.ofReal δ) :
    Measure.pi (fun _ : Fin m => P)
      {x | ε < er P (hannekeLearner L (labeled f x) []) f} ≤ ENNReal.ofReal δ := by
  have hK : 1 < (d : ℝ) + Real.log (18 / δ) := by
    have h18 : (18 : ℝ) < 18 / δ := by rw [lt_div_iff₀ hδ0]; nlinarith
    have : (1 : ℝ) < Real.log (18 / δ) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := Real.exp_one_lt_d9; linarith
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hlt := Nat.lt_floor_add_one (1800 / ε * ((d : ℝ) + Real.log (18 / δ)))
  have hm' : (⌊1800 / ε * ((d : ℝ) + Real.log (18 / δ))⌋₊ : ℝ) ≤ m := by exact_mod_cast hm
  have hbig : 1800 / ε * ((d : ℝ) + Real.log (18 / δ)) < (m : ℝ) + 1 := by linarith
  have hm1 : 1 ≤ m := by
    have h1800 : (1800 : ℝ) < 1800 / ε * ((d : ℝ) + Real.log (18 / δ)) := by
      have : (1800 : ℝ) ≤ 1800 / ε := by rw [le_div_iff₀ hε0]; nlinarith
      nlinarith
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  refine le_trans (measure_mono ?_) (h9 hm1)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  refine lt_of_le_of_lt ?_ hx
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hε0] at hbig
  linarith


end OptimalPAC.SampleComplexity


open MeasureTheory OptimalPAC.SampleComplexity in
theorem solution {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (L : List (X × Bool) → X → Bool) (hL : IsConsistentLearner C L) (hLm : LearnerMeasurable L)
    (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool) (hf : f ∈ C)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : ⌊1800 / ε * (d + Real.log (18 / δ))⌋₊ ≤ m) :
    Measure.pi (fun _ : Fin m => P)
      {x | ε < er P (hannekeLearner L (labeled f x) []) f}
      ≤ ENNReal.ofReal δ := by
  exact g1b_pac_of_claim9 P f L d ε δ hε0 hε1 hδ0 hδ1 m hm
    (fun hm1 => claim9_of_L4 C hCm hC3 d hd L hL hLm P f hf
      (fun Q hQ δ' h0 h1 N hN =>
        @consistent_error_bound X _ C hCm hC3 d hd hWB δ' h0 h1 N hN f hf Q hQ)
      m hm1 δ hδ0 hδ1 [] (by simp))
