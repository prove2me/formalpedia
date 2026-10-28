-- Prove2me | solution 1 for PrivateRelease.VCLowerBound.theorem_3_11_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T05:52:31.853024+00:00
-- url     : https://prove2.me/submissions/c1869e17-5f04-49fc-92d7-15aa9ea18ad8

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_HighDimProb_Chaining_VcDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_PrivateRelease_VCLowerBound_Queries
import Definitions.Def_PrivLearn_Generic_Privacy
import Mathlib.Tactic.Finiteness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Ring



namespace PrivateRelease.VCLowerBound
open HighDimProb.Chaining

/-- Shattering restricts to any subset. -/
theorem shatters_subset {X : Type} {C : Set (X → Bool)} {S T : Set X}
    (h : Shatters C S) (hTS : T ⊆ S) : Shatters C T := by
  classical
  intro g
  let G : S → Bool := fun x => if hx : x.1 ∈ T then g ⟨x.1, hx⟩ else false
  obtain ⟨f, hf, hfg⟩ := h G
  refine ⟨f, hf, ?_⟩
  intro x
  simpa [G, x.property] using hfg ⟨x.1, hTS x.property⟩

/-- A finite lower bound on the supremum in VC dimension has a finite shattered witness. -/
theorem exists_shattered_of_succ_le_vcDim {X : Type} (C : Set (X → Bool)) (k : ℕ)
    (hvc : ((k + 1 : ℕ) : ℕ∞) ≤ vcDim C) :
    ∃ S : Set X, Shatters C S ∧ S.encard = (k + 1 : ℕ) := by
  classical
  have hex : ∃ S : {S : Set X // Shatters C S}, (k : ℕ∞) < S.val.encard := by
    by_contra hn
    push_neg at hn
    have hup : vcDim C ≤ (k : ℕ∞) := iSup_le hn
    have hbad := hvc.trans hup
    exact (Nat.not_succ_le_self k) (by exact_mod_cast hbad)
  obtain ⟨S, hS⟩ := hex
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ S.val.encard := by
    simpa only [Nat.cast_add, Nat.cast_one] using (ENat.natCast_add_one_le_iff.mpr hS)
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_encard_eq hle
  exact ⟨T, shatters_subset S.property hTS, hT⟩

end PrivateRelease.VCLowerBound


namespace PrivateRelease.VCLowerBound
open HighDimProb.Chaining

/-- A shattered pair of alternatives for every database coordinate. -/
theorem exists_shattered_pairs {X : Type} (C : Set (X → Bool)) (n : ℕ)
    (hn : 1 ≤ n) (hvc : ((2 * n : ℕ) : ℕ∞) ≤ vcDim C) :
    ∃ e : (Fin n × Bool) → X, Function.Injective e ∧
      ∀ g : (Fin n × Bool) → Bool, ∃ φ ∈ C, ∀ p, φ (e p) = g p := by
  classical
  have hk : ((2 * n - 1 + 1 : ℕ) : ℕ∞) ≤ vcDim C := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] using hvc
  obtain ⟨S, hS, hcard⟩ := exists_shattered_of_succ_le_vcDim C (2 * n - 1) hk
  have hcard' : S.encard = (2 * n : ℕ) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] using hcard
  letI : Fintype S := (Set.finite_of_encard_eq_coe hcard').fintype
  have hc : Fintype.card (Fin n × Bool) = Fintype.card S := by
    have hs : Fintype.card S = 2 * n := by
      simpa only [Set.encard, ENat.card_eq_coe_fintype_card, Nat.cast_inj] using hcard'
    simp [hs, Nat.mul_comm]
  let E : (Fin n × Bool) ≃ S := Fintype.equivOfCardEq hc
  refine ⟨fun p => (E p).val, Subtype.val_injective.comp E.injective, ?_⟩
  intro g
  obtain ⟨φ, hφ, hφg⟩ := hS (fun x => g (E.symm x))
  refine ⟨φ, hφ, ?_⟩
  intro p
  simpa using hφg (E p)

end PrivateRelease.VCLowerBound





namespace PrivateRelease.VCLowerBound
open MeasureTheory

/-- Measurably choose a satisfied condition from a finite family whenever one exists. -/
theorem finite_measurable_selector {O B : Type} [MeasurableSpace O]
    [MeasurableSpace B] (d : B) (s : Finset B) (S : B → Set O)
    (hS : ∀ b ∈ s, MeasurableSet (S b)) :
    ∃ g : O → B, Measurable g ∧
      ∀ o, (∃ b ∈ s, o ∈ S b) → o ∈ S (g o) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => d, measurable_const, ?_⟩
      simp
  | @insert b s hb ih =>
      obtain ⟨g, hgm, hg⟩ := ih (fun a ha => hS a (Finset.mem_insert_of_mem ha))
      refine ⟨fun o => if o ∈ S b then b else g o,
        Measurable.ite (hS b (Finset.mem_insert_self b s)) measurable_const hgm, ?_⟩
      intro o ho
      by_cases hob : o ∈ S b
      · simpa [hob]
      · simp only [hob, ↓reduceIte]
        apply hg o
        obtain ⟨a, ha, hoa⟩ := ho
        refine ⟨a, ?_, hoa⟩
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact False.elim (hob hoa)
        · exact ha

end PrivateRelease.VCLowerBound




namespace PrivateRelease.VCLowerBound
open MeasureTheory

/-- One record is selected independently from each pair. -/
def pairDatabase {X : Type} {n : ℕ} (e : (Fin n × Bool) → X)
    (b : Fin n → Bool) : Fin n → X := fun i => e (i, b i)

/-- Labels separating the records chosen only by the first bit string. -/
def separatingLabels {n : ℕ} (b c : Fin n → Bool) (p : Fin n × Bool) : Bool :=
  if b p.1 = c p.1 then false else decide (p.2 = b p.1)

/-- A pair-separating counting query reads off normalized Hamming distance. -/
theorem pair_separating_count {X : Type} {n : ℕ} (e : (Fin n × Bool) → X)
    (b c : Fin n → Bool) (φ : X → Bool)
    (hφ : ∀ p, φ (e p) = separatingLabels b c p) :
    countQ φ (pairDatabase e b) =
        ((Finset.univ.filter fun i => b i ≠ c i).card : ℝ) / n ∧
      countQ φ (pairDatabase e c) = 0 := by
  classical
  have hb : ∀ i, φ (pairDatabase e b i) = decide (b i ≠ c i) := by
    intro i
    rw [pairDatabase, hφ]
    by_cases h : b i = c i <;> simp [separatingLabels, h]
  have hc : ∀ i, φ (pairDatabase e c i) = false := by
    intro i
    rw [pairDatabase, hφ]
    by_cases h : b i = c i
    · simp [separatingLabels, h]
    · simp [separatingLabels, h, Ne.symm h]
  constructor
  · simp only [countQ, hb, decide_eq_true_eq]
  · simp [countQ, hc]

/-- Two candidates agreeing with a common answer vector differ in at most `2αn` bits. -/
theorem candidate_hamming_bound {X : Type} {n : ℕ}
    (e : (Fin n × Bool) → X) (b c : Fin n → Bool) (φ : X → Bool)
    (hφ : ∀ p, φ (e p) = separatingLabels b c p)
    (a α : ℝ) (hn : 0 < n)
    (hb : |a - countQ φ (pairDatabase e b)| ≤ α)
    (hc : |a - countQ φ (pairDatabase e c)| ≤ α) :
    ((Finset.univ.filter fun i => b i ≠ c i).card : ℝ) ≤ 2 * α * n := by
  classical
  obtain ⟨hqb, hqc⟩ := pair_separating_count e b c φ hφ
  rw [hqb] at hb
  rw [hqc, sub_zero] at hc
  have hh : ((Finset.univ.filter fun i => b i ≠ c i).card : ℝ) / n ≤ 2 * α := by
    have hb' := (abs_le.mp hb).1
    have hc' := (abs_le.mp hc).2
    linarith
  exact (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mp hh

end PrivateRelease.VCLowerBound



namespace PrivateRelease.VCLowerBound
open MeasureTheory

/-- The finite family of shattered labels admits a measurable approximate reconstruction. -/
theorem exists_measurable_reconstruction {X O : Type} [MeasurableSpace O] {n : ℕ}
    (C : Set (X → Bool)) (e : (Fin n × Bool) → X)
    (rep : ((Fin n × Bool) → Bool) → (X → Bool))
    (hrep : ∀ g p, rep g (e p) = g p) (hmem : ∀ g, rep g ∈ C)
    (hn : 0 < n) (M : (Fin n → X) → Measure O)
    (ans : O → (X → Bool) → ℝ) (α δ : ℝ)
    (hans : ∀ φ ∈ C, Measurable fun o => ans o φ)
    (huse : IsUseful C α δ M ans) :
    ∃ (guess : O → (Fin n → Bool)) (G : (Fin n → Bool) → Set O),
      Measurable guess ∧ (∀ b, MeasurableSet (G b)) ∧
      (∀ b, ENNReal.ofReal (1 - δ) ≤ M (pairDatabase e b) (G b)) ∧
      ∀ b o, o ∈ G b →
        ((Finset.univ.filter fun i => b i ≠ guess o i).card : ℝ) ≤ 2 * α * n := by
  classical
  let G : (Fin n → Bool) → Set O := fun b =>
    {o | ∀ g : (Fin n × Bool) → Bool,
      |ans o (rep g) - countQ (rep g) (pairDatabase e b)| ≤ α}
  have hG : ∀ b, MeasurableSet (G b) := by
    intro b
    change MeasurableSet {o | ∀ g : (Fin n × Bool) → Bool,
      |ans o (rep g) - countQ (rep g) (pairDatabase e b)| ≤ α}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun g =>
      measurableSet_le ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable.comp (hans (rep g) (hmem g))) measurable_const
  obtain ⟨guess, hm, hg⟩ := finite_measurable_selector
    (fun _ : Fin n => false) Finset.univ G (fun b _ => hG b)
  refine ⟨guess, G, hm, hG, ?_, ?_⟩
  · intro b
    apply (huse (pairDatabase e b)).trans
    apply measure_mono
    intro o ho
    exact fun g => ho (rep g) (hmem g)
  · intro b o hob
    have hoc : o ∈ G (guess o) := hg o ⟨b, Finset.mem_univ b, hob⟩
    exact candidate_hamming_bound e b (guess o) (rep (separatingLabels b (guess o)))
      (hrep _) (ans o (rep (separatingLabels b (guess o)))) α hn
      (hob _) (hoc _)

end PrivateRelease.VCLowerBound

namespace PrivateRelease.VCLowerBound

/-- Flipping one pair choice changes exactly its corresponding record. -/
theorem pairDatabase_neighbors {X : Type} {n : ℕ} (e : (Fin n × Bool) → X)
    (he : Function.Injective e) (b : Fin n → Bool) (i : Fin n) :
    PrivLearn.Generic.Neighbors (pairDatabase e b)
      (pairDatabase e (Function.update b i (!(b i)))) := by
  classical
  refine ⟨i, ?_, ?_⟩
  · intro h
    have hpair := he h
    have hh : b i = !(b i) := by
      simpa [pairDatabase] using congrArg Prod.snd hpair
    cases hbi : b i <;> simp [hbi] at hh
  · intro j hj
    simp [pairDatabase, hj]

end PrivateRelease.VCLowerBound





namespace PrivateRelease.VCLowerBound
open MeasureTheory

 def bitFlip {n : ℕ} (b : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update b i (!(b i))

 theorem bitFlip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (fun b => bitFlip b i) := by
  intro b
  funext j
  by_cases h : j = i
  · subst j; simp [bitFlip]
  · simp [bitFlip, h]

 theorem bitFlip_average_dp {X O : Type*} [MeasurableSpace O] {n : ℕ}
    (db : (Fin n → Bool) → (Fin n → X))
    (hd : ∀ b i, PrivLearn.Generic.Neighbors (db b) (db (bitFlip b i)))
    (guess : O → (Fin n → Bool)) (hguess : ∀ i, Measurable (fun o => guess o i))
    (M : (Fin n → X) → Measure O) (hprob : ∀ z, IsProbabilityMeasure (M z))
    (ε : ℝ) (hdp : PrivLearn.Generic.IsDP M ε) :
    ∑ b, ∑ i, (M (db b) {o | guess o i = b i}).toReal ≤
      Real.exp ε * ∑ b, ∑ i, (M (db b) {o | guess o i ≠ b i}).toReal := by
  classical
  have hterm (b : Fin n → Bool) (i : Fin n) :
      (M (db b) {o | guess o i = b i}).toReal ≤
        Real.exp ε * (M (db (bitFlip b i)) {o | guess o i ≠ bitFlip b i i}).toReal := by
    have hm : MeasurableSet {o | guess o i = b i} :=
      (hguess i) (measurableSet_singleton (b i))
    have h := hdp (db b) (db (bitFlip b i)) (hd b i) _ hm
    haveI := hprob (db (bitFlip b i))
    haveI := hprob (db b)
    have hr := ENNReal.toReal_mono (by finiteness) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos ε).le] at hr
    convert hr using 2
    congr 2
    ext o
    simp only [Set.mem_setOf_eq, bitFlip, Function.update_self]
    cases guess o i <;> cases b i <;> decide
  calc
    _ ≤ ∑ b, ∑ i, Real.exp ε *
        (M (db (bitFlip b i)) {o | guess o i ≠ bitFlip b i i}).toReal :=
      Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ => hterm b i
    _ = Real.exp ε * ∑ b, ∑ i,
        (M (db (bitFlip b i)) {o | guess o i ≠ bitFlip b i i}).toReal := by
      simp_rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      rw [Finset.sum_comm, Finset.sum_comm (f := fun b i =>
        (M (db b) {o | guess o i ≠ b i}).toReal)]
      apply Finset.sum_congr rfl
      intro i _
      exact Fintype.sum_equiv ((bitFlip_involutive i).toPerm _) _ _ (fun b => rfl)

end PrivateRelease.VCLowerBound





namespace PrivateRelease.VCLowerBound
open MeasureTheory

/-- The expected number of events is the sum of their probabilities. -/
theorem integral_event_count {O I : Type*} [MeasurableSpace O] [Fintype I]
    (μ : Measure O) [IsProbabilityMeasure μ] (S : I → Set O)
    (hS : ∀ i, MeasurableSet (S i)) :
    ∫ o, ∑ i, (S i).indicator (fun _ => (1 : ℝ)) o ∂μ = ∑ i, (μ (S i)).toReal := by
  classical
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_one (hS i)
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hS i)

 theorem reconstruction_probability_bounds {O : Type*} [MeasurableSpace O] {n : ℕ}
    (μ : Measure O) [IsProbabilityMeasure μ] (guess : O → (Fin n → Bool))
    (hguess : ∀ i, Measurable (fun o => guess o i)) (b : Fin n → Bool)
    (G : Set O) (hG : MeasurableSet G) (α δ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ENNReal.ofReal (1 - δ) ≤ μ G)
    (herr : ∀ o ∈ G, ((Finset.univ.filter fun i => b i ≠ guess o i).card : ℝ) ≤
      2 * α * n) :
    (∑ i, (μ {o | guess o i ≠ b i}).toReal ≤ (n : ℝ) * (δ + 2 * α)) ∧
    ((n : ℝ) * (1 - δ) * (1 - 2 * α) ≤
      ∑ i, (μ {o | guess o i = b i}).toReal) := by
  classical
  let E : Fin n → Set O := fun i => {o | guess o i ≠ b i}
  let A : Fin n → Set O := fun i => {o | guess o i = b i}
  have hA i : MeasurableSet (A i) := (hguess i) (measurableSet_singleton (b i))
  have hE i : MeasurableSet (E i) := (hA i).compl
  let e : O → ℝ := fun o => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) o
  let a : O → ℝ := fun o => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) o
  have he : Integrable e μ := by
    apply integrable_finsetSum
    intro i _
    exact (integrable_const (1 : ℝ)).indicator (hE i)
  have ha : Integrable a μ := by
    apply integrable_finsetSum
    intro i _
    exact (integrable_const (1 : ℝ)).indicator (hA i)
  have heq o : e o = ((Finset.univ.filter fun i => b i ≠ guess o i).card : ℝ) := by
    simp [e, E, Set.indicator, ne_comm, Finset.card_filter]
  have hae o : a o + e o = n := by
    rw [← Finset.sum_add_distrib]
    have hh i : (A i).indicator (fun _ => (1 : ℝ)) o +
        (E i).indicator (fun _ => (1 : ℝ)) o = 1 := by
      by_cases h : guess o i = b i <;> simp [A, E, Set.indicator, h]
    simp only [a, e] at *
    simp_rw [hh]
    simp
  have henon o : 0 ≤ e o := by rw [heq]; positivity
  have hanon o : 0 ≤ a o := Finset.sum_nonneg fun i _ => by
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hemax o : e o ≤ n := by linarith [hae o, hanon o]
  have hmG : 1 - δ ≤ (μ G).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top μ G) hgood
    simpa [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)] using this
  have hcompl : (μ Gᶜ).toReal ≤ δ := by
    have hh := measure_add_measure_compl hG (μ := μ)
    have hh' := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_add (measure_ne_top μ G) (measure_ne_top μ Gᶜ)] at hh'
    simp at hh'
    linarith
  have hupper : ∫ o, e o ∂μ ≤ 2 * α * n + (n : ℝ) * (μ Gᶜ).toReal := by
    have hmono : e ≤ fun o => 2 * α * n + (n : ℝ) * Gᶜ.indicator (fun _ => (1 : ℝ)) o := by
      intro o
      by_cases ho : o ∈ G
      · simp only [Set.indicator, Set.mem_compl_iff, ho, not_true_eq_false, ↓reduceIte, mul_zero, add_zero]
        rw [heq]
        exact herr o ho
      · have hn : 0 ≤ 2 * α * n := by positivity
        simp only [Set.indicator, Set.mem_compl_iff, ho, not_false_eq_true, ↓reduceIte, mul_one]
        linarith [hemax o]
    calc
      _ ≤ ∫ o, 2 * α * n + (n : ℝ) * Gᶜ.indicator (fun _ => (1 : ℝ)) o ∂μ :=
        integral_mono he ((integrable_const _).add
          (((integrable_const (1 : ℝ)).indicator hG.compl).const_mul _)) hmono
      _ = _ := by rw [integral_add (integrable_const _)
          (((integrable_const (1 : ℝ)).indicator hG.compl).const_mul _),
          integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hG.compl]; simp [Measure.real]
  have hlower : (n : ℝ) * (1 - 2 * α) * (μ G).toReal ≤ ∫ o, a o ∂μ := by
    have hmono : (fun o => (n : ℝ) * (1 - 2 * α) * G.indicator (fun _ => (1 : ℝ)) o) ≤ a := by
      intro o
      by_cases ho : o ∈ G
      · simp only [Set.indicator_of_mem ho, mul_one]
        have hh := herr o ho
        rw [← heq] at hh
        linarith [hae o]
      · simpa [Set.indicator_of_notMem ho] using hanon o
    have hh := integral_mono
      (((integrable_const (1 : ℝ)).indicator hG).const_mul ((n : ℝ) * (1 - 2 * α))) ha hmono
    simpa [integral_const_mul, integral_indicator_const (1 : ℝ) hG, Measure.real] using hh
  rw [integral_event_count μ E hE] at hupper
  rw [integral_event_count μ A hA] at hlower
  constructor
  · dsimp [E] at hupper
    nlinarith [mul_le_mul_of_nonneg_left hcompl (Nat.cast_nonneg n)]
  · dsimp [A] at hlower
    have hn : 0 ≤ (n : ℝ) * (1 - 2 * α) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hmG hn]

end PrivateRelease.VCLowerBound







namespace PrivateRelease.VCLowerBound
open MeasureTheory

/-- Privacy versus finite measurable reconstruction, preserving the failure probability. -/
theorem theorem_3_11_explicit {X O : Type} [MeasurableSpace O] (C : Set (X → Bool)) (n : ℕ)
    (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) (ε α δ : ℝ)
    (hn : 1 ≤ n) (hvc : ((2 * n : ℕ) : ℕ∞) ≤ HighDimProb.Chaining.vcDim C)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hprob : ∀ z, IsProbabilityMeasure (M z))
    (hans : ∀ φ ∈ C, Measurable fun o => ans o φ)
    (hdp : PrivLearn.Generic.IsDP M ε) (huse : IsUseful C α δ M ans) :
    (1 - δ) * (1 - 2 * α) ≤ Real.exp ε * (δ + 2 * α) := by
  classical
  by_cases hα1 : α ≤ 1 / 2
  swap
  · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)).trans
      (mul_nonneg (Real.exp_pos ε).le (by linarith))
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨e, he, hs⟩ := exists_shattered_pairs C n hn hvc
  choose rep hmem hrep using hs
  obtain ⟨guess, G, hguess, hG, hgood, herr⟩ :=
    exists_measurable_reconstruction C e rep hrep hmem hn0 M ans α δ hans huse
  have hα0 : 0 ≤ α := by
    let b : Fin n → Bool := fun _ => false
    have hgpos : 0 < M (pairDatabase e b) (G b) :=
      (ENNReal.ofReal_pos.mpr (by linarith)).trans_le (hgood b)
    have hne : (G b).Nonempty := by
      by_contra h
      have hzero : G b = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hzero, measure_empty] at hgpos
      exact (lt_irrefl 0) hgpos
    obtain ⟨o, ho⟩ := hne
    have hh := herr b o ho
    have hc : (0 : ℝ) ≤ (Finset.univ.filter fun i => b i ≠ guess o i).card :=
      Nat.cast_nonneg _
    nlinarith
  have hcoord : ∀ i, Measurable (fun o => guess o i) :=
    fun i => (measurable_pi_apply i).comp hguess
  have hp (b : Fin n → Bool) :
      (∑ i, (M (pairDatabase e b) {o | guess o i ≠ b i}).toReal ≤
        (n : ℝ) * (δ + 2 * α)) ∧
      ((n : ℝ) * (1 - δ) * (1 - 2 * α) ≤
        ∑ i, (M (pairDatabase e b) {o | guess o i = b i}).toReal) := by
    letI : IsProbabilityMeasure (M (pairDatabase e b)) := hprob _
    exact reconstruction_probability_bounds (M (pairDatabase e b)) guess hcoord b
      (G b) (hG b) α δ hα0 hα1 hδ0.le hδ1.le (hgood b) (herr b)
  have hdpavg := bitFlip_average_dp (pairDatabase e)
    (fun b i => by simpa only [bitFlip] using pairDatabase_neighbors e he b i)
    guess hcoord M hprob ε hdp
  let K : ℝ := Fintype.card (Fin n → Bool)
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast Fintype.card_pos
  have hsumlow : K * ((n : ℝ) * (1 - δ) * (1 - 2 * α)) ≤
      ∑ b, ∑ i, (M (pairDatabase e b) {o | guess o i = b i}).toReal := by
    calc
      _ = ∑ _b : Fin n → Bool, (n : ℝ) * (1 - δ) * (1 - 2 * α) := by
        simp [K]
      _ ≤ _ := Finset.sum_le_sum fun b _ => (hp b).2
  have hsumup : (∑ b, ∑ i, (M (pairDatabase e b) {o | guess o i ≠ b i}).toReal) ≤
      K * ((n : ℝ) * (δ + 2 * α)) := by
    calc
      _ ≤ ∑ _b : Fin n → Bool, (n : ℝ) * (δ + 2 * α) :=
        Finset.sum_le_sum fun b _ => (hp b).1
      _ = _ := by simp [K]
  have hh := hsumlow.trans (hdpavg.trans
    (mul_le_mul_of_nonneg_left hsumup (Real.exp_pos ε).le))
  have hKn : 0 < K * (n : ℝ) := mul_pos hK hnR
  apply le_of_mul_le_mul_left (a := K * (n : ℝ)) ?_ hKn
  calc
    (K * (n : ℝ)) * ((1 - δ) * (1 - 2 * α)) =
        K * ((n : ℝ) * (1 - δ) * (1 - 2 * α)) := by ring
    _ ≤ Real.exp ε * (K * ((n : ℝ) * (δ + 2 * α))) := hh
    _ = (K * (n : ℝ)) * (Real.exp ε * (δ + 2 * α)) := by ring
end PrivateRelease.VCLowerBound




open MeasureTheory PrivateRelease.VCLowerBound

theorem solution {X O : Type} [MeasurableSpace O] (C : Set (X → Bool)) (n : ℕ)
    (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) (ε α δ : ℝ)
    (hn : 1 ≤ n) (hvc : ((2 * n : ℕ) : ℕ∞) ≤ HighDimProb.Chaining.vcDim C)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hprob : ∀ z, IsProbabilityMeasure (M z))
    (hans : ∀ φ ∈ C, Measurable fun o => ans o φ)
    (hdp : PrivLearn.Generic.IsDP M ε) (huse : IsUseful C α δ M ans) :
    (1 - δ) * (1 - 2 * α) ≤ Real.exp ε * (δ + 2 * α) := by
  exact PrivateRelease.VCLowerBound.theorem_3_11_explicit C n M ans ε α δ hn hvc hδ0 hδ1 hprob hans hdp huse

#print axioms solution
