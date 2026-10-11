-- Prove2me | solution 1 for TamingMonster.Regret.ips_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T11:50:32.467922+00:00
-- url     : https://prove2.me/submissions/c0634e9c-4c11-49c7-926d-1d613930a176

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

set_option autoImplicit false

namespace TamingMonster.Regret

open MeasureTheory

theorem epochOf_spec' {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ epochOf τ t ∧ τ (epochOf τ t - 1) < t ∧ t ≤ τ (epochOf τ t) := by
  have hne : ({m : ℕ | t ≤ τ m} : Set ℕ).Nonempty := ⟨t, (hτ.id_le t : t ≤ τ t)⟩
  have hmem : t ≤ τ (epochOf τ t) := Nat.sInf_mem hne
  have h1 : 1 ≤ epochOf τ t := by
    by_contra h
    push_neg at h
    have h0 : epochOf τ t = 0 := by omega
    rw [h0, hτ0] at hmem
    omega
  refine ⟨h1, ?_, hmem⟩
  have hlt : epochOf τ t - 1 < sInf {m : ℕ | t ≤ τ m} := by
    show epochOf τ t - 1 < epochOf τ t
    omega
  have := Nat.notMem_of_lt_sInf hlt
  simp only [Set.mem_setOf_eq, not_le] at this
  exact this


/-- For `0 < u ≤ 1`, `drawAction p u = a` iff `u` lies in the `a`-th CDF interval. -/
theorem drawAction_iff {K : ℕ} [NeZero K] (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (a : Fin K) :
    drawAction p u = a ↔ (∑ c ∈ Finset.Iio a, p c < u ∧ u ≤ ∑ c ∈ Finset.Iic a, p c) := by
  set S := Finset.univ.filter (fun b : Fin K => ∑ c ∈ Finset.Iic b, p c < u) with hS
  have hval : (drawAction p u).val = min S.card (K - 1) := rfl
  have hle : ∀ b : Fin K, S.card ≤ b.val ↔ u ≤ ∑ c ∈ Finset.Iic b, p c := by
    intro b
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      have hsub : Finset.Iic b ⊆ S := by
        intro c hc
        rw [hS, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ h'⟩
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Iic_subset_Iic.mpr (Finset.mem_Iic.mp hc)) (fun i _ _ => hp i)
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this
      omega
    · intro h
      have hsub : S ⊆ Finset.Iio b := by
        intro c hc
        rw [hS, Finset.mem_filter] at hc
        rw [Finset.mem_Iio]
        by_contra hcb
        push_neg at hcb
        have : ∑ i ∈ Finset.Iic b, p i ≤ ∑ i ∈ Finset.Iic c, p i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hcb)
            (fun i _ _ => hp i)
        linarith [hc.2]
      have := Finset.card_le_card hsub
      rwa [Fin.card_Iio] at this
  have hge : ∀ b : Fin K, b.val ≤ S.card ↔ ∑ c ∈ Finset.Iio b, p c < u := by
    intro b
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      rcases Nat.eq_zero_or_pos b.val with hb | hb
      · have : Finset.Iio b = ∅ := by
          ext c
          simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt, Fin.le_def]
          omega
        rw [this, Finset.sum_empty] at h'
        linarith
      · set b' : Fin K := ⟨b.val - 1, by omega⟩ with hb'
        have hsub : S ⊆ Finset.Iio b' := by
          intro c hc
          rw [hS, Finset.mem_filter] at hc
          rw [Finset.mem_Iio]
          by_contra hcb
          push_neg at hcb
          have hsub2 : Finset.Iio b ⊆ Finset.Iic c := by
            intro i hi
            rw [Finset.mem_Iio, Fin.lt_def] at hi
            rw [Finset.mem_Iic, Fin.le_def]
            rw [Fin.le_def] at hcb
            simp only [hb'] at hcb
            omega
          have : ∑ i ∈ Finset.Iio b, p i ≤ ∑ i ∈ Finset.Iic c, p i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => hp i)
          linarith [hc.2]
        have := Finset.card_le_card hsub
        rw [Fin.card_Iio] at this
        simp only [hb'] at this
        omega
    · intro h
      have hsub : Finset.Iio b ⊆ S := by
        intro c hc
        rw [hS, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ h⟩
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => hp i)
        intro i hi
        rw [Finset.mem_Iic] at hi
        rw [Finset.mem_Iio] at hc ⊢
        exact lt_of_le_of_lt hi hc
      have := Finset.card_le_card hsub
      rwa [Fin.card_Iio] at this
  rw [Fin.ext_iff, hval]
  have haK := a.isLt
  by_cases ha : a.val < K - 1
  · rw [← hge a, ← hle a]
    constructor
    · intro h
      constructor <;> omega
    · intro h
      omega
  · have hIic : Finset.Iic a = Finset.univ := by
      ext c
      have := c.isLt
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
      omega
    rw [hIic, hsum, ← hge a]
    constructor
    · intro h
      exact ⟨by omega, hu1⟩
    · intro h
      omega

/-- The law of `drawAction p U` for `U` uniform on `[0,1]` is `p`. -/
theorem drawAction_law {K : ℕ} [NeZero K] (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (a : Fin K) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) {u | drawAction p u = a} = ENNReal.ofReal (p a) := by
  set L := ∑ c ∈ Finset.Iio a, p c with hL
  set F := ∑ c ∈ Finset.Iic a, p c with hF
  have hFL : F = L + p a := by
    rw [hF, hL, ← Finset.Iio_insert, Finset.sum_insert (by simp)]
    ring
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun i _ => hp i)
  have hF1 : F ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)
  have hEq : {u : ℝ | drawAction p u = a} ∩ Set.Ioc 0 1 = Set.Ioc L F := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨hE, hu0, hu1⟩
      exact (drawAction_iff p hp hsum hu0 hu1 a).mp hE
    · rintro ⟨h1, h2⟩
      have hu0 : 0 < u := lt_of_le_of_lt hL0 h1
      have hu1 : u ≤ 1 := le_trans h2 hF1
      exact ⟨(drawAction_iff p hp hsum hu0 hu1 a).mpr ⟨h1, h2⟩, hu0, hu1⟩
  rw [Measure.restrict_apply' measurableSet_Icc]
  have hvol : volume (Set.Ioc L F) = ENNReal.ofReal (p a) := by
    rw [Real.volume_Ioc, hFL]
    ring_nf
  apply le_antisymm
  · calc volume ({u : ℝ | drawAction p u = a} ∩ Set.Icc 0 1)
        ≤ volume (Set.Ioc L F ∪ {0}) := by
          apply measure_mono
          intro u hu
          rcases eq_or_lt_of_le hu.2.1 with h | h
          · exact Or.inr h.symm
          · left
            rw [← hEq]
            exact ⟨hu.1, h, hu.2.2⟩
      _ ≤ volume (Set.Ioc L F) + volume ({0} : Set ℝ) := measure_union_le _ _
      _ = ENNReal.ofReal (p a) := by rw [Real.volume_singleton, add_zero, hvol]
  · rw [← hvol, ← hEq]
    exact measure_mono (Set.inter_subset_inter_right _ Set.Ioc_subset_Icc_self)

theorem measurable_drawAction_comp {α : Type*} [MeasurableSpace α] {K : ℕ} [NeZero K]
    {f : α → Fin K → ℝ} {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => drawAction (f x) (g x)) := by
  have hcard : Measurable (fun x =>
      (Finset.univ.filter (fun b : Fin K => ∑ c ∈ Finset.Iic b, f x c < g x)).card) := by
    simp_rw [Finset.card_filter]
    apply Finset.measurable_sum
    intro b _
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_lt (Finset.measurable_sum _
      (fun c _ => (measurable_pi_apply c).comp hf)) hg
  let G : ℕ → Fin K := fun n => ⟨min n (K - 1), by have := NeZero.pos K; omega⟩
  exact (measurable_of_countable G).comp hcard

theorem measurable_eval_pair {K : ℕ} :
    Measurable (fun fa : (Fin K → ℝ) × Fin K => fa.1 fa.2) :=
  measurable_from_prod_countable_left (fun a => measurable_pi_apply a)

theorem measurable_smoothProj {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (Q : Pi → ℝ) (μ : ℝ) :
    Measurable (fun x => smoothProj Pi Q μ x) := by
  classical
  apply measurable_pi_lambda
  intro a
  unfold smoothProj
  simp_rw [Finset.sum_filter]
  apply Measurable.add_const
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro π _
  apply Measurable.ite _ measurable_const measurable_const
  exact (hPiMeas π π.2) (measurableSet_singleton a)

theorem smoothProj_nonneg {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (hQ0 : ∀ π, 0 ≤ Q π) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    0 ≤ smoothProj Pi Q μ x a := by
  unfold smoothProj
  have := Finset.sum_nonneg (fun π (_ : π ∈ Finset.univ.filter
    (fun π : Pi => (π : X → Fin K) x = a)) => hQ0 π)
  have h1 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  positivity

theorem sum_weighted_fiber {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (x : X) (c : Fin K → ℝ) :
    ∑ a, (∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π) * c a
      = ∑ π : Pi, Q π * c ((π : X → Fin K) x) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun π : Pi => (π : X → Fin K) x)
    (fun π => Q π * c ((π : X → Fin K) x))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Finset.mem_filter] at hπ
  rw [hπ.2]

theorem smoothProj_sum {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (hQ1 : ∑ π, Q π = 1) (μ : ℝ) (x : X) : ∑ a, smoothProj Pi Q μ x a = 1 := by
  unfold smoothProj
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have := sum_weighted_fiber Pi Q x (fun _ => 1)
  simp only [mul_one] at this
  rw [this, hQ1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_drawAction {K : ℕ} [NeZero K] (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (f : Fin K → ℝ) :
    ∫ u, f (drawAction p u) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = ∑ a, p a * f a := by
  have hmeas : Measurable (fun u : ℝ => drawAction p u) :=
    measurable_drawAction_comp measurable_const measurable_id
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
  rw [← integral_map hmeas.aemeasurable (measurable_of_countable f).aestronglyMeasurable]
  have : IsProbabilityMeasure ((volume.restrict (Set.Icc (0 : ℝ) 1)).map
    (fun u => drawAction p u)) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def, Measure.map_apply hmeas (measurableSet_singleton a), smul_eq_mul]
  have : (fun u => drawAction p u) ⁻¹' {a} = {u | drawAction p u = a} := rfl
  rw [this, drawAction_law p hp hsum a, ENNReal.toReal_ofReal (hp a)]


section Hist

variable {X : Type*} {K : ℕ} [NeZero K] {Ω : Type*}

/-- The record of round `j + 1`. -/
noncomputable def recAt (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (j : ℕ) : Rec X K :=
  A.roundRecord (A.history Z U ω j) j (Z (j + 1) ω) (U (j + 1) ω)

theorem history_length (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℕ) : (A.history Z U ω t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [AlgoParams.history, ih]

theorem history_eq_ofFn (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℕ) : A.history Z U ω t = List.ofFn (fun j : Fin t => recAt A Z U ω j) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [AlgoParams.history, Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    rfl

theorem history_prefix (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (t k : ℕ) : ∃ l, A.history Z U ω (t + k) = A.history Z U ω t ++ l := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ [A.roundRecord (A.history Z U ω (t + k)) (t + k) (Z (t + k + 1) ω)
      (U (t + k + 1) ω)], ?_⟩
    show A.history Z U ω (t + k + 1) = _
    simp only [AlgoParams.history]
    rw [hl, List.append_assoc]

theorem history_take (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) {t n : ℕ} (h : t ≤ n) : (A.history Z U ω n).take t = A.history Z U ω t := by
  obtain ⟨l, hl⟩ := history_prefix A Z U ω t (n - t)
  rw [show n = t + (n - t) by omega, hl, List.take_left' (history_length A Z U ω t)]

theorem history_congr (A : AlgoParams X K) {Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ)
    (h : ∀ s, 1 ≤ s → s ≤ t → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    A.history Z U ω t = A.history Z' U' ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [AlgoParams.history]
    rw [ih (fun s h1 h2 => h s h1 (by omega)), (h (t + 1) (by omega) le_rfl).1,
      (h (t + 1) (by omega) le_rfl).2]

theorem measurable_recAt [MeasurableSpace X] [MeasurableSpace Ω] (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hrules : A.RulesMeasurable)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hU : ∀ t, Measurable (U t)) :
    ∀ j, Measurable (fun ω => recAt A Z U ω j) := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ (t := j + 1) (by omega)
  have hτm : A.τ (epochOf A.τ (j + 1) - 1) ≤ j := by omega
  have hHeq : ∀ ω, (A.history Z U ω j).take (A.τ (epochOf A.τ (j + 1) - 1))
      = List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k) := by
    intro ω
    rw [history_take A Z U ω hτm, history_eq_ofFn]
  have hHmeas : Measurable (fun ω => fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) =>
      recAt A Z U ω k) :=
    measurable_pi_lambda _ (fun k => ih k (by omega))
  have hsel : ∀ π : A.Pi, Measurable (fun ω => A.sel (epochOf A.τ (j + 1) - 1)
      (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)) π) :=
    fun π => (hrules.2 _ _ π).comp hHmeas
  have hpick : ∀ π : A.Pi, MeasurableSet {ω | A.pick
      (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)) = π} :=
    fun π => hHmeas (hrules.1 _ π)
  have hQt : ∀ π : A.Pi, Measurable (fun ω => complete A.Pi
      (A.weights (epochOf A.τ (j + 1) - 1)
        (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
      (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
      π) := by
    intro π
    have hw : ∀ π' : A.Pi, Measurable (fun ω => A.weights (epochOf A.τ (j + 1) - 1)
        (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)) π') := by
      intro π'
      by_cases hm : epochOf A.τ (j + 1) - 1 = 0
      · simp only [AlgoParams.weights, hm, if_true]
        exact measurable_const
      · simp only [AlgoParams.weights, hm, if_false]
        exact hsel π'
    unfold complete
    apply (hw π).add
    apply Measurable.ite _ (measurable_const.sub (Finset.measurable_sum _ (fun π' _ => hw π')))
      measurable_const
    have := hpick π
    simp only [eq_comm (a := π)]
    exact this
  have hp : Measurable (fun ω => smoothProj A.Pi (complete A.Pi
      (A.weights (epochOf A.τ (j + 1) - 1)
        (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
      (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k))))
      (muM A.Pi A.δ A.τ (epochOf A.τ (j + 1) - 1)) (Z (j + 1) ω).1) := by
    apply measurable_pi_lambda
    intro a
    unfold smoothProj
    simp_rw [Finset.sum_filter]
    apply Measurable.add_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro π _
    exact Measurable.ite ((hPiMeas π π.2).comp (measurable_fst.comp (hZ (j + 1)))
      (measurableSet_singleton a)) (hQt π) measurable_const
  have ha := measurable_drawAction_comp hp (hU (j + 1))
  have hrec : (fun ω => recAt A Z U ω j) = fun ω =>
      ((Z (j + 1) ω).1,
        drawAction (smoothProj A.Pi (complete A.Pi
          (A.weights (epochOf A.τ (j + 1) - 1)
            (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
          (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k))))
          (muM A.Pi A.δ A.τ (epochOf A.τ (j + 1) - 1)) (Z (j + 1) ω).1) (U (j + 1) ω),
        (Z (j + 1) ω).2 (drawAction (smoothProj A.Pi (complete A.Pi
          (A.weights (epochOf A.τ (j + 1) - 1)
            (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
          (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k))))
          (muM A.Pi A.δ A.τ (epochOf A.τ (j + 1) - 1)) (Z (j + 1) ω).1) (U (j + 1) ω)),
        smoothProj A.Pi (complete A.Pi
          (A.weights (epochOf A.τ (j + 1) - 1)
            (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
          (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k))))
          (muM A.Pi A.δ A.τ (epochOf A.τ (j + 1) - 1)) (Z (j + 1) ω).1
          (drawAction (smoothProj A.Pi (complete A.Pi
          (A.weights (epochOf A.τ (j + 1) - 1)
            (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k)))
          (A.pick (List.ofFn (fun k : Fin (A.τ (epochOf A.τ (j + 1) - 1)) => recAt A Z U ω k))))
          (muM A.Pi A.δ A.τ (epochOf A.τ (j + 1) - 1)) (Z (j + 1) ω).1) (U (j + 1) ω))) := by
    funext ω
    simp only [recAt, AlgoParams.roundRecord, hHeq]
  rw [hrec]
  exact (measurable_fst.comp (hZ (j + 1))).prodMk (ha.prodMk
    ((measurable_eval_pair.comp ((measurable_snd.comp (hZ (j + 1))).prodMk ha)).prodMk
      (measurable_eval_pair.comp (hp.prodMk ha))))

end Hist

section Incr

variable {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K] {Ω : Type*}

noncomputable def Bterm (A : AlgoParams X K) (D : Measure (X × (Fin K → ℝ)))
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  (1 - (K : ℝ) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) *
      ∑ π : A.Pi, A.Qtilde Z U ω (epochOf A.τ t - 1) π * polRegret A.Pi D (π : X → Fin K)
    + ((K : ℝ) - 1) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)

noncomputable def incr (A : AlgoParams X K) (D : Measure (X × (Fin K → ℝ)))
    (πstar : X → Fin K) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  ((Z t ω).2 (πstar (Z t ω).1) - (Z t ω).2 (A.action Z U ω t)) - Bterm A D Z U ω t

theorem Qtilde_congr (A : AlgoParams X K) {Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (m : ℕ)
    (h : ∀ s, 1 ≤ s → s ≤ A.τ m → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    A.Qtilde Z U ω m = A.Qtilde Z' U' ω' m := by
  unfold AlgoParams.Qtilde
  rw [history_congr A Z U ω Z' U' ω' _ h]

theorem Bterm_congr (A : AlgoParams X K) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (D : Measure (X × (Fin K → ℝ))) {Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ s, 1 ≤ s → s < t → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    Bterm A D Z U ω t = Bterm A D Z' U' ω' t := by
  obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ ht
  unfold Bterm
  rw [Qtilde_congr A Z U ω Z' U' ω' _ (fun s h1 h2 => h s h1 (by omega))]

theorem action_congr (A : AlgoParams X K) {Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ)
    (h : ∀ s, 1 ≤ s → s ≤ t + 1 → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    A.action Z U ω (t + 1) = A.action Z' U' ω' (t + 1) := by
  simp only [AlgoParams.action, Nat.add_sub_cancel]
  rw [history_congr A Z U ω Z' U' ω' t (fun s h1 h2 => h s h1 (by omega)),
    (h (t + 1) (by omega) le_rfl).1, (h (t + 1) (by omega) le_rfl).2]

theorem incr_congr (A : AlgoParams X K) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (D : Measure (X × (Fin K → ℝ))) (πstar : X → Fin K) {Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ s, 1 ≤ s → s ≤ t → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    incr A D πstar Z U ω t = incr A D πstar Z' U' ω' t := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  unfold incr
  rw [action_congr A Z U ω Z' U' ω' t' h,
    Bterm_congr A hτ0 hτ D Z U ω Z' U' ω' (t' + 1) ht (fun s h1 h2 => h s h1 h2.le),
    (h (t' + 1) ht le_rfl).1]

theorem measurable_Qtilde [MeasurableSpace Ω] (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hrules : A.RulesMeasurable)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hU : ∀ t, Measurable (U t)) (m : ℕ) (π : A.Pi) :
    Measurable (fun ω => A.Qtilde Z U ω m π) := by
  classical
  have hHmeas : Measurable (fun ω => fun k : Fin (A.τ m) => recAt A Z U ω k) :=
    measurable_pi_lambda _ (fun k => measurable_recAt A hPiMeas hrules hτ0 hτ Z U hZ hU k)
  have hw : ∀ π' : A.Pi, Measurable (fun ω => A.weights m (A.history Z U ω (A.τ m)) π') := by
    intro π'
    by_cases hm : m = 0
    · simp only [AlgoParams.weights, hm, if_true]
      exact measurable_const
    · simp only [AlgoParams.weights, hm, if_false, history_eq_ofFn]
      exact (hrules.2 m (A.τ m) π').comp hHmeas
  have hpick : MeasurableSet {ω | A.pick (A.history Z U ω (A.τ m)) = π} := by
    simp only [history_eq_ofFn]
    exact hHmeas (hrules.1 _ π)
  unfold AlgoParams.Qtilde complete
  apply (hw π).add
  apply Measurable.ite _ (measurable_const.sub (Finset.measurable_sum _ (fun π' _ => hw π')))
    measurable_const
  simp only [eq_comm (a := π)]
  exact hpick

theorem measurable_Bterm [MeasurableSpace Ω] (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hrules : A.RulesMeasurable)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (D : Measure (X × (Fin K → ℝ)))
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hU : ∀ t, Measurable (U t)) (t : ℕ) :
    Measurable (fun ω => Bterm A D Z U ω t) := by
  unfold Bterm
  exact (measurable_const.mul (Finset.measurable_sum _ (fun π _ =>
    (measurable_Qtilde A hPiMeas hrules hτ0 hτ Z U hZ hU _ π).mul_const _))).add
    measurable_const

theorem measurable_incr [MeasurableSpace Ω] (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hrules : A.RulesMeasurable)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (D : Measure (X × (Fin K → ℝ)))
    (πstar : X → Fin K) (hπ : Measurable πstar)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hU : ∀ t, Measurable (U t)) (t : ℕ) (ht : 1 ≤ t) :
    Measurable (fun ω => incr A D πstar Z U ω t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hact : Measurable (fun ω => A.action Z U ω (t' + 1)) := by
    have : (fun ω => A.action Z U ω (t' + 1)) = fun ω => (recAt A Z U ω t').2.1 := by
      funext ω
      simp only [AlgoParams.action, recAt, Nat.add_sub_cancel, Rec.act]
    rw [this]
    exact measurable_fst.comp (measurable_snd.comp
      (measurable_recAt A hPiMeas hrules hτ0 hτ Z U hZ hU t'))
  unfold incr
  refine Measurable.sub (Measurable.sub ?_ ?_)
    (measurable_Bterm A hPiMeas hrules hτ0 hτ D Z U hZ hU _)
  · exact measurable_eval_pair.comp ((measurable_snd.comp (hZ _)).prodMk
      (hπ.comp (measurable_fst.comp (hZ _))))
  · exact measurable_eval_pair.comp ((measurable_snd.comp (hZ _)).prodMk hact)

theorem Qtilde_prob (A : AlgoParams X K) (hsel : A.SelSolvesOP)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    (∀ π, 0 ≤ A.Qtilde Z U ω m π) ∧ ∑ π, A.Qtilde Z U ω m π = 1 := by
  classical
  have hQ : (∀ π, 0 ≤ A.weights m (A.history Z U ω (A.τ m)) π) ∧
      ∑ π, A.weights m (A.history Z U ω (A.τ m)) π ≤ 1 := by
    by_cases hm : m = 0
    · simp [AlgoParams.weights, hm]
    · have hop := hsel m (by omega) _ (history_length A Z U ω (A.τ m))
      simp only [AlgoParams.weights, hm, if_false]
      exact ⟨hop.1, hop.2.1⟩
  unfold AlgoParams.Qtilde complete
  constructor
  · intro π
    split_ifs
    · linarith [hQ.1 π, hQ.2]
    · linarith [hQ.1 π]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp

end Incr

theorem lintegral_indep_split {Ω S E : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] {V : Ω → S} {W : Ω → E}
    (hV : Measurable V) (hW : Measurable W) (hind : ProbabilityTheory.IndepFun V W P)
    {G : S × E → ENNReal} (hG : Measurable G) :
    ∫⁻ ω, G (V ω, W ω) ∂P = ∫⁻ s, ∫⁻ e, G (s, e) ∂(P.map W) ∂(P.map V) := by
  rw [← lintegral_prod G hG.aemeasurable,
    ← (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable
      hW.aemeasurable).mp hind, lintegral_map hG (hV.prodMk hW)]

section MGF

variable {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]

/-- Coordinates of the canonical sequence space. -/
def seqZ : ℕ → (ℕ → (X × (Fin K → ℝ)) × ℝ) → X × (Fin K → ℝ) := fun t s => (s t).1
def seqU : ℕ → (ℕ → (X × (Fin K → ℝ)) × ℝ) → ℝ := fun t s => (s t).2

theorem measurable_seqZ (t : ℕ) : Measurable (seqZ (X := X) (K := K) t) :=
  measurable_fst.comp (measurable_pi_apply t)

theorem measurable_seqU (t : ℕ) : Measurable (seqU (X := X) (K := K) t) :=
  measurable_snd.comp (measurable_pi_apply t)

/-- The data of the first `n` rounds (coordinate `0` repeated beyond `n`). -/
def preSeq {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ℕ → (X × (Fin K → ℝ)) × ℝ :=
  fun k => if k ≤ n then (Z k ω, U k ω) else (Z 0 ω, U 0 ω)

theorem muM_nonneg' (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) (m : ℕ) :
    0 ≤ muM Pi δ τ m := by
  unfold muM
  split_ifs
  · positivity
  · exact le_min (by positivity) (Real.sqrt_nonneg _)

theorem K_muM_le (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) (m : ℕ) :
    (K : ℝ) * muM Pi δ τ m ≤ 1 := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have h : muM Pi δ τ m ≤ 1 / (2 * (K : ℝ)) := by
    unfold muM
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have := mul_le_mul_of_nonneg_left h hK.le
  have e : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by field_simp
  linarith

theorem action_succ_eq {Ω : Type*} (A : AlgoParams X K) (hτ0 : A.τ 0 = 0)
    (hτ : StrictMono A.τ) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    A.action Z U ω (t + 1) = drawAction (smoothProj A.Pi
      (A.Qtilde Z U ω (epochOf A.τ (t + 1) - 1)) (muM A.Pi A.δ A.τ (epochOf A.τ (t + 1) - 1))
      (Z (t + 1) ω).1) (U (t + 1) ω) := by
  obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ (t := t + 1) (by omega)
  simp only [AlgoParams.action, AlgoParams.roundRecord, Nat.add_sub_cancel, Rec.act,
    AlgoParams.Qtilde]
  rw [history_take A Z U ω (by omega : A.τ (epochOf A.τ (t + 1) - 1) ≤ t)]

end MGF

theorem epochOf_eq_succ' {τ : ℕ → ℕ} (hτ : StrictMono τ) {m t : ℕ} (h1 : τ m < t)
    (h2 : t ≤ τ (m + 1)) : epochOf τ t = m + 1 := by
  unfold epochOf
  apply le_antisymm (Nat.sInf_le (show m + 1 ∈ {k : ℕ | t ≤ τ k} from h2))
  apply le_csInf ⟨m + 1, h2⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have : τ k ≤ τ m := hτ.monotone (by omega)
  simp only [Set.mem_setOf_eq] at hk
  omega

theorem epochOf_le_of' {τ : ℕ → ℕ} {t M : ℕ} (h : t ≤ τ M) : epochOf τ t ≤ M :=
  Nat.sInf_le h


lemma l13_sp_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (μ : ℝ)
    (hQ : ∀ π, 0 ≤ Q π) (hμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    μ ≤ smoothProj Pi Q μ x a := by
  unfold smoothProj
  have h1 : 0 ≤ ∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π :=
    Finset.sum_nonneg (fun π _ => hQ π)
  have h2 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  nlinarith [mul_nonneg h2 h1]

/-- `d_t / t` is antitone on `t ≥ 1`. -/
lemma l13_dT_ratio {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    dT Pi δ b / (b : ℝ) ≤ dT Pi δ a / (a : ℝ) := by
  have hcard : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPi
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  set y := 16 * (a : ℝ) ^ 2 * Pi.card / δ with hy
  have hy16 : 16 ≤ y := by
    rw [hy, le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ (a : ℝ) ^ 2 * Pi.card := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha') hcard
    nlinarith
  have hypos : 0 < y := by linarith
  have hL2 : 2 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hypos]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hdb : dT Pi δ b = Real.log y + 2 * Real.log ((b : ℝ) / a) := by
    unfold dT
    have e : 16 * (b : ℝ) ^ 2 * Pi.card / δ = y * ((b : ℝ) / a) ^ 2 := by
      rw [hy]; field_simp
    rw [e, Real.log_mul hypos.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have hda : dT Pi δ a = Real.log y := rfl
  have hlog : Real.log ((b : ℝ) / a) ≤ (b : ℝ) / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlog' : (a : ℝ) * Real.log ((b : ℝ) / a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left hlog hapos.le
    have e : (a : ℝ) * ((b : ℝ) / a - 1) = b - a := by field_simp
    linarith
  rw [div_le_div_iff₀ hbpos hapos, hdb, hda]
  nlinarith [mul_le_mul_of_nonneg_right hL2 (by linarith : (0 : ℝ) ≤ b - a)]

section Params

variable {X : Type*} {K : ℕ} [NeZero K]

lemma l13_mu_le (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) (m : ℕ) :
    muM Pi δ τ m ≤ 1 / (2 * (K : ℝ)) := by
  unfold muM
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma l13_mu_anti (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) {j k : ℕ} (hjk : j ≤ k) :
    muM Pi δ τ k ≤ muM Pi δ τ j := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  by_cases hj : j = 0
  · subst hj
    have : muM Pi δ τ 0 = 1 / (2 * (K : ℝ)) := by simp [muM]
    rw [this]; exact l13_mu_le Pi δ τ k
  · have hk : k ≠ 0 := by omega
    unfold muM
    rw [if_neg hj, if_neg hk]
    apply min_le_min le_rfl
    apply Real.sqrt_le_sqrt
    have hτj : 1 ≤ τ j := by have := hτ (Nat.pos_of_ne_zero hj); omega
    have hr := l13_dT_ratio Pi hPi hδ0 hδ1 hτj (hτ.monotone hjk)
    rw [mul_comm (K : ℝ) (τ k : ℝ), mul_comm (K : ℝ) (τ j : ℝ), ← div_div, ← div_div]
    exact div_le_div_of_nonneg_right hr hK.le

end Params

section Main2

variable {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]

lemma l13_expReward_mem (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1) (π : X → Fin K) :
    0 ≤ expReward D π ∧ expReward D π ≤ 1 := by
  unfold expReward
  constructor
  · exact integral_nonneg_of_ae (hD.mono (fun z hz => (hz (π z.1)).1))
  · have h := norm_integral_le_of_norm_le_const (μ := D)
      (f := fun z : X × (Fin K → ℝ) => z.2 (π z.1)) (C := 1)
      (hD.mono (fun z hz => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hz (π z.1)).1, (hz (π z.1)).2]))
    have hu : D.real Set.univ = 1 := by simp [Measure.real]
    rw [hu, mul_one, Real.norm_eq_abs] at h
    exact (abs_le.mp h).2

end Main2


section IPS

variable {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]

/-- The IPS term of one record. -/
noncomputable def ipsTerm (π : X → Fin K) (e : Rec X K) : ℝ :=
  if π e.ctx = e.act then e.rew / e.prop else 0

/-- IPS term of a round with distribution `p`, data `z` and uniform number `u`. -/
noncomputable def Yv (π : X → Fin K) (p : Fin K → ℝ) (z : X × (Fin K → ℝ)) (u : ℝ) : ℝ :=
  if π z.1 = drawAction p u then z.2 (drawAction p u) / p (drawAction p u) else 0

theorem measurable_ipsTerm {π : X → Fin K} (hπ : Measurable π) :
    Measurable (fun e : Rec X K => ipsTerm π e) := by
  unfold ipsTerm
  apply Measurable.ite _ ?_ measurable_const
  · exact measurableSet_eq_fun (hπ.comp measurable_fst) (measurable_fst.comp measurable_snd)
  · exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).div
      (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem ips_hist_sum {Ω : Type*} (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ))
    (U : ℕ → Ω → ℝ) (ω : Ω) (π : X → Fin K) :
    ∀ t, ((A.history Z U ω t).map (fun e => if π e.ctx = e.act then e.rew / e.prop else 0)).sum
      = ∑ s ∈ Finset.Icc 1 t, ipsTerm π (recAt A Z U ω (s - 1)) := by
  intro t
  induction t with
  | zero => simp [AlgoParams.history]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [AlgoParams.history, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.add_sub_cancel]
    rfl

theorem ipsEst_history {Ω : Type*} (A : AlgoParams X K) (Z : ℕ → Ω → X × (Fin K → ℝ))
    (U : ℕ → Ω → ℝ) (ω : Ω) (π : X → Fin K) (t : ℕ) :
    ipsEst (A.history Z U ω t) π
      = (∑ s ∈ Finset.Icc 1 t, ipsTerm π (recAt A Z U ω (s - 1))) / t := by
  unfold ipsEst
  rw [ips_hist_sum, history_length]

theorem ipsTerm_recAt {Ω : Type*} (A : AlgoParams X K) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (π : X → Fin K) (t : ℕ) :
    ipsTerm π (recAt A Z U ω t) = Yv π (smoothProj A.Pi
      (A.Qtilde Z U ω (epochOf A.τ (t + 1) - 1)) (muM A.Pi A.δ A.τ (epochOf A.τ (t + 1) - 1))
      (Z (t + 1) ω).1) (Z (t + 1) ω) (U (t + 1) ω) := by
  obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ (t := t + 1) (by omega)
  simp only [ipsTerm, Yv, recAt, AlgoParams.roundRecord, AlgoParams.Qtilde, Rec.ctx, Rec.act,
    Rec.rew, Rec.prop]
  simp only [history_take A Z U ω (by omega : A.τ (epochOf A.τ (t + 1) - 1) ≤ t)]
  exact if_congr Iff.rfl rfl rfl

/-- `V(Q̃_{m(t)−1}, π, μ_{m(t)−1})` for round `t`. -/
noncomputable def Vround {Ω : Type*} (A : AlgoParams X K) (ν : Measure X)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (π : X → Fin K) (t : ℕ) : ℝ :=
  Vpop ν A.Pi (A.Qtilde Z U ω (epochOf A.τ t - 1)) π (muM A.Pi A.δ A.τ (epochOf A.τ t - 1))

/-- Freedman increment of round `t` with sign `σ` and parameter `l`. -/
noncomputable def fIncr {Ω : Type*} (A : AlgoParams X K) (D : Measure (X × (Fin K → ℝ)))
    (π : X → Fin K) (σ l : ℝ) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (t : ℕ) : ℝ :=
  σ * l * (ipsTerm π (recAt A Z U ω (t - 1)) - expReward D π)
    - l ^ 2 * Vround A (D.map Prod.fst) Z U ω π t

theorem recAt_congr (A : AlgoParams X K) {Ω Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ)
    (h : ∀ s, 1 ≤ s → s ≤ t + 1 → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    recAt A Z U ω t = recAt A Z' U' ω' t := by
  unfold recAt
  rw [history_congr A Z U ω Z' U' ω' t (fun s h1 h2 => h s h1 (by omega)),
    (h (t + 1) (by omega) le_rfl).1, (h (t + 1) (by omega) le_rfl).2]

theorem fIncr_congr (A : AlgoParams X K) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (D : Measure (X × (Fin K → ℝ))) (π : X → Fin K) (σ l : ℝ) {Ω Ω' : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω)
    (Z' : ℕ → Ω' → X × (Fin K → ℝ)) (U' : ℕ → Ω' → ℝ) (ω' : Ω') (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ s, 1 ≤ s → s ≤ t → Z s ω = Z' s ω' ∧ U s ω = U' s ω') :
    fIncr A D π σ l Z U ω t = fIncr A D π σ l Z' U' ω' t := by
  obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ ht
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  unfold fIncr Vround
  rw [Nat.add_sub_cancel, recAt_congr A Z U ω Z' U' ω' t' h,
    Qtilde_congr A Z U ω Z' U' ω' _ (fun s h1 h2 => h s h1 (by omega))]

theorem measurable_Vpop_Q (ν : Measure X) [SFinite ν] (Pi : Finset (X → Fin K))
    (hPiMeas : ∀ π ∈ Pi, Measurable π) (π : X → Fin K) (hπ : Measurable π) (μ : ℝ) :
    Measurable (fun Q : Pi → ℝ => Vpop ν Pi Q π μ) := by
  classical
  have hj : Measurable (fun p : (Pi → ℝ) × X => 1 / smoothProj Pi p.1 μ p.2 (π p.2)) := by
    unfold smoothProj
    simp_rw [Finset.sum_filter]
    apply Measurable.div measurable_const
    apply Measurable.add_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro π' _
    apply Measurable.ite _ ((measurable_pi_apply π').comp measurable_fst) measurable_const
    exact measurableSet_eq_fun ((hPiMeas π' π'.2).comp measurable_snd) (hπ.comp measurable_snd)
  unfold Vpop
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem measurable_fIncr {Ω : Type*} [MeasurableSpace Ω] (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hrules : A.RulesMeasurable)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (D : Measure (X × (Fin K → ℝ)))
    [IsProbabilityMeasure D] (π : X → Fin K) (hπ : Measurable π) (σ l : ℝ)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hU : ∀ t, Measurable (U t)) (t : ℕ) :
    Measurable (fun ω => fIncr A D π σ l Z U ω t) := by
  haveI : IsProbabilityMeasure (D.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  unfold fIncr Vround
  exact (measurable_const.mul (((measurable_ipsTerm hπ).comp
    (measurable_recAt A hPiMeas hrules hτ0 hτ Z U hZ hU (t - 1))).sub_const _)).sub
    (measurable_const.mul ((measurable_Vpop_Q (D.map Prod.fst) A.Pi hPiMeas π hπ _).comp
      (measurable_pi_lambda _
        (fun π' => measurable_Qtilde A hPiMeas hrules hτ0 hτ Z U hZ hU _ π'))))

theorem exp_le_quad {y : ℝ} (hy : y ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  rcases le_or_gt (-1) y with h | h
  · have h1 : |y| ≤ 1 := abs_le.mpr ⟨h, hy⟩
    have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h1)).2
    linarith
  · have h3 : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith

theorem lintegral_drawAction (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (f : Fin K → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∫⁻ u, ENNReal.ofReal (f (drawAction p u)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ENNReal.ofReal (∑ a, p a * f a) := by
  have hmeas : Measurable (fun u : ℝ => drawAction p u) :=
    measurable_drawAction_comp measurable_const measurable_id
  rw [← lintegral_map (f := fun a => ENNReal.ofReal (f a)) (measurable_of_countable _) hmeas,
    lintegral_fintype, ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hp a) (hf a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.map_apply hmeas (measurableSet_singleton a)]
  have : (fun u => drawAction p u) ⁻¹' {a} = {u | drawAction p u = a} := rfl
  rw [this, drawAction_law p hp hsum a, ← ENNReal.ofReal_mul (hf a), mul_comm]

/-- One-round exponential bound: `E[exp(σλ(Ŷ − R) − λ² V)] ≤ 1` for `0 < λ ≤ μ`. -/
theorem inner_ips_le (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    (Q : Pi → ℝ) (hQ0 : ∀ π, 0 ≤ Q π) (hQ1 : ∑ π, Q π = 1)
    {μ : ℝ} (hμ1 : (K : ℝ) * μ ≤ 1) (π : X → Fin K) (hπ : Measurable π)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {l : ℝ} (hl0 : 0 < l) (hlμ : l ≤ μ) :
    ∫⁻ e, ENNReal.ofReal (Real.exp (σ * l * (Yv π (smoothProj Pi Q μ e.1.1) e.1 e.2
        - expReward D π) - l ^ 2 * Vpop (D.map Prod.fst) Pi Q π μ))
      ∂(D.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ≤ 1 := by
  classical
  haveI hν : IsProbabilityMeasure (D.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ0 : 0 < μ := lt_of_lt_of_le hl0 hlμ
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hμ1' : μ ≤ 1 := by nlinarith
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  obtain ⟨hR0, hR1⟩ := l13_expReward_mem D hD π
  have hp : ∀ x a, μ ≤ smoothProj Pi Q μ x a := fun x a => l13_sp_ge Pi Q μ hQ0 hμ1 x a
  have hpsum : ∀ x, ∑ a, smoothProj Pi Q μ x a = 1 := fun x => smoothProj_sum Pi Q hQ1 μ x
  have hp0 : ∀ x a, 0 ≤ smoothProj Pi Q μ x a := fun x a => hμ0.le.trans (hp x a)
  set R := expReward D π with hRdef
  set V := Vpop (D.map Prod.fst) Pi Q π μ with hVdef
  -- per-action quantities
  let Ya : X × (Fin K → ℝ) → Fin K → ℝ := fun z a =>
    if π z.1 = a then z.2 a / smoothProj Pi Q μ z.1 a else 0
  let Fz : X × (Fin K → ℝ) → Fin K → ℝ := fun z a =>
    1 + σ * l * (Ya z a - R) + l ^ 2 * (Ya z a - R) ^ 2
  have hsq : ∀ w : ℝ, (σ * l * w) ^ 2 = l ^ 2 * w ^ 2 := by
    intro w
    rw [mul_pow, mul_pow, hσ2, one_mul]
  have hFz0 : ∀ z a, 0 ≤ Fz z a := by
    intro z a
    show 0 ≤ 1 + σ * l * (Ya z a - R) + l ^ 2 * (Ya z a - R) ^ 2
    rw [← hsq]
    nlinarith [sq_nonneg (σ * l * (Ya z a - R) + 1 / 2)]
  have hpt : ∀ z : X × (Fin K → ℝ), (∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1) → ∀ u : ℝ,
      Real.exp (σ * l * (Yv π (smoothProj Pi Q μ z.1) z u - R) - l ^ 2 * V)
        ≤ Fz z (drawAction (smoothProj Pi Q μ z.1) u) * Real.exp (-(l ^ 2 * V)) := by
    intro z hz u
    have hY : Yv π (smoothProj Pi Q μ z.1) z u = Ya z (drawAction (smoothProj Pi Q μ z.1) u) :=
      rfl
    generalize drawAction (smoothProj Pi Q μ z.1) u = a at hY ⊢
    have hY0 : 0 ≤ Ya z a := by
      show 0 ≤ (if π z.1 = a then z.2 a / smoothProj Pi Q μ z.1 a else 0)
      split_ifs
      · exact div_nonneg (hz a).1 (hp0 _ _)
      · exact le_rfl
    have hY1 : l * Ya z a ≤ 1 := by
      show l * (if π z.1 = a then z.2 a / smoothProj Pi Q μ z.1 a else 0) ≤ 1
      split_ifs
      · have hpa := hp z.1 a
        have hpa0 : 0 < smoothProj Pi Q μ z.1 a := lt_of_lt_of_le hμ0 hpa
        rw [mul_div_assoc', div_le_one hpa0]
        nlinarith [(hz a).1, (hz a).2]
      · linarith
    have hlY : 0 ≤ l * Ya z a := mul_nonneg hl0.le hY0
    have hlR : l * R ≤ l := by nlinarith
    have hlR0 : 0 ≤ l * R := mul_nonneg hl0.le hR0
    have hg : σ * l * (Ya z a - R) ≤ 1 := by
      rcases hσ with h | h <;> rw [h] <;> nlinarith
    rw [hY, sub_eq_add_neg, Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 := exp_le_quad hg
    have h2 := hsq (Ya z a - R)
    show _ ≤ 1 + σ * l * (Ya z a - R) + l ^ 2 * (Ya z a - R) ^ 2
    linarith
  have hsum_z : ∀ z : X × (Fin K → ℝ), ∑ a, smoothProj Pi Q μ z.1 a * Fz z a
      = (1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
        + l ^ 2 * (z.2 (π z.1) ^ 2 / smoothProj Pi Q μ z.1 (π z.1)) := by
    intro z
    have hpz : smoothProj Pi Q μ z.1 (π z.1) ≠ 0 := (lt_of_lt_of_le hμ0 (hp _ _)).ne'
    have e : ∀ a, smoothProj Pi Q μ z.1 a * Fz z a
        = (1 - σ * l * R + l ^ 2 * R ^ 2) * smoothProj Pi Q μ z.1 a
          + (σ * l - 2 * l ^ 2 * R) * (if π z.1 = a then z.2 a else 0)
          + l ^ 2 * (if π z.1 = a then z.2 a ^ 2 / smoothProj Pi Q μ z.1 a else 0) := by
      intro a
      show smoothProj Pi Q μ z.1 a * (1 + σ * l * ((if π z.1 = a then
          z.2 a / smoothProj Pi Q μ z.1 a else 0) - R)
        + l ^ 2 * ((if π z.1 = a then z.2 a / smoothProj Pi Q μ z.1 a else 0) - R) ^ 2) = _
      split_ifs with h
      · subst h
        field_simp
        ring
      · ring
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hpsum, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, mul_one]
  have hHge : ∀ z : X × (Fin K → ℝ), (∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1) →
      ∑ a, smoothProj Pi Q μ z.1 a * Fz z a
        ≤ (1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
          + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1)) := by
    intro z hz
    rw [hsum_z z]
    have hr := hz (π z.1)
    have hp0' : 0 < smoothProj Pi Q μ z.1 (π z.1) := lt_of_lt_of_le hμ0 (hp _ _)
    have h1 : z.2 (π z.1) ^ 2 / smoothProj Pi Q μ z.1 (π z.1)
        ≤ 1 / smoothProj Pi Q μ z.1 (π z.1) := by
      apply div_le_div_of_nonneg_right _ hp0'.le
      nlinarith [hr.1, hr.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg l)
    linarith
  have hS0 : ∀ z : X × (Fin K → ℝ), 0 ≤ ∑ a, smoothProj Pi Q μ z.1 a * Fz z a :=
    fun z => Finset.sum_nonneg (fun a _ => mul_nonneg (hp0 _ _) (hFz0 z a))
  have hmeasY : Measurable (fun z : X × (Fin K → ℝ) => z.2 (π z.1)) :=
    measurable_eval_pair.comp (measurable_snd.prodMk (hπ.comp measurable_fst))
  have hmeasP : Measurable (fun x : X => 1 / smoothProj Pi Q μ x (π x)) :=
    measurable_const.div
      (measurable_eval_pair.comp ((measurable_smoothProj Pi hPiMeas Q μ).prodMk hπ))
  have hIr : Integrable (fun z : X × (Fin K → ℝ) => z.2 (π z.1)) D :=
    Integrable.of_bound hmeasY.aestronglyMeasurable 1 (hD.mono (fun z hz => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hz (π z.1)).1, (hz (π z.1)).2]))
  have hIp : Integrable (fun x : X => 1 / smoothProj Pi Q μ x (π x)) (D.map Prod.fst) :=
    Integrable.of_bound hmeasP.aestronglyMeasurable (1 / μ) (ae_of_all _ (fun x => by
      have h1 := hp x (π x)
      have h2 : 0 < smoothProj Pi Q μ x (π x) := lt_of_lt_of_le hμ0 h1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le hμ0 h1))
  have hIp' : Integrable (fun z : X × (Fin K → ℝ) => 1 / smoothProj Pi Q μ z.1 (π z.1)) D :=
    hIp.comp_measurable measurable_fst
  have hVeq : ∫ z, 1 / smoothProj Pi Q μ z.1 (π z.1) ∂D = V := by
    rw [hVdef, Vpop, integral_map measurable_fst.aemeasurable hmeasP.aestronglyMeasurable]
  have hIH : Integrable (fun z : X × (Fin K → ℝ) => (1 - σ * l * R + l ^ 2 * R ^ 2)
      + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
      + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1))) D :=
    ((integrable_const _).add (hIr.const_mul _)).add (hIp'.const_mul _)
  have hintH : ∫ z, ((1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
      + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1))) ∂D
      = (1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * R + l ^ 2 * V := by
    have e1 : ∫ z, ((1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
        + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1))) ∂D
        = ∫ z, ((1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)) ∂D
          + ∫ z, l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1)) ∂D :=
      integral_add ((integrable_const _).add (hIr.const_mul _)) (hIp'.const_mul _)
    have e2 : ∫ z, ((1 - σ * l * R + l ^ 2 * R ^ 2) + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)) ∂D
        = ∫ z, (1 - σ * l * R + l ^ 2 * R ^ 2) ∂D
          + ∫ z, (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1) ∂D :=
      integral_add (integrable_const _) (hIr.const_mul _)
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const, hVeq]
    simp [hRdef, expReward]
  calc ∫⁻ e, ENNReal.ofReal (Real.exp (σ * l * (Yv π (smoothProj Pi Q μ e.1.1) e.1 e.2
          - R) - l ^ 2 * V)) ∂(D.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      ≤ ∫⁻ z, ∫⁻ u, ENNReal.ofReal (Real.exp (σ * l * (Yv π (smoothProj Pi Q μ z.1) z u
          - R) - l ^ 2 * V)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂D :=
        lintegral_prod_le _
    _ ≤ ∫⁻ z, ENNReal.ofReal ((1 - σ * l * R + l ^ 2 * R ^ 2)
          + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
          + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1)))
          * ENNReal.ofReal (Real.exp (-(l ^ 2 * V))) ∂D := by
        apply lintegral_mono_ae
        filter_upwards [hD] with z hz
        calc ∫⁻ u, ENNReal.ofReal (Real.exp (σ * l * (Yv π (smoothProj Pi Q μ z.1) z u
              - R) - l ^ 2 * V)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
            ≤ ∫⁻ u, ENNReal.ofReal (Fz z (drawAction (smoothProj Pi Q μ z.1) u))
                * ENNReal.ofReal (Real.exp (-(l ^ 2 * V)))
                ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
              apply lintegral_mono
              intro u
              exact (ENNReal.ofReal_le_ofReal (hpt z hz u)).trans_eq
                (ENNReal.ofReal_mul (hFz0 _ _))
          _ = ENNReal.ofReal (∑ a, smoothProj Pi Q μ z.1 a * Fz z a)
                * ENNReal.ofReal (Real.exp (-(l ^ 2 * V))) := by
              rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
                lintegral_drawAction _ (hp0 z.1) (hpsum _) _ (hFz0 z)]
          _ ≤ _ := by
              gcongr
              exact hHge z hz
    _ = ENNReal.ofReal (∫ z, ((1 - σ * l * R + l ^ 2 * R ^ 2)
          + (σ * l - 2 * l ^ 2 * R) * z.2 (π z.1)
          + l ^ 2 * (1 / smoothProj Pi Q μ z.1 (π z.1))) ∂D)
          * ENNReal.ofReal (Real.exp (-(l ^ 2 * V))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal hIH]
        filter_upwards [hD] with z hz
        exact (hS0 z).trans (hHge z hz)
    _ ≤ ENNReal.ofReal (Real.exp (l ^ 2 * V)) * ENNReal.ofReal (Real.exp (-(l ^ 2 * V))) := by
        gcongr
        rw [hintH]
        have := Real.add_one_le_exp (l ^ 2 * V)
        nlinarith [sq_nonneg (l * R)]
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one]

theorem mgf_fIncr_le (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP) (hrules : A.RulesMeasurable)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZmeas : ∀ t, Measurable (Z t)) (hUmeas : ∀ t, Measurable (U t))
    (hindep : ProbabilityTheory.iIndepFun (fun t ω => (Z t ω, U t ω)) P)
    (hZU : ∀ t, ProbabilityTheory.IndepFun (Z t) (U t) P)
    (hZlaw : ∀ t, P.map (Z t) = D)
    (hUlaw : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1))
    (π : X → Fin K) (hπ : Measurable π) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {l : ℝ} (hl : 0 < l)
    (n : ℕ) (hlμ : ∀ t, 1 ≤ t → t ≤ n → l ≤ muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t)) ∂P ≤ 1 := by
  classical
  have hW : ∀ t, Measurable (fun ω => (Z t ω, U t ω)) := fun t => (hZmeas t).prodMk (hUmeas t)
  have hlaw : ∀ t, P.map (fun ω => (Z t ω, U t ω))
      = D.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro t
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (hZmeas t).aemeasurable
      (hUmeas t).aemeasurable).mp (hZU t), hZlaw t, hUlaw t]
  have hfS : ∀ t, Measurable (fun s : ℕ → (X × (Fin K → ℝ)) × ℝ =>
      fIncr A D π σ l seqZ seqU s t) := fun t =>
    measurable_fIncr A hPiMeas hrules hτ0 hτ D π hπ σ l seqZ seqU measurable_seqZ
      measurable_seqU t
  induction n with
  | zero => simp
  | succ n ih =>
  have ih' := ih (fun t h1 h2 => hlμ t h1 (by omega))
  have hPreM : Measurable (preSeq Z U n) := by
    apply measurable_pi_lambda
    intro k
    by_cases h : k ≤ n
    · simp only [preSeq, h, if_true]
      exact hW k
    · simp only [preSeq, h, if_false]
      exact hW 0
  have hind : ProbabilityTheory.IndepFun (preSeq Z U n) (fun ω => (Z (n + 1) ω, U (n + 1) ω))
      P := by
    have h0 := hindep.indepFun_finset (Finset.range (n + 1)) {n + 1} (by simp) hW
    have hφ : Measurable (fun v : (i : Finset.range (n + 1)) → (X × (Fin K → ℝ)) × ℝ =>
        fun k : ℕ => if h : k ≤ n then v ⟨k, Finset.mem_range.mpr (by omega)⟩
          else v ⟨0, Finset.mem_range.mpr (by omega)⟩) := by
      apply measurable_pi_lambda
      intro k
      by_cases h : k ≤ n
      · simp only [h, dif_pos]
        exact measurable_pi_apply _
      · simp only [h, dif_neg, not_false_eq_true]
        exact measurable_pi_apply _
    have hψ : Measurable (fun v : (i : ({n + 1} : Finset ℕ)) → (X × (Fin K → ℝ)) × ℝ =>
        v ⟨n + 1, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
    have h1 := h0.comp hφ hψ
    convert h1 using 1
    all_goals first
      | rfl
      | (funext ω k
         simp only [preSeq, Function.comp]
         split_ifs <;> rfl)
  have hSfM : Measurable (fun s : ℕ → (X × (Fin K → ℝ)) × ℝ =>
      ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l seqZ seqU s t) :=
    Finset.measurable_sum _ (fun t _ => hfS t)
  have hYfM : Measurable (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
      fIncr A D π σ l seqZ seqU (Function.update p.1 (n + 1) p.2) (n + 1)) :=
    (hfS (n + 1)).comp measurable_update'
  have hI1 : ∀ ω, ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t
      = ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l seqZ seqU (preSeq Z U n ω) t := by
    intro ω
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    apply fIncr_congr A hτ0 hτ D π σ l Z U ω seqZ seqU _ t ht.1
    intro s h1 h2
    constructor <;> simp only [seqZ, seqU, preSeq, if_pos (le_trans h2 ht.2)]
  have hI2 : ∀ ω, fIncr A D π σ l Z U ω (n + 1)
      = fIncr A D π σ l seqZ seqU
          (Function.update (preSeq Z U n ω) (n + 1) (Z (n + 1) ω, U (n + 1) ω)) (n + 1) := by
    intro ω
    apply fIncr_congr A hτ0 hτ D π σ l Z U ω seqZ seqU _ (n + 1) (by omega)
    intro s h1 h2
    rcases Nat.lt_or_ge s (n + 1) with hs | hs
    · constructor <;> simp only [seqZ, seqU, Function.update_of_ne (show s ≠ n + 1 by omega),
        preSeq, if_pos (show s ≤ n by omega)]
    · obtain rfl : s = n + 1 := by omega
      constructor <;> simp only [seqZ, seqU, Function.update_self]
  -- inner bound
  have hinner : ∀ s : ℕ → (X × (Fin K → ℝ)) × ℝ,
      ∫⁻ e, ENNReal.ofReal (Real.exp (fIncr A D π σ l seqZ seqU
          (Function.update s (n + 1) e) (n + 1))) ∂(P.map (fun ω => (Z (n + 1) ω, U (n + 1) ω)))
        ≤ 1 := by
    intro s
    rw [hlaw (n + 1)]
    obtain ⟨hQ0, hQ1⟩ := Qtilde_prob A hsel seqZ seqU s (epochOf A.τ (n + 1) - 1)
    obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ (t := n + 1) (by omega)
    have hY : ∀ e : (X × (Fin K → ℝ)) × ℝ, fIncr A D π σ l seqZ seqU
        (Function.update s (n + 1) e) (n + 1)
        = σ * l * (Yv π (smoothProj A.Pi (A.Qtilde seqZ seqU s (epochOf A.τ (n + 1) - 1))
            (muM A.Pi A.δ A.τ (epochOf A.τ (n + 1) - 1)) e.1.1) e.1 e.2 - expReward D π)
          - l ^ 2 * Vpop (D.map Prod.fst) A.Pi (A.Qtilde seqZ seqU s (epochOf A.τ (n + 1) - 1))
            π (muM A.Pi A.δ A.τ (epochOf A.τ (n + 1) - 1)) := by
      intro e
      have hag : ∀ s', 1 ≤ s' → s' ≤ A.τ (epochOf A.τ (n + 1) - 1) →
          seqZ s' (Function.update s (n + 1) e) = seqZ s' s ∧
          seqU s' (Function.update s (n + 1) e) = seqU s' s := by
        intro s' _ h2
        constructor <;> simp only [seqZ, seqU, Function.update_of_ne (show s' ≠ n + 1 by omega)]
      unfold fIncr Vround
      rw [Nat.add_sub_cancel, ipsTerm_recAt A hτ0 hτ,
        Qtilde_congr A _ _ _ seqZ seqU s _ hag]
      simp only [seqZ, seqU, Function.update_self]
    simp_rw [hY]
    exact inner_ips_le A.Pi hPiMeas D hD _ hQ0 hQ1 (K_muM_le _ _ _ _) π hπ hσ hl
      (hlμ (n + 1) (by omega) le_rfl)
  -- assemble
  have hGM : Measurable (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
      ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l seqZ seqU p.1 t))
        * ENNReal.ofReal (Real.exp (fIncr A D π σ l seqZ seqU
          (Function.update p.1 (n + 1) p.2) (n + 1)))) :=
    ((hSfM.comp measurable_fst).exp.ennreal_ofReal).mul (hYfM.exp.ennreal_ofReal)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 (n + 1),
        fIncr A D π σ l Z U ω t)) ∂P
      = ∫⁻ ω, (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
          ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l seqZ seqU p.1 t))
          * ENNReal.ofReal (Real.exp (fIncr A D π σ l seqZ seqU
            (Function.update p.1 (n + 1) p.2) (n + 1))))
          (preSeq Z U n ω, (Z (n + 1) ω, U (n + 1) ω)) ∂P := by
        apply lintegral_congr
        intro ω
        simp only
        rw [Finset.sum_Icc_succ_top (by omega), hI1, hI2, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ s, ∫⁻ e, (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
          ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l seqZ seqU p.1 t))
          * ENNReal.ofReal (Real.exp (fIncr A D π σ l seqZ seqU
            (Function.update p.1 (n + 1) p.2) (n + 1)))) (s, e)
          ∂(P.map (fun ω => (Z (n + 1) ω, U (n + 1) ω))) ∂(P.map (preSeq Z U n)) :=
        lintegral_indep_split P hPreM (hW (n + 1)) hind hGM
    _ ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n,
            fIncr A D π σ l seqZ seqU s t)) ∂(P.map (preSeq Z U n)) := by
        apply lintegral_mono
        intro s
        simp only
        rw [lintegral_const_mul _ (f := fun e => ENNReal.ofReal (Real.exp (fIncr A D π σ l
          seqZ seqU (Function.update s (n + 1) e) (n + 1))))
          (by exact (hYfM.comp (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)]
        calc _ ≤ ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n,
              fIncr A D π σ l seqZ seqU s t)) * 1 := by
              gcongr
              exact hinner s
          _ = _ := mul_one _
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n,
            fIncr A D π σ l Z U ω t)) ∂P := by
        rw [lintegral_map (f := fun s => ENNReal.ofReal (Real.exp (∑ t ∈ Finset.Icc 1 n,
            fIncr A D π σ l seqZ seqU s t)))
          (by exact hSfM.exp.ennreal_ofReal) hPreM]
        apply lintegral_congr
        intro ω
        rw [hI1]
    _ ≤ 1 := ih'

theorem tail_fIncr (A : AlgoParams X K)
    (hPiMeas : ∀ π ∈ A.Pi, Measurable π) (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP) (hrules : A.RulesMeasurable)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZmeas : ∀ t, Measurable (Z t)) (hUmeas : ∀ t, Measurable (U t))
    (hindep : ProbabilityTheory.iIndepFun (fun t ω => (Z t ω, U t ω)) P)
    (hZU : ∀ t, ProbabilityTheory.IndepFun (Z t) (U t) P)
    (hZlaw : ∀ t, P.map (Z t) = D)
    (hUlaw : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1))
    (π : X → Fin K) (hπ : Measurable π) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {l : ℝ} (hl : 0 < l)
    (n : ℕ) (hlμ : ∀ t, 1 ≤ t → t ≤ n → l ≤ muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) (L : ℝ) :
    P {ω | L < ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t}
      ≤ ENNReal.ofReal (Real.exp (-L)) := by
  have hmgf := mgf_fIncr_le A hPiMeas hτ0 hτ hsel hrules D hD P Z U hZmeas hUmeas hindep hZU
    hZlaw hUlaw π hπ hσ hl n hlμ
  have hmeasS : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t) :=
    Finset.measurable_sum _ (fun t _ => measurable_fIncr A hPiMeas hrules hτ0 hτ D π hπ σ l
      Z U hZmeas hUmeas t)
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := P) (f := fun ω => ENNReal.ofReal (Real.exp
      (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t)))
    (by exact hmeasS.exp.ennreal_ofReal.aemeasurable) (ENNReal.ofReal (Real.exp L))
  have hsub : {ω | L < ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t}
      ⊆ {ω | ENNReal.ofReal (Real.exp L) ≤ ENNReal.ofReal (Real.exp
          (∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω.le)
  have key : ENNReal.ofReal (Real.exp L)
      * P {ω | L < ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t} ≤ 1 := by
    refine le_trans ?_ (le_trans hmarkov hmgf)
    gcongr
  have hone : ENNReal.ofReal (Real.exp (-L)) * ENNReal.ofReal (Real.exp L) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc P {ω | L < ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t}
      = ENNReal.ofReal (Real.exp (-L)) * (ENNReal.ofReal (Real.exp L)
          * P {ω | L < ∑ t ∈ Finset.Icc 1 n, fIncr A D π σ l Z U ω t}) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-L)) * 1 := by gcongr
    _ = ENNReal.ofReal (Real.exp (-L)) := mul_one _

end IPS

section Main3

variable {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]

/-- The bad event for round `k + 1`, policy `π` and sign `b`. -/
def badSet {Ω : Type*} (A : AlgoParams X K) (D : Measure (X × (Fin K → ℝ)))
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (lam : ℕ → ℝ) (δ' : ℝ) (k : ℕ)
    (π : A.Pi) (b : Bool) : Set Ω :=
  {ω | Real.log (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') <
    ∑ s ∈ Finset.Icc 1 (k + 1), fIncr A D (π : X → Fin K) (if b then 1 else -1)
      (lam (epochOf A.τ (k + 1) - 1)) Z U ω s}

theorem ips_dev_main (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP) (hrules : A.RulesMeasurable)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZmeas : ∀ t, Measurable (Z t)) (hUmeas : ∀ t, Measurable (U t))
    (hindep : ProbabilityTheory.iIndepFun (fun t ω => (Z t ω, U t ω)) P)
    (hZU : ∀ t, ProbabilityTheory.IndepFun (Z t) (U t) P)
    (hZlaw : ∀ t, P.map (Z t) = D)
    (hUlaw : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1))
    (δ' : ℝ) (hδ'0 : 0 < δ') (hδ'1 : δ' < 1)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 < lam j ∧ lam j ≤ muM A.Pi A.δ A.τ j) :
    P {ω | ∃ π : A.Pi, ∃ m : ℕ, 1 ≤ m ∧ ∃ t : ℕ, A.τ (m - 1) < t ∧ t ≤ A.τ m ∧
        A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * lam (m - 1)
          + Real.log (4 * (t : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') / ((t : ℝ) * lam (m - 1))
        < |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)|}
      ≤ ENNReal.ofReal δ' := by
  classical
  have hcard : (1 : ℝ) ≤ (A.Pi.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPi
  have hcard0 : (0 : ℝ) < (A.Pi.card : ℝ) := by linarith
  -- probability of one bad event
  have hBP : ∀ k (π : A.Pi) (b : Bool), P (badSet A D Z U lam δ' k π b)
      ≤ ENNReal.ofReal (δ' / (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ))) := by
    intro k π b
    have hσ : (if b then (1 : ℝ) else -1) = 1 ∨ (if b then (1 : ℝ) else -1) = -1 := by
      cases b <;> simp
    refine (tail_fIncr A hPiMeas hτ0 hτ hsel hrules D hD P Z U hZmeas hUmeas hindep hZU hZlaw
      hUlaw (π : X → Fin K) (hPiMeas _ π.2) hσ (hlam _).1 (k + 1) ?_ _).trans (le_of_eq ?_)
    · intro s hs1 hs2
      refine (hlam _).2.trans (l13_mu_anti A.Pi hPi hδ0 hδ1 hτ0 hτ ?_)
      have := epochOf_le_of' (τ := A.τ) (t := s) (M := epochOf A.τ (k + 1))
        (le_trans hs2 (epochOf_spec' hτ0 hτ (t := k + 1) (by omega)).2.2)
      omega
    · have hpos : 0 < 4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ' := by
        have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        positivity
      rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  -- the zeta sum
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    rw [Finset.sum_range_one] at h1
    norm_num at h1
    simpa only [one_div] using h1
  have hz2 : HasSum (fun k : ℕ => δ' / 2 * (1 / ((k : ℝ) + 1) ^ 2))
      (δ' / 2 * (Real.pi ^ 2 / 6)) := hz.mul_left _
  have hBad : P (⋃ k, ⋃ π : A.Pi, ⋃ b : Bool, badSet A D Z U lam δ' k π b)
      ≤ ENNReal.ofReal δ' := by
    calc P (⋃ k, ⋃ π : A.Pi, ⋃ b : Bool, badSet A D Z U lam δ' k π b)
        ≤ ∑' k, P (⋃ π : A.Pi, ⋃ b : Bool, badSet A D Z U lam δ' k π b) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (δ' / 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          calc P (⋃ π : A.Pi, ⋃ b : Bool, badSet A D Z U lam δ' k π b)
              ≤ ∑ π : A.Pi, P (⋃ b : Bool, badSet A D Z U lam δ' k π b) :=
                measure_iUnion_fintype_le _ _
            _ ≤ ∑ π : A.Pi, ∑ b : Bool, P (badSet A D Z U lam δ' k π b) :=
                Finset.sum_le_sum (fun π _ => measure_iUnion_fintype_le _ _)
            _ ≤ ∑ π : A.Pi, ∑ b : Bool,
                  ENNReal.ofReal (δ' / (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ))) :=
                Finset.sum_le_sum (fun π _ => Finset.sum_le_sum (fun b _ => hBP k π b))
            _ = ENNReal.ofReal (δ' / 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
                rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
                  Fintype.card_bool, Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul,
                  ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
                  ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                push_cast
                field_simp
                ring
      _ = ENNReal.ofReal (∑' k : ℕ, δ' / 2 * (1 / ((k : ℝ) + 1) ^ 2)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hz2.summable).symm
      _ ≤ ENNReal.ofReal δ' := by
          apply ENNReal.ofReal_le_ofReal
          rw [hz2.tsum_eq]
          have hpi := Real.pi_lt_d2
          have hpi0 := Real.pi_pos
          have h12 : Real.pi ^ 2 ≤ 12 := by nlinarith
          calc δ' / 2 * (Real.pi ^ 2 / 6) = δ' * Real.pi ^ 2 / 12 := by ring
            _ ≤ δ' * 12 / 12 := by gcongr
            _ = δ' := by ring
  -- containment
  refine le_trans (measure_mono ?_) hBad
  rintro ω ⟨π, m, hm, t, ht1, ht2, hlt⟩
  have ht : 1 ≤ t := by omega
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hep : epochOf A.τ (k + 1) = m := by
    have := epochOf_eq_succ' hτ (m := m - 1) (t := k + 1) ht1
      (by rw [Nat.sub_add_cancel hm]; exact ht2)
    omega
  have hl0 : 0 < lam (m - 1) := (hlam _).1
  have hTpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  -- the sum of centred IPS terms and of variances
  have hVle : ∀ s ∈ Finset.Icc 1 (k + 1), Vround A (D.map Prod.fst) Z U ω (π : X → Fin K) s
      ≤ A.calV (D.map Prod.fst) Z U ω (k + 1) (π : X → Fin K) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs1, -, -⟩ := epochOf_spec' hτ0 hτ hs.1
    have hle : epochOf A.τ s ≤ epochOf A.τ (k + 1) := epochOf_le_of'
      (le_trans hs.2 (epochOf_spec' hτ0 hτ (t := k + 1) (by omega)).2.2)
    have hpos : 0 < epochOf A.τ (k + 1) := by omega
    unfold AlgoParams.calV
    rw [dif_pos hpos]
    exact Finset.le_sup' (fun m => Vpop (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m)
      (π : X → Fin K) (muM A.Pi A.δ A.τ m)) (Finset.mem_range.mpr (by omega))
  have hWle : ∑ s ∈ Finset.Icc 1 (k + 1), Vround A (D.map Prod.fst) Z U ω (π : X → Fin K) s
      ≤ ((k + 1 : ℕ) : ℝ) * A.calV (D.map Prod.fst) Z U ω (k + 1) (π : X → Fin K) := by
    calc _ ≤ ∑ s ∈ Finset.Icc 1 (k + 1), A.calV (D.map Prod.fst) Z U ω (k + 1)
          (π : X → Fin K) := Finset.sum_le_sum hVle
      _ = _ := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hest : ipsEst (A.history Z U ω (k + 1)) (π : X → Fin K) - expReward D (π : X → Fin K)
      = (∑ s ∈ Finset.Icc 1 (k + 1), (ipsTerm (π : X → Fin K) (recAt A Z U ω (s - 1))
          - expReward D (π : X → Fin K))) / ((k + 1 : ℕ) : ℝ) := by
    rw [ipsEst_history, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hTpos.ne']
  have hsum : ∀ σ : ℝ, ∑ s ∈ Finset.Icc 1 (k + 1),
      fIncr A D (π : X → Fin K) σ (lam (m - 1)) Z U ω s
      = σ * lam (m - 1) * ∑ s ∈ Finset.Icc 1 (k + 1),
          (ipsTerm (π : X → Fin K) (recAt A Z U ω (s - 1)) - expReward D (π : X → Fin K))
        - lam (m - 1) ^ 2 * ∑ s ∈ Finset.Icc 1 (k + 1),
          Vround A (D.map Prod.fst) Z U ω (π : X → Fin K) s := by
    intro σ
    unfold fIncr
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hest] at hlt
  generalize hS : ∑ s ∈ Finset.Icc 1 (k + 1),
      (ipsTerm (π : X → Fin K) (recAt A Z U ω (s - 1)) - expReward D (π : X → Fin K)) = S
    at hlt hsum
  generalize hWd : ∑ s ∈ Finset.Icc 1 (k + 1),
      Vround A (D.map Prod.fst) Z U ω (π : X → Fin K) s = W at hWle hsum
  generalize hcV : A.calV (D.map Prod.fst) Z U ω (k + 1) (π : X → Fin K) = cV at hWle hlt
  generalize hLg : Real.log (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') = Lg at hlt
  generalize hl : lam (m - 1) = l at hlt hsum hl0
  generalize hT : ((k + 1 : ℕ) : ℝ) = T at hlt hWle hTpos
  -- the key inequality  l² W + Lg < l |S|
  rw [abs_div, abs_of_pos hTpos] at hlt
  have hTl : 0 < T * l := mul_pos hTpos hl0
  have h1 := mul_lt_mul_of_pos_right hlt hTl
  rw [add_mul, div_mul_cancel₀ _ hTl.ne'] at h1
  have e2 : |S| / T * (T * l) = |S| * l := by field_simp
  rw [e2] at h1
  have h3 : l ^ 2 * W ≤ cV * l * (T * l) := by
    have := mul_le_mul_of_nonneg_left hWle (sq_nonneg l)
    have e3 : l ^ 2 * (T * cV) = cV * l * (T * l) := by ring
    linarith
  have hkey : l ^ 2 * W + Lg < l * |S| := by linarith
  -- membership in the union
  have hmem : ∀ b : Bool, Lg < ∑ s ∈ Finset.Icc 1 (k + 1),
      fIncr A D (π : X → Fin K) (if b then 1 else -1) (lam (epochOf A.τ (k + 1) - 1)) Z U ω s →
      ω ∈ ⋃ k, ⋃ π : A.Pi, ⋃ b : Bool, badSet A D Z U lam δ' k π b := by
    intro b hb
    refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨π, Set.mem_iUnion.mpr ⟨b, ?_⟩⟩⟩
    show Real.log (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') < _
    rw [hLg]
    exact hb
  rw [hep, hl] at hmem
  rcases le_or_gt 0 S with hS0 | hS0
  · apply hmem true
    simp only [if_true]
    rw [hsum 1]
    rw [abs_of_nonneg hS0] at hkey
    linarith
  · apply hmem false
    simp only [Bool.false_eq_true, if_false]
    rw [hsum (-1)]
    rw [abs_of_neg hS0] at hkey
    linarith

end Main3

end TamingMonster.Regret

open TamingMonster.Regret MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP) (hrules : A.RulesMeasurable)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZmeas : ∀ t, Measurable (Z t)) (hUmeas : ∀ t, Measurable (U t))
    (hindep : ProbabilityTheory.iIndepFun (fun t ω => (Z t ω, U t ω)) P)
    (hZU : ∀ t, ProbabilityTheory.IndepFun (Z t) (U t) P)
    (hZlaw : ∀ t, P.map (Z t) = D)
    (hUlaw : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1))
    (δ' : ℝ) (hδ'0 : 0 < δ') (hδ'1 : δ' < 1)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 < lam j ∧ lam j ≤ muM A.Pi A.δ A.τ j) :
    P {ω | ∃ π : A.Pi, ∃ m : ℕ, 1 ≤ m ∧ ∃ t : ℕ, A.τ (m - 1) < t ∧ t ≤ A.τ m ∧
        A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * lam (m - 1)
          + Real.log (4 * (t : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') / ((t : ℝ) * lam (m - 1))
        < |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)|}
      ≤ ENNReal.ofReal δ' := by
  exact ips_dev_main A hPi hPiMeas hδ0 hδ1 hτ0 hτ hsel hrules D hD P Z U hZmeas hUmeas hindep
    hZU hZlaw hUlaw δ' hδ'0 hδ'1 lam hlam
