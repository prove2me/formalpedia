-- Prove2me | solution 1 for ProcessingNetworks.Stability.drift_condition_implies_positive_recurrent
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:00:44.301211+00:00
-- url     : https://prove2.me/submissions/47160d16-6925-4d71-8d31-a06f25a8bf56

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability
open scoped ENNReal Cardinal

namespace PN1Counterexample

/-! ### Piece 1: Star Graph CTMC on `ℕ` (irreducible, not positive recurrent) -/

/-- Geometric(1/2) PMF on `ℕ`: `p(k) = (1/2)^(k+1)`. -/
noncomputable def geomPMF : PMF ℕ :=
  ⟨fun k => ((2 : ℝ≥0∞)⁻¹) ^ (k + 1), by
    rw [ENNReal.summable.hasSum_iff]
    have hgeom : ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k = (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ :=
      ENNReal.tsum_geometric _
    have hsub : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
      have h : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
      exact ENNReal.sub_eq_of_eq_add (by simp) h.symm
    have hmul : ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) =
        (2 : ℝ≥0∞)⁻¹ * ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k := by
      simp_rw [pow_succ', ENNReal.tsum_mul_left]
    rw [hmul, hgeom, hsub, inv_inv, ENNReal.inv_mul_cancel (by simp) (by simp)]⟩

/-- Jump matrix of the star graph on `ℕ`:
`0` jumps to `k + 1` with prob `(1/2)^(k+1)`; every `k + 1` jumps deterministically to `0`. -/
noncomputable def starJump : ℕ → PMF ℕ
  | 0 => geomPMF.map (· + 1)
  | _ + 1 => PMF.pure 0

/-- Exit rates of the star graph: `rate 0 = 1`, `rate (k + 1) = (1/2)^(k+1)`. -/
noncomputable def starRate : ℕ → ℝ
  | 0 => 1
  | k + 1 => ((2 : ℝ)⁻¹) ^ (k + 1)

lemma starRate_pos (x : ℕ) : 0 < starRate x := by
  cases x with
  | zero => simp [starRate]
  | succ k => unfold starRate; positivity

lemma starRate_le_one (x : ℕ) : starRate x ≤ 1 := by
  cases x with
  | zero => simp [starRate]
  | succ k =>
    unfold starRate
    exact pow_le_one₀ (by positivity) (by norm_num)

lemma geomPMF_apply (k : ℕ) : geomPMF k = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := rfl

lemma starJump_zero_apply (y : ℕ) :
    starJump 0 y = match y with | 0 => 0 | k + 1 => ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
  cases y with
  | zero =>
    simp [starJump, PMF.map_apply]
  | succ k =>
    simp only [starJump, PMF.map_apply, Nat.succ.injEq, tsum_ite_eq', geomPMF_apply]

lemma starJump_irrefl (x : ℕ) : starJump x x = 0 := by
  cases x with
  | zero => simp [starJump_zero_apply]
  | succ k => simp [starJump, PMF.pure_apply]

lemma starJump_irreducible : Irreducible starJump := by
  intro x y
  cases x with
  | zero =>
    cases y with
    | zero =>
      exact ⟨0, by simp [stepIter, PMF.pure_apply]⟩
    | succ k =>
      refine ⟨1, ?_⟩
      simp only [stepIter, PMF.bind_apply, PMF.pure_apply, mul_ite, mul_one, mul_zero,
        tsum_ite_eq', starJump_zero_apply]
      exact ENNReal.pow_pos (by simp) _
  | succ j =>
    cases y with
    | zero =>
      refine ⟨1, ?_⟩
      simp [stepIter, starJump, PMF.pure_apply]
    | succ k =>
      refine ⟨2, ?_⟩
      simp only [stepIter, starJump, PMF.pure_bind, PMF.bind_apply, PMF.pure_apply,
        mul_ite, mul_one, mul_zero, tsum_ite_eq']
      rw [PMF.map_apply]
      simp only [Nat.succ.injEq, tsum_ite_eq', geomPMF_apply]
      exact ENNReal.pow_pos (by simp) _

lemma not_positiveRecurrent_star : ¬ PositiveRecurrent starJump starRate := by
  intro hpr
  have hlt := (hpr 0).2
  have hge : ∑' y : ℕ, tabooProb starJump 0 1 y * ENNReal.ofReal (starRate y)⁻¹ ≤
      meanReturnTime starJump starRate 0 :=
    ENNReal.le_tsum (1 : ℕ)
  have hterm : ∀ k : ℕ,
      tabooProb starJump 0 1 (k + 1) * ENNReal.ofReal (starRate (k + 1))⁻¹ = 1 := by
    intro k
    have htab : tabooProb starJump 0 1 (k + 1) = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
      simp [tabooProb, starJump_zero_apply]
    rw [htab]
    have hrate : ENNReal.ofReal (starRate (k + 1))⁻¹ = (2 : ℝ≥0∞) ^ (k + 1) := by
      simp only [starRate, inv_pow, inv_inv]
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hrate, ← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  have htop : ∑' y : ℕ, tabooProb starJump 0 1 y * ENNReal.ofReal (starRate y)⁻¹ = ⊤ := by
    by_contra hne
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hne
    have hle : (N : ℝ≥0∞) ≤
        ∑' y : ℕ, tabooProb starJump 0 1 y * ENNReal.ofReal (starRate y)⁻¹ := by
      have hsum : (N : ℝ≥0∞) = ∑ k ∈ (Finset.range N).map ⟨(· + 1), Nat.succ_injective⟩,
          tabooProb starJump 0 1 k * ENNReal.ofReal (starRate k)⁻¹ := by
        rw [Finset.sum_map]
        simp [hterm]
      rw [hsum]
      exact ENNReal.sum_le_tsum _
    exact not_lt_of_ge hle hN
  rw [htop] at hge
  exact not_lt_of_ge hge hlt

/-! ### Piece 2: Jump Chain Space `Ω_Y = ℕ × (ℕ → ℕ)` -/

noncomputable def geomMeasure : Measure ℕ := geomPMF.toMeasure

instance : IsProbabilityMeasure geomMeasure :=
  PMF.toMeasure.isProbabilityMeasure geomPMF

lemma isProbabilityMeasure_infinitePi_const {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ)) := by
  constructor
  have h := Measure.infinitePi_pi (fun _ : ℕ => μ) (s := ∅) (t := fun _ => Set.univ) (by simp)
  simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty] using h

noncomputable def μY : Measure (ℕ × (ℕ → ℕ)) :=
  geomMeasure.prod (Measure.infinitePi (fun _ : ℕ => geomMeasure))

instance : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => geomMeasure)) :=
  isProbabilityMeasure_infinitePi_const geomMeasure

instance : IsProbabilityMeasure μY := Measure.prod.instIsProbabilityMeasure _ _

/-- The star-graph jump chain `Y` on `ℕ × (ℕ → ℕ)`. -/
def starY : ℕ → ℕ × (ℕ → ℕ) → ℕ
  | n, (0, u) => if n % 2 = 0 then 0 else u (n / 2) + 1
  | 0, (k + 1, _) => k + 1
  | n + 1, (_ + 1, u) => if n % 2 = 0 then 0 else u (n / 2) + 1

lemma starY_zero (ω : ℕ × (ℕ → ℕ)) : starY 0 ω = ω.1 := by
  rcases ω with ⟨x, u⟩
  cases x <;> simp [starY]

lemma starY_succ_of_ne_zero {n : ℕ} {ω : ℕ × (ℕ → ℕ)} (h : starY n ω ≠ 0) :
    starY (n + 1) ω = 0 := by
  rcases ω with ⟨x, u⟩
  cases x with
  | zero =>
    simp only [starY] at h ⊢
    split_ifs at h with hmod
    · exact absurd rfl h
    · have : (n + 1) % 2 = 0 := by omega
      simp [this]
  | succ k =>
    cases n with
    | zero => simp [starY]
    | succ m =>
      simp only [starY] at h ⊢
      split_ifs at h with hmod
      · exact absurd rfl h
      · have : (m + 1) % 2 = 0 := by omega
        simp [this]

lemma starY_odd_of_pos {k : ℕ} {u : ℕ → ℕ} (m : ℕ) :
    starY (2 * m + 1) (k + 1, u) = 0 := by
  simp [starY]

lemma starY_isJumpChain :
    @IsJumpChain ℕ (ℕ × (ℕ → ℕ)) ⟨μY⟩ starJump starY := by
  intro n path y
  change μY {ω | (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = y} =
    μY {ω | ∀ k : Fin (n + 1), starY k ω = path k} * starJump (path (Fin.last n)) y
  by_cases hlast : path (Fin.last n) = 0
  · rw [hlast, starJump_zero_apply]
    cases y with
    | zero =>
      have hemp : {ω : ℕ × (ℕ → ℕ) |
          (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = 0} = ∅ := by
        ext ⟨x, u⟩
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hall hnext
        have hn := hall (Fin.last n)
        simp only [Fin.val_last, hlast] at hn
        cases x with
        | zero =>
          simp only [starY] at hn hnext
          split_ifs at hn with h1
          · have h2 : (n + 1) % 2 ≠ 0 := by omega
            simp [h2] at hnext
        | succ k =>
          cases n with
          | zero => simp [starY] at hn
          | succ m =>
            simp only [starY] at hn hnext
            split_ifs at hn with h1
            · have h2 : (m + 1) % 2 ≠ 0 := by omega
              simp [h2] at hnext
      rw [hemp, measure_empty, mul_zero]
    | succ r =>
      by_cases hne : ({ω : ℕ × (ℕ → ℕ) | ∀ k : Fin (n + 1), starY k ω = path k}).Nonempty
      · rcases hne with ⟨⟨x0, u0⟩, h0⟩
        have hx0 : path 0 = x0 := by
          have := h0 0
          simpa [starY_zero] using this.symm
        cases x0 with
        | zero =>
          have hn_even : n % 2 = 0 := by
            have := h0 (Fin.last n)
            simp only [Fin.val_last, hlast, starY] at this
            split_ifs at this with hm
            · exact hm
          set m := n / 2 with hm_def
          have hn_eq : n = 2 * m := by omega
          have hset : {ω : ℕ × (ℕ → ℕ) | ∀ k : Fin (n + 1), starY k ω = path k} =
              ({(0 : ℕ)} : Set ℕ) ×ˢ
                ((Finset.range m : Set ℕ).pi (fun i => {u0 i})) := by
            ext ⟨x, u⟩
            simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
              Set.mem_pi, Finset.mem_coe, Finset.mem_range]
            constructor
            · intro hall
              have hx : x = 0 := by
                have := hall 0
                simp only [Fin.val_zero, starY_zero, hx0] at this
                exact this
              refine ⟨hx, fun i hi => ?_⟩
              have h1 := hall ⟨2 * i + 1, by omega⟩
              have h2 := h0 ⟨2 * i + 1, by omega⟩
              rw [hx] at h1
              simp only [starY, show (2 * i + 1) % 2 ≠ 0 by omega, ↓reduceIte,
                show (2 * i + 1) / 2 = i by omega] at h1 h2
              omega
            · rintro ⟨rfl, hu⟩ k
              have hk0 := h0 k
              rw [← hk0]
              simp only [starY]
              split_ifs with hmod
              · rfl
              · have hlt : k.1 / 2 < m := by omega
                rw [hu (k.1 / 2) hlt]
          have hset' : {ω : ℕ × (ℕ → ℕ) |
              (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = r + 1} =
              ({(0 : ℕ)} : Set ℕ) ×ˢ
                ((Finset.range (m + 1) : Set ℕ).pi
                  (fun i => if i = m then {r} else {u0 i})) := by
            ext ⟨x, u⟩
            rw [Set.mem_ofPred_eq, show (∀ k : Fin (n + 1), starY k (x, u) = path k) ↔
              (x, u) ∈ ({(0 : ℕ)} : Set ℕ) ×ˢ
                ((Finset.range m : Set ℕ).pi (fun i => {u0 i})) by
              rw [← hset]; rfl]
            simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
              Finset.mem_range]
            constructor
            · rintro ⟨⟨rfl, hu⟩, hnext⟩
              refine ⟨rfl, fun i hi => ?_⟩
              by_cases him : i = m
              · subst him
                simp only [↓reduceIte, Set.mem_singleton_iff]
                simp only [starY, show (n + 1) % 2 ≠ 0 by omega, ↓reduceIte,
                  show (n + 1) / 2 = m by omega] at hnext
                omega
              · simp only [him, ↓reduceIte, Set.mem_singleton_iff]
                exact hu i (by omega)
            · rintro ⟨rfl, hu⟩
              refine ⟨⟨rfl, fun i hi => ?_⟩, ?_⟩
              · have := hu i (by omega)
                simpa [show i ≠ m by omega] using this
              · have := hu m (by omega)
                simp only [↓reduceIte, Set.mem_singleton_iff] at this
                simp only [starY, show (n + 1) % 2 ≠ 0 by omega, ↓reduceIte,
                  show (n + 1) / 2 = m by omega, this]
          rw [hset, hset', μY, Measure.prod_prod, Measure.prod_prod]
          rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
          rw [Measure.infinitePi_pi _ (fun i _ => by split_ifs <;> exact measurableSet_singleton _)]
          rw [Finset.prod_range_succ]
          simp only [↓reduceIte]
          have hprod : ∏ i ∈ Finset.range m,
              geomMeasure (if i = m then {r} else {u0 i}) =
              ∏ i ∈ Finset.range m, geomMeasure {u0 i} := by
            refine Finset.prod_congr rfl fun i hi => ?_
            have : i ≠ m := ne_of_lt (Finset.mem_range.mp hi)
            simp [this]
          rw [hprod, mul_assoc]
          congr 2
          simp [geomMeasure, PMF.toMeasure_apply_singleton, geomPMF_apply]
        | succ k0 =>
          have hn_pos : 0 < n := by
            by_contra h
            have hn0 : n = 0 := by omega
            subst hn0
            have h00 := h0 0
            simp only [starY] at h00
            have hlast0 : path 0 = 0 := hlast
            omega
          have hn_odd : n % 2 = 1 := by
            have := h0 (Fin.last n)
            obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            simp only [Fin.val_last, hlast, starY] at this
            split_ifs at this with hm
            · omega
          set m := (n - 1) / 2 with hm_def
          have hn_eq : n = 2 * m + 1 := by omega
          have hset : {ω : ℕ × (ℕ → ℕ) | ∀ k : Fin (n + 1), starY k ω = path k} =
              ({k0 + 1} : Set ℕ) ×ˢ
                ((Finset.range m : Set ℕ).pi (fun i => {u0 i})) := by
            ext ⟨x, u⟩
            simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
              Set.mem_pi, Finset.mem_coe, Finset.mem_range]
            constructor
            · intro hall
              have hx : x = k0 + 1 := by
                have := hall 0
                simp only [Fin.val_zero, starY_zero, hx0] at this
                exact this
              refine ⟨hx, fun i hi => ?_⟩
              have h1 := hall ⟨2 * i + 2, by omega⟩
              have h2 := h0 ⟨2 * i + 2, by omega⟩
              rw [hx] at h1
              simp only [starY, show (2 * i + 1) % 2 ≠ 0 by omega, ↓reduceIte,
                show (2 * i + 1) / 2 = i by omega] at h1 h2
              omega
            · rintro ⟨rfl, hu⟩ k
              have hk0 := h0 k
              rw [← hk0]
              rcases k with ⟨kv, hkv⟩
              cases kv with
              | zero => rfl
              | succ kv' =>
                simp only [starY]
                split_ifs with hmod
                · rfl
                · have hlt : kv' / 2 < m := by omega
                  rw [hu (kv' / 2) hlt]
          have hset' : {ω : ℕ × (ℕ → ℕ) |
              (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = r + 1} =
              ({k0 + 1} : Set ℕ) ×ˢ
                ((Finset.range (m + 1) : Set ℕ).pi
                  (fun i => if i = m then {r} else {u0 i})) := by
            ext ⟨x, u⟩
            rw [Set.mem_ofPred_eq, show (∀ k : Fin (n + 1), starY k (x, u) = path k) ↔
              (x, u) ∈ ({k0 + 1} : Set ℕ) ×ˢ
                ((Finset.range m : Set ℕ).pi (fun i => {u0 i})) by
              rw [← hset]; rfl]
            simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
              Finset.mem_range]
            constructor
            · rintro ⟨⟨rfl, hu⟩, hnext⟩
              refine ⟨rfl, fun i hi => ?_⟩
              by_cases him : i = m
              · subst him
                simp only [↓reduceIte, Set.mem_singleton_iff]
                simp only [starY, show n % 2 ≠ 0 by omega, ↓reduceIte,
                  show n / 2 = m by omega] at hnext
                omega
              · simp only [him, ↓reduceIte, Set.mem_singleton_iff]
                exact hu i (by omega)
            · rintro ⟨rfl, hu⟩
              refine ⟨⟨rfl, fun i hi => ?_⟩, ?_⟩
              · have := hu i (by omega)
                simpa [show i ≠ m by omega] using this
              · have := hu m (by omega)
                simp only [↓reduceIte, Set.mem_singleton_iff] at this
                simp only [starY, show n % 2 ≠ 0 by omega, ↓reduceIte,
                  show n / 2 = m by omega, this]
          rw [hset, hset', μY, Measure.prod_prod, Measure.prod_prod]
          rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
          rw [Measure.infinitePi_pi _ (fun i _ => by split_ifs <;> exact measurableSet_singleton _)]
          rw [Finset.prod_range_succ]
          simp only [↓reduceIte]
          have hprod : ∏ i ∈ Finset.range m,
              geomMeasure (if i = m then {r} else {u0 i}) =
              ∏ i ∈ Finset.range m, geomMeasure {u0 i} := by
            refine Finset.prod_congr rfl fun i hi => ?_
            have : i ≠ m := ne_of_lt (Finset.mem_range.mp hi)
            simp [this]
          rw [hprod, mul_assoc]
          congr 2
          simp [geomMeasure, PMF.toMeasure_apply_singleton, geomPMF_apply]
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have hne' : {ω : ℕ × (ℕ → ℕ) |
            (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = r + 1} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hall _
          have : ω ∈ ({ω | ∀ k : Fin (n + 1), starY k ω = path k} : Set _) := hall
          rw [hne] at this
          exact this
        rw [hne, hne', measure_empty, zero_mul]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hlast
    rw [hj]
    cases y with
    | zero =>
      simp only [starJump, PMF.pure_apply_self, mul_one]
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro hall
      apply starY_succ_of_ne_zero
      have := hall (Fin.last n)
      simp only [Fin.val_last, hj] at this
      omega
    | succ r =>
      simp only [starJump, PMF.pure_apply, Nat.succ_ne_zero, ↓reduceIte, mul_zero]
      have hemp : {ω : ℕ × (ℕ → ℕ) |
          (∀ k : Fin (n + 1), starY k ω = path k) ∧ starY (n + 1) ω = r + 1} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hall hnext
        have h0 : starY (n + 1) ω = 0 := by
          apply starY_succ_of_ne_zero
          have := hall (Fin.last n)
          simp only [Fin.val_last, hj] at this
          omega
        omega
      rw [hemp, measure_empty]

/-! ### Piece 3: Unit Exponential Measure and Bernstein Partition of `ℝ` -/

noncomputable def exp1Dens (x : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (Real.exp (-x)) else 0

lemma measurable_exp1Dens : Measurable exp1Dens := by
  unfold exp1Dens
  exact Measurable.ite measurableSet_Ioi
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp measurable_neg))
    measurable_const

noncomputable def exp1Measure : Measure ℝ :=
  volume.withDensity exp1Dens

lemma exp1Measure_le_volume : exp1Measure ≤ volume := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [exp1Measure, withDensity_apply _ hs]
  calc ∫⁻ x in s, exp1Dens x ∂volume
      ≤ ∫⁻ _ in s, (1 : ℝ≥0∞) ∂volume := by
        refine lintegral_mono fun x => ?_
        unfold exp1Dens
        split_ifs with hx
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith))
        · simp
    _ = volume s := by simp

lemma exp1Measure_Iic_zero : exp1Measure (Set.Iic 0) = 0 := by
  rw [exp1Measure, withDensity_apply _ measurableSet_Iic]
  have h : ∀ x ∈ Set.Iic (0 : ℝ), exp1Dens x = 0 := by
    intro x hx
    simp only [exp1Dens, Set.mem_Iic] at hx ⊢
    rw [if_neg (not_lt.mpr hx)]
  rw [setLIntegral_congr_fun measurableSet_Iic h]
  simp

lemma exp1Measure_Ioi (s : ℝ) (hs : 0 ≤ s) :
    exp1Measure (Set.Ioi s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [exp1Measure, withDensity_apply _ measurableSet_Ioi]
  have hcongr : ∀ x ∈ Set.Ioi s, exp1Dens x = ENNReal.ofReal (Real.exp (-x)) := by
    intro x hx
    simp only [exp1Dens, Set.mem_Ioi] at hx ⊢
    rw [if_pos (by linarith)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi s) volume :=
    integrableOn_exp_neg_Ioi s
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-x)).le)]
  have hval : ∫ x in Set.Ioi s, Real.exp (-x) = Real.exp (-s) := by
    have hderiv : ∀ x ∈ Set.Ici s,
        HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg
      simpa [Function.comp_def, Pi.neg_def] using h1
    have htend : Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simpa using h1.neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
    simpa using h
  rw [hval]

instance isProbabilityMeasure_exp1Measure : IsProbabilityMeasure exp1Measure := by
  constructor
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi 0) :=
    Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr (Set.mem_Iic.mp h1) (Set.mem_Ioi.mp h2)
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := Set.Iic_union_Ioi
  rw [← huniv, measure_union hdisj measurableSet_Ioi,
    exp1Measure_Iic_zero, exp1Measure_Ioi 0 le_rfl]
  simp

/-- Every closed set in `ℝ` of positive `exp1Measure` has cardinality at least `𝔠`. -/
lemma closed_pos_exp1Measure_card (F : Set ℝ) (hF : IsClosed F) (hpos : exp1Measure F ≠ 0) :
    𝔠 ≤ #F := by
  set φ : ℝ → ℝ := fun t => (exp1Measure (F ∩ Set.Iic t)).toReal
  have hφ_mono : Monotone φ := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.inter_subset_inter_right F (Set.Iic_subset_Iic.mpr hab)))
  have hφ_zero : φ 0 = 0 := by
    have hle : exp1Measure (F ∩ Set.Iic 0) ≤ exp1Measure (Set.Iic 0) :=
      measure_mono Set.inter_subset_right
    rw [exp1Measure_Iic_zero, nonpos_iff_eq_zero] at hle
    simp [φ, hle]
  have hφ_lip : ∀ a b : ℝ, a ≤ b → φ b - φ a ≤ b - a := by
    intro a b hab
    have hdisj : Disjoint (F ∩ Set.Iic a) (F ∩ Set.Ioc a b) :=
      Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr h1.2 h2.2.1
    have hunion : F ∩ Set.Iic b = (F ∩ Set.Iic a) ∪ (F ∩ Set.Ioc a b) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ⟨hxF, hxb⟩
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hxF, hxa⟩
        · exact Or.inr ⟨hxF, lt_of_not_ge hxa, hxb⟩
      · rintro (⟨hxF, hxa⟩ | ⟨hxF, _, hxb⟩)
        · exact ⟨hxF, hxa.trans hab⟩
        · exact ⟨hxF, hxb⟩
    have hm : exp1Measure (F ∩ Set.Iic b) =
        exp1Measure (F ∩ Set.Iic a) + exp1Measure (F ∩ Set.Ioc a b) := by
      rw [hunion, measure_union hdisj (hF.measurableSet.inter measurableSet_Ioc)]
    have hdiff : φ b - φ a = (exp1Measure (F ∩ Set.Ioc a b)).toReal := by
      simp only [φ, hm]
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    rw [hdiff]
    have hle : exp1Measure (F ∩ Set.Ioc a b) ≤ volume (Set.Ioc a b) :=
      (measure_mono Set.inter_subset_right).trans (exp1Measure_le_volume (Set.Ioc a b))
    calc (exp1Measure (F ∩ Set.Ioc a b)).toReal
        ≤ (volume (Set.Ioc a b)).toReal := ENNReal.toReal_mono (by simp) hle
      _ = b - a := by simp [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hφ_cont : Continuous φ := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr (hφ_mono hxy))]
      calc φ y - φ x ≤ y - x := hφ_lip x y hxy
        _ ≤ |y - x| := le_abs_self _
        _ < ε := hy
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hφ_mono hyx))]
      calc φ x - φ y ≤ x - y := hφ_lip y x hyx
        _ = |y - x| := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)]
        _ < ε := hy
  set c := (exp1Measure F).toReal
  have hc_pos : 0 < c := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have hφ_tend : Tendsto (fun n : ℕ => φ n) atTop (nhds c) := by
    have hunion : (⋃ n : ℕ, F ∩ Set.Iic (n : ℝ)) = F := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · rintro ⟨_, hx, _⟩; exact hx
      · intro hx; obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, hx, hn⟩
    have hm : Monotone (fun n : ℕ => F ∩ Set.Iic (n : ℝ)) := fun a b hab =>
      Set.inter_subset_inter_right F (Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hab))
    have ht := tendsto_measure_iUnion_atTop (μ := exp1Measure) hm
    rw [hunion] at ht
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  -- Map `y ∈ (0, c)` to `t_y = sInf {t | y ≤ φ t} ∈ F`
  have hmem : ∀ y ∈ Set.Ioo 0 c,
      let S := {t : ℝ | y ≤ φ t}
      sInf S ∈ F ∧ φ (sInf S) = y := by
    intro y ⟨hy0, hyc⟩
    dsimp only
    set S := {t : ℝ | y ≤ φ t}
    have hS_ne : S.Nonempty := by
      have hev : ∀ᶠ n : ℕ in atTop, y < φ n :=
        hφ_tend.eventually (Ioi_mem_nhds hyc)
      obtain ⟨n, hn⟩ := hev.exists
      exact ⟨(n : ℝ), hn.le⟩
    have hS_bdd : BddBelow S := by
      refine ⟨0, fun t ht => ?_⟩
      by_contra hlt
      push Not at hlt
      have h1 : φ t ≤ φ 0 := hφ_mono hlt.le
      rw [hφ_zero] at h1
      have h2 : y ≤ φ t := ht
      linarith
    have hS_closed : IsClosed S := isClosed_le continuous_const hφ_cont
    have ht_mem : sInf S ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have hφ_eq : φ (sInf S) = y := by
      apply le_antisymm _ ht_mem
      by_contra hgt
      push Not at hgt
      have hopen : IsOpen {t : ℝ | y < φ t} := isOpen_lt continuous_const hφ_cont
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (sInf S) hgt
      have hmem' : sInf S - ε / 2 ∈ S := by
        have hdist : dist (sInf S - ε / 2) (sInf S) < ε := by
          rw [Real.dist_eq, show sInf S - ε / 2 - sInf S = -(ε / 2) by ring,
            abs_neg, abs_of_pos (half_pos hε)]
          linarith
        have hlt : y < φ (sInf S - ε / 2) := hball hdist
        exact le_of_lt hlt
      have hle := csInf_le hS_bdd hmem'
      linarith
    refine ⟨?_, hφ_eq⟩
    by_contra hnotF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl (sInf S) hnotF
    have heq_set : F ∩ Set.Iic (sInf S) = F ∩ Set.Iic (sInf S - ε / 2) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · intro ⟨hxF, hle⟩
        refine ⟨hxF, ?_⟩
        by_contra hgt
        push Not at hgt
        have hdist : dist x (sInf S) < ε := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith
        exact hball hdist hxF
      · intro ⟨hxF, hle⟩
        exact ⟨hxF, by linarith⟩
    have hφ_le : φ (sInf S - ε / 2) = y := by
      rw [← hφ_eq]
      simp only [φ, heq_set]
    have hle := csInf_le hS_bdd (show sInf S - ε / 2 ∈ S from hφ_le.ge)
    linarith
  let g : Set.Ioo 0 c → F := fun y => ⟨sInf {t : ℝ | y.1 ≤ φ t}, (hmem y.1 y.2).1⟩
  have hg_inj : Function.Injective g := by
    intro y1 y2 h
    have h1 := (hmem y1.1 y1.2).2
    have h2 := (hmem y2.1 y2.2).2
    have hval : sInf {t : ℝ | y1.1 ≤ φ t} = sInf {t : ℝ | y2.1 ≤ φ t} :=
      congrArg Subtype.val h
    rw [hval] at h1
    exact Subtype.ext (h1.symm.trans h2)
  rw [← Cardinal.mk_Ioo_real hc_pos]
  exact Cardinal.mk_le_of_injective hg_inj

lemma card_closed_real_le : #{F : Set ℝ // IsClosed F} ≤ 𝔠 := by
  obtain ⟨B, hB_count, _, hB_basis⟩ := TopologicalSpace.exists_countable_basis ℝ
  have hinj : Function.Injective (fun F : {F : Set ℝ // IsClosed F} =>
      {b : B | (b : Set ℝ) ⊆ F.1ᶜ}) := by
    intro F1 F2 h
    dsimp only at h
    apply Subtype.ext
    have hcompl : F1.1ᶜ = F2.1ᶜ := by
      ext x
      constructor
      · intro hx
        obtain ⟨U, hUB, hxU, hUF⟩ := hB_basis.mem_nhds_iff.mp (F1.2.isOpen_compl.mem_nhds hx)
        have hmem : (⟨U, hUB⟩ : B) ∈ {b : B | (b : Set ℝ) ⊆ F1.1ᶜ} := hUF
        rw [h] at hmem
        exact hmem hxU
      · intro hx
        obtain ⟨U, hUB, hxU, hUF⟩ := hB_basis.mem_nhds_iff.mp (F2.2.isOpen_compl.mem_nhds hx)
        have hmem : (⟨U, hUB⟩ : B) ∈ {b : B | (b : Set ℝ) ⊆ F2.1ᶜ} := hUF
        rw [← h] at hmem
        exact hmem hxU
    exact compl_injective hcompl
  calc #{F : Set ℝ // IsClosed F}
      ≤ #(Set B) := Cardinal.mk_le_of_injective hinj
    _ = 2 ^ #B := Cardinal.mk_set
    _ ≤ 2 ^ ℵ₀ := Cardinal.power_le_power_left (by norm_num) (Cardinal.le_aleph0_iff_set_countable.mpr hB_count)
    _ = 𝔠 := Cardinal.two_power_aleph0

/-- Bernstein partition of `ℝ` into `ℕ`-indexed buckets, each intersecting every Borel set of
positive `exp1Measure`. -/
lemma exists_bernstein_partition :
    ∃ bucket : ℝ → ℕ, ∀ (B : Set ℝ), MeasurableSet B → exp1Measure B ≠ 0 →
      ∀ k : ℕ, ∃ x ∈ B, bucket x = k := by
  let I := {F : Set ℝ // IsClosed F ∧ exp1Measure F ≠ 0} × ℕ
  have hI_ne : Nonempty I :=
    ⟨(⟨Set.univ, isClosed_univ, by simp⟩, 0)⟩
  have hI_card : #I ≤ 𝔠 := by
    have h1 : #{F : Set ℝ // IsClosed F ∧ exp1Measure F ≠ 0} ≤ #{F : Set ℝ // IsClosed F} :=
      Cardinal.mk_le_of_injective (f := fun F => (⟨F.1, F.2.1⟩ : {F : Set ℝ // IsClosed F}))
        (fun _ _ h => Subtype.ext (congrArg (fun x : {F : Set ℝ // IsClosed F} => x.1) h))
    calc #I = #{F : Set ℝ // IsClosed F ∧ exp1Measure F ≠ 0} * #ℕ := by
            simp only [I, Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ 𝔠 * ℵ₀ := mul_le_mul' (h1.trans card_closed_real_le) (by simp)
      _ = 𝔠 := Cardinal.mul_eq_left Cardinal.aleph0_le_continuum Cardinal.aleph0_le_continuum
            Cardinal.aleph0_ne_zero
  -- Surjection from `Set.Iio (Cardinal.ord (𝔠 : Cardinal.{0}))` onto `I`
  let αTy := Set.Iio (Cardinal.ord (𝔠 : Cardinal.{0}))
  have hcard_ord : #αTy = Cardinal.lift.{1, 0} (𝔠 : Cardinal.{0}) := by
    simp only [αTy, Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  have hle : Cardinal.lift.{1, 0} #I ≤ Cardinal.lift.{0, 1} #αTy := by
    rw [Cardinal.lift_id', hcard_ord]
    exact Cardinal.lift_le.mpr hI_card
  obtain ⟨injI⟩ := Cardinal.lift_mk_le'.mp hle
  let _ : Nonempty I := hI_ne
  let enum : αTy → I := Function.invFun injI
  have henum : Function.Surjective enum := Function.invFun_surjective injI.injective
  -- Transfinite recursion on `α : αTy`
  have hlt_card : ∀ α : αTy, #{β : αTy // β < α} < Cardinal.lift.{1, 0} (𝔠 : Cardinal.{0}) := by
    intro α
    have hinj : Function.Injective (fun β : {β : αTy // β < α} =>
        (⟨β.1.1, β.2⟩ : Set.Iio α.1)) := by
      intro b1 b2 h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : Set.Iio α.1 => x.1) h))
    calc #{β : αTy // β < α}
        ≤ #(Set.Iio α.1) := Cardinal.mk_le_of_injective hinj
      _ = Cardinal.lift.{1, 0} α.1.card := Cardinal.mk_Iio_ordinal α.1
      _ < Cardinal.lift.{1, 0} (𝔠 : Cardinal.{0}) := Cardinal.lift_lt.mpr (Cardinal.lt_ord.mp α.2)
  let chosen : αTy → ℝ :=
    WellFounded.fix (wellFounded_lt (α := αTy)) fun α rec =>
      let prev : Set ℝ := Set.range (fun β : {β // β < α} => rec β.1 β.2)
      let F := (enum α).1.1
      have hprev_lt : #prev < #F := by
        have h1 : Cardinal.lift.{1, 0} #prev ≤ #{β : αTy // β < α} := by
          simpa only [Cardinal.lift_id'] using
            (Cardinal.mk_range_le_lift (f := fun β : {β // β < α} => rec β.1 β.2))
        have h2 : Cardinal.lift.{1, 0} #prev < Cardinal.lift.{1, 0} (𝔠 : Cardinal.{0}) :=
          h1.trans_lt (hlt_card α)
        exact (Cardinal.lift_lt.mp h2).trans_le
          (closed_pos_exp1Measure_card F (enum α).1.2.1 (enum α).1.2.2)
      have hne : (F \ prev).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
        exact not_lt_of_ge (Cardinal.mk_le_mk_of_subset hemp) hprev_lt
      Classical.choose hne
  have hchosen_spec : ∀ α : αTy,
      chosen α ∈ (enum α).1.1 ∧ ∀ β < α, chosen α ≠ chosen β := by
    intro α
    have hfix : chosen α = _ := WellFounded.fix_eq (wellFounded_lt (α := αTy)) _ α
    dsimp only [chosen] at hfix ⊢
    rw [hfix]
    have hspec := Classical.choose_spec (show ((enum α).1.1 \
      Set.range (fun β : {β // β < α} => chosen β.1)).Nonempty from by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
      have h1 : Cardinal.lift.{1, 0} #(Set.range (fun β : {β // β < α} => chosen β.1)) ≤
          #{β : αTy // β < α} := by
        simpa only [Cardinal.lift_id'] using
          (Cardinal.mk_range_le_lift (f := fun β : {β // β < α} => chosen β.1))
      have h2 : #(Set.range (fun β : {β // β < α} => chosen β.1)) < (𝔠 : Cardinal.{0}) :=
        Cardinal.lift_lt.mp (h1.trans_lt (hlt_card α))
      have h3 := closed_pos_exp1Measure_card _ (enum α).1.2.1 (enum α).1.2.2
      exact not_lt_of_ge (Cardinal.mk_le_mk_of_subset hemp) (h2.trans_le h3))
    refine ⟨hspec.1, fun β hβα heq => hspec.2 ⟨⟨β, hβα⟩, heq.symm⟩⟩
  have hchosen_inj : Function.Injective chosen := by
    intro α β h
    rcases lt_trichotomy α β with hlt | rfl | hgt
    · exact absurd h.symm ((hchosen_spec β).2 α hlt)
    · rfl
    · exact absurd h ((hchosen_spec α).2 β hgt)
  open Classical in
  refine ⟨fun x => if h : ∃ α, chosen α = x then (enum (Classical.choose h)).2 else 0, ?_⟩
  intro B hB hpos k
  obtain ⟨K, hKB, hK_comp, hK_diff⟩ := hB.exists_isCompact_sdiff_lt (measure_ne_top exp1Measure _) hpos
  have hK_pos : exp1Measure K ≠ 0 := by
    intro h0
    have hle : exp1Measure B ≤ exp1Measure (B \ K) + exp1Measure K := by
      calc exp1Measure B ≤ exp1Measure ((B \ K) ∪ K) := measure_mono (by intro x hx; by_cases h : x ∈ K <;> simp [hx, h])
        _ ≤ exp1Measure (B \ K) + exp1Measure K := measure_union_le _ _
    rw [h0, add_zero] at hle
    exact not_lt_of_ge hle hK_diff
  obtain ⟨α, hα⟩ := henum (⟨K, hK_comp.isClosed, hK_pos⟩, k)
  refine ⟨chosen α, hKB (by simpa [hα] using (hchosen_spec α).1), ?_⟩
  have hex : ∃ β, chosen β = chosen α := ⟨α, rfl⟩
  dsimp only
  rw [dif_pos hex]
  have heq : Classical.choose hex = α := hchosen_inj (Classical.choose_spec hex)
  rw [heq, hα]

/-! ### Piece 4: Non-Measurable Clock, Compact Slice Picking, and Thick Subspace `ΩGood` -/

noncomputable def bucket : ℝ → ℕ := Classical.choose exists_bernstein_partition

lemma bucket_dense (B : Set ℝ) (hB : MeasurableSet B) (hpos : exp1Measure B ≠ 0) (k : ℕ) :
    ∃ x ∈ B, bucket x = k :=
  Classical.choose_spec exists_bernstein_partition B hB hpos k

/-- Non-measurable clock function: equals `t` on bucket 0 (for `t > 0`), and `min t (2^{-(j+1)})`
on bucket `j + 1` (for `t > 0`), and `1` for `t ≤ 0`. -/
noncomputable def clockVal (t : ℝ) : ℝ :=
  if t ≤ 0 then 1
  else match bucket t with
    | 0 => t
    | j + 1 => min t ((2 : ℝ)⁻¹ ^ (j + 1))

lemma clockVal_pos (t : ℝ) : 0 < clockVal t := by
  unfold clockVal
  split_ifs with ht
  · norm_num
  · cases bucket t with
    | zero => linarith
    | succ j => exact lt_min (by linarith) (by positivity)

lemma clockVal_le_self {t : ℝ} (ht : 0 < t) : clockVal t ≤ t := by
  unfold clockVal
  rw [if_neg (not_le.mpr ht)]
  cases bucket t with
  | zero => exact le_rfl
  | succ j => exact min_le_left _ _

lemma clockVal_eq_self {t : ℝ} (ht : 0 < t) (hb : bucket t = 0) : clockVal t = t := by
  unfold clockVal
  rw [if_neg (not_le.mpr ht), hb]

lemma clockVal_le_pow {t : ℝ} (ht : 0 < t) {j : ℕ} (hb : bucket t = j + 1) :
    clockVal t ≤ (2 : ℝ)⁻¹ ^ (j + 1) := by
  unfold clockVal
  rw [if_neg (not_le.mpr ht), hb]
  exact min_le_right _ _

lemma exp1Measure_clockVal_gt (s : ℝ) (hs : 0 ≤ s) :
    exp1Measure {t : ℝ | s < clockVal t} = ENNReal.ofReal (Real.exp (-s)) := by
  apply le_antisymm
  · have hsub : {t : ℝ | s < clockVal t} ⊆ Set.Iic 0 ∪ Set.Ioi s := by
      intro t ht
      by_cases ht0 : t ≤ 0
      · exact Or.inl ht0
      · push Not at ht0
        exact Or.inr (lt_of_lt_of_le ht (clockVal_le_self ht0))
    calc exp1Measure {t : ℝ | s < clockVal t}
        ≤ exp1Measure (Set.Iic 0 ∪ Set.Ioi s) := measure_mono hsub
      _ ≤ exp1Measure (Set.Iic 0) + exp1Measure (Set.Ioi s) := measure_union_le _ _
      _ = ENNReal.ofReal (Real.exp (-s)) := by
          rw [exp1Measure_Iic_zero, zero_add, exp1Measure_Ioi s hs]
  · rw [← exp1Measure_Ioi s hs]
    let A : Set ℝ := {t : ℝ | 0 < t ∧ bucket t = 0 ∧ s < t}
    have hA_sub : A ⊆ {t : ℝ | s < clockVal t} := by
      intro t ⟨ht0, hb, hst⟩
      show s < clockVal t
      rw [clockVal_eq_self ht0 hb]
      exact hst
    let U := toMeasurable exp1Measure A
    have hU_meas : MeasurableSet U := measurableSet_toMeasurable exp1Measure A
    have hdiff_zero : exp1Measure (Set.Ioi s \ U) = 0 := by
      by_contra hpos
      obtain ⟨x, ⟨hxs, hxU⟩, hbx⟩ := bucket_dense (Set.Ioi s \ U)
        (measurableSet_Ioi.diff hU_meas) hpos 0
      have hxA : x ∈ A := ⟨lt_of_le_of_lt hs hxs, hbx, hxs⟩
      exact hxU (subset_toMeasurable exp1Measure A hxA)
    calc exp1Measure (Set.Ioi s)
        ≤ exp1Measure (U ∪ (Set.Ioi s \ U)) := measure_mono (fun x hx => by
            by_cases h : x ∈ U <;> simp [hx, h])
      _ ≤ exp1Measure U + exp1Measure (Set.Ioi s \ U) := measure_union_le _ _
      _ = exp1Measure A := by rw [hdiff_zero, add_zero, measure_toMeasurable]
      _ ≤ exp1Measure {t : ℝ | s < clockVal t} := measure_mono hA_sub

noncomputable def μClock : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => exp1Measure)

instance isProbabilityMeasure_μClock : IsProbabilityMeasure μClock :=
  isProbabilityMeasure_infinitePi_const exp1Measure

/-- The non-explosion set in `ℕ → ℝ` for `clockVal`. -/
def ΩGood : Set (ℕ → ℝ) :=
  {ω : ℕ → ℝ | Tendsto (fun n => ∑ k ∈ Finset.range n, clockVal (ω k)) atTop atTop}

/-- Measurable equivalence splitting `ℕ → ℝ` into head `ω 0` and tail `fun n => ω (n + 1)`. -/
def consEquiv : (ℕ → ℝ) ≃ᵐ ℝ × (ℕ → ℝ) where
  toFun ω := (ω 0, fun n => ω (n + 1))
  invFun p := fun n => match n with | 0 => p.1 | k + 1 => p.2 k
  left_inv ω := by ext n; cases n <;> rfl
  right_inv p := by rcases p with ⟨x, u⟩; rfl
  measurable_toFun := (measurable_pi_apply 0).prodMk
    (measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1))
  measurable_invFun := measurable_pi_lambda _ fun n => by
    cases n with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd

lemma continuous_consEquiv_symm : Continuous consEquiv.symm := by
  refine continuous_pi fun n => ?_
  cases n with
  | zero => exact continuous_fst
  | succ k => exact (continuous_apply k).comp continuous_snd

lemma map_consEquiv_symm_μClock :
    Measure.map consEquiv.symm (exp1Measure.prod μClock) = μClock := by
  symm
  refine (Measure.eq_infinitePi (fun _ : ℕ => exp1Measure) ?_).symm
  intro s t ht
  rw [Measure.map_apply consEquiv.symm.measurable
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  let s' : Finset ℕ := (s.filter (· ≠ 0)).image (· - 1)
  have hpre : consEquiv.symm ⁻¹' ((s : Set ℕ).pi t) =
      (if 0 ∈ s then t 0 else Set.univ) ×ˢ ((s' : Set ℕ).pi fun k => t (k + 1)) := by
    ext ⟨x, u⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, s',
      Finset.mem_image, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · split_ifs with h0
        · exact h 0 h0
        · trivial
      · rintro k ⟨i, ⟨his, hi0⟩, rfl⟩
        obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        exact h (i' + 1) his
    · rintro ⟨hx, hu⟩ i his
      cases i with
      | zero =>
        simp only [his, ↓reduceIte] at hx
        exact hx
      | succ k =>
        exact hu k ⟨k + 1, ⟨his, Nat.succ_ne_zero k⟩, rfl⟩
  rw [hpre, Measure.prod_prod]
  rw [μClock, Measure.infinitePi_pi (fun _ : ℕ => exp1Measure) (fun k _ => ht (k + 1))]
  have hprod_s' : ∏ k ∈ s', exp1Measure (t (k + 1)) =
      ∏ i ∈ s.filter (· ≠ 0), exp1Measure (t i) := by
    have hinj : Set.InjOn (· - 1) (s.filter (· ≠ 0) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      dsimp only at hab
      omega
    rw [Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)]
  rw [hprod_s']
  by_cases h0 : 0 ∈ s
  · simp only [h0, ↓reduceIte]
    have hfilt : s.filter (· ≠ 0) = s.erase 0 := by
      ext i; simp [and_comm]
    rw [hfilt, Finset.mul_prod_erase s (fun i => exp1Measure (t i)) h0]
  · simp only [h0, ↓reduceIte, measure_univ, one_mul]
    have hfilt : s.filter (· ≠ 0) = s := by
      ext i
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hi hi0; exact h0 (hi0 ▸ hi)
    rw [hfilt]

lemma map_consEquiv_μClock :
    Measure.map consEquiv μClock = exp1Measure.prod μClock := by
  calc Measure.map consEquiv μClock
      = Measure.map consEquiv (Measure.map consEquiv.symm (exp1Measure.prod μClock)) := by
          rw [map_consEquiv_symm_μClock]
    _ = exp1Measure.prod μClock := by
          rw [Measure.map_map consEquiv.measurable consEquiv.symm.measurable]
          simp

/-- A.s. under `μClock`, infinitely many coordinates are `≥ 1`. -/
lemma μClock_io_ge_one :
    μClock {ω : ℕ → ℝ | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m} = 1 := by
  have hmeas : MeasurableSet {ω : ℕ → ℝ | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m} := by
    have heq : {ω : ℕ → ℝ | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m} =
        ⋂ M : ℕ, ⋃ m : ℕ, ⋃ (_ : m ≥ M), {ω : ℕ → ℝ | 1 ≤ ω m} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (measurable_pi_apply m)
  have hcompl_zero : μClock ({ω : ℕ → ℝ | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m})ᶜ = 0 := by
    have hcompl : ({ω : ℕ → ℝ | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m})ᶜ =
        ⋃ M : ℕ, {ω : ℕ → ℝ | ∀ m ≥ M, ω m < 1} := by
      ext ω; simp
    rw [hcompl]
    refine measure_iUnion_null fun M => ?_
    have hq_lt : exp1Measure (Set.Iio 1) < 1 := by
      have hdisj : Disjoint (Set.Iio (1 : ℝ)) (Set.Ici 1) :=
        Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr (Set.mem_Ici.mp h2) (Set.mem_Iio.mp h1)
      have hunion : Set.Iio (1 : ℝ) ∪ Set.Ici 1 = Set.univ := Set.Iio_union_Ici
      have hsum : exp1Measure (Set.Iio 1) + exp1Measure (Set.Ici 1) = 1 := by
        rw [← measure_union hdisj measurableSet_Ici, hunion, measure_univ]
      have hpos : 0 < exp1Measure (Set.Ici 1) := by
        calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-1)) :=
              ENNReal.ofReal_pos.mpr (Real.exp_pos _)
          _ = exp1Measure (Set.Ioi 1) := (exp1Measure_Ioi 1 (by norm_num)).symm
          _ ≤ exp1Measure (Set.Ici 1) := measure_mono Set.Ioi_subset_Ici_self
      have hne : exp1Measure (Set.Iio 1) ≠ 1 := by
        intro h1
        rw [h1] at hsum
        have hzero : exp1Measure (Set.Ici 1) = 0 := by
          have := (ENNReal.add_right_inj (a := (1 : ℝ≥0∞)) (b := exp1Measure (Set.Ici 1))
            (c := 0) (by simp)).mp (by simpa using hsum)
          exact this
        exact ne_of_gt hpos hzero
      exact lt_of_le_of_ne prob_le_one hne
    have hle : ∀ k : ℕ, μClock {ω : ℕ → ℝ | ∀ m ≥ M, ω m < 1} ≤
        (exp1Measure (Set.Iio 1)) ^ k := by
      intro k
      have hsub : {ω : ℕ → ℝ | ∀ m ≥ M, ω m < 1} ⊆
          ((Finset.Ico M (M + k) : Set ℕ).pi fun _ => Set.Iio 1) := by
        intro ω hω m hm
        simp only [Finset.mem_coe, Finset.mem_Ico] at hm
        exact hω m hm.1
      calc μClock {ω : ℕ → ℝ | ∀ m ≥ M, ω m < 1}
          ≤ μClock ((Finset.Ico M (M + k) : Set ℕ).pi fun _ => Set.Iio 1) := measure_mono hsub
        _ = ∏ _ ∈ Finset.Ico M (M + k), exp1Measure (Set.Iio 1) :=
            Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iio)
        _ = (exp1Measure (Set.Iio 1)) ^ k := by simp
    have htend : Tendsto (fun k : ℕ => (exp1Measure (Set.Iio 1)) ^ k) atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq_lt
    exact le_antisymm (ge_of_tendsto' htend hle) bot_le
  have hsum := measure_add_measure_compl hmeas (μ := μClock)
  rw [hcompl_zero, add_zero, measure_univ] at hsum
  exact hsum

/-- Single-step compact slice picking: given compact `K` with `μClock K ≠ 0` and bucket `k`,
there exists `x` with `bucket x = k` such that the slice `{tail | cons (x, tail) ∈ K}` is compact
and has positive `μClock`-measure. -/
lemma step_compact {K : Set (ℕ → ℝ)} (hK : IsCompact K) (hpos : μClock K ≠ 0) (k : ℕ) :
    ∃ x : ℝ, bucket x = k ∧
      let Kx : Set (ℕ → ℝ) := {tail | consEquiv.symm (x, tail) ∈ K}
      IsCompact Kx ∧ μClock Kx ≠ 0 := by
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hS_meas : MeasurableSet (consEquiv.symm ⁻¹' K) := consEquiv.symm.measurable hK_meas
  have hprod_pos : (exp1Measure.prod μClock) (consEquiv.symm ⁻¹' K) ≠ 0 := by
    rw [← Measure.map_apply consEquiv.symm.measurable hK_meas, map_consEquiv_symm_μClock]
    exact hpos
  rw [Measure.prod_apply hS_meas] at hprod_pos
  have hfn_meas : Measurable (fun x : ℝ => μClock (Prod.mk x ⁻¹' (consEquiv.symm ⁻¹' K))) :=
    measurable_measure_prodMk_left hS_meas
  have hpos_set : exp1Measure {x : ℝ | μClock (Prod.mk x ⁻¹' (consEquiv.symm ⁻¹' K)) ≠ 0} ≠ 0 := by
    intro hzero
    apply hprod_pos
    refine lintegral_eq_zero_iff hfn_meas |>.mpr ?_
    filter_upwards [compl_mem_ae_iff.mpr hzero] with x hx
    simpa using hx
  have hmeas_set : MeasurableSet {x : ℝ | μClock (Prod.mk x ⁻¹' (consEquiv.symm ⁻¹' K)) ≠ 0} :=
    (hfn_meas (measurableSet_singleton 0)).compl
  obtain ⟨x, hx_pos, hbx⟩ := bucket_dense _ hmeas_set hpos_set k
  refine ⟨x, hbx, ?_, hx_pos⟩
  -- Compactness of the slice `{tail | consEquiv.symm (x, tail) ∈ K}`
  have hclosed : IsClosed {tail : ℕ → ℝ | consEquiv.symm (x, tail) ∈ K} :=
    hK.isClosed.preimage (continuous_consEquiv_symm.comp (continuous_const.prodMk continuous_id))
  have hsub : {tail : ℕ → ℝ | consEquiv.symm (x, tail) ∈ K} ⊆
      (fun ω : ℕ → ℝ => fun n => ω (n + 1)) '' K := by
    intro tail htail
    exact ⟨consEquiv.symm (x, tail), htail, by ext n; rfl⟩
  have hcomp_img : IsCompact ((fun ω : ℕ → ℝ => fun n => ω (n + 1)) '' K) :=
    hK.image (continuous_pi fun n => continuous_apply (n + 1))
  exact hcomp_img.of_isClosed_subset hclosed hsub

/-- Main Compact Slice Picking Lemma: every measurable set `E` with `μClock E ≠ 0` contains a point
`ω ∈ E ∩ ΩGood` with prescribed buckets on the first `N` coordinates. -/
lemma exists_in_good_of_pos {E : Set (ℕ → ℝ)} (hE : MeasurableSet E) (hpos : μClock E ≠ 0)
    (N : ℕ) (c : Fin N → ℕ) :
    ∃ ω ∈ E ∩ ΩGood, ∀ i : Fin N, bucket (ω i) = c i := by
  let IO : Set (ℕ → ℝ) := {ω | ∀ M : ℕ, ∃ m ≥ M, 1 ≤ ω m}
  have hIO_meas : MeasurableSet IO := by
    have heq : IO = ⋂ M : ℕ, ⋃ m : ℕ, ⋃ (_ : m ≥ M), {ω : ℕ → ℝ | 1 ≤ ω m} := by
      ext ω; simp [IO]
    rw [heq]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (measurable_pi_apply m)
  have hE'_pos : μClock (E ∩ IO) ≠ 0 := by
    have hcompl : μClock IOᶜ = 0 := by
      rw [measure_compl hIO_meas (measure_ne_top _ _), μClock_io_ge_one, measure_univ, tsub_self]
    have heq : μClock (E ∩ IO) = μClock E := by
      apply le_antisymm (measure_mono Set.inter_subset_left)
      calc μClock E ≤ μClock ((E ∩ IO) ∪ IOᶜ) :=
            measure_mono fun x hx => by by_cases h : x ∈ IO <;> simp [hx, h]
        _ ≤ μClock (E ∩ IO) + μClock IOᶜ := measure_union_le _ _
        _ = μClock (E ∩ IO) := by rw [hcompl, add_zero]
    rw [heq]; exact hpos
  obtain ⟨K0, hK0_sub, hK0_comp, hK0_diff⟩ :=
    (hE.inter hIO_meas).exists_isCompact_sdiff_lt (measure_ne_top μClock _) hE'_pos
  have hK0_pos : μClock K0 ≠ 0 := by
    intro h0
    have hle : μClock (E ∩ IO) ≤ μClock ((E ∩ IO) \ K0) + μClock K0 :=
      (measure_mono fun x hx => by by_cases h : x ∈ K0 <;> simp [hx, h]).trans
        (measure_union_le _ _)
    rw [h0, add_zero] at hle
    exact not_lt_of_ge hle hK0_diff
  -- Helper: if `K ⊆ IO` is compact with `μClock K ≠ 0`, pick `m` such that `K ∩ {1 ≤ ω m}` has pos measure
  have pick_ge_one : ∀ (K : Set (ℕ → ℝ)), IsCompact K → μClock K ≠ 0 → K ⊆ IO →
      ∃ m : ℕ, IsCompact (K ∩ {ω | 1 ≤ ω m}) ∧ μClock (K ∩ {ω | 1 ≤ ω m}) ≠ 0 := by
    intro K hKc hKp hKIO
    have hcov : K ⊆ ⋃ m : ℕ, (K ∩ {ω | 1 ≤ ω m}) := by
      intro ω hω
      obtain ⟨m, _, hm⟩ := hKIO hω 0
      exact Set.mem_iUnion.mpr ⟨m, hω, hm⟩
    have hex : ∃ m : ℕ, μClock (K ∩ {ω | 1 ≤ ω m}) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hKp (measure_mono_null hcov (measure_iUnion_null hall))
    obtain ⟨m, hm⟩ := hex
    refine ⟨m, hKc.inter_right (isClosed_le continuous_const (continuous_apply m)), hm⟩
  -- Build inductively a sequence of states `(K_n, d_n)` and chosen reals `x_n`
  -- Invariant: `K_n` is compact, `μClock K_n ≠ 0`, `K_n ⊆ IO`, and for `n ≥ N`, `∀ ω ∈ K_n, 1 ≤ ω d_n`.
  let State := {p : Set (ℕ → ℝ) × ℕ // IsCompact p.1 ∧ μClock p.1 ≠ 0 ∧ p.1 ⊆ IO}
  let initState : State := ⟨(K0, 0), hK0_comp, hK0_pos, hK0_sub.trans Set.inter_subset_right⟩
  have shift_IO : ∀ {x : ℝ} {K : Set (ℕ → ℝ)}, K ⊆ IO →
      {tail : ℕ → ℝ | consEquiv.symm (x, tail) ∈ K} ⊆ IO := by
    intro x K hKIO tail htail M
    obtain ⟨m, hmM, hm1⟩ := hKIO htail (M + 1)
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact ⟨m', by omega, hm1⟩
  let stepFn : ℕ → State → ℝ × State := fun n st =>
    let K := st.1.1
    let d := st.1.2
    if hn : n < N then
      let h := step_compact st.2.1 st.2.2.1 (c ⟨n, hn⟩)
      let x := Classical.choose h
      let hspec := Classical.choose_spec h
      let K' := {tail : ℕ → ℝ | consEquiv.symm (x, tail) ∈ K}
      if hn1 : n + 1 = N then
        -- Entering the tail phase: pick initial countdown `d'`
        let hge := pick_ge_one K' hspec.2.1 hspec.2.2 (shift_IO st.2.2.2)
        let d' := Classical.choose hge
        let hd' := Classical.choose_spec hge
        (x, ⟨(K' ∩ {ω | 1 ≤ ω d'}, d'), hd'.1, hd'.2,
          Set.inter_subset_left.trans (shift_IO st.2.2.2)⟩)
      else
        (x, ⟨(K', 0), hspec.2.1, hspec.2.2, shift_IO st.2.2.2⟩)
    else
      -- Tail phase (`n ≥ N`): pick with bucket 0
      let h := step_compact st.2.1 st.2.2.1 0
      let x := Classical.choose h
      let hspec := Classical.choose_spec h
      let K' := {tail : ℕ → ℝ | consEquiv.symm (x, tail) ∈ K}
      match d with
      | 0 =>
        let hge := pick_ge_one K' hspec.2.1 hspec.2.2 (shift_IO st.2.2.2)
        let d' := Classical.choose hge
        let hd' := Classical.choose_spec hge
        (x, ⟨(K' ∩ {ω | 1 ≤ ω d'}, d'), hd'.1, hd'.2,
          Set.inter_subset_left.trans (shift_IO st.2.2.2)⟩)
      | d' + 1 =>
        (x, ⟨(K', d'), hspec.2.1, hspec.2.2, shift_IO st.2.2.2⟩)
  -- Initial state for `N = 0` needs countdown initialized too
  let startState : State :=
    if N = 0 then
      let hge := pick_ge_one K0 hK0_comp hK0_pos (hK0_sub.trans Set.inter_subset_right)
      let d0 := Classical.choose hge
      let hd0 := Classical.choose_spec hge
      ⟨(K0 ∩ {ω | 1 ≤ ω d0}, d0), hd0.1, hd0.2,
        Set.inter_subset_left.trans (hK0_sub.trans Set.inter_subset_right)⟩
    else initState
  let states : ℕ → State := Nat.rec startState (fun n st => (stepFn n st).2)
  let ω : ℕ → ℝ := fun n => (stepFn n (states n)).1
  -- Key properties of `states` and `ω`:
  -- 1. `K_{n+1} ⊆ {tail | cons (ω n, tail) ∈ K_n}`
  have hslice_sub : ∀ n : ℕ,
      (states (n + 1)).1.1 ⊆ {tail | consEquiv.symm (ω n, tail) ∈ (states n).1.1} := by
    intro n
    change (stepFn n (states n)).2.1.1 ⊆ _
    dsimp only [stepFn, ω]
    split_ifs with hn hn1
    · exact Set.inter_subset_left
    · exact Set.Subset.rfl
    · cases (states n).1.2 with
      | zero => exact Set.inter_subset_left
      | succ d' => exact Set.Subset.rfl
  -- 2. Buckets: for `n < N`, `bucket (ω n) = c n`; for `n ≥ N`, `bucket (ω n) = 0`.
  have hbucket_lt : ∀ (n : ℕ) (hn : n < N), bucket (ω n) = c ⟨n, hn⟩ := by
    intro n hn
    dsimp only [ω, stepFn]
    rw [dif_pos hn]
    split_ifs
    · exact (Classical.choose_spec (step_compact (states n).2.1 (states n).2.2.1 (c ⟨n, hn⟩))).1
    · exact (Classical.choose_spec (step_compact (states n).2.1 (states n).2.2.1 (c ⟨n, hn⟩))).1
  have hbucket_ge : ∀ (n : ℕ), N ≤ n → bucket (ω n) = 0 := by
    intro n hn
    dsimp only [ω, stepFn]
    rw [dif_neg (not_lt.mpr hn)]
    cases (states n).1.2 <;>
      exact (Classical.choose_spec (step_compact (states n).2.1 (states n).2.2.1 0)).1
  -- 3. Countdown invariant: for `n ≥ N`, `∀ u ∈ (states n).1.1, 1 ≤ u ((states n).1.2)`
  have hcd_inv : ∀ n : ℕ, N ≤ n → ∀ u ∈ (states n).1.1, 1 ≤ u (states n).1.2 := by
    intro n
    induction n with
    | zero =>
      intro hN0
      have hN : N = 0 := Nat.le_zero.mp hN0
      dsimp only [states, startState]
      rw [if_pos hN]
      intro u hu
      exact hu.2
    | succ n ih =>
      intro hn1
      by_cases hlt : n < N
      · have heq : n + 1 = N := by omega
        change ∀ u ∈ (stepFn n (states n)).2.1.1, 1 ≤ u (stepFn n (states n)).2.1.2
        dsimp only [stepFn]
        rw [dif_pos hlt, dif_pos heq]
        intro u hu
        exact hu.2
      · have hge : N ≤ n := not_lt.mp hlt
        change ∀ u ∈ (stepFn n (states n)).2.1.1, 1 ≤ u (stepFn n (states n)).2.1.2
        dsimp only [stepFn]
        rw [dif_neg hlt]
        cases hd : (states n).1.2 with
        | zero =>
          intro u hu
          exact hu.2
        | succ d' =>
          intro u hu
          have hmem : consEquiv.symm (_, u) ∈ (states n).1.1 := hu
          have h1 := ih hge _ hmem
          rw [hd] at h1
          exact h1
  -- 4. Whenever `n ≥ N` and `(states n).1.2 = 0`, we have `1 ≤ ω n` and `1 ≤ clockVal (ω n)`.
  have hge_one_of_zero : ∀ n : ℕ, N ≤ n → (states n).1.2 = 0 → 1 ≤ clockVal (ω n) := by
    intro n hn hd0
    have hne : (states (n + 1)).1.1.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact (states (n + 1)).2.2.1 (by rw [hemp, measure_empty])
    obtain ⟨u, hu⟩ := hne
    have hmem : consEquiv.symm (ω n, u) ∈ (states n).1.1 := hslice_sub n hu
    have h1 := hcd_inv n hn _ hmem
    rw [hd0] at h1
    have hω1 : 1 ≤ ω n := h1
    rw [clockVal_eq_self (by linarith) (hbucket_ge n hn)]
    exact hω1
  -- 5. Countdown hits 0 infinitely often!
  have hcd_step : ∀ n : ℕ, N ≤ n → ∀ d', (states n).1.2 = d' + 1 → (states (n + 1)).1.2 = d' := by
    intro n hn d' hd
    change (stepFn n (states n)).2.1.2 = d'
    dsimp only [stepFn]
    rw [dif_neg (not_lt.mpr hn), hd]
  have hhits_zero : ∀ M : ℕ, ∃ m ≥ M, 1 ≤ clockVal (ω m) := by
    intro M
    let M' := max M N
    have hM' : N ≤ M' := le_max_right M N
    suffices ∀ d : ℕ, ∀ k : ℕ, N ≤ k → (states k).1.2 = d → ∃ m ≥ k, 1 ≤ clockVal (ω m) by
      obtain ⟨m, hm, h1⟩ := this (states M').1.2 M' hM' rfl
      exact ⟨m, (le_max_left M N).trans hm, h1⟩
    intro d
    induction d with
    | zero =>
      intro k hk hd
      exact ⟨k, le_rfl, hge_one_of_zero k hk hd⟩
    | succ d' ih =>
      intro k hk hd
      obtain ⟨m, hm, h1⟩ := ih (k + 1) (by omega) (hcd_step k hk d' hd)
      exact ⟨m, by omega, h1⟩
  -- 6. Therefore `ω ∈ ΩGood`!
  have hω_good : ω ∈ ΩGood := by
    rw [ΩGood, Set.mem_ofPred_eq, Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨k, hk⟩ := exists_nat_gt b
    -- Find `k` distinct indices with `clockVal (ω m) ≥ 1`
    have hfind : ∀ j : ℕ, ∃ n : ℕ, (j : ℝ) ≤ ∑ i ∈ Finset.range n, clockVal (ω i) := by
      intro j
      induction j with
      | zero => exact ⟨0, by simp⟩
      | succ j ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm, hm1⟩ := hhits_zero n
        refine ⟨m + 1, ?_⟩
        have hsplit : ∑ i ∈ Finset.range (m + 1), clockVal (ω i) =
            ∑ i ∈ Finset.range m, clockVal (ω i) + clockVal (ω m) := Finset.sum_range_succ _ m
        have hmono : ∑ i ∈ Finset.range n, clockVal (ω i) ≤
            ∑ i ∈ Finset.range m, clockVal (ω i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
            (fun i _ _ => (clockVal_pos _).le)
        push_cast
        linarith
    obtain ⟨n0, hn0⟩ := hfind k
    refine ⟨n0, fun n hn => ?_⟩
    have hmono : ∑ i ∈ Finset.range n0, clockVal (ω i) ≤
        ∑ i ∈ Finset.range n, clockVal (ω i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun i _ _ => (clockVal_pos _).le)
    linarith
  -- 7. Show `ω ∈ K0 ⊆ E` by showing for every `n`, there exists `y ∈ K0` agreeing with `ω` on `0..n-1`.
  have happrox : ∀ n : ℕ, ∀ u ∈ (states n).1.1,
      (fun i => if i < n then ω i else u (i - n)) ∈ K0 := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have hsub0 : (states 0).1.1 ⊆ K0 := by
        dsimp only [states, startState]
        split_ifs
        · exact Set.inter_subset_left
        · exact Set.Subset.rfl
      simpa using hsub0 hu
    | succ n ih =>
      intro u hu
      have hmem : consEquiv.symm (ω n, u) ∈ (states n).1.1 := hslice_sub n hu
      have hK := ih _ hmem
      convert hK using 1
      ext i
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega]
      · by_cases hin : i = n
        · subst hin
          simp [consEquiv]
        · have hgt : ¬ i < n + 1 := by omega
          simp only [hi, hgt, ↓reduceIte]
          have hsub : i - n = (i - (n + 1)) + 1 := by omega
          rw [hsub]
          rfl
  have hω_K0 : ω ∈ K0 := by
    apply hK0_comp.isClosed.mem_of_tendsto (b := atTop) (f := fun n : ℕ =>
      let u := Classical.choose (show (states n).1.1.Nonempty by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        exact (states n).2.2.1 (by rw [hemp, measure_empty]))
      fun i => if i < n then ω i else u (i - n))
    · rw [tendsto_pi_nhds]
      intro i
      refine tendsto_atTop_of_eventually_const (i₀ := i + 1) fun n hn => ?_
      simp [show i < n by omega]
    · exact Eventually.of_forall fun n => happrox n _ (Classical.choose_spec _)
  exact ⟨ω, ⟨(hK0_sub hω_K0).1, hω_good⟩, fun i => hbucket_lt i.1 i.2⟩

/-! ### Piece 4b: Thick Subspace Measure `μGood` and Outer Measure Product Factorization -/

lemma μClock_eq_zero_of_disjoint_ΩGood {E : Set (ℕ → ℝ)} (hE : MeasurableSet E)
    (hdisj : E ∩ ΩGood = ∅) : μClock E = 0 := by
  by_contra hpos
  obtain ⟨ω, hω, _⟩ := exists_in_good_of_pos hE hpos 0 Fin.elim0
  rw [hdisj] at hω
  exact hω

lemma μClock_eq_of_preimage_eq {E₁ E₂ : Set (ℕ → ℝ)} (hE₁ : MeasurableSet E₁)
    (hE₂ : MeasurableSet E₂) (heq : (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' E₁ = Subtype.val ⁻¹' E₂) :
    μClock E₁ = μClock E₂ := by
  have h12 : (E₁ \ E₂) ∩ ΩGood = ∅ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨h1, h2⟩ hG
    have : (⟨ω, hG⟩ : ΩGood) ∈ (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' E₁ := h1
    rw [heq] at this
    exact h2 this
  have h21 : (E₂ \ E₁) ∩ ΩGood = ∅ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨h2, h1⟩ hG
    have : (⟨ω, hG⟩ : ΩGood) ∈ (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' E₂ := h2
    rw [← heq] at this
    exact h1 this
  have hd1 : μClock (E₁ \ E₂) = 0 := μClock_eq_zero_of_disjoint_ΩGood (hE₁.diff hE₂) h12
  have hd2 : μClock (E₂ \ E₁) = 0 := μClock_eq_zero_of_disjoint_ΩGood (hE₂.diff hE₁) h21
  apply le_antisymm
  · calc μClock E₁ ≤ μClock (E₂ ∪ (E₁ \ E₂)) :=
          measure_mono fun x hx => by by_cases h : x ∈ E₂ <;> simp [hx, h]
      _ ≤ μClock E₂ + μClock (E₁ \ E₂) := measure_union_le _ _
      _ = μClock E₂ := by rw [hd1, add_zero]
  · calc μClock E₂ ≤ μClock (E₁ ∪ (E₂ \ E₁)) :=
          measure_mono fun x hx => by by_cases h : x ∈ E₁ <;> simp [hx, h]
      _ ≤ μClock E₁ + μClock (E₂ \ E₁) := measure_union_le _ _
      _ = μClock E₁ := by rw [hd2, add_zero]

/-- The induced probability measure on the thick subspace `ΩGood`. -/
noncomputable def μGood : Measure ΩGood :=
  Measure.ofMeasurable
    (fun t ht => μClock (Classical.choose (MeasurableSpace.measurableSet_comap.mp ht)))
    (by
      have hspec := Classical.choose_spec
        (MeasurableSpace.measurableSet_comap.mp (MeasurableSet.empty : MeasurableSet (∅ : Set ΩGood)))
      rw [μClock_eq_of_preimage_eq hspec.1 MeasurableSet.empty (hspec.2.trans Set.preimage_empty.symm)]
      exact measure_empty)
    (by
      intro f hf hdisj
      let u : ℕ → Set (ℕ → ℝ) := fun n =>
        Classical.choose (MeasurableSpace.measurableSet_comap.mp (hf n))
      have hu_meas : ∀ n, MeasurableSet (u n) := fun n =>
        (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp (hf n))).1
      have hu_pre : ∀ n, (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' (u n) = f n := fun n =>
        (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp (hf n))).2
      have hspecU := Classical.choose_spec
        (MeasurableSpace.measurableSet_comap.mp (MeasurableSet.iUnion hf))
      have hpreU : (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' (⋃ n, u n) = ⋃ n, f n := by
        rw [Set.preimage_iUnion]
        congr 1; funext n; exact hu_pre n
      rw [μClock_eq_of_preimage_eq hspecU.1 (MeasurableSet.iUnion hu_meas)
        (hspecU.2.trans hpreU.symm)]
      have hae : Pairwise (Function.onFun (AEDisjoint μClock) u) := by
        intro i j hij
        refine μClock_eq_zero_of_disjoint_ΩGood ((hu_meas i).inter (hu_meas j)) ?_
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro ⟨hi, hj⟩ hG
        have h1 : (⟨ω, hG⟩ : ΩGood) ∈ f i := by rw [← hu_pre i]; exact hi
        have h2 : (⟨ω, hG⟩ : ΩGood) ∈ f j := by rw [← hu_pre j]; exact hj
        exact Set.disjoint_left.mp (hdisj hij) h1 h2
      exact measure_iUnion₀ hae (fun n => (hu_meas n).nullMeasurableSet))

lemma μGood_apply_preimage {u : Set (ℕ → ℝ)} (hu : MeasurableSet u) :
    μGood ((Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' u) = μClock u := by
  have hmeas : MeasurableSet ((Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' u) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨u, hu, rfl⟩
  rw [μGood, Measure.ofMeasurable_apply _ hmeas]
  have hspec := Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp hmeas)
  exact μClock_eq_of_preimage_eq hspec.1 hu hspec.2

instance isProbabilityMeasure_μGood : IsProbabilityMeasure μGood := by
  constructor
  rw [← Set.preimage_univ (f := (Subtype.val : ΩGood → ℕ → ℝ)),
    μGood_apply_preimage MeasurableSet.univ, measure_univ]

lemma μGood_eq_μClock_image (A : Set ΩGood) :
    μGood A = μClock ((Subtype.val : ΩGood → ℕ → ℝ) '' A) := by
  apply le_antisymm
  · let U := toMeasurable μClock ((Subtype.val : ΩGood → ℕ → ℝ) '' A)
    have hsub : A ⊆ (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' U :=
      fun x hx => subset_toMeasurable μClock _ ⟨x, hx, rfl⟩
    calc μGood A ≤ μGood ((Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' U) := measure_mono hsub
      _ = μClock U := μGood_apply_preimage (measurableSet_toMeasurable _ _)
      _ = μClock ((Subtype.val : ΩGood → ℕ → ℝ) '' A) := measure_toMeasurable _
  · let V := toMeasurable μGood A
    obtain ⟨U, hU_meas, hU_pre⟩ :=
      MeasurableSpace.measurableSet_comap.mp (measurableSet_toMeasurable μGood A)
    have hsub : (Subtype.val : ΩGood → ℕ → ℝ) '' A ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hxV : x ∈ toMeasurable μGood A := subset_toMeasurable μGood A hx
      rw [← hU_pre] at hxV
      exact hxV
    calc μClock ((Subtype.val : ΩGood → ℕ → ℝ) '' A)
        ≤ μClock U := measure_mono hsub
      _ = μGood ((Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' U) := (μGood_apply_preimage hU_meas).symm
      _ = μGood V := by rw [hU_pre]
      _ = μGood A := measure_toMeasurable _

/-- Outer measure of a Cartesian product of ARBITRARY (possibly non-measurable) sets in a product
of probability spaces equals the product of outer measures. -/
lemma prod_outerMeasure_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (B : Set β) :
    (μ.prod ν) (A ×ˢ B) = μ A * ν B := by
  apply le_antisymm
  · calc (μ.prod ν) (A ×ˢ B)
        ≤ (μ.prod ν) (toMeasurable μ A ×ˢ toMeasurable ν B) :=
          measure_mono (Set.prod_mono (subset_toMeasurable μ A) (subset_toMeasurable ν B))
      _ = μ (toMeasurable μ A) * ν (toMeasurable ν B) := Measure.prod_prod _ _
      _ = μ A * ν B := by rw [measure_toMeasurable, measure_toMeasurable]
  · let W := toMeasurable (μ.prod ν) (A ×ˢ B)
    have hW_meas : MeasurableSet W := measurableSet_toMeasurable _ _
    have hW_eq : (μ.prod ν) (A ×ˢ B) = ∫⁻ x, ν (Prod.mk x ⁻¹' W) ∂μ := by
      rw [← measure_toMeasurable (A ×ˢ B), Measure.prod_apply hW_meas]
    rw [hW_eq]
    have hsub : A ⊆ {x : α | ν B ≤ ν (Prod.mk x ⁻¹' W)} := by
      intro x hx
      refine measure_mono fun y hy => ?_
      exact subset_toMeasurable (μ.prod ν) (A ×ˢ B) ⟨hx, hy⟩
    have hfn : Measurable (fun x : α => ν (Prod.mk x ⁻¹' W)) :=
      measurable_measure_prodMk_left hW_meas
    calc μ A * ν B = ν B * μ A := mul_comm _ _
      _ ≤ ν B * μ {x : α | ν B ≤ ν (Prod.mk x ⁻¹' W)} := by gcongr
      _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' W) ∂μ := mul_meas_ge_le_lintegral₀ hfn.aemeasurable _

/-- Splitting `Measure.infinitePi` along a decidable predicate `p`. -/
lemma map_piEquivPiSubtypeProd_infinitePi {ι α : Type*} [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    Measure.map (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) p).symm
      ((Measure.infinitePi (fun i : Subtype p => μ i.1)).prod
        (Measure.infinitePi (fun i : {i // ¬ p i} => μ i.1))) =
      Measure.infinitePi μ := by
  have : IsProbabilityMeasure (Measure.infinitePi (fun i : Subtype p => μ i.1)) := by
    constructor
    have h := Measure.infinitePi_pi (fun i : Subtype p => μ i.1) (s := ∅) (t := fun _ => Set.univ)
      (by simp)
    simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty] using h
  have : IsProbabilityMeasure (Measure.infinitePi (fun i : {i // ¬ p i} => μ i.1)) := by
    constructor
    have h := Measure.infinitePi_pi (fun i : {i // ¬ p i} => μ i.1) (s := ∅) (t := fun _ => Set.univ)
      (by simp)
    simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty] using h
  refine Measure.eq_infinitePi μ ?_
  intro s t ht
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) p
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  let s1 : Finset (Subtype p) := (s.filter p).attach.map
    ⟨fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩, fun a b h => by
      exact Subtype.ext (congrArg (fun x : Subtype p => x.1) h)⟩
  let q : ι → Prop := fun i => ¬ p i
  let s2 : Finset {i // ¬ p i} := (s.filter q).attach.map
    ⟨fun x => ⟨x.1, ((Finset.mem_filter (p := q)).mp x.2).2⟩, fun a b h => by
      exact Subtype.ext (congrArg (fun x : {i // ¬ p i} => x.1) h)⟩
  have hpre : e.symm ⁻¹' ((s : Set ι).pi t) =
      ((s1 : Set (Subtype p)).pi fun i => t i.1) ×ˢ
        ((s2 : Set {i // ¬ p i}).pi fun i => t i.1) := by
    ext ⟨u1, u2⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, s1, s2,
      Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi⟩ ⟨j, ⟨hjs, hjp⟩, hjeq⟩
        have hij : j = i := congrArg Subtype.val hjeq
        subst hij
        have := h j hjs
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hjp] using this
      · rintro ⟨i, hi⟩ ⟨j, ⟨hjs, hjp⟩, hjeq⟩
        have hij : j = i := congrArg Subtype.val hjeq
        subst hij
        have hnp : ¬ p j := hjp
        have := h j hjs
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hnp] using this
    · rintro ⟨h1, h2⟩ i his
      by_cases hip : p i
      · have := h1 ⟨i, hip⟩ ⟨i, ⟨his, hip⟩, rfl⟩
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip] using this
      · have := h2 ⟨i, hip⟩ ⟨i, ⟨his, hip⟩, rfl⟩
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip] using this
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht i.1),
    Measure.infinitePi_pi _ (fun i _ => ht i.1)]
  have hp1 : ∏ i ∈ s1, μ i.1 (t i.1) = ∏ i ∈ s.filter p, μ i (t i) := by
    simp only [s1, Finset.prod_map]
    exact Finset.prod_attach (s.filter p) (fun i => μ i (t i))
  have hp2 : ∏ i ∈ s2, μ i.1 (t i.1) = ∏ i ∈ s.filter (fun i => ¬ p i), μ i (t i) := by
    simp only [s2, Finset.prod_map]
    exact Finset.prod_attach (s.filter q) (fun i => μ i (t i))
  rw [hp1, hp2, Finset.prod_filter_mul_prod_filter_not]

/-- Outer measure of a finite cylinder intersected with `ΩGood` factorizes as the product of
one-dimensional `exp1Measure` outer measures, even for NON-MEASURABLE `A i`! -/
lemma μClock_ΩGood_inter_pi (s : Finset ℕ) (A : ℕ → Set ℝ) :
    μClock (ΩGood ∩ (s : Set ℕ).pi A) = ∏ i ∈ s, exp1Measure (A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Set.empty_pi, Set.inter_univ, Finset.prod_empty]
    have h1 : μClock ΩGood = 1 := by
      have h := μGood_eq_μClock_image Set.univ
      simpa using h.symm
    exact h1
  | @insert a s ha ih =>
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => ℝ) (· = a)
    let μ1 := Measure.infinitePi (fun _ : {i : ℕ // i = a} => exp1Measure)
    let μ2 := Measure.infinitePi (fun _ : {i : ℕ // i ≠ a} => exp1Measure)
    have : IsProbabilityMeasure μ1 := by
      constructor
      have h := Measure.infinitePi_pi (fun _ : {i : ℕ // i = a} => exp1Measure)
        (s := ∅) (t := fun _ => Set.univ) (by simp)
      simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty] using h
    have : IsProbabilityMeasure μ2 := by
      constructor
      have h := Measure.infinitePi_pi (fun _ : {i : ℕ // i ≠ a} => exp1Measure)
        (s := ∅) (t := fun _ => Set.univ) (by simp)
      simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty] using h
    have hmap : Measure.map e.symm (μ1.prod μ2) = μClock :=
      map_piEquivPiSubtypeProd_infinitePi (fun _ : ℕ => exp1Measure) (· = a)
    -- `ΩGood` does not depend on coordinate `a`!
    have hΩGood_indep : ∀ (u1 v1 : {i : ℕ // i = a} → ℝ) (u2 : {i : ℕ // i ≠ a} → ℝ),
        e.symm (u1, u2) ∈ ΩGood ↔ e.symm (v1, u2) ∈ ΩGood := by
      intro u1 v1 u2
      have hdiff : ∀ n ≥ a + 1,
          (∑ k ∈ Finset.range n, clockVal (e.symm (u1, u2) k)) -
            (∑ k ∈ Finset.range n, clockVal (e.symm (v1, u2) k)) =
            clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩) := by
        intro n hn
        rw [← Finset.sum_sub_distrib]
        have ha_mem : a ∈ Finset.range n := Finset.mem_range.mpr (by omega)
        rw [Finset.sum_eq_single a]
        · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
        · intro k _ hka
          simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hka]
        · intro h; exact absurd ha_mem h
      have hiff : ∀ f g : ℕ → ℝ, (∀ᶠ n in atTop, f n - g n = clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩)) →
          (Tendsto f atTop atTop ↔ Tendsto g atTop atTop) := by
        intro f g hfg
        constructor
        · intro hf
          have hg : ∀ᶠ n in atTop, g n = f n - (clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩)) :=
            hfg.mono fun n hn => by linarith
          exact (hf.atTop_add (tendsto_const_nhds (x := -(clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩))))).congr'
            (hg.mono fun n hn => by linarith)
        · intro hg
          have hf : ∀ᶠ n in atTop, f n = g n + (clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩)) :=
            hfg.mono fun n hn => by linarith
          exact (hg.atTop_add (tendsto_const_nhds (x := clockVal (u1 ⟨a, rfl⟩) - clockVal (v1 ⟨a, rfl⟩)))).congr'
            (hf.mono fun n hn => by linarith)
      exact hiff _ _ (eventually_atTop.mpr ⟨a + 1, hdiff⟩)
    -- Express `e.symm ⁻¹' (ΩGood ∩ (insert a s).pi A)` as a Cartesian product `S1 ×ˢ S2`
    let S1 : Set ({i : ℕ // i = a} → ℝ) := {u1 | u1 ⟨a, rfl⟩ ∈ A a}
    let S2 : Set ({i : ℕ // i ≠ a} → ℝ) :=
      {u2 | e.symm (fun _ => 1, u2) ∈ ΩGood ∧ ∀ i ∈ s, ∀ (hi : i ≠ a), u2 ⟨i, hi⟩ ∈ A i}
    have hpre_eq : e.symm ⁻¹' (ΩGood ∩ ((insert a s : Finset ℕ) : Set ℕ).pi A) = S1 ×ˢ S2 := by
      ext ⟨u1, u2⟩
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
        Finset.mem_insert, Set.mem_prod, S1, S2, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hG, hpi⟩
        refine ⟨?_, (hΩGood_indep u1 (fun _ => 1) u2).mp hG, fun i his hia => ?_⟩
        · have := hpi a (Or.inl rfl)
          simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using this
        · have := hpi i (Or.inr his)
          simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hia] using this
      · rintro ⟨hu1, hG, hu2⟩
        refine ⟨(hΩGood_indep u1 (fun _ => 1) u2).mpr hG, ?_⟩
        rintro i (rfl | his)
        · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using hu1
        · have hia : i ≠ a := fun h => ha (h ▸ his)
          simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hia] using
            hu2 i his hia
    have hpre_univ : e.symm ⁻¹' (ΩGood ∩ (s : Set ℕ).pi A) = Set.univ ×ˢ S2 := by
      ext ⟨u1, u2⟩
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
        Set.mem_prod, Set.mem_univ, true_and, S2, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hG, hpi⟩
        refine ⟨(hΩGood_indep u1 (fun _ => 1) u2).mp hG, fun i his hia => ?_⟩
        have := hpi i his
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hia] using this
      · rintro ⟨hG, hu2⟩
        refine ⟨(hΩGood_indep u1 (fun _ => 1) u2).mpr hG, fun i his => ?_⟩
        have hia : i ≠ a := fun h => ha (h ▸ his)
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hia] using
          hu2 i his hia
    -- Since `e.symm` is a `MeasurableEquiv`, `Measure.map e.symm` preserves outer measures!
    have houter_map : ∀ T : Set (ℕ → ℝ), μClock T = (μ1.prod μ2) (e.symm ⁻¹' T) := by
      intro T
      rw [← hmap]
      apply le_antisymm
      · let U := toMeasurable (μ1.prod μ2) (e.symm ⁻¹' T)
        have hsub : T ⊆ e ⁻¹' U := by
          intro x hx
          have : e.symm (e x) ∈ T := by simp [hx]
          exact subset_toMeasurable (μ1.prod μ2) (e.symm ⁻¹' T) this
        calc Measure.map e.symm (μ1.prod μ2) T
            ≤ Measure.map e.symm (μ1.prod μ2) (e ⁻¹' U) := measure_mono hsub
          _ = (μ1.prod μ2) (e.symm ⁻¹' (e ⁻¹' U)) :=
              Measure.map_apply e.symm.measurable (e.measurable (measurableSet_toMeasurable _ _))
          _ = (μ1.prod μ2) U := by congr 1; ext y; simp
          _ = (μ1.prod μ2) (e.symm ⁻¹' T) := measure_toMeasurable _
      · let V := toMeasurable (Measure.map e.symm (μ1.prod μ2)) T
        have hsub : e.symm ⁻¹' T ⊆ e.symm ⁻¹' V := Set.preimage_mono (subset_toMeasurable _ _)
        calc (μ1.prod μ2) (e.symm ⁻¹' T)
            ≤ (μ1.prod μ2) (e.symm ⁻¹' V) := measure_mono hsub
          _ = Measure.map e.symm (μ1.prod μ2) V :=
              (Measure.map_apply e.symm.measurable (measurableSet_toMeasurable _ _)).symm
          _ = Measure.map e.symm (μ1.prod μ2) T := measure_toMeasurable _
    -- Compute `μ1 S1 = exp1Measure (A a)`
    have hμ1_S1 : μ1 S1 = exp1Measure (A a) := by
      let ev : ({i : ℕ // i = a} → ℝ) ≃ᵐ ℝ :=
        { toFun := fun u => u ⟨a, rfl⟩
          invFun := fun x _ => x
          left_inv := fun u => by ext ⟨i, hi⟩; subst hi; rfl
          right_inv := fun _ => rfl
          measurable_toFun := measurable_pi_apply _
          measurable_invFun := measurable_pi_lambda _ fun _ => measurable_id }
      have hev_map : Measure.map ev μ1 = exp1Measure :=
        Measure.infinitePi_map_eval (fun _ : {i : ℕ // i = a} => exp1Measure) ⟨a, rfl⟩
      have hS1_eq : S1 = ev ⁻¹' A a := rfl
      rw [hS1_eq]
      apply le_antisymm
      · let U := toMeasurable exp1Measure (A a)
        calc μ1 (ev ⁻¹' A a) ≤ μ1 (ev ⁻¹' U) := measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
          _ = Measure.map ev μ1 U := (Measure.map_apply ev.measurable (measurableSet_toMeasurable _ _)).symm
          _ = exp1Measure U := by rw [hev_map]
          _ = exp1Measure (A a) := measure_toMeasurable _
      · let V := toMeasurable μ1 (ev ⁻¹' A a)
        have hsub : A a ⊆ ev.symm ⁻¹' V := by
          intro x hx
          have : ev (ev.symm x) ∈ A a := by simpa using hx
          exact subset_toMeasurable μ1 (ev ⁻¹' A a) this
        calc exp1Measure (A a) ≤ exp1Measure (ev.symm ⁻¹' V) := measure_mono hsub
          _ = Measure.map ev μ1 (ev.symm ⁻¹' V) := by rw [hev_map]
          _ = μ1 (ev ⁻¹' (ev.symm ⁻¹' V)) :=
              Measure.map_apply ev.measurable (ev.symm.measurable (measurableSet_toMeasurable _ _))
          _ = μ1 V := by congr 1; ext y; simp
          _ = μ1 (ev ⁻¹' A a) := measure_toMeasurable _
    -- Combine!
    have hS2 : μ2 S2 = ∏ i ∈ s, exp1Measure (A i) := by
      have h := houter_map (ΩGood ∩ (s : Set ℕ).pi A)
      rw [ih, hpre_univ, prod_outerMeasure_prod, measure_univ, one_mul] at h
      exact h.symm
    rw [houter_map, hpre_eq, prod_outerMeasure_prod, hμ1_S1, hS2, Finset.prod_insert ha]

/-! ### Piece 5: Full Counterexample `MarkovRepresentation` and Disproof -/

abbrev ΩCounter := ΩGood × (ℕ × (ℕ → ℕ))

noncomputable def μCounter : Measure ΩCounter := μGood.prod μY

instance : IsProbabilityMeasure μCounter := Measure.prod.instIsProbabilityMeasure _ _

noncomputable instance : MeasureSpace ΩCounter := ⟨μCounter⟩

noncomputable def counterClock (n : ℕ) (ω : ΩCounter) : ℝ :=
  clockVal (ω.1.1 n)

def counterY (n : ℕ) (ω : ΩCounter) : ℕ :=
  starY n ω.2

lemma counter_jumpTime_eq (n : ℕ) (ω : ΩCounter) :
    jumpTime starRate counterY counterClock n ω =
      ∑ k ∈ Finset.range n, counterClock k ω / starRate (counterY k ω) := by
  induction n with
  | zero => simp [jumpTime]
  | succ n ih => simp [jumpTime, Finset.sum_range_succ, ih]

lemma counter_nonexplosive (ω : ΩCounter) :
    Tendsto (fun n => jumpTime starRate counterY counterClock n ω) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) ω.1.2
  rw [counter_jumpTime_eq]
  refine Finset.sum_le_sum fun k _ => ?_
  have hpos : 0 < starRate (counterY k ω) := starRate_pos _
  have hle : starRate (counterY k ω) ≤ 1 := starRate_le_one _
  have hc : 0 < clockVal (ω.1.1 k) := clockVal_pos _
  dsimp only [counterClock]
  exact le_div_iff₀ hpos |>.mpr (by nlinarith)

lemma counter_jumpTime_strictMono (ω : ΩCounter) :
    StrictMono (fun n => jumpTime starRate counterY counterClock n ω) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [jumpTime, lt_add_iff_pos_right]
  exact div_pos (clockVal_pos _) (starRate_pos _)

open Classical in
noncomputable def counterX (t : ℝ) (ω : ΩCounter) : ℕ :=
  if h : ∃ n : ℕ, t < jumpTime starRate counterY counterClock (n + 1) ω then
    counterY (Nat.find h) ω
  else
    counterY 0 ω

lemma counterX_eq_of_mem (ω : ΩCounter) (n : ℕ) (t : ℝ)
    (h1 : jumpTime starRate counterY counterClock n ω ≤ t)
    (h2 : t < jumpTime starRate counterY counterClock (n + 1) ω) :
    counterX t ω = counterY n ω := by
  have hex : ∃ m : ℕ, t < jumpTime starRate counterY counterClock (m + 1) ω := ⟨n, h2⟩
  rw [counterX, dif_pos hex]
  have hfind : Nat.find hex = n := by
    apply le_antisymm
    · exact Nat.find_min' hex h2
    · by_contra hlt
      push Not at hlt
      have hspec := Nat.find_spec hex
      have hle : jumpTime starRate counterY counterClock (Nat.find hex + 1) ω ≤
          jumpTime starRate counterY counterClock n ω :=
        (counter_jumpTime_strictMono ω).monotone (by omega)
      linarith
  rw [hfind]

lemma counterX_zero (ω : ΩCounter) : counterX 0 ω = ω.2.1 := by
  have h := counterX_eq_of_mem ω 0 0 (by simp [jumpTime])
    (by simp [jumpTime]; exact div_pos (clockVal_pos _) (starRate_pos _))
  rw [h, counterY, starY_zero]

noncomputable def counterN (_ : ℝ) (_ : ΩCounter) : Fin 0 → ℕ := Fin.elim0
noncomputable def counterZ (t : ℝ) (ω : ΩCounter) : Fin 1 → ℕ := fun _ => counterX t ω

noncomputable def counterM : MarkovRepresentation ℕ 1 0 counterN counterZ where
  jump := starJump
  rate := starRate
  Y := counterY
  clock := counterClock
  X := counterX
  f := fun x => (Fin.elim0, fun _ => x)
  rate_pos := starRate_pos
  jump_irrefl := starJump_irrefl
  jump_chain := by
    intro n path y
    change μCounter {ω | (∀ k : Fin (n + 1), starY k ω.2 = path k) ∧ starY (n + 1) ω.2 = y} =
      μCounter {ω | ∀ k : Fin (n + 1), starY k ω.2 = path k} * starJump (path (Fin.last n)) y
    have h1 : {ω : ΩCounter | (∀ k : Fin (n + 1), starY k ω.2 = path k) ∧ starY (n + 1) ω.2 = y} =
        Set.univ ×ˢ {ωY | (∀ k : Fin (n + 1), starY k ωY = path k) ∧ starY (n + 1) ωY = y} := by
      ext ⟨_, _⟩; simp
    have h2 : {ω : ΩCounter | ∀ k : Fin (n + 1), starY k ω.2 = path k} =
        Set.univ ×ˢ {ωY | ∀ k : Fin (n + 1), starY k ωY = path k} := by
      ext ⟨_, _⟩; simp
    rw [h1, h2, μCounter, prod_outerMeasure_prod, prod_outerMeasure_prod, measure_univ, one_mul, one_mul]
    exact starY_isJumpChain n path y
  clock_pos := fun n ω => clockVal_pos (ω.1.1 n)
  clock_exp := by
    intro n s hs
    change μCounter {ω | s < clockVal (ω.1.1 n)} = ENNReal.ofReal (Real.exp (-s))
    have hset : {ω : ΩCounter | s < clockVal (ω.1.1 n)} =
        {ωG : ΩGood | s < clockVal (ωG.1 n)} ×ˢ Set.univ := by
      ext ⟨_, _⟩; simp
    rw [hset, μCounter, prod_outerMeasure_prod, measure_univ, mul_one, μGood_eq_μClock_image]
    have himg : (Subtype.val : ΩGood → ℕ → ℝ) '' {ωG : ΩGood | s < clockVal (ωG.1 n)} =
        ΩGood ∩ (({n} : Finset ℕ) : Set ℕ).pi (fun _ => {t : ℝ | s < clockVal t}) := by
      ext ω
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right,
        exists_eq_right, Set.mem_inter_iff, Set.mem_pi, Finset.coe_singleton,
        Set.mem_singleton_iff, forall_eq, exists_prop]
    rw [himg, μClock_ΩGood_inter_pi, Finset.prod_singleton, exp1Measure_clockVal_gt s hs]
  clock_iid := by
    rw [iIndepFun_iff]
    intro s f' hf'
    have hexB : ∀ i : ℕ, ∃ B : Set ℝ, i ∈ s → f' i = {ω : ΩCounter | clockVal (ω.1.1 i) ∈ B} := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨B, _, hBeq⟩ := MeasurableSpace.measurableSet_comap.mp (hf' i hi)
        exact ⟨B, fun _ => hBeq.symm⟩
      · exact ⟨Set.univ, fun h => absurd h hi⟩
    choose B hB_eq using hexB
    have hinter : (⋂ i ∈ s, f' i) =
        {ωG : ΩGood | ∀ i ∈ s, clockVal (ωG.1 i) ∈ B i} ×ˢ Set.univ := by
      ext ⟨ωG, ωY⟩
      simp only [Set.mem_iInter, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true]
      exact forall₂_congr fun i hi => by rw [hB_eq i hi]; rfl
    change μCounter (⋂ i ∈ s, f' i) = ∏ i ∈ s, μCounter (f' i)
    rw [hinter, μCounter, prod_outerMeasure_prod, measure_univ, mul_one, μGood_eq_μClock_image]
    have himg : (Subtype.val : ΩGood → ℕ → ℝ) ''
        {ωG : ΩGood | ∀ i ∈ s, clockVal (ωG.1 i) ∈ B i} =
        ΩGood ∩ (s : Set ℕ).pi (fun i => clockVal ⁻¹' B i) := by
      ext ω
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right,
        exists_eq_right, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe, Set.mem_preimage,
        exists_prop]
    rw [himg, μClock_ΩGood_inter_pi]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hB_eq i hi]
    have hset : {ω : ΩCounter | clockVal (ω.1.1 i) ∈ B i} =
        {ωG : ΩGood | clockVal (ωG.1 i) ∈ B i} ×ˢ Set.univ := by
      ext ⟨_, _⟩; simp
    rw [hset]
    change _ = (μGood.prod μY) _
    rw [prod_outerMeasure_prod, measure_univ, mul_one, μGood_eq_μClock_image]
    have himg1 : (Subtype.val : ΩGood → ℕ → ℝ) ''
        {ωG : ΩGood | clockVal (ωG.1 i) ∈ B i} =
        ΩGood ∩ (({i} : Finset ℕ) : Set ℕ).pi (fun _ => clockVal ⁻¹' B i) := by
      ext ω
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right,
        exists_eq_right, Set.mem_inter_iff, Set.mem_pi, Finset.coe_singleton,
        Set.mem_singleton_iff, forall_eq, Set.mem_preimage, exists_prop]
    rw [himg1, μClock_ΩGood_inter_pi, Finset.prod_singleton]
  clock_indep_jumpChain := by
    rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S1, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht1
    obtain ⟨S2, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht2
    let A1 : Set ΩGood := {ωG | (fun n => clockVal (ωG.1 n)) ∈ S1}
    let A2 : Set (ℕ × (ℕ → ℕ)) := {ωY | (fun n => starY n ωY) ∈ S2}
    have h1 : (fun ω : ΩCounter => fun n => counterClock n ω) ⁻¹' S1 = A1 ×ˢ Set.univ := by
      ext ⟨_, _⟩; simp [A1, counterClock]
    have h2 : (fun ω : ΩCounter => fun n => counterY n ω) ⁻¹' S2 = Set.univ ×ˢ A2 := by
      ext ⟨_, _⟩; simp [A2, counterY]
    change μCounter (((fun ω => fun n => counterClock n ω) ⁻¹' S1) ∩
      ((fun ω => fun n => counterY n ω) ⁻¹' S2)) =
      μCounter ((fun ω => fun n => counterClock n ω) ⁻¹' S1) *
      μCounter ((fun ω => fun n => counterY n ω) ⁻¹' S2)
    rw [h1, h2, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter, μCounter,
      prod_outerMeasure_prod, prod_outerMeasure_prod, prod_outerMeasure_prod]
    simp [measure_univ]
  nonexplosive := counter_nonexplosive
  sample_path := counterX_eq_of_mem
  irreducible := starJump_irreducible
  sample_path_eq := fun _ _ => rfl
  finite_fiber := by
    intro z
    refine Set.Finite.subset (Set.finite_singleton (z 0)) ?_
    rintro x ⟨_, hx⟩
    have := congrArg (fun p : (Fin 0 → ℕ) × (Fin 1 → ℕ) => p.2 0) hx
    simpa using this
  empty_state := ⟨0, by ext i <;> [exact Fin.elim0 i; rfl]⟩

lemma counterM_size (x : ℕ) : counterM.size x = (x : ℝ) := by
  simp [MarkovRepresentation.size, counterM]

lemma counterM_hsupp (x : ℕ) : ℙ {ω : ΩCounter | counterM.X 0 ω = x} ≠ 0 := by
  change μCounter {ω : ΩCounter | counterX 0 ω = x} ≠ 0
  have hset : {ω : ΩCounter | counterX 0 ω = x} =
      Set.univ ×ˢ (({x} : Set ℕ) ×ˢ Set.univ) := by
    ext ⟨_, ⟨y, _⟩⟩
    simp [counterX_zero]
  rw [hset, μCounter, μY, prod_outerMeasure_prod, prod_outerMeasure_prod]
  simp only [measure_univ, one_mul, mul_one]
  rw [geomMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), geomPMF_apply]
  exact pow_ne_zero _ (by simp)

/-- For every `k ≥ 1`, the Lebesgue integral of `Z (k * 1) · 0` under `ℙ[|{X 0 = k}]` is ZERO! -/
lemma counterM_lintegral_zero (k : ℕ) :
    ∫⁻ ω, ((counterZ (counterM.size (k + 1) * 1) ω 0 : ℕ) : ℝ≥0∞)
      ∂(ℙ[|{ω : ΩCounter | counterM.X 0 ω = k + 1}]) = 0 := by
  let A : Set ΩCounter := {ω : ΩCounter | counterM.X 0 ω = k + 1}
  have hA_meas : MeasurableSet A := by
    have hset : A = Set.univ ×ˢ (({k + 1} : Set ℕ) ×ˢ Set.univ) := by
      ext ⟨_, ⟨y, _⟩⟩; simp [A, counterM, counterX_zero]
    rw [hset]
    exact MeasurableSet.univ.prod ((measurableSet_singleton _).prod MeasurableSet.univ)
  change ∫⁻ ω, ((counterZ (counterM.size (k + 1) * 1) ω 0 : ℕ) : ℝ≥0∞) ∂(ℙ[|A]) = 0
  rw [lintegral]
  refine iSup₂_eq_bot.mpr fun s hs => ?_
  rw [SimpleFunc.lintegral]
  refine Finset.sum_eq_zero fun c hc => ?_
  by_cases hc0 : c = 0
  · simp [hc0]
  · suffices hzero : (ℙ[|A]) (s ⁻¹' {c}) = 0 by simp [hzero]
    rw [cond_apply hA_meas]
    suffices hmeas0 : ℙ (A ∩ s ⁻¹' {c}) = 0 by simp [hmeas0]
    by_contra hpos
    let E : Set ΩCounter := s ⁻¹' {c}
    have hE_meas : MeasurableSet E := s.measurableSet_fiber c
    have hE_ne0 : ∀ ω ∈ E, counterX ((k + 1 : ℕ) : ℝ) ω ≠ 0 := by
      intro ω hω hX0
      have hsc : s ω = c := hω
      have hle := hs ω
      rw [hsc, counterM_size, mul_one] at hle
      simp only [counterZ, hX0, Nat.cast_zero, nonpos_iff_eq_zero] at hle
      exact hc0 hle
    -- By Tonelli on `μGood.prod μY`, find a slice `ωY` with positive `μGood`-measure
    have hprod_pos : (μGood.prod μY) (A ∩ E) ≠ 0 := hpos
    rw [Measure.prod_apply_symm (hA_meas.inter hE_meas)] at hprod_pos
    have hex_Y : ∃ ωY : ℕ × (ℕ → ℕ),
        μGood ((fun ωG => (ωG, ωY)) ⁻¹' (A ∩ E)) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hprod_pos
      simp_rw [hall]
      simp
    obtain ⟨ωY, hωY_pos⟩ := hex_Y
    have hslice_ne : ((fun ωG => (ωG, ωY)) ⁻¹' (A ∩ E)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hωY_pos (by rw [hemp, measure_empty])
    obtain ⟨ωG0, hωG0⟩ := hslice_ne
    have hωY1 : ωY.1 = k + 1 := by
      have hA0 : (ωG0, ωY) ∈ A := hωG0.1
      simpa [A, counterM, counterX_zero] using hA0
    have hslice_meas : MeasurableSet ((fun ωG => (ωG, ωY)) ⁻¹' (A ∩ E)) :=
      (hA_meas.inter hE_meas).preimage (measurable_id.prodMk measurable_const)
    obtain ⟨E_raw, hE_raw_meas, hE_raw_pre⟩ :=
      MeasurableSpace.measurableSet_comap.mp hslice_meas
    have hE_raw_pos : μClock E_raw ≠ 0 := by
      rw [← μGood_apply_preimage hE_raw_meas, hE_raw_pre]
      exact hωY_pos
    -- Intersect `E_raw` with `{∀ i, 0 < ω i}` (measure 1) and `{∃ m, k + 1 < ω (2*m + 1)}` (measure 1)
    let PosAll : Set (ℕ → ℝ) := {ω | ∀ i : ℕ, 0 < ω i}
    have hPosAll_meas : MeasurableSet PosAll := by
      have heq : PosAll = ⋂ i : ℕ, {ω : ℕ → ℝ | 0 < ω i} := by ext ω; simp [PosAll]
      rw [heq]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    have hPosAll_compl : μClock PosAllᶜ = 0 := by
      have heq : PosAllᶜ = ⋃ i : ℕ, {ω : ℕ → ℝ | ω i ≤ 0} := by ext ω; simp [PosAll]
      rw [heq]
      refine measure_iUnion_null fun i => ?_
      have hpre : {ω : ℕ → ℝ | ω i ≤ 0} = (fun ω : ℕ → ℝ => ω i) ⁻¹' Set.Iic 0 := rfl
      rw [hpre, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic,
        μClock, Measure.infinitePi_map_eval, exp1Measure_Iic_zero]
    let BigOdd : Set (ℕ → ℝ) := ⋃ m : ℕ, {ω : ℕ → ℝ | ((k + 1 : ℕ) : ℝ) < ω (2 * m + 1)}
    have hBigOdd_meas : MeasurableSet BigOdd :=
      MeasurableSet.iUnion fun m =>
        measurableSet_lt measurable_const (measurable_pi_apply (2 * m + 1))
    have hBigOdd_compl : μClock BigOddᶜ = 0 := by
      have hq_lt : exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ)) < 1 := by
        have hdisj : Disjoint (Set.Iic ((k + 1 : ℕ) : ℝ)) (Set.Ioi ((k + 1 : ℕ) : ℝ)) :=
          Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr (Set.mem_Iic.mp h1) (Set.mem_Ioi.mp h2)
        have hsum : exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ)) +
            exp1Measure (Set.Ioi ((k + 1 : ℕ) : ℝ)) = 1 := by
          rw [← measure_union hdisj measurableSet_Ioi, Set.Iic_union_Ioi, measure_univ]
        have hpos_gt : 0 < exp1Measure (Set.Ioi ((k + 1 : ℕ) : ℝ)) := by
          rw [exp1Measure_Ioi _ (by positivity)]
          exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
        have hne1 : exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ)) ≠ 1 := by
          intro h1
          rw [h1] at hsum
          have h0 := (ENNReal.add_right_inj (a := (1 : ℝ≥0∞))
            (b := exp1Measure (Set.Ioi ((k + 1 : ℕ) : ℝ))) (c := 0) (by simp)).mp
            (by simpa using hsum)
          exact ne_of_gt hpos_gt h0
        exact lt_of_le_of_ne prob_le_one hne1
      have hle : ∀ r : ℕ, μClock BigOddᶜ ≤ (exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ))) ^ r := by
        intro r
        let S : Finset ℕ := (Finset.range r).image (fun m => 2 * m + 1)
        have hcard : S.card = r := by
          rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
        have hsub : BigOddᶜ ⊆ (S : Set ℕ).pi (fun _ => Set.Iic ((k + 1 : ℕ) : ℝ)) := by
          intro ω hω i hi
          simp only [S, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hi
          rcases hi with ⟨m, _, rfl⟩
          simp only [BigOdd, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
            not_lt] at hω
          exact hω m
        calc μClock BigOddᶜ
            ≤ μClock ((S : Set ℕ).pi (fun _ => Set.Iic ((k + 1 : ℕ) : ℝ))) := measure_mono hsub
          _ = ∏ _ ∈ S, exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ)) :=
              Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic)
          _ = (exp1Measure (Set.Iic ((k + 1 : ℕ) : ℝ))) ^ r := by
              rw [Finset.prod_const, hcard]
      have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq_lt
      exact le_antisymm (ge_of_tendsto' htend hle) bot_le
    have hE_inter_pos : μClock (E_raw ∩ PosAll ∩ BigOdd) ≠ 0 := by
      have heq1 : μClock (E_raw ∩ PosAll) = μClock E_raw := by
        apply le_antisymm (measure_mono Set.inter_subset_left)
        calc μClock E_raw ≤ μClock ((E_raw ∩ PosAll) ∪ PosAllᶜ) :=
              measure_mono fun x hx => by by_cases h : x ∈ PosAll <;> simp [hx, h]
          _ ≤ μClock (E_raw ∩ PosAll) + μClock PosAllᶜ := measure_union_le _ _
          _ = μClock (E_raw ∩ PosAll) := by rw [hPosAll_compl, add_zero]
      have heq2 : μClock (E_raw ∩ PosAll ∩ BigOdd) = μClock (E_raw ∩ PosAll) := by
        apply le_antisymm (measure_mono Set.inter_subset_left)
        calc μClock (E_raw ∩ PosAll) ≤ μClock ((E_raw ∩ PosAll ∩ BigOdd) ∪ BigOddᶜ) :=
              measure_mono fun x hx => by by_cases h : x ∈ BigOdd <;> simp [hx, h]
          _ ≤ μClock (E_raw ∩ PosAll ∩ BigOdd) + μClock BigOddᶜ := measure_union_le _ _
          _ = μClock (E_raw ∩ PosAll ∩ BigOdd) := by rw [hBigOdd_compl, add_zero]
      rw [heq2, heq1]
      exact hE_raw_pos
    have hex_m : ∃ m : ℕ,
        μClock (E_raw ∩ PosAll ∩ {ω : ℕ → ℝ | ((k + 1 : ℕ) : ℝ) < ω (2 * m + 1)}) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hcov : E_raw ∩ PosAll ∩ BigOdd ⊆
          ⋃ m : ℕ, (E_raw ∩ PosAll ∩ {ω : ℕ → ℝ | ((k + 1 : ℕ) : ℝ) < ω (2 * m + 1)}) := by
        intro ω ⟨h1, h2⟩
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp h2
        exact Set.mem_iUnion.mpr ⟨m, h1, hm⟩
      exact hE_inter_pos (measure_mono_null hcov (measure_iUnion_null hall))
    obtain ⟨m, hm_pos⟩ := hex_m
    let M_max : ℝ := ∑ i ∈ Finset.range (2 * m + 1), (starRate (starY i ωY))⁻¹
    have hM_nonneg : 0 ≤ M_max := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (starRate_pos _).le
    have htend_half : Tendsto (fun j : ℕ => ((2 : ℝ)⁻¹ ^ (j + 1)) * M_max) atTop (nhds 0) := by
      have h1 : Tendsto (fun j : ℕ => (2 : ℝ)⁻¹ ^ j) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 : Tendsto (fun j : ℕ => (2 : ℝ)⁻¹ ^ (j + 1)) atTop (nhds 0) :=
        h1.comp (tendsto_add_atTop_nat 1)
      simpa using h2.mul_const M_max
    obtain ⟨j, hj⟩ := (htend_half.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
    let Em := E_raw ∩ PosAll ∩ {ω : ℕ → ℝ | ((k + 1 : ℕ) : ℝ) < ω (2 * m + 1)}
    have hEm_meas : MeasurableSet Em :=
      (hE_raw_meas.inter hPosAll_meas).inter
        (measurableSet_lt measurable_const (measurable_pi_apply (2 * m + 1)))
    obtain ⟨ω_raw, ⟨⟨⟨hω_Eraw, hω_pos⟩, hω_big⟩, hω_good⟩, hω_buck⟩ :=
      exists_in_good_of_pos hEm_meas hm_pos (2 * m + 2)
        (fun i => if i.1 < 2 * m + 1 then j + 1 else 0)
    let ω : ΩCounter := (⟨ω_raw, hω_good⟩, ωY)
    have hω_in_E : ω ∈ E := by
      have hmem : (⟨ω_raw, hω_good⟩ : ΩGood) ∈ (Subtype.val : ΩGood → ℕ → ℝ) ⁻¹' E_raw := hω_Eraw
      rw [hE_raw_pre] at hmem
      exact hmem.2
    -- Show `jumpTime (2*m + 1) ω ≤ k + 1 < jumpTime (2*m + 2) ω`
    have hjt_le : jumpTime starRate counterY counterClock (2 * m + 1) ω ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [counter_jumpTime_eq]
      calc ∑ i ∈ Finset.range (2 * m + 1), counterClock i ω / starRate (counterY i ω)
          ≤ ∑ i ∈ Finset.range (2 * m + 1),
              ((2 : ℝ)⁻¹ ^ (j + 1)) * (starRate (starY i ωY))⁻¹ := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi_lt : i < 2 * m + 1 := Finset.mem_range.mp hi
            rw [div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (starRate_pos _).le)
            have hbi : bucket (ω_raw i) = j + 1 := by
              have := hω_buck ⟨i, by omega⟩
              simpa [hi_lt] using this
            exact clockVal_le_pow (hω_pos i) hbi
        _ = ((2 : ℝ)⁻¹ ^ (j + 1)) * M_max := by rw [← Finset.mul_sum]
        _ ≤ 1 := le_of_lt hj
        _ ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hY_odd : counterY (2 * m + 1) ω = 0 := by
      rcases ωY with ⟨y0, u⟩
      dsimp only at hωY1
      subst hωY1
      exact starY_odd_of_pos m
    have hjt_gt : ((k + 1 : ℕ) : ℝ) < jumpTime starRate counterY counterClock (2 * m + 2) ω := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, jumpTime, hY_odd, starRate, div_one]
      have hjt_nonneg : 0 ≤ jumpTime starRate counterY counterClock (2 * m + 1) ω := by
        rw [counter_jumpTime_eq]
        exact Finset.sum_nonneg fun i _ => div_nonneg (clockVal_pos _).le (starRate_pos _).le
      have hb_odd : bucket (ω_raw (2 * m + 1)) = 0 := by
        have := hω_buck ⟨2 * m + 1, by omega⟩
        simp at this
        exact this
      have hclk_odd : counterClock (2 * m + 1) ω = ω_raw (2 * m + 1) :=
        clockVal_eq_self (hω_pos (2 * m + 1)) hb_odd
      rw [hclk_odd]
      have hbig : ((k + 1 : ℕ) : ℝ) < ω_raw (2 * m + 1) := hω_big
      linarith
    have hX0 : counterX ((k + 1 : ℕ) : ℝ) ω = 0 := by
      rw [counterX_eq_of_mem ω (2 * m + 1) ((k + 1 : ℕ) : ℝ) hjt_le hjt_gt, hY_odd]
    exact hE_ne0 ω hω_in_E hX0

lemma counterM_hdrift :
    Tendsto (fun x : ℕ => fun i : Fin 1 =>
        (∫⁻ ω, ((counterZ (counterM.size x * 1) ω i : ℕ) : ℝ≥0∞)
          ∂(ℙ[|{ω : ΩCounter | counterM.X 0 ω = x}])) /
          ENNReal.ofReal (counterM.size x))
      (Filter.comap counterM.size Filter.atTop) (nhds (0 : Fin 1 → ℝ≥0∞)) := by
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_comap]
  refine Filter.eventually_atTop.mpr ⟨1, fun r hr x hx => ?_⟩
  ext i
  fin_cases i
  have hx_ge : (1 : ℝ) ≤ (x : ℝ) := by rw [counterM_size] at hx; linarith
  have hx_pos : 1 ≤ x := by exact_mod_cast hx_ge
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  have hz := counterM_lintegral_zero k
  simp only [mul_one] at hz
  simp [hz]

end PN1Counterexample

/-- Disproof of `ProcessingNetworks.Stability.drift_condition_implies_positive_recurrent` as
formalized: because `MarkovRepresentation` does not require `clock` to be measurable in `Ω`,
one can construct an irreducible, non-explosive, non-positive-recurrent star-graph CTMC whose
non-measurable exponential clocks make the Lebesgue integral `∫⁻ ω, Z(|x|δ) ω i ∂(ℙ[|{X 0 = x}])`
vanish identically for all `|x| ≥ 1`, so `hdrift` holds while `PositiveRecurrent` fails. -/
theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (_hsupp : ∀ x : Xstate, ℙ {ω | M.X 0 ω = x} ≠ 0)
    (δ : ℝ) (_hδ : 0 < δ)
    (_hdrift :
      Tendsto (fun x : Xstate => fun i : Fin I =>
          (∫⁻ ω, ((Z (M.size x * δ) ω i : ℕ) : ℝ≥0∞) ∂(ℙ[|{ω | M.X 0 ω = x}])) /
            ENNReal.ofReal (M.size x))
        (Filter.comap M.size Filter.atTop) (nhds (0 : Fin I → ℝ≥0∞))),
    PositiveRecurrent M.jump M.rate) := by
  intro h
  exact PN1Counterexample.not_positiveRecurrent_star
    (h PN1Counterexample.counterM PN1Counterexample.counterM_hsupp 1 one_pos
      PN1Counterexample.counterM_hdrift)


