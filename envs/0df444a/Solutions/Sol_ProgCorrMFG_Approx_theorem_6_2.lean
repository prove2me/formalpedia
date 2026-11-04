-- Prove2me | solution 1 for ProgCorrMFG.Approx.theorem_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:04:10.5442+00:00
-- url     : https://prove2.me/submissions/8badee92-fa2a-4dbf-b13c-5497366c6d2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Theorems.Thm_ProgCorrMFG_Approx_eq_6_2
import Theorems.Thm_ProgCorrMFG_Approx_eq_6_3

namespace ProgCorrMFG.Approx.Red62

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-! ### Boundedness of the costs under (A3) -/

theorem distTV_le_one {X : Type} [Fintype X] (μ μ' : Meas X) : distTV μ μ' ≤ 1 := by
  show (1 / 2 : ℝ) * ∑ x, |μ.1 x - μ'.1 x| ≤ 1
  have h1 : ∑ x, μ.1 x = 1 := μ.2.2
  have h2 : ∑ x, μ'.1 x = 1 := μ'.2.2
  have hle : ∑ x, |μ.1 x - μ'.1 x| ≤ ∑ x, (μ.1 x + μ'.1 x) := by
    apply Finset.sum_le_sum
    intro x _
    have a : 0 ≤ μ.1 x := μ.2.1 x
    have b : 0 ≤ μ'.1 x := μ'.2.1 x
    rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, h1, h2] at hle
  linarith

theorem distTV_nonneg {X : Type} [Fintype X] (μ μ' : Meas X) : 0 ≤ distTV μ μ' := by
  unfold distTV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem A3_bound {T : ℕ} {X G : Type} [Fintype X] [Nonempty X] [Fintype G] [MeasurableSpace X]
    [MeasurableSpace G] (M : Model T X G) (hA3 : M.A3) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t x m g, |M.f t x m g| ≤ B) ∧ ∀ x m, |M.F x m| ≤ B := by
  classical
  obtain ⟨L, hf, hF⟩ := hA3
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  let c : Meas X := ⟨Pi.single x₀ 1, single_mem_stdSimplex ℝ x₀⟩
  let K : ℝ := (∑ q : Fin T × X × G, |M.f q.1 q.2.1 c q.2.2|) + ∑ x, |M.F x c|
  have hK1 : ∀ t x g, |M.f t x c g| ≤ K := by
    intro t x g
    have := Finset.single_le_sum (f := fun q : Fin T × X × G => |M.f q.1 q.2.1 c q.2.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (t, x, g))
    have h2 : 0 ≤ ∑ x, |M.F x c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  have hK2 : ∀ x, |M.F x c| ≤ K := by
    intro x
    have := Finset.single_le_sum (f := fun x => |M.F x c|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
    have h2 : 0 ≤ ∑ q : Fin T × X × G, |M.f q.1 q.2.1 c q.2.2| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  have hLd : ∀ m, L * distTV m c ≤ |L| := by
    intro m
    have h0 := distTV_nonneg m c
    have h1 := distTV_le_one m c
    calc L * distTV m c ≤ |L| * distTV m c :=
          mul_le_mul_of_nonneg_right (le_abs_self L) h0
      _ ≤ |L| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)
      _ = |L| := mul_one _
  refine ⟨K + |L|, ?_, ?_, ?_⟩
  · have := hK2 x₀
    have := abs_nonneg (M.F x₀ c)
    have := abs_nonneg L
    linarith
  · intro t x m g
    have h1 := hf t x g m c
    have h2 := abs_sub_abs_le_abs_sub (M.f t x m g) (M.f t x c g)
    have := hK1 t x g
    have := hLd m
    linarith
  · intro x m
    have h1 := hF x m c
    have h2 := abs_sub_abs_le_abs_sub (M.F x m) (M.F x c)
    have := hK2 x
    have := hLd m
    linarith

theorem NRealization.cost_abs_le {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] {M : Model T X G} {N : ℕ} {i : Fin N} {mN : Measure (Fin N → X)}
    {γ : Measure (Fin N → ProgN T X G (N - 1))}
    {γ' : Measure (ProgN T X G (N - 1) × ProgN T X G (N - 1))}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (R : NRealization M N i mN γ γ' P) (B : ℝ)
    (hf : ∀ t x m g, |M.f t x m g| ≤ B) (hF : ∀ x m, |M.F x m| ≤ B) :
    |R.cost| ≤ (T + 1) * B := by
  unfold NRealization.cost
  have := norm_integral_le_of_norm_le_const (μ := P) (C := (T + 1) * B)
    (f := fun ω => (∑ t : Fin T, M.f t (R.state ω t.castSucc i)
      (empOthers (R.state ω t.castSucc) i).1
      ((R.dev ω t).1 (fun s => R.state ω s i) (fun s => empOthers (R.state ω s) i))) +
      M.F (R.state ω (Fin.last T) i) (empOthers (R.state ω (Fin.last T)) i).1)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      have h1 : |∑ t : Fin T, M.f t (R.state ω t.castSucc i)
          (empOthers (R.state ω t.castSucc) i).1
          ((R.dev ω t).1 (fun s => R.state ω s i) (fun s => empOthers (R.state ω s) i))|
          ≤ T * B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun t _ => hf _ _ _ _).trans ?_
        simp
      have h2 := hF (R.state ω (Fin.last T) i) (empOthers (R.state ω (Fin.last T)) i).1
      linarith)
  simpa [Real.norm_eq_abs] using this

/-! ### A generic non-anticipative recursion -/

section Gen

variable {T : ℕ} {Θ Y : Type}

/-- After `k` steps, coordinates `0, …, k` hold the solution, the others still hold `x₀ θ`. -/
noncomputable def genPath (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    ℕ → Fin (T + 1) → Y
  | 0 => fun _ => x₀ θ
  | k + 1 =>
    if h : k < T then
      Function.update (genPath x₀ step θ k) ⟨k + 1, by omega⟩ (step ⟨k, h⟩ θ (genPath x₀ step θ k))
    else genPath x₀ step θ k

theorem genPath_succ_of_ne (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (k : ℕ) (j : Fin (T + 1)) (hj : j.1 ≠ k + 1) :
    genPath x₀ step θ (k + 1) j = genPath x₀ step θ k j := by
  simp only [genPath]
  split_ifs with h
  · rw [Function.update_of_ne]
    exact fun h' => hj (by rw [h'])
  · rfl

theorem genPath_stable (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (j : Fin (T + 1)) : ∀ d, genPath x₀ step θ (j.1 + d) j = genPath x₀ step θ j.1 j := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, genPath_succ_of_ne _ _ _ _ _ (by omega), ih]

theorem genPath_le (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (j : Fin (T + 1)) (k : ℕ) (hk : j.1 ≤ k) :
    genPath x₀ step θ k j = genPath x₀ step θ j.1 j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact genPath_stable x₀ step θ j d

/-- The solution of the recursion. -/
noncomputable def gen (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    Fin (T + 1) → Y := genPath x₀ step θ T

def NonAntStep (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) : Prop :=
  ∀ t θ p p', (∀ s : Fin (T + 1), s ≤ t.castSucc → p s = p' s) → step t θ p = step t θ p'

theorem gen_zero (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    gen x₀ step θ 0 = x₀ θ := by
  unfold gen
  rw [genPath_le x₀ step θ 0 T (by simp)]
  rfl

theorem gen_succ (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hstep : NonAntStep step) (θ : Θ) (t : Fin T) :
    gen x₀ step θ t.succ = step t θ (gen x₀ step θ) := by
  unfold gen
  rw [genPath_le x₀ step θ t.succ T (by simp)]
  have : (t.succ : Fin (T + 1)).1 = t.1 + 1 := rfl
  rw [this]
  simp only [genPath, t.2, dite_true]
  have e : (⟨t.1 + 1, by omega⟩ : Fin (T + 1)) = t.succ := rfl
  rw [e, Function.update_self]
  apply hstep
  intro s hs
  have hs' : s.1 ≤ t.1 := hs
  rw [genPath_le x₀ step θ s t.1 hs', genPath_le x₀ step θ s T (by omega)]

theorem gen_unique (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hstep : NonAntStep step) (θ : Θ) (s : Fin (T + 1) → Y) (h0 : s 0 = x₀ θ)
    (hs : ∀ t : Fin T, s t.succ = step t θ s) : s = gen x₀ step θ := by
  have key : ∀ n, ∀ j : Fin (T + 1), j.1 ≤ n → s j = gen x₀ step θ j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      obtain rfl : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [h0, gen_zero]
    | succ n ih =>
      intro j hj
      rcases Nat.lt_or_ge j.1 (n + 1) with h | h
      · exact ih j (by omega)
      · have hjT : n < T := by have := j.2; omega
        have ej : j = (⟨n, hjT⟩ : Fin T).succ := Fin.ext (by simp; omega)
        rw [ej, hs, gen_succ x₀ step hstep]
        apply hstep
        intro s' hs'
        exact ih s' hs'
  funext j
  exact key j.1 j le_rfl

variable [MeasurableSpace Θ] [MeasurableSpace Y]

theorem measurable_gen (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hx₀ : Measurable x₀)
    (hstep : ∀ t, Measurable (fun q : Θ × (Fin (T + 1) → Y) => step t q.1 q.2)) :
    Measurable (gen x₀ step) := by
  have : ∀ k, Measurable (fun θ => genPath x₀ step θ k) := by
    intro k
    induction k with
    | zero => exact measurable_pi_lambda _ (fun _ => hx₀)
    | succ k ih =>
      by_cases hk : k < T
      · simp only [genPath, hk, dite_true]
        apply measurable_pi_lambda
        intro j
        by_cases hj : j = ⟨k + 1, by omega⟩
        · rw [hj]
          simp only [Function.update_self]
          exact (hstep ⟨k, hk⟩).comp (measurable_id.prodMk ih)
        · simp only [Function.update_of_ne hj]
          exact (measurable_pi_apply _).comp ih
      · simp only [genPath, hk, dite_false]
        exact ih
  exact this T

end Gen


/-! ### Existence of realizations -/

section Exist

variable {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]

theorem exists_MFGReal (M : Model T X G) (hΨ : M.PsiMeasurable)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (MFGRealization M m₀ ρ iotaMFG P) := by
  let step : Fin T → X × (Fin T → I) × (Strat T X G × Flow T X) → (Fin (T + 1) → X) → X :=
    fun t θ p => M.Ψ t (p t.castSucc) (θ.2.2.2 t.castSucc) (θ.2.2.1 t (p t.castSucc)) (θ.2.1 t)
  have hna : NonAntStep step := by
    intro t θ p p' h
    simp only [step, h t.castSucc le_rfl]
  have hmeas : ∀ t, Measurable (fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
      (Fin (T + 1) → X) => step t q.1 q.2) := by
    intro t
    have h3 : Measurable (fun r : Strat T X G × (Fin (T + 1) → X) => r.1 t (r.2 t.castSucc)) :=
      measurable_of_countable _
    have h3' : Measurable (fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => q.1.2.2.1 t (q.2 t.castSucc)) :=
      h3.comp (f := fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => (q.1.2.2.1, q.2)) (by fun_prop)
    exact (hΨ t).comp (f := fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => (q.2 t.castSucc, q.1.2.2.2 t.castSucc,
          q.1.2.2.1 t (q.2 t.castSucc), q.1.2.1 t))
      (Measurable.prodMk (by fun_prop) (Measurable.prodMk (by fun_prop)
        (Measurable.prodMk h3' (by fun_prop))))
  refine ⟨X × (Fin T → I) × (Strat T X G × Flow T X), inferInstance,
    m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ), inferInstance,
    ⟨{ state := gen Prod.fst step
       sugg := fun ω => ω.2.2.1
       flow := fun ω => ω.2.2.2
       noise := fun ω => ω.2.1
       measurable_state := measurable_gen _ _ measurable_fst hmeas
       measurable_sugg := by fun_prop
       measurable_flow := by fun_prop
       measurable_noise := by fun_prop
       law := ?_
       dynamics := ?_ }⟩⟩
  · have : (fun ω : X × (Fin T → I) × (Strat T X G × Flow T X) =>
        (gen Prod.fst step ω 0, ω.2.1, (ω.2.2.1, ω.2.2.2))) = id := by
      funext ω
      rw [gen_zero]
      rfl
    rw [this, Measure.map_id]
  · exact Filter.Eventually.of_forall fun ω t => gen_succ _ _ hna ω t

theorem played_self {T : ℕ} {X G : Type} [Fintype X] {n N : ℕ} (i : Fin N)
    (sugg : Fin N → ProgN T X G n) (j : Fin N) : played i sugg (sugg i) j = sugg j := by
  unfold played
  split_ifs with h
  · rw [h]
  · rfl

theorem measurable_evalN (t : Fin T) (N : ℕ) (j : Fin N) :
    Measurable (fun r : CompN T X G (N - 1) t × (Fin (T + 1) → Fin N → X) =>
      r.1.1 (fun s => r.2 s j) (fun s => empOthers (r.2 s) j)) :=
  measurable_from_prod_countable_left (fun _ => measurable_from_top)

abbrev ThetaN (T : ℕ) (X G : Type) [Fintype X] (N : ℕ) : Type :=
  (Fin T → Fin N → I) × ((Fin N → X) × ((Fin T → I) × (Fin N → ProgN T X G (N - 1))))

theorem exists_NReal (M : Model T X G) (hΨ : M.PsiMeasurable) (N : ℕ) (i : Fin N)
    (mN : Measure (Fin N → X)) [IsProbabilityMeasure mN]
    (γ : Measure (Fin N → ProgN T X G (N - 1))) [IsProbabilityMeasure γ] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (NRealization M N i mN γ (iotaN (γ.map (fun φ => φ i))) P) := by
  let step : Fin T → ThetaN T X G N → (Fin (T + 1) → Fin N → X) → (Fin N → X) :=
    fun t θ p j => M.Ψ t (p t.castSucc j) (empOthers (p t.castSucc) j).1
      ((θ.2.2.2 j t).1 (fun s => p s j) (fun s => empOthers (p s) j)) (θ.1 t j)
  have hna : NonAntStep step := by
    intro t θ p p' h
    funext j
    simp only [step]
    rw [h t.castSucc le_rfl]
    congr 2
    apply (θ.2.2.2 j t).2
    intro s hs
    rw [h s hs]
    exact ⟨rfl, rfl⟩
  have hmeas : ∀ t, Measurable (fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) => step t q.1 q.2) := by
    intro t
    apply measurable_pi_lambda
    intro j
    have h2 : Measurable (fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) =>
        (empOthers (q.2 t.castSucc) j).1) :=
      (measurable_of_countable (fun p : Fin (T + 1) → Fin N → X =>
        (empOthers (p t.castSucc) j).1)).comp measurable_snd
    have h3 : Measurable (fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) =>
        (q.1.2.2.2 j t).1 (fun s => q.2 s j) (fun s => empOthers (q.2 s) j)) :=
      (measurable_evalN t N j).comp (f := fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) =>
        (q.1.2.2.2 j t, q.2)) (by fun_prop)
    exact (hΨ t).comp (f := fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) =>
        (q.2 t.castSucc j, (empOthers (q.2 t.castSucc) j).1,
          (q.1.2.2.2 j t).1 (fun s => q.2 s j) (fun s => empOthers (q.2 s) j), q.1.1 t j))
      (Measurable.prodMk (by fun_prop) (Measurable.prodMk h2 (Measurable.prodMk h3 (by fun_prop))))
  let P : Measure (ThetaN T X G N) := (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).prod
      (mN.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod γ))
  have hPγ : P.map (fun ω : ThetaN T X G N => ω.2.2.2) = γ := by
    have : (fun ω : ThetaN T X G N => ω.2.2.2) = Prod.snd ∘ Prod.snd ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [P, Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨ThetaN T X G N, inferInstance, P, by infer_instance,
    ⟨{ state := gen (fun θ : ThetaN T X G N => θ.2.1) step
       sugg := fun ω => ω.2.2.2
       dev := fun ω => ω.2.2.2 i
       noise := fun ω => ω.1
       coin := fun ω => ω.2.2.1
       measurable_state := measurable_gen _ _ (by fun_prop) hmeas
       measurable_sugg := by fun_prop
       measurable_dev := by fun_prop
       measurable_noise := by fun_prop
       measurable_coin := by fun_prop
       law := ?_
       dev_law := ?_
       dev_adapted := ?_
       dynamics := ?_ }⟩⟩
  · have : (fun ω : ThetaN T X G N => (ω.1, gen (fun θ : ThetaN T X G N => θ.2.1) step ω 0, ω.2.2.1, ω.2.2.2)) = id := by
      funext ω
      rw [gen_zero]
      rfl
    rw [this, Measure.map_id]
  · unfold iotaN
    rw [← hPγ, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · intro t
    have : (fun ω : ThetaN T X G N => ω.2.2.2 i t) =
        (fun p : ProgN T X G (N - 1) × I => p.1 t) ∘ (fun ω : ThetaN T X G N => (ω.2.2.2 i, ω.2.2.1 t)) := rfl
    rw [this]
    exact (measurable_pi_apply t).comp (measurable_fst.comp (comap_measurable _))
  · refine Filter.Eventually.of_forall fun ω t j => ?_
    rw [gen_succ _ _ hna ω t]
    simp only [step]
    rw [played_self]

end Exist

/-! ### Symmetry -/

section Symm

theorem empOthers_val {X : Type} [Fintype X] [DecidableEq X] {N : ℕ} (x : Fin N → X)
    (l : Fin N) : (empOthers x l).1.1 = if 2 ≤ N then empVal x l else Pi.single (x l) 1 := by
  unfold empOthers
  by_cases h : 2 ≤ N <;> simp [h]

theorem empOthers_comp {X : Type} [Fintype X] [DecidableEq X] {N : ℕ} (x : Fin N → X)
    (e : Equiv.Perm (Fin N)) (j : Fin N) : empOthers (x ∘ e) j = empOthers x (e j) := by
  apply Subtype.ext; apply Subtype.ext
  rw [empOthers_val, empOthers_val]
  split_ifs with h
  · funext y
    unfold empVal
    congr 1
    apply Finset.sum_equiv e
    · intro k
      simp
    · intro k _
      rfl
  · rfl

theorem played_comp {T : ℕ} {X G : Type} [Fintype X] {n N : ℕ} (e : Equiv.Perm (Fin N))
    (i i' : Fin N) (he : e i' = i) (sugg : Fin N → ProgN T X G n) (dev : ProgN T X G n)
    (j : Fin N) : played i' (sugg ∘ e) dev j = played i sugg dev (e j) := by
  unfold played
  by_cases h : j = i'
  · subst h; simp [he]
  · have : e j ≠ i := by
      rw [← he]; exact fun h' => h (e.injective h')
    simp [h, this]

theorem pi_comp_perm {ι α : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (e : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => μ).map (fun x => x ∘ e) = Measure.pi fun _ => μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hm : Measurable (fun x : ι → α => x ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → α => x ∘ e) ⁻¹' Set.univ.pi s = Set.univ.pi (fun j => s (e.symm j)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h j
      have := h (e.symm j)
      simpa using this
    · intro h j
      have := h (e j)
      rwa [Equiv.symm_apply_apply] at this
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp e.symm (fun j => μ (s j))

variable {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]

theorem transfer (M : Model T X G) (N : ℕ) (e : Equiv.Perm (Fin N)) (i i' : Fin N)
    (he : e i' = i) (mN : Measure (Fin N → X)) [IsProbabilityMeasure mN]
    (γ : Measure (Fin N → ProgN T X G (N - 1))) [IsProbabilityMeasure γ]
    (hγ : γ.map (fun s => s ∘ e) = γ) (hmN : mN.map (fun x => x ∘ e) = mN)
    (γ' γ'' : Measure (ProgN T X G (N - 1) × ProgN T X G (N - 1))) (hγ' : γ' = γ'')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : NRealization M N i mN γ γ' P) :
    ∃ R' : NRealization M N i' mN γ γ'' P, R'.cost = R.cost := by
  have hcs : Measurable (fun x : Fin N → X => x ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hcsI : Measurable (fun x : Fin N → I => x ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hcsP : Measurable (fun x : Fin N → ProgN T X G (N - 1) => x ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hnz : Measurable (fun n : Fin T → Fin N → I => fun t => n t ∘ e) :=
    measurable_pi_lambda _ fun t => hcsI.comp (measurable_pi_apply t)
  have hst : Measurable (fun x : Fin (T + 1) → Fin N → X => fun t => x t ∘ e) :=
    measurable_pi_lambda _ fun t => hcs.comp (measurable_pi_apply t)
  have hnoise : (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).map
      (fun n t => n t ∘ e) = Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I) := by
    rw [Measure.pi_map_pi (fun _ => hcsI.aemeasurable)]
    simp only [pi_comp_perm]
  refine ⟨{ state := fun ω t => R.state ω t ∘ e
            sugg := fun ω => R.sugg ω ∘ e
            dev := R.dev
            noise := fun ω t => R.noise ω t ∘ e
            coin := R.coin
            measurable_state := hst.comp R.measurable_state
            measurable_sugg := hcsP.comp R.measurable_sugg
            measurable_dev := R.measurable_dev
            measurable_noise := hnz.comp R.measurable_noise
            measurable_coin := R.measurable_coin
            law := ?_
            dev_law := ?_
            dev_adapted := ?_
            dynamics := ?_ }, ?_⟩
  · have hV : Measurable (fun ω => (R.noise ω, R.state ω 0, R.coin ω, R.sugg ω)) :=
      R.measurable_noise.prodMk (((measurable_pi_apply 0).comp R.measurable_state).prodMk
        (R.measurable_coin.prodMk R.measurable_sugg))
    have : (fun ω => ((fun t => R.noise ω t ∘ e), R.state ω 0 ∘ e, R.coin ω, R.sugg ω ∘ e)) =
        (Prod.map (fun n : Fin T → Fin N → I => fun t => n t ∘ e)
          (Prod.map (fun x : Fin N → X => x ∘ e) (Prod.map id (fun x : Fin N → ProgN T X G (N - 1) =>
            x ∘ e)))) ∘ (fun ω => (R.noise ω, R.state ω 0, R.coin ω, R.sugg ω)) := rfl
    rw [this, ← Measure.map_map (by fun_prop) hV, R.law,
      ← Measure.map_prod_map _ _ hnz (by fun_prop),
      ← Measure.map_prod_map _ _ hcs (by fun_prop),
      ← Measure.map_prod_map _ _ measurable_id hcsP, Measure.map_id, hnoise, hγ, hmN]
  · have h1 : (fun ω => ((R.sugg ω ∘ e) i', R.dev ω)) = (fun ω => (R.sugg ω i, R.dev ω)) := by
      funext ω; simp [he]
    rw [h1, R.dev_law, hγ']
  · intro t
    have : (fun ω => ((R.sugg ω ∘ e) i', R.coin ω t)) = (fun ω => (R.sugg ω i, R.coin ω t)) := by
      funext ω; simp [he]
    rw [this]
    exact R.dev_adapted t
  · filter_upwards [R.dynamics] with ω hω t j
    show R.state ω t.succ (e j) = _
    rw [hω t (e j)]
    simp only [Function.comp_apply, empOthers_comp, played_comp e i i' he]
  · unfold NRealization.cost
    congr 1
    funext ω
    simp only [Function.comp_apply, empOthers_comp, he]

end Symm

/-! ### The correlated suggestion `γ^N` -/

section Gamma

variable {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Fintype G] [MeasurableSpace G]
  [DiscreteMeasurableSpace G]

theorem gammaN_singleton (ρ₂ : Measure (Flow T X)) (ρ₁ : Kernel (Flow T X) (Strat T X G)) (N : ℕ)
    (ψ : Fin N → Strat T X G) : gammaN ρ₂ ρ₁ N {ψ} = ∫⁻ m, ∏ j, ρ₁ m {ψ j} ∂ρ₂ := by
  unfold gammaN
  rw [Measure.sum_apply _ (measurableSet_singleton ψ)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ψ]
  · simp
  · intro b hb
    simp [hb]

theorem gammaN_prob (ρ₂ : Measure (Flow T X)) [IsProbabilityMeasure ρ₂]
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁] (N : ℕ) :
    IsProbabilityMeasure (gammaN ρ₂ ρ₁ N) := by
  constructor
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp only [gammaN_singleton]
  rw [← lintegral_finsetSum]
  · have : ∀ m, ∑ ψ : Fin N → Strat T X G, ∏ j, ρ₁ m {ψ j} = 1 := by
      intro m
      rw [← Fintype.prod_sum (fun (_ : Fin N) (φ : Strat T X G) => ρ₁ m {φ})]
      have h1 : ∑ φ : Strat T X G, ρ₁ m {φ} = 1 := by
        rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
      simp [h1]
    simp [this]
  · intro ψ _
    exact Finset.measurable_prod _ fun j _ => Kernel.measurable_coe ρ₁ (measurableSet_singleton _)

theorem gammaN_perm (ρ₂ : Measure (Flow T X)) (ρ₁ : Kernel (Flow T X) (Strat T X G)) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : (gammaN ρ₂ ρ₁ N).map (fun s => s ∘ e) = gammaN ρ₂ ρ₁ N := by
  have hm : Measurable (fun s : Fin N → Strat T X G => s ∘ e) := measurable_of_countable _
  rw [Measure.ext_iff_singleton]
  intro ψ
  rw [Measure.map_apply hm (measurableSet_singleton ψ)]
  have : (fun s : Fin N → Strat T X G => s ∘ e) ⁻¹' {ψ} = {ψ ∘ e.symm} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl; funext j; simp
    · rintro rfl; funext j; simp
  rw [this, gammaN_singleton, gammaN_singleton]
  congr 1
  funext m
  exact Equiv.prod_comp e.symm (fun j => ρ₁ m {ψ j})

theorem liftSugg_perm {N : ℕ} (γ : Measure (Fin N → Strat T X G)) (e : Equiv.Perm (Fin N))
    (hγ : γ.map (fun s => s ∘ e) = γ) :
    (liftSugg γ).map (fun s => s ∘ e) = liftSugg γ := by
  unfold liftSugg
  have hL : Measurable (fun (φs : Fin N → Strat T X G) (j : Fin N) =>
      (embN (φs j) : ProgN T X G (N - 1))) := measurable_of_countable _
  have hP : Measurable (fun x : Fin N → ProgN T X G (N - 1) => x ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  rw [Measure.map_map hP hL]
  conv_rhs => rw [← hγ]
  rw [Measure.map_map hL (measurable_of_countable _)]
  rfl

theorem marg_eq {α : Type} [MeasurableSpace α] {N : ℕ} (γ : Measure (Fin N → α)) (e : Equiv.Perm (Fin N))
    (hγ : γ.map (fun s => s ∘ e) = γ) (i' : Fin N) :
    γ.map (fun φ => φ i') = γ.map (fun φ => φ (e i')) := by
  have hf : Measurable (fun s : Fin N → α => s ∘ e) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  conv_lhs => rw [← hγ]
  rw [Measure.map_map (measurable_pi_apply i') hf]
  rfl

theorem iotaN_mem {n : ℕ} (γ₁ : Measure (ProgN T X G n)) : iotaN γ₁ ∈ StratModSet γ₁ := by
  refine ⟨fun t => Kernel.deterministic (fun φ => φ t) (measurable_pi_apply t),
    fun t => inferInstance, ?_⟩
  have h1 : ∀ φ : ProgN T X G n, (Measure.pi fun t =>
      Kernel.deterministic (fun φ : ProgN T X G n => φ t) (measurable_pi_apply t) φ).map
        (fun ψ => (φ, ψ)) = Measure.dirac (φ, φ) := by
    intro φ
    simp only [Kernel.deterministic_apply]
    rw [← Measure.infinitePi_eq_pi, Measure.infinitePi_dirac,
      Measure.map_dirac' (f := fun ψ => (φ, ψ)) (by fun_prop)]
  simp only [h1]
  rw [Measure.bind_dirac_eq_map (f := fun φ => (φ, φ)) _ (by fun_prop)]
  rfl

end Gamma

end ProgCorrMFG.Approx.Red62

open MeasureTheory ProbabilityTheory unitInterval Filter Topology ProgCorrMFG.Approx
  ProgCorrMFG.Approx.Red62

theorem solution {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap) :
    ∃ ε : ℕ → ℝ, (∀ N, 0 ≤ ε N) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ N, 2 ≤ N → IsEpsCorrEq M N (ε N) (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N))
        (Measure.pi fun _ : Fin N => m₀) := by
  classical
  obtain ⟨B, hB0, hfB, hFB⟩ := A3_bound M hA3
  haveI : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hΓprob : ∀ N, IsProbabilityMeasure (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N)) := by
    intro N
    haveI := gammaN_prob (ρ.map Prod.snd) ρ₁ N
    exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hΓinv : ∀ N (e : Equiv.Perm (Fin N)),
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N)).map (fun s => s ∘ e) =
        liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N) :=
    fun N e => liftSugg_perm _ e (gammaN_perm _ _ N e)
  have hminv : ∀ N (e : Equiv.Perm (Fin N)),
      (Measure.pi fun _ : Fin N => m₀).map (fun x => x ∘ e) = Measure.pi fun _ : Fin N => m₀ :=
    fun N e => pi_comp_perm m₀ e
  -- the set of all gains from deviating
  let S : ℕ → Set ℝ := fun N => {r | ∃ (i : Fin N)
    (γ' : Measure (ProgN T X G (N - 1) × ProgN T X G (N - 1)))
    (_ : γ' ∈ StratModSet ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N)).map (fun φ => φ i)))
    (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
    (R₀ : NRealization M N i (Measure.pi fun _ : Fin N => m₀)
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N))
      (iotaN ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N)).map (fun φ => φ i))) P₀)
    (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
    (R₁ : NRealization M N i (Measure.pi fun _ : Fin N => m₀)
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N)) γ' P₁), r = R₀.cost - R₁.cost}
  have hbdd : ∀ N, ∀ r ∈ S N, |r| ≤ 2 * ((T + 1) * B) := by
    rintro N r ⟨i, γ', _, Ω₀, _, P₀, _, R₀, Ω₁, _, P₁, _, R₁, rfl⟩
    have h0 := ProgCorrMFG.Approx.Red62.NRealization.cost_abs_le R₀ B hfB hFB
    have h1 := ProgCorrMFG.Approx.Red62.NRealization.cost_abs_le R₁ B hfB hFB
    rw [abs_le] at h0 h1 ⊢
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have hBdd : ∀ N, BddAbove (S N) := fun N =>
    ⟨2 * ((T + 1) * B), fun r hr => (le_abs_self r).trans (hbdd N r hr)⟩
  refine ⟨fun N => max 0 (sSup (S N)), fun N => le_max_left _ _, ?_, ?_⟩
  swap
  · intro N _ i γ' hγ' Ω₀ _ P₀ _ R₀ Ω₁ _ P₁ _ R₁
    have hmem : R₀.cost - R₁.cost ∈ S N :=
      ⟨i, γ', hγ', Ω₀, inferInstance, P₀, inferInstance, R₀, Ω₁, inferInstance, P₁, inferInstance, R₁, rfl⟩
    have h1 := le_csSup (hBdd N) hmem
    have h2 := le_max_right 0 (sSup (S N))
    linarith
  -- convergence
  have hne : ∀ n, (S (n + 2)).Nonempty := by
    intro n
    haveI := hΓprob (n + 2)
    obtain ⟨Ω, _, P, _, ⟨R⟩⟩ := exists_NReal M hΨ (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2)))
    exact ⟨0, 0, _, iotaN_mem _, Ω, inferInstance, P, inferInstance, R, Ω, inferInstance, P,
      inferInstance, R, by ring⟩
  have hpick : ∀ n : ℕ, ∃ (γ' : Measure (ProgN T X G (n + 2 - 1) × ProgN T X G (n + 2 - 1)))
      (_ : γ' ∈ StratModSet ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))).map (fun φ => φ 0)))
      (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (R₀ : NRealization M (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
        (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2)))
        (iotaN ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))).map (fun φ => φ 0))) P₀)
      (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (R₁ : NRealization M (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
        (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))) γ' P₁),
      sSup (S (n + 2)) - 1 / ((n : ℝ) + 1) < R₀.cost - R₁.cost := by
    intro n
    haveI := hΓprob (n + 2)
    obtain ⟨r, ⟨i, γ', hγ', Ω₀, _, P₀, _, R₀, Ω₁, _, P₁, _, R₁, rfl⟩, hr⟩ :=
      exists_lt_of_lt_csSup (hne n) (show sSup (S (n + 2)) - 1 / ((n : ℝ) + 1) < sSup (S (n + 2)) by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
    let e : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 i
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    have hmarg := marg_eq _ e (hΓinv (n + 2) e) 0
    rw [he] at hmarg
    obtain ⟨R₀', hc₀⟩ := transfer M (n + 2) e i 0 he _ _ (hΓinv (n + 2) e) (hminv (n + 2) e)
      _ (iotaN ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))).map (fun φ => φ 0)))
      (by rw [hmarg]) P₀ R₀
    obtain ⟨R₁', hc₁⟩ := transfer M (n + 2) e i 0 he _ _ (hΓinv (n + 2) e) (hminv (n + 2) e)
      _ γ' rfl P₁ R₁
    refine ⟨γ', by rw [hmarg]; exact hγ', Ω₀, inferInstance, P₀, inferInstance, R₀', Ω₁,
      inferInstance, P₁, inferInstance, R₁', ?_⟩
    rw [hc₀, hc₁]
    exact hr
  choose γ' hγ' Ω₀ inst₀ P₀ hP₀ R₀ Ω₁ inst₁ P₁ hP₁ R₁ hgap using hpick
  obtain ⟨Ωl, _, Pl, _, ⟨Rl⟩⟩ := exists_MFGReal M hΨ m₀ ρ
  have h62 := eq_6_2 M hΨ hA1 hA2 hA3 m₀ ρ hsol hR1 hR2 ρ₁ hρ₁ Ω₀ P₀ R₀ Ωl Pl Rl
  have h63 := eq_6_3 M hΨ hA1 hA2 hA3 m₀ ρ hsol hR1 hR2 ρ₁ hρ₁ γ' hγ' Ω₁ P₁ R₁ Ωl Pl Rl
  rw [← tendsto_add_atTop_iff_nat 2]
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h62) (δ / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (h63 (δ / 4) (by positivity))
  obtain ⟨N₃, hN₃⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ / 4 by positivity)
  refine ⟨max N₁ (max N₂ N₃), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have a1 := hN₁ n hn1
  have a2 := hN₂ n hn2
  have a3 := hgap n
  have a4 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₃ : ℝ) + 1) :=
    Nat.one_div_le_one_div hn3
  rw [Real.dist_eq] at a1
  rw [abs_lt] at a1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
  apply max_lt hδ
  linarith [a1.1, a1.2]
