-- Prove2me | solution 1 for ProgCorrMFG.Approx.eq_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:18:55.982093+00:00
-- url     : https://prove2.me/submissions/8cc66e88-64ec-4cc8-b809-78b2abd818da

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx.Sol64

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

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

theorem continuous_of_lip {X : Type} [Fintype X] (h : Meas X → ℝ) (L : ℝ)
    (hL : ∀ m m', |h m - h m'| ≤ L * distTV m m') : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro m
  have hd : Continuous (fun m' : Meas X => distTV m' m) := by
    show Continuous (fun m' : Meas X => (1 / 2 : ℝ) * ∑ x, |m'.1 x - m.1 x|)
    exact continuous_const.mul (continuous_finsetSum _ fun x _ =>
      (((continuous_apply x).comp continuous_subtype_val).sub continuous_const).abs)
  have h0 : distTV m m = 0 := by simp [distTV]
  have hlim : Tendsto (fun m' => |L| * distTV m' m) (𝓝 m) (𝓝 0) := by
    have := (hd.tendsto m).const_mul |L|
    rwa [h0, mul_zero] at this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m' => ?_) hlim
  rw [Real.norm_eq_abs]
  calc |h m' - h m| ≤ L * distTV m' m := hL m' m
    _ ≤ |L| * distTV m' m := mul_le_mul_of_nonneg_right (le_abs_self L) (distTV_nonneg _ _)

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

theorem gammaN_singleton {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Fintype G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (ρ₂ : Measure (Flow T X)) (ρ₁ : Kernel (Flow T X) (Strat T X G)) (N : ℕ)
    (ψ : Fin N → Strat T X G) : gammaN ρ₂ ρ₁ N {ψ} = ∫⁻ m, ∏ j, ρ₁ m {ψ j} ∂ρ₂ := by
  unfold gammaN
  rw [Measure.sum_apply _ (measurableSet_singleton ψ)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ψ]
  · simp
  · intro b hb
    simp [hb]


theorem finite_empMeas (X : Type) [Fintype X] (n : ℕ) (hn : 1 ≤ n) : Finite (EmpMeas X n) := by
  classical
  have hle : ∀ (m : EmpMeas X n) (y : X), m.1.1 y ≤ 1 := by
    intro m y
    have h1 : ∑ x, m.1.1 x = 1 := m.1.2.2
    have := Finset.single_le_sum (f := fun x => m.1.1 x) (fun x _ => m.1.2.1 x) (Finset.mem_univ y)
    simpa [h1] using this
  let f : EmpMeas X n → (X → Fin (n + 1)) := fun m y =>
    ⟨⌊m.1.1 y * n⌋₊, by
      have h1 : m.1.1 y * n ≤ n := by
        have := hle m y
        have hn' : (0 : ℝ) ≤ n := by positivity
        nlinarith
      have : ⌊m.1.1 y * n⌋₊ ≤ n := Nat.floor_le_of_le h1
      omega⟩
  refine Finite.of_injective f ?_
  intro m m' hmm
  apply Subtype.ext; apply Subtype.ext
  funext y
  have h := congrFun hmm y
  simp only [f, Fin.mk.injEq] at h
  obtain ⟨k, hk⟩ := m.2
  obtain ⟨k', hk'⟩ := m'.2
  have e1 : m.1.1 y * n = k y := hk y
  have e2 : m'.1.1 y * n = k' y := hk' y
  rw [e1, e2, Nat.floor_natCast, Nat.floor_natCast] at h
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have : m.1.1 y * n = m'.1.1 y * n := by rw [e1, e2, h]
  exact mul_right_cancel₀ hn0 this

section Exist

variable {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]

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


noncomputable def stepN (M : Model T X G) (N : ℕ) :
    Fin T → ThetaN T X G N → (Fin (T + 1) → Fin N → X) → (Fin N → X) :=
  fun t θ p j => M.Ψ t (p t.castSucc j) (empOthers (p t.castSucc) j).1
    ((θ.2.2.2 j t).1 (fun s => p s j) (fun s => empOthers (p s) j)) (θ.1 t j)

theorem stepN_nonAnt (M : Model T X G) (N : ℕ) : NonAntStep (stepN M N) := by
  intro t θ p p' h
  funext j
  simp only [stepN]
  rw [h t.castSucc le_rfl]
  congr 2
  apply (θ.2.2.2 j t).2
  intro s hs
  rw [h s hs]
  exact ⟨rfl, rfl⟩

theorem stepN_meas (M : Model T X G) (hΨ : M.PsiMeasurable) (N : ℕ) (t : Fin T) :
    Measurable (fun q : ThetaN T X G N × (Fin (T + 1) → Fin N → X) => stepN M N t q.1 q.2) := by
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

end Exist

section Gamma

variable {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Fintype G] [MeasurableSpace G]
  [DiscreteMeasurableSpace G]

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

end Gamma

end ProgCorrMFG.Approx.Sol64

open MeasureTheory ProbabilityTheory unitInterval Filter Topology ProgCorrMFG.Approx
  ProgCorrMFG.Approx.Sol64

theorem solution {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ₂ : Measure (Flow T X)) [IsProbabilityMeasure ρ₂]
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (N : ℕ) (hN : 2 ≤ N)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : NRealization M N ⟨0, by omega⟩ (Measure.pi fun _ : Fin N => m₀)
      (liftSugg (gammaN ρ₂ ρ₁ N))
      (iotaN ((liftSugg (gammaN ρ₂ ρ₁ N)).map (fun φ => φ ⟨0, by omega⟩))) P)
    (c : Flow T X → ℝ)
    (hc : ∀ᵐ m ∂ρ₂, ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (R' : NRealization M N ⟨0, by omega⟩ (Measure.pi fun _ : Fin N => m₀)
        (liftSugg (Measure.pi fun _ : Fin N => ρ₁ m))
        (iotaN ((liftSugg (Measure.pi fun _ : Fin N => ρ₁ m)).map (fun φ => φ ⟨0, by omega⟩))) P'),
      R'.cost = c m) :
    R.cost = ∫ m, c m ∂ρ₂ := by
  classical
  haveI : Finite (EmpMeas X (N - 1)) := finite_empMeas X (N - 1) (by omega)
  haveI : ∀ t : Fin T, Countable (CompN T X G (N - 1) t) := fun t => by
    unfold CompN; infer_instance
  haveI : Countable (ProgN T X G (N - 1)) := inferInstance
  obtain ⟨B, hB0, hfB, hFB⟩ := A3_bound M hA3
  let i0 : Fin N := ⟨0, by omega⟩
  let x0 : ThetaN T X G N → (Fin N → X) := fun θ => θ.2.1
  let path := gen x0 (stepN M N)
  have hpath : Measurable path := measurable_gen _ _ (by fun_prop) (stepN_meas M hΨ N)
  let Hc : (Fin (T + 1) → Fin N → X) × ProgN T X G (N - 1) → ℝ := fun q =>
    (∑ t : Fin T, M.f t (q.1 t.castSucc i0) (empOthers (q.1 t.castSucc) i0).1
      ((q.2 t).1 (fun s => q.1 s i0) (fun s => empOthers (q.1 s) i0))) +
    M.F (q.1 (Fin.last T) i0) (empOthers (q.1 (Fin.last T)) i0).1
  have hHcb : ∀ q, |Hc q| ≤ (T + 1) * B := by
    intro q
    refine (abs_add_le _ _).trans ?_
    have h1 : |∑ t : Fin T, M.f t (q.1 t.castSucc i0) (empOthers (q.1 t.castSucc) i0).1
        ((q.2 t).1 (fun s => q.1 s i0) (fun s => empOthers (q.1 s) i0))| ≤ T * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun t _ => hfB _ _ _ _).trans ?_
      simp
    have h2 := hFB (q.1 (Fin.last T) i0) (empOthers (q.1 (Fin.last T)) i0).1
    linarith
  let KN : ThetaN T X G N → ℝ := fun θ => Hc (path θ, θ.2.2.2 i0)
  have hKN : Measurable KN := (measurable_of_countable Hc).comp (hpath.prodMk (by fun_prop))
  have hKNb : ∀ θ, |KN θ| ≤ (T + 1) * B := fun θ => hHcb _
  let A := Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)
  let C := Measure.pi fun _ : Fin T => (volume : Measure I)
  let mN := Measure.pi fun _ : Fin N => m₀
  -- law uniqueness
  have hD : MeasurableSet {q : ProgN T X G (N - 1) × ProgN T X G (N - 1) | q.1 = q.2} := by
    have : {q : ProgN T X G (N - 1) × ProgN T X G (N - 1) | q.1 = q.2} =
        ⋃ a, ({a} ×ˢ {a} : Set (ProgN T X G (N - 1) × ProgN T X G (N - 1))) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨q.2, h, rfl⟩
      · rintro ⟨a, h1, h2⟩; rw [h1, h2]
    rw [this]
    exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (measurableSet_singleton a)
  have key : ∀ (γ : Measure (Fin N → ProgN T X G (N - 1))) [IsProbabilityMeasure γ]
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (R : NRealization M N i0 mN γ (iotaN (γ.map (fun φ => φ i0))) P),
      R.cost = ∫ θ, KN θ ∂(A.prod (mN.prod (C.prod γ))) := by
    intro γ _ Ω _ P _ R
    have hdev : ∀ᵐ ω ∂P, R.dev ω = R.sugg ω i0 := by
      have hm : Measurable (fun ω => (R.sugg ω i0, R.dev ω)) :=
        ((measurable_pi_apply i0).comp R.measurable_sugg).prodMk R.measurable_dev
      have h0 : P ((fun ω => (R.sugg ω i0, R.dev ω)) ⁻¹'
          {q : ProgN T X G (N - 1) × ProgN T X G (N - 1) | q.1 = q.2}ᶜ) = 0 := by
        rw [← Measure.map_apply hm hD.compl, R.dev_law]
        unfold iotaN
        rw [Measure.map_apply (f := fun φ : ProgN T X G (N - 1) => (φ, φ)) (by fun_prop) hD.compl]
        have : (fun φ : ProgN T X G (N - 1) => (φ, φ)) ⁻¹'
            {q : ProgN T X G (N - 1) × ProgN T X G (N - 1) | q.1 = q.2}ᶜ = ∅ := by
          ext; simp
        rw [this, measure_empty]
      rw [ae_iff]
      convert h0 using 2
      ext ω
      simp [eq_comm]
    have hV : Measurable (fun ω => (R.noise ω, R.state ω 0, R.coin ω, R.sugg ω)) :=
      R.measurable_noise.prodMk (((measurable_pi_apply 0).comp R.measurable_state).prodMk
        (R.measurable_coin.prodMk R.measurable_sugg))
    rw [← R.law, integral_map hV.aemeasurable hKN.aestronglyMeasurable]
    unfold NRealization.cost
    apply integral_congr_ae
    filter_upwards [R.dynamics, hdev] with ω hω hd
    have hs : R.state ω = path (R.noise ω, R.state ω 0, R.coin ω, R.sugg ω) :=
      gen_unique x0 (stepN M N) (stepN_nonAnt M N) _ (R.state ω) rfl (fun t => by
        funext j
        rw [hω t j, hd, played_self]
        rfl)
    simp only [KN, Hc, ← hs, hd]
  -- reassociation
  let E : ((Fin T → Fin N → I) × ((Fin N → X) × (Fin T → I))) × (Fin N → ProgN T X G (N - 1)) →
      ThetaN T X G N := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
  have hE : Measurable E := by fun_prop
  let μ₁ := A.prod (mN.prod C)
  have hreassoc : ∀ (γ : Measure (Fin N → ProgN T X G (N - 1))) [IsProbabilityMeasure γ],
      A.prod (mN.prod (C.prod γ)) = (μ₁.prod γ).map E := by
    intro γ _
    have e1 : (μ₁.prod γ).map E = ((μ₁.prod γ).map MeasurableEquiv.prodAssoc).map
        (Prod.map id MeasurableEquiv.prodAssoc) := by
      rw [Measure.map_map (measurable_id.prodMap (MeasurableEquiv.measurable _))
        (MeasurableEquiv.measurable _)]
      rfl
    rw [e1, Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id
      (MeasurableEquiv.measurable _), Measure.map_id, Measure.prodAssoc_prod]
  let K' : ((Fin T → Fin N → I) × ((Fin N → X) × (Fin T → I))) × (Fin N → ProgN T X G (N - 1)) →
      ℝ := fun q => KN (E q)
  have hK' : Measurable K' := hKN.comp hE
  have hK'b : ∀ q, |K' q| ≤ (T + 1) * B := fun q => hKNb _
  have hI : ∀ (γ : Measure (Fin N → ProgN T X G (N - 1))) [IsProbabilityMeasure γ],
      ∫ θ, KN θ ∂(A.prod (mN.prod (C.prod γ))) = ∫ y, ∫ s, K' (y, s) ∂γ ∂μ₁ := by
    intro γ _
    rw [hreassoc γ, integral_map hE.aemeasurable hKN.aestronglyMeasurable]
    exact integral_prod K' (Integrable.of_bound hK'.aestronglyMeasurable ((T + 1) * B)
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hK'b q))
  let Lf : (Fin N → Strat T X G) → (Fin N → ProgN T X G (N - 1)) := fun ψ j => embN (ψ j)
  have hL : Measurable Lf := measurable_of_countable _
  let h : ((Fin T → Fin N → I) × ((Fin N → X) × (Fin T → I))) → Flow T X → ℝ := fun y m =>
    ∑ ψ : Fin N → Strat T X G, (∏ j, (ρ₁ m {ψ j}).toReal) * K' (y, Lf ψ)
  have hh : Measurable (Function.uncurry h) := by
    apply Finset.measurable_sum
    intro ψ _
    refine (Finset.measurable_prod _ fun j _ =>
      ((Kernel.measurable_coe ρ₁ (measurableSet_singleton _)).ennreal_toReal.comp
        measurable_snd)).mul ?_
    exact hK'.comp (measurable_fst.prodMk measurable_const)
  have hhb : ∀ y m, |h y m| ≤ (Fintype.card (Fin N → Strat T X G) : ℝ) * ((T + 1) * B) := by
    intro y m
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ ψ ∈ (Finset.univ : Finset (Fin N → Strat T X G)),
        |(∏ j, (ρ₁ m {ψ j}).toReal) * K' (y, Lf ψ)| ≤ (T + 1) * B := by
      intro ψ _
      rw [abs_mul]
      have h1 : |∏ j, (ρ₁ m {ψ j}).toReal| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => ENNReal.toReal_nonneg)]
        exact Finset.prod_le_one (fun j _ => ENNReal.toReal_nonneg)
          (fun j _ => measureReal_le_one (μ := ρ₁ m))
      calc |∏ j, (ρ₁ m {ψ j}).toReal| * |K' (y, Lf ψ)| ≤ 1 * ((T + 1) * B) :=
            mul_le_mul h1 (hK'b _) (abs_nonneg _) zero_le_one
        _ = (T + 1) * B := one_mul _
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hKs : ∀ y, Measurable (fun s => K' (y, s)) := fun y =>
    hK'.comp (measurable_const.prodMk measurable_id)
  -- the conditional N-player game
  have claim1 : ∀ y m, ∫ s, K' (y, s) ∂(liftSugg (Measure.pi fun _ : Fin N => ρ₁ m)) = h y m := by
    intro y m
    unfold liftSugg
    rw [integral_map hL.aemeasurable (hKs y).aestronglyMeasurable,
      integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [smul_eq_mul, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  have claim2 : ∀ y, ∫ s, K' (y, s) ∂(liftSugg (gammaN ρ₂ ρ₁ N)) = ∫ m, h y m ∂ρ₂ := by
    intro y
    haveI := gammaN_prob ρ₂ ρ₁ N
    unfold liftSugg
    rw [integral_map hL.aemeasurable (hKs y).aestronglyMeasurable,
      integral_fintype Integrable.of_finite]
    simp only [h]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [integral_mul_const, smul_eq_mul, measureReal_def, gammaN_singleton]
      congr 1
      have hm : Measurable (fun m => ∏ j, ρ₁ m {ψ j}) :=
        Finset.measurable_prod _ fun j _ => Kernel.measurable_coe ρ₁ (measurableSet_singleton _)
      rw [← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall fun m =>
        ENNReal.prod_lt_top fun j _ => measure_lt_top _ _)]
      congr 1
      funext m
      rw [ENNReal.toReal_prod]
    · intro ψ _
      refine Integrable.of_bound ((Finset.measurable_prod _ fun j _ =>
        (Kernel.measurable_coe ρ₁ (measurableSet_singleton _)).ennreal_toReal).mul
          measurable_const).aestronglyMeasurable (1 * |K' (y, Lf ψ)|)
        (Filter.Eventually.of_forall fun m => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => ENNReal.toReal_nonneg)]
      exact Finset.prod_le_one (fun j _ => ENNReal.toReal_nonneg)
        (fun j _ => measureReal_le_one (μ := ρ₁ m))
  have hhint : Integrable (Function.uncurry h) (μ₁.prod ρ₂) :=
    Integrable.of_bound hh.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hhb q.1 q.2)
  haveI := gammaN_prob ρ₂ ρ₁ N
  haveI : IsProbabilityMeasure (liftSugg (gammaN ρ₂ ρ₁ N)) :=
    Measure.isProbabilityMeasure_map hL.aemeasurable
  rw [key _ P R, hI]
  simp_rw [claim2]
  rw [integral_integral_swap hhint]
  apply integral_congr_ae
  filter_upwards [hc] with m hm
  haveI : IsProbabilityMeasure (liftSugg (Measure.pi fun _ : Fin N => ρ₁ m)) :=
    Measure.isProbabilityMeasure_map hL.aemeasurable
  obtain ⟨Ω', _, P', _, ⟨R'⟩⟩ := exists_NReal M hΨ N i0 mN
    (liftSugg (Measure.pi fun _ : Fin N => ρ₁ m))
  rw [← hm Ω' P' R', key _ P' R', hI]
  simp_rw [claim1]
