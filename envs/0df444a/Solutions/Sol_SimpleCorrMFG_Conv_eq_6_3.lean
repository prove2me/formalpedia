-- Prove2me | solution 1 for SimpleCorrMFG.Conv.eq_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:11:03.388401+00:00
-- url     : https://prove2.me/submissions/d6e2943d-d769-41d4-b90d-18a42b0847cc

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

lemma measurable_iterFin_go {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {T : ℕ} (s₀ : Ω → C) (hs₀ : Measurable s₀)
    (step : Ω → Fin T → C → C) (hstep : ∀ t c, Measurable (fun ω => step ω t c)) :
    ∀ k : ℕ, Measurable (fun ω => iterFin.go (s₀ ω) (step ω) k) := by
  intro k
  induction k with
  | zero => simpa [iterFin.go] using hs₀
  | succ k ih =>
    by_cases hk : k < T
    · simp only [iterFin.go, dif_pos hk]
      have : Measurable (fun p : Ω × C => step p.1 ⟨k, hk⟩ p.2) :=
        measurable_from_prod_countable_left (fun c => hstep _ c)
      exact this.comp (measurable_id.prodMk ih)
    · simpa [iterFin.go, dif_neg hk] using ih

lemma measurable_iterFin {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {T : ℕ} (s₀ : Ω → C) (hs₀ : Measurable s₀)
    (step : Ω → Fin T → C → C) (hstep : ∀ t c, Measurable (fun ω => step ω t c)) (t : Fin (T + 1)) :
    Measurable (fun ω => iterFin (s₀ ω) (step ω) t) :=
  measurable_iterFin_go s₀ hs₀ step hstep t.val

section
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma measurable_Ψ_app (M : Model T X Γ) (hM : M.Standing) {Ω : Type} [MeasurableSpace Ω]
    (t : Fin T) (x : X) (m : Meas X) (a : Ω → Γ) (ha : Measurable a) (z : Ω → I) (hz : Measurable z) :
    Measurable (fun ω => M.Ψ t x m (a ω) (z ω)) :=
  (hM.1 t).comp (measurable_const.prodMk (measurable_const.prodMk (ha.prodMk hz)))

lemma measurable_hatPath (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => hatPath M ω t) := by
  unfold hatPath
  refine measurable_iterFin (fun ω : NOmega T N X Γ => ω.1) measurable_fst
    (fun ω t x j => M.Ψ t (x j) (empOthers x 0) (ω.2.1 j t (x j)) (ω.2.2 t j)) (fun s x => ?_) t
  refine measurable_pi_lambda _ (fun j => ?_)
  refine measurable_Ψ_app M hM s _ _ _ ?_ _ ?_
  · fun_prop
  · fun_prop

lemma measurable_nPath (M : Model T X Γ) (hM : M.Standing) {N : ℕ} (i : Fin N)
    (u : Strat T X Γ → Strat T X Γ) (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => nPath M i u ω t) := by
  unfold nPath
  refine measurable_iterFin (fun ω : NOmega T N X Γ => ω.1) measurable_fst
    (fun ω t x j => M.Ψ t (x j) (empOthers x j) (played i u ω.2.1 j t (x j)) (ω.2.2 t j)) (fun s x => ?_) t
  refine measurable_pi_lambda _ (fun j => ?_)
  refine measurable_Ψ_app M hM s _ _ _ ?_ _ ?_
  · unfold played
    by_cases h : j = i
    · simp only [h, if_true]
      have : Measurable (fun φ : Strat T X Γ => u φ s (x i)) := measurable_of_countable _
      exact this.comp (by fun_prop)
    · simp only [h, if_false]; fun_prop
  · fun_prop

lemma empOn_apply' {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S : Finset ι) (hS : S.Nonempty) (x : ι → X) (y : X) :
    (empOn S x).1 y = (1 / (S.card : ℝ)) * ∑ j ∈ S, (if x j = y then (1 : ℝ) else 0) := by
  rw [empOn, dif_pos hS]
  show (∑ j ∈ S, if x j = y then (1:ℝ) else 0) / (S.card : ℝ) = _
  ring

lemma distTV_empOn_le {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S : Finset ι) (hS : S.Nonempty) (x x' : ι → X) :
    distTV (empOn S x) (empOn S x') ≤
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i ≠ x' i then (1 : ℝ) else 0) := by
  unfold distTV
  show (1 / 2 : ℝ) * ∑ y, |(empOn S x).1 y - (empOn S x').1 y| ≤ _
  simp_rw [empOn_apply' S hS]
  have hNpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have key : ∀ y : X, |(1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i = y then (1 : ℝ) else 0) -
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x' i = y then (1 : ℝ) else 0)| ≤
      (1 / (S.card : ℝ)) * ∑ i ∈ S, |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)| := by
    intro y
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have key2 : ∀ i : ι, ∑ y : X, |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)|
      = 2 * (if x i ≠ x' i then (1 : ℝ) else 0) := by
    intro i
    by_cases h : x i = x' i
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (x i)),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ (x' i)⟩)]
      rw [Finset.sum_eq_zero]
      · simp [h, Ne.symm h]; norm_num
      · intro y hy
        have h1 : y ≠ x' i := (Finset.mem_erase.mp hy).1
        have h2 : y ≠ x i := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        simp [Ne.symm h1, Ne.symm h2]
  calc (1 / 2 : ℝ) * ∑ y, |(1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i = y then (1 : ℝ) else 0) -
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x' i = y then (1 : ℝ) else 0)|
      ≤ (1 / 2 : ℝ) * ∑ y : X, (1 / (S.card : ℝ)) * ∑ i ∈ S,
          |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)| := by
        gcongr with y; exact key y
    _ = (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i ≠ x' i then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [key2]
        rw [← Finset.mul_sum]; ring

/-- Relabelling: `empOn` over `S` of `x ∘ e` equals `empOn` over `S'` of `x` when `e` maps `S` onto `S'`. -/
lemma empOn_comp_equiv {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S S' : Finset ι) (e : ι ≃ ι) (he : ∀ i, i ∈ S ↔ e i ∈ S') (x : ι → X) :
    empOn S (x ∘ e) = empOn S' x := by
  have hsum : ∀ g : ι → ℝ, ∑ j ∈ S, g (e j) = ∑ j ∈ S', g j := fun g =>
    Finset.sum_equiv e he (fun _ _ => rfl)
  have hcard : S.card = S'.card := Finset.card_equiv e he
  by_cases hS : S.Nonempty
  · have hS' : S'.Nonempty := by
      obtain ⟨i, hi⟩ := hS; exact ⟨e i, (he i).1 hi⟩
    apply Subtype.ext; funext y
    show (empOn S (x ∘ e)).1 y = (empOn S' x).1 y
    rw [empOn_apply' S hS, empOn_apply' S' hS', hcard]
    congr 1
    exact hsum (fun j => if x j = y then (1:ℝ) else 0)
  · have hS' : ¬ S'.Nonempty := by
      rintro ⟨i, hi⟩; exact hS ⟨e.symm i, (he _).2 (by simpa using hi)⟩
    simp only [empOn, dif_neg hS, dif_neg hS']

lemma pointwise_6_3 {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (xh xt : Fin N → X) (j : Fin N) :
    distTV (empOthers xh 0) (empOthers xt j) ≤
      1 / ((N - 1 : ℕ) : ℝ) + (1 / ((N - 1 : ℕ) : ℝ)) *
        ∑ l ∈ Finset.univ.erase (0 : Fin N), (if xh l ≠ xt l then (1 : ℝ) else 0) := by
  set S := (Finset.univ.erase (0 : Fin N)) with hSdef
  have hcard : S.card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hS : S.Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hc : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
  have hsum_nn : 0 ≤ ∑ l ∈ S, (if xh l ≠ xt l then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  -- rewrite `empOthers xt j` as an empirical measure over `S` of a relabelled vector
  have hrel : empOthers xt j = empOn S (xt ∘ Equiv.swap 0 j) := by
    rw [empOn_comp_equiv S (Finset.univ.erase j) (Equiv.swap 0 j)]
    intro i
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
    constructor
    · intro hi h; apply hi
      have := congrArg (Equiv.swap 0 j) h
      simpa using this
    · intro hi h; apply hi; rw [h]; simp
  rw [hrel]
  refine (distTV_empOn_le S hS xh _).trans ?_
  rw [hcard]
  -- compare the mismatch counts
  have hcmp : ∑ l ∈ S, (if xh l ≠ (xt ∘ Equiv.swap 0 j) l then (1 : ℝ) else 0) ≤
      1 + ∑ l ∈ S, (if xh l ≠ xt l then (1 : ℝ) else 0) := by
    by_cases hj : j ∈ S
    · rw [← Finset.add_sum_erase S _ hj, ← Finset.add_sum_erase S (fun l => if xh l ≠ xt l then (1:ℝ) else 0) hj]
      have hrest : ∑ l ∈ S.erase j, (if xh l ≠ (xt ∘ Equiv.swap 0 j) l then (1 : ℝ) else 0) =
          ∑ l ∈ S.erase j, (if xh l ≠ xt l then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro l hl
        have hl1 : l ≠ j := (Finset.mem_erase.mp hl).1
        have hl0 : l ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hl0 hl1]
      rw [hrest]
      have h1 : (if xh j ≠ (xt ∘ Equiv.swap 0 j) j then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ (if xh j ≠ xt j then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      linarith
    · have hj0 : j = 0 := by
        by_contra h; exact hj (by simp [hSdef, h])
      subst hj0
      simp only [Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
      linarith
  calc (1 / ((N - 1 : ℕ) : ℝ)) * ∑ l ∈ S, (if xh l ≠ (xt ∘ Equiv.swap 0 j) l then (1 : ℝ) else 0)
      ≤ (1 / ((N - 1 : ℕ) : ℝ)) * (1 + ∑ l ∈ S, (if xh l ≠ xt l then (1 : ℝ) else 0)) := by
        gcongr
    _ = _ := by ring

end

theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (j : Fin N) (t : Fin (T + 1)) :
    ∫ ω, distTV (hatEmp M ω t) (tildeEmp M u ω j t) ∂(nLaw mN γ) ≤
      1 / ((N - 1 : ℕ) : ℝ) + (1 / ((N - 1 : ℕ) : ℝ)) *
        ∑ l ∈ Finset.univ.erase (0 : Fin N),
          (nLaw mN γ).real {ω | hatPath M ω t l ≠ tildePath M u ω t l} := by
  set μ := nLaw mN γ
  set c : ℝ := 1 / ((N - 1 : ℕ) : ℝ)
  set A : Fin N → Set (NOmega T N X Γ) := fun l => {ω | hatPath M ω t l ≠ tildePath M u ω t l}
  have hA : ∀ l, MeasurableSet (A l) := by
    intro l
    have h1 : Measurable (fun ω : NOmega T N X Γ => hatPath M ω t l) :=
      (measurable_pi_apply l).comp (measurable_hatPath M hM t)
    have h2 : Measurable (fun ω : NOmega T N X Γ => tildePath M u ω t l) :=
      (measurable_pi_apply l).comp (measurable_nPath M hM 0 u t)
    exact (measurableSet_eq_fun h1 h2).compl
  have hpt : ∀ ω, distTV (hatEmp M ω t) (tildeEmp M u ω j t) ≤
      c + c * ∑ l ∈ Finset.univ.erase (0 : Fin N), (A l).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    have := pointwise_6_3 hN (hatPath M ω t) (tildePath M u ω t) j
    refine this.trans (le_of_eq ?_)
    congr 2
    apply Finset.sum_congr rfl
    intro l _
    simp [A, Set.indicator_apply]
  have hint : Integrable (fun ω => c + c * ∑ l ∈ Finset.univ.erase (0 : Fin N),
      (A l).indicator (fun _ => (1 : ℝ)) ω) μ := by
    refine (integrable_const c).add (Integrable.const_mul ?_ c)
    exact integrable_finset_sum _ (fun l _ => (integrable_const (1 : ℝ)).indicator (hA l))
  have hnn : ∀ ω, 0 ≤ distTV (hatEmp M ω t) (tildeEmp M u ω j t) := by
    intro ω; unfold distTV
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  calc ∫ ω, distTV (hatEmp M ω t) (tildeEmp M u ω j t) ∂μ
      ≤ ∫ ω, (c + c * ∑ l ∈ Finset.univ.erase (0 : Fin N), (A l).indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ hnn) hint (ae_of_all _ hpt)
    _ = c + c * ∑ l ∈ Finset.univ.erase (0 : Fin N), μ.real (A l) := by
        rw [integral_add (integrable_const c) (hint.sub (integrable_const c) |>.congr
          (ae_of_all _ (fun ω => by simp))), integral_const, integral_const_mul,
          integral_finset_sum _ (fun l _ => (integrable_const (1 : ℝ)).indicator (hA l))]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        congr 2
        apply Finset.sum_congr rfl
        intro l _
        rw [integral_indicator (hA l), setIntegral_const, smul_eq_mul, mul_one]
