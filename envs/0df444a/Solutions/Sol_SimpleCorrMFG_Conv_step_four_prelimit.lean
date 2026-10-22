-- Prove2me | solution 1 for SimpleCorrMFG.Conv.step_four_prelimit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:15:45.00146+00:00
-- url     : https://prove2.me/submissions/e3693b6c-26b9-4770-b482-fdf748dca6e4

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

lemma measurable_hatPath_unused (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (t : Fin (T + 1)) :
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


lemma pi_map_comp_perm {ι α : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (e : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => μ).map (fun x => x ∘ e) = Measure.pi fun _ : ι => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (show Measurable (fun x : ι → α => x ∘ e) from
    measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))) (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → α => x ∘ e) ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => s (e.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h i; simpa using h (e.symm i)
    · intro h i; simpa using h (e i)
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp e.symm (fun i => μ (s i))

section
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- Relabel the players of a sample point by the permutation `e`. -/
def permΩ {N : ℕ} (e : Equiv.Perm (Fin N)) (ω : NOmega T N X Γ) : NOmega T N X Γ :=
  (ω.1 ∘ e, ω.2.1 ∘ e, fun t => ω.2.2 t ∘ e)

lemma measurable_permΩ {N : ℕ} (e : Equiv.Perm (Fin N)) :
    Measurable (permΩ (T := T) (X := X) (Γ := Γ) e) := by
  unfold permΩ
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp measurable_fst
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp
      (measurable_fst.comp measurable_snd)
  · exact measurable_pi_lambda _ (fun t => measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply (e i)).comp ((measurable_pi_apply t).comp
        (measurable_snd.comp measurable_snd))))

lemma nLaw_map_permΩ {N : ℕ} (m : Meas X) (γ : ProbabilityMeasure (Fin N → Strat T X Γ))
    (hγ : IsSymmetric γ) (e : Equiv.Perm (Fin N)) :
    (nLaw (prodInit N m) γ).map (permΩ e) = nLaw (prodInit N m) γ := by
  have hpe : ∀ {β : Type} [MeasurableSpace β], Measurable (fun x : Fin N → β => x ∘ e) :=
    fun {β} _ => measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  have hnoise : Measurable (fun ξ : Fin T → Fin N → I => fun t => ξ t ∘ e) :=
    measurable_pi_lambda _ (fun t => hpe.comp (measurable_pi_apply t))
  have h1 : ((prodInit N m : ProbabilityMeasure (Fin N → X)) : Measure (Fin N → X)).map
      (fun x => x ∘ e) = (prodInit N m : Measure (Fin N → X)) := by
    simp only [prodInit, ProbabilityMeasure.coe_mk]
    exact pi_map_comp_perm _ e
  have h2 : (γ : Measure (Fin N → Strat T X Γ)).map (fun φ => φ ∘ e) = γ := hγ e
  have h3 : (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).map
      (fun ξ t => ξ t ∘ e) = Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I) := by
    rw [Measure.pi_map_pi (fun _ => hpe.aemeasurable)]
    simp_rw [pi_map_comp_perm]
  unfold nLaw
  have : permΩ (T := T) (X := X) (Γ := Γ) e =
      Prod.map (fun x : Fin N → X => x ∘ e) (Prod.map (fun φ : Fin N → Strat T X Γ => φ ∘ e)
        (fun ξ : Fin T → Fin N → I => fun t => ξ t ∘ e)) := rfl
  rw [this, ← Measure.map_prod_map _ _ hpe (hpe.prodMap hnoise), ← Measure.map_prod_map _ _ hpe hnoise,
    h1, h2, h3]

lemma played_zero_id {N : ℕ} [NeZero N] (φ : Fin N → Strat T X Γ) (j : Fin N) :
    played 0 id φ j = φ j := by
  unfold played; split_ifs <;> rfl

lemma empOthers_comp_perm {N : ℕ} (x : Fin N → X) (e : Equiv.Perm (Fin N)) (j : Fin N) :
    empOthers (x ∘ e) j = empOthers x (e j) := by
  unfold empOthers
  apply empOn_comp_equiv
  intro i; simp

lemma nPath_permΩ (M : Model T X Γ) {N : ℕ} [NeZero N] (e : Equiv.Perm (Fin N))
    (ω : NOmega T N X Γ) (t : Fin (T + 1)) :
    nPath M 0 id (permΩ e ω) t = nPath M 0 id ω t ∘ e := by
  unfold nPath iterFin
  generalize t.val = k
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < T
    · simp only [iterFin.go, dif_pos hk]
      rw [ih]
      funext j
      simp only [Function.comp_apply, played_zero_id, empOthers_comp_perm]
      rfl
    · simp only [iterFin.go, dif_neg hk]
      exact ih

end

theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (hγ : IsSymmetric γ)
    (t : Fin (T + 1)) (x : X) (B : Set (Flow T X)) (hB : MeasurableSet B) :
    (nLaw (prodInit N m) γ).real
        {ω | nPath M 0 id ω t 0 = x ∧ (fun s => empOn Finset.univ (nPath M 0 id ω s)) ∈ B} =
      ∫ ω, B.indicator (fun μ : Flow T X => ((μ t : Meas X) : X → ℝ) x)
        (fun s => empOn Finset.univ (nPath M 0 id ω s)) ∂(nLaw (prodInit N m) γ) := by
  set P := nLaw (prodInit N m) γ
  set μf : NOmega T N X Γ → Flow T X := fun ω s => empOn Finset.univ (nPath M 0 id ω s) with hμf
  set E : Fin N → Set (NOmega T N X Γ) := fun i => {ω | nPath M 0 id ω t i = x ∧ μf ω ∈ B} with hE
  have hpaths : Measurable (fun ω : NOmega T N X Γ => fun s => nPath M 0 id ω s) :=
    measurable_pi_lambda _ (fun s => measurable_nPath M hM 0 id s)
  have hμfm : Measurable μf :=
    (measurable_of_countable (fun p : Fin (T + 1) → Fin N → X => fun s => empOn Finset.univ (p s))).comp hpaths
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    refine MeasurableSet.inter ?_ (hμfm hB)
    exact (measurable_pi_apply i).comp (measurable_nPath M hM 0 id t) (measurableSet_singleton x)
  -- invariance: every player has the same probability
  have hEq : ∀ i, P.real (E i) = P.real (E 0) := by
    intro i
    have hpre : permΩ (Equiv.swap 0 i) ⁻¹' (E 0) = E i := by
      ext ω
      simp only [hE, Set.mem_preimage, Set.mem_setOf_eq, hμf, nPath_permΩ, Function.comp_apply,
        Equiv.swap_apply_left]
      have : ∀ s, empOn Finset.univ (nPath M 0 id ω s ∘ Equiv.swap 0 i) =
          empOn Finset.univ (nPath M 0 id ω s) := fun s =>
        empOn_comp_equiv _ _ _ (by simp) _
      simp only [this]
    rw [← hpre, measureReal_def, measureReal_def, ← Measure.map_apply (measurable_permΩ _) (hEm 0),
      nLaw_map_permΩ m γ hγ]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨0⟩
  -- pointwise identity for the right-hand side
  have hrhs : ∀ ω, B.indicator (fun μ : Flow T X => ((μ t : Meas X) : X → ℝ) x) (μf ω) =
      (1 / (N : ℝ)) * ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : μf ω ∈ B
    · rw [Set.indicator_of_mem hω]
      show (empOn Finset.univ (nPath M 0 id ω t)).1 x = _
      rw [empOn_apply' _ hne, Finset.card_univ, Fintype.card_fin]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : nPath M 0 id ω t i = x
      · rw [if_pos hi, Set.indicator_of_mem (show ω ∈ E i from ⟨hi, hω⟩)]
      · rw [if_neg hi, Set.indicator_of_notMem (show ω ∉ E i from fun h => hi h.1)]
    · rw [Set.indicator_of_notMem hω]
      symm
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun h => hω h.2) _
  show P.real (E 0) = ∫ ω, B.indicator (fun μ : Flow T X => ((μ t : Meas X) : X → ℝ) x) (μf ω) ∂P
  rw [integral_congr_ae (ae_of_all _ hrhs)]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => (integrable_const (1 : ℝ)).indicator (hEm i))]
  have hI : ∀ i, ∫ ω, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P = P.real (E 0) := by
    intro i
    rw [integral_indicator (hEm i), setIntegral_const, smul_eq_mul, mul_one, hEq]
  simp_rw [hI]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
