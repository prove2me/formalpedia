-- Prove2me | solution 1 for PalmQueueing.Loynes.maximal_solution
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:27:07.88622+00:00
-- url     : https://prove2.me/submissions/ad711e7d-5601-40f6-85a2-c4d8212b25d0

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_MultiserverQueue

open MeasureTheory Filter Topology PalmQueueing.Loynes

namespace LoynesMaximalProof

section OrderAndKWStep

lemma order_monotone_coords {s : ℕ} (v : Fin s → ℝ) : Monotone (order v) :=
  Tuple.monotone_sort v

lemma order_nonneg {s : ℕ} {v : Fin s → ℝ} (hv : ∀ j, 0 ≤ v j) : ∀ j, 0 ≤ order v j :=
  fun j => hv (Tuple.sort v j)

lemma sum_order {s : ℕ} (v : Fin s → ℝ) : ∑ j : Fin s, order v j = ∑ j : Fin s, v j :=
  Equiv.sum_comp (Tuple.sort v) v

lemma order_mono {s : ℕ} {u v : Fin s → ℝ} (h : ∀ j, u j ≤ v j) :
    ∀ j, order u j ≤ order v j := by
  intro j
  by_contra hlt
  push Not at hlt
  set c := order v j
  have hu_ge : ∀ i : Fin s, j ≤ i → c < order u i :=
    fun i hi => lt_of_lt_of_le hlt (order_monotone_coords u hi)
  have hcard_u : (Finset.univ.filter (fun i : Fin s => j ≤ i)).card ≤
      (Finset.univ.filter (fun i : Fin s => c < order u i)).card :=
    Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hu_ge i hi)
  have hperm_u : (Finset.univ.filter (fun i : Fin s => c < order u i)).card =
      (Finset.univ.filter (fun i : Fin s => c < u i)).card := by
    apply Finset.card_bij (fun i _ => Tuple.sort u i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    · intro i₁ _ i₂ _ hEq
      exact (Tuple.sort u).injective hEq
    · intro i hi
      refine ⟨(Tuple.sort u).symm i, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simpa [order] using hi
  have hsub_uv : (Finset.univ.filter (fun i : Fin s => c < u i)).card ≤
      (Finset.univ.filter (fun i : Fin s => c < v i)).card :=
    Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_lt_of_le hi (h i))
  have hperm_v : (Finset.univ.filter (fun i : Fin s => c < v i)).card =
      (Finset.univ.filter (fun i : Fin s => c < order v i)).card := by
    apply Finset.card_bij (fun i _ => (Tuple.sort v).symm i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simpa [order] using hi
    · intro i₁ _ i₂ _ hEq
      exact (Tuple.sort v).symm.injective hEq
    · intro i hi
      refine ⟨Tuple.sort v i, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
  have hv_le : (Finset.univ.filter (fun i : Fin s => c < order v i)).card ≤
      (Finset.univ.filter (fun i : Fin s => j < i)).card :=
    Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hle
      push Not at hle
      exact not_lt_of_ge (order_monotone_coords v hle) hi)
  have hlt_card : (Finset.univ.filter (fun i : Fin s => j < i)).card <
      (Finset.univ.filter (fun i : Fin s => j ≤ i)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact le_of_lt hi,
       fun hEq => by
        have : j ∈ Finset.univ.filter (fun i : Fin s => j < i) := by
          rw [hEq]; simp
        simp at this⟩)
  omega

lemma eq_of_monotone_perm {s : ℕ} {u v : Fin s → ℝ} (hu : Monotone u) (hv : Monotone v)
    (σ : Equiv.Perm (Fin s)) (hσ : ∀ j, u j = v (σ j)) : u = v := by
  funext j
  have hle : ∀ u v : Fin s → ℝ, Monotone u → Monotone v →
      (∃ σ : Equiv.Perm (Fin s), ∀ j, u j = v (σ j)) → ∀ j, u j ≤ v j := by
    intro u v hu hv ⟨σ, hσ⟩ j
    by_contra hlt
    push Not at hlt
    set c := v j
    have hu_ge : (Finset.univ.filter (fun i : Fin s => j ≤ i)).card ≤
        (Finset.univ.filter (fun i : Fin s => c < u i)).card :=
      Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact lt_of_lt_of_le hlt (hu hi))
    have hperm : (Finset.univ.filter (fun i : Fin s => c < u i)).card =
        (Finset.univ.filter (fun i : Fin s => c < v i)).card := by
      apply Finset.card_bij (fun i _ => σ i)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rwa [← hσ i]
      · intro i₁ _ i₂ _ hEq; exact σ.injective hEq
      · intro i hi
        refine ⟨σ.symm i, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [hσ]; simpa using hi
    have hv_le : (Finset.univ.filter (fun i : Fin s => c < v i)).card ≤
        (Finset.univ.filter (fun i : Fin s => j < i)).card :=
      Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra hle; push Not at hle
        exact not_lt_of_ge (hv hle) hi)
    have hlt_card : (Finset.univ.filter (fun i : Fin s => j < i)).card <
        (Finset.univ.filter (fun i : Fin s => j ≤ i)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact le_of_lt hi,
         fun hEq => by
          have : j ∈ Finset.univ.filter (fun i : Fin s => j < i) := by rw [hEq]; simp
          simp at this⟩)
    omega
  exact le_antisymm (hle u v hu hv ⟨σ, hσ⟩ j)
    (hle v u hv hu ⟨σ.symm, fun i => by rw [hσ]; simp⟩ j)

lemma order_of_monotone {s : ℕ} {v : Fin s → ℝ} (hv : Monotone v) : order v = v :=
  eq_of_monotone_perm (order_monotone_coords v) hv (Tuple.sort v) (fun _ => rfl)

lemma order_add_const {s : ℕ} (v : Fin s → ℝ) (c : ℝ) :
    order (fun j => v j + c) = fun j => order v j + c := by
  exact eq_of_monotone_perm (order_monotone_coords _)
    (fun i j hij => add_le_add_left (order_monotone_coords v hij) c)
    ((Tuple.sort (fun j => v j + c)).trans (Tuple.sort v).symm)
    (fun j => by simp [order])

lemma lipschitz_order {s : ℕ} : LipschitzWith 1 (order : (Fin s → ℝ) → (Fin s → ℝ)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  simp only [NNReal.coe_one, one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  have h1 : ∀ i, v i + (-dist u v) ≤ u i := fun i => by
    have := dist_le_pi_dist u v i
    rw [Real.dist_eq, abs_sub_le_iff] at this
    linarith
  have h2 : ∀ i, u i ≤ v i + dist u v := fun i => by
    have := dist_le_pi_dist u v i
    rw [Real.dist_eq, abs_sub_le_iff] at this
    linarith
  have ho1 := order_mono h1 j
  have ho2 := order_mono h2 j
  rw [order_add_const] at ho1 ho2
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith

lemma continuous_order {s : ℕ} : Continuous (order : (Fin s → ℝ) → (Fin s → ℝ)) :=
  lipschitz_order.continuous

lemma order_tail_sum {s : ℕ} {v : Fin s → ℝ} {k : ℕ}
    (hsep : ∀ i j : Fin s, i.1 < s - k → s - k ≤ j.1 → v i < v j) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin s => s - k ≤ j.1), order v j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin s => s - k ≤ j.1), v j := by
  set S := Finset.univ.filter (fun j : Fin s => s - k ≤ j.1)
  set σ := Tuple.sort v
  have hmaps : ∀ j ∈ S, σ j ∈ S := by
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_contra hlt
    push Not at hlt
    have hle_lt : ∀ l : Fin s, l ≤ j → (σ l).1 < s - k := by
      intro l hlj
      by_contra hge
      push Not at hge
      have h1 : v (σ j) < v (σ l) := hsep (σ j) (σ l) hlt hge
      have h2 : v (σ l) ≤ v (σ j) := order_monotone_coords v hlj
      linarith
    have hcard1 : (Finset.univ.filter (fun l : Fin s => l ≤ j)).card ≤
        (Finset.univ.filter (fun m : Fin s => m.1 < s - k)).card := by
      apply Finset.card_le_card_of_injOn (fun l => σ l)
      · intro l hl
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        exact hle_lt l hl
      · intro l₁ _ l₂ _ hEq; exact σ.injective hEq
    have hcard_le : (Finset.univ.filter (fun l : Fin s => l ≤ j)).card = j.1 + 1 := by
      have : (Finset.univ.filter (fun l : Fin s => l ≤ j)) = Finset.Iic j := by
        ext l; simp
      rw [this, Fin.card_Iic]
    have hcard_lt : (Finset.univ.filter (fun m : Fin s => m.1 < s - k)).card = s - k := by
      have hbi : (Finset.univ.filter (fun m : Fin s => m.1 < s - k)).card =
          (Finset.range (s - k)).card := by
        apply Finset.card_bij (fun m _ => m.1)
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hm ⊢
          exact hm
        · intro m₁ _ m₂ _ hEq; exact Fin.ext hEq
        · intro n hn
          rw [Finset.mem_range] at hn
          exact ⟨⟨n, by omega⟩, by simp [hn], rfl⟩
      rw [hbi, Finset.card_range]
    omega
  have hsurj : Set.SurjOn σ S S :=
    Finset.surjOn_of_injOn_of_card_le (f := σ) (s := S) (t := S) hmaps
      (fun a _ b _ h => σ.injective h) le_rfl
  exact Finset.sum_bij (fun j _ => σ j) hmaps (fun a _ b _ h => σ.injective h)
    (fun b hb => by
      obtain ⟨a, ha, rfl⟩ := hsurj hb
      exact ⟨a, ha, rfl⟩)
    (fun _ _ => rfl)

lemma kwStep_monotone_coords {s : ℕ} (sig tau : ℝ) (v : Fin s → ℝ) :
    Monotone (kwStep sig tau v) :=
  order_monotone_coords _

lemma kwStep_nonneg {s : ℕ} (sig tau : ℝ) (v : Fin s → ℝ) :
    ∀ j, 0 ≤ kwStep sig tau v j :=
  order_nonneg (fun _ => le_max_right _ _)

lemma kwStep_mono {s : ℕ} (sig tau : ℝ) {u v : Fin s → ℝ} (h : ∀ j, u j ≤ v j) :
    ∀ j, kwStep sig tau u j ≤ kwStep sig tau v j :=
  order_mono (fun j => max_le_max_right 0 (by linarith [h j]))

lemma kwStep_add_const_le {s : ℕ} (sig tau : ℝ) (v : Fin s → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ j, kwStep sig tau (fun i => v i + c) j ≤ kwStep sig tau v j + c := by
  intro j
  have hle : ∀ i, max (v i + c + sig * kwUnit s i - tau) 0 ≤
      max (v i + sig * kwUnit s i - tau) 0 + c := fun i => by
    apply max_le
    · linarith [le_max_left (v i + sig * kwUnit s i - tau) 0]
    · linarith [le_max_right (v i + sig * kwUnit s i - tau) 0]
  have h := order_mono hle j
  rwa [order_add_const] at h

lemma kwStep_ge_sub_tau {s : ℕ} {sig tau : ℝ} (hsig : 0 ≤ sig) {v : Fin s → ℝ}
    (hv : Monotone v) : ∀ j, v j - tau ≤ kwStep sig tau v j := by
  intro j
  have hmon : Monotone (fun i => max (v i - tau) 0) :=
    fun a b hab => max_le_max_right 0 (sub_le_sub_right (hv hab) tau)
  have hle : ∀ i, max (v i - tau) 0 ≤ max (v i + sig * kwUnit s i - tau) 0 := fun i => by
    apply max_le_max_right 0
    have hku : 0 ≤ kwUnit s i := by unfold kwUnit; split_ifs <;> norm_num
    nlinarith
  calc v j - tau ≤ max (v j - tau) 0 := le_max_left _ _
    _ = order (fun i => max (v i - tau) 0) j := by rw [order_of_monotone hmon]
    _ ≤ kwStep sig tau v j := order_mono hle j

lemma kwStep_le_add_sig {s : ℕ} {sig tau : ℝ} (hsig : 0 ≤ sig) (htau : 0 ≤ tau)
    {v : Fin s → ℝ} (hv : Monotone v) (hv0 : ∀ j, 0 ≤ v j) :
    ∀ j, kwStep sig tau v j ≤ v j + sig := by
  intro j
  have hmon : Monotone (fun i => v i + sig) :=
    fun a b hab => add_le_add_left (hv hab) sig
  have hle : ∀ i, max (v i + sig * kwUnit s i - tau) 0 ≤ v i + sig := fun i => by
    apply max_le
    · have hku : kwUnit s i ≤ 1 := by unfold kwUnit; split_ifs <;> norm_num
      nlinarith
    · linarith [hv0 i]
  calc kwStep sig tau v j ≤ order (fun i => v i + sig) j := order_mono hle j
    _ = v j + sig := by rw [order_of_monotone hmon]

lemma continuous_kwStep {s : ℕ} (sig tau : ℝ) :
    Continuous (kwStep sig tau : (Fin s → ℝ) → (Fin s → ℝ)) := by
  unfold kwStep
  have hinner : Continuous (fun v : Fin s → ℝ => fun j : Fin s => max (v j + sig * kwUnit s j - tau) 0) :=
    continuous_pi fun j =>
      (((continuous_apply j).add continuous_const).sub continuous_const).max continuous_const
  exact (continuous_order (s := s)).comp hinner

lemma continuous_kwStep_uncurry {s : ℕ} :
    Continuous (fun p : (ℝ × ℝ) × (Fin s → ℝ) => kwStep p.1.1 p.1.2 p.2) := by
  unfold kwStep
  have hinner : Continuous (fun p : (ℝ × ℝ) × (Fin s → ℝ) =>
      fun j : Fin s => max (p.2 j + p.1.1 * kwUnit s j - p.1.2) 0) :=
    continuous_pi fun j => by
      have h1 : Continuous (fun p : (ℝ × ℝ) × (Fin s → ℝ) => p.2 j) :=
        (continuous_apply j).comp continuous_snd
      have h2 : Continuous (fun p : (ℝ × ℝ) × (Fin s → ℝ) => p.1.1 * kwUnit s j) :=
        (continuous_fst.comp continuous_fst).mul continuous_const
      have h3 : Continuous (fun p : (ℝ × ℝ) × (Fin s → ℝ) => p.1.2) :=
        continuous_snd.comp continuous_fst
      exact ((h1.add h2).sub h3).max continuous_const
  exact (continuous_order (s := s)).comp hinner

end OrderAndKWStep

section ErgodicHelpers

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurePreserving_symm {P0 : Measure Ω} {shift : Ω ≃ᵐ Ω}
    (hmp : MeasurePreserving shift P0 P0) :
    MeasurePreserving shift.symm P0 P0 := by
  refine ⟨shift.symm.measurable, ?_⟩
  calc Measure.map shift.symm P0
      = Measure.map shift.symm (Measure.map shift P0) := by rw [hmp.map_eq]
    _ = Measure.map (shift.symm ∘ shift) P0 :=
        Measure.map_map shift.symm.measurable shift.measurable
    _ = Measure.map id P0 := by
        congr 1; funext ω; exact shift.symm_apply_apply ω
    _ = P0 := Measure.map_id

lemma ae_iterate_of_ae {P0 : Measure Ω} {f : Ω → Ω}
    (hmp : MeasurePreserving f P0 P0) {P : Ω → Prop} (hP : ∀ᵐ ω ∂P0, P ω) :
    ∀ᵐ ω ∂P0, ∀ n : ℕ, P (f^[n] ω) := by
  rw [ae_all_iff]
  intro n
  exact (hmp.iterate n).quasiMeasurePreserving.ae hP

lemma clamp_lipschitz (n : ℕ) (a b : ℝ) :
    |max (-(n : ℝ)) (min (n : ℝ) a) - max (-(n : ℝ)) (min (n : ℝ) b)| ≤ |a - b| := by
  have hmin : ∀ c x y : ℝ, |min c x - min c y| ≤ |x - y| := by
    intro c x y
    have h1 : ∀ u v : ℝ, min c u - min c v ≤ |u - v| := fun u v => by
      have : min c u - |u - v| ≤ min c v :=
        le_min (by linarith [min_le_left c u, abs_nonneg (u - v)])
          (by linarith [min_le_right c u, le_abs_self (u - v)])
      linarith
    rw [abs_le]
    constructor
    · have := h1 y x; rw [abs_sub_comm] at this; linarith
    · exact h1 x y
  have hmax : ∀ c x y : ℝ, |max c x - max c y| ≤ |x - y| := by
    intro c x y
    have h1 : ∀ u v : ℝ, max c u - max c v ≤ |u - v| := fun u v => by
      have : max c u ≤ max c v + |u - v| :=
        max_le (by linarith [le_max_left c v, abs_nonneg (u - v)])
          (by linarith [le_max_right c v, le_abs_self (u - v)])
      linarith
    rw [abs_le]
    constructor
    · have := h1 y x; rw [abs_sub_comm] at this; linarith
    · exact h1 x y
  exact le_trans (hmax _ _ _) (hmin _ _ _)

lemma integral_comp_sub_eq_zero {P0 : Measure Ω} [IsProbabilityMeasure P0]
    {shift : Ω ≃ᵐ Ω} (hmp : MeasurePreserving shift P0 P0)
    {f : Ω → ℝ} (hf : AEMeasurable f P0)
    (hint : Integrable (fun ω => f (shift ω) - f ω) P0) :
    ∫ ω, (f (shift ω) - f ω) ∂P0 = 0 := by
  let clamp : ℕ → ℝ → ℝ := fun n x => max (-(n : ℝ)) (min (n : ℝ) x)
  have hclamp_cont : ∀ n, Continuous (clamp n) := fun n =>
    continuous_const.max (continuous_const.min continuous_id)
  let fn : ℕ → Ω → ℝ := fun n ω => clamp n (f ω)
  have hfn_meas : ∀ n, AEStronglyMeasurable (fn n) P0 := fun n =>
    ((hclamp_cont n).measurable.comp_aemeasurable hf).aestronglyMeasurable
  have hfn_bound : ∀ n ω, ‖fn n ω‖ ≤ (n : ℝ) := fun n ω => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hfn_int : ∀ n, Integrable (fn n) P0 := fun n =>
    Integrable.of_bound (hfn_meas n) (n : ℝ) (Eventually.of_forall (hfn_bound n))
  have hfn_shift_int : ∀ n, Integrable (fun ω => fn n (shift ω)) P0 := fun n =>
    Integrable.of_bound ((hfn_meas n).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving)
      (n : ℝ) (Eventually.of_forall fun ω => hfn_bound n (shift ω))
  have hzero : ∀ n, ∫ ω, (fn n (shift ω) - fn n ω) ∂P0 = 0 := fun n => by
    rw [integral_sub (hfn_shift_int n) (hfn_int n)]
    rw [hmp.integral_comp' (g := fn n)]
    exact sub_self _
  have htend : ∀ᵐ ω ∂P0, Tendsto (fun n => fn n (shift ω) - fn n ω) atTop
      (𝓝 (f (shift ω) - f ω)) := by
    refine Eventually.of_forall (fun ω => ?_)
    have h1 : ∀ᶠ n : ℕ in atTop, fn n (shift ω) = f (shift ω) := by
      obtain ⟨N, hN⟩ := exists_nat_ge |f (shift ω)|
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hle : |f (shift ω)| ≤ (n : ℝ) := le_trans hN (Nat.cast_le.mpr hn)
      rw [abs_le] at hle
      simp [fn, clamp, min_eq_right hle.2, max_eq_right hle.1]
    have h2 : ∀ᶠ n : ℕ in atTop, fn n ω = f ω := by
      obtain ⟨N, hN⟩ := exists_nat_ge |f ω|
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hle : |f ω| ≤ (n : ℝ) := le_trans hN (Nat.cast_le.mpr hn)
      rw [abs_le] at hle
      simp [fn, clamp, min_eq_right hle.2, max_eq_right hle.1]
    exact tendsto_const_nhds.congr' (by
      filter_upwards [h1, h2] with n hn1 hn2
      rw [hn1, hn2])
  have hdom : ∀ n, ∀ᵐ ω ∂P0, ‖fn n (shift ω) - fn n ω‖ ≤ ‖f (shift ω) - f ω‖ := fun n =>
    Eventually.of_forall (fun ω => by
      simp only [Real.norm_eq_abs]
      exact clamp_lipschitz n (f (shift ω)) (f ω))
  have hlim := tendsto_integral_of_dominated_convergence (fun ω => ‖f (shift ω) - f ω‖)
    (fun n => (hfn_shift_int n).aestronglyMeasurable.sub (hfn_meas n))
    hint.norm hdom htend
  have hlim0 : Tendsto (fun n => ∫ ω, (fn n (shift ω) - fn n ω) ∂P0) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim0

lemma ergodic_ae_subset_shift {P0 : Measure Ω} [IsProbabilityMeasure P0]
    {shift : Ω ≃ᵐ Ω} (herg : Ergodic shift P0)
    {A : Set Ω} (hA : MeasurableSet A) (hsub : ∀ᵐ ω ∂P0, ω ∈ A → shift ω ∈ A) :
    P0 A = 0 ∨ P0 Aᶜ = 0 := by
  have hmp := herg.toMeasurePreserving
  have hA_diff : P0 (A \ shift ⁻¹' A) = 0 := by
    rw [ae_iff] at hsub
    convert hsub using 2
    ext ω
    simp [Set.mem_sdiff]
  have hA_inter : P0 (A ∩ shift ⁻¹' A) = P0 A := by
    have h := measure_inter_add_sdiff A (hA.preimage shift.measurable) (μ := P0)
    rw [hA_diff, add_zero] at h
    exact h
  have hshift_eq : P0 (shift ⁻¹' A) = P0 A := hmp.measure_preimage hA.nullMeasurableSet
  have hshift_diff : P0 (shift ⁻¹' A \ A) = 0 := by
    have h := measure_inter_add_sdiff (shift ⁻¹' A) hA (μ := P0)
    rw [Set.inter_comm, hA_inter, hshift_eq] at h
    have hfin : P0 A ≠ ⊤ := measure_ne_top P0 A
    exact (ENNReal.add_right_inj hfin).mp (by rw [h, add_zero])
  have hae_iff : ∀ᵐ ω ∂P0, shift ω ∈ A ↔ ω ∈ A := by
    have h1 : ∀ᵐ ω ∂P0, ω ∉ A \ shift ⁻¹' A := by
      rw [ae_iff]; convert hA_diff using 2; ext ω; simp
    have h2 : ∀ᵐ ω ∂P0, ω ∉ shift ⁻¹' A \ A := by
      rw [ae_iff]; convert hshift_diff using 2; ext ω; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    simp only [Set.mem_sdiff, Set.mem_preimage, not_and, not_not] at hω1 hω2
    exact ⟨hω2, hω1⟩
  have hae_iter : ∀ᵐ ω ∂P0, ∀ k : ℕ, shift^[k] ω ∈ A ↔ ω ∈ A := by
    have hstep := ae_iterate_of_ae hmp hae_iff
    filter_upwards [hstep] with ω hω k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hω k).trans ih
  let B : Set Ω := ⋂ m : ℕ, ⋃ n : ℕ, shift^[m + n] ⁻¹' A
  have hB_meas : MeasurableSet B :=
    MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
      hA.preimage (shift.measurable.iterate (m + n))
  have hB_inv : shift ⁻¹' B = B := by
    ext ω
    simp only [B, Set.mem_preimage, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h m
      rcases m with _ | m
      · obtain ⟨n, hn⟩ := h 0
        refine ⟨n + 1, ?_⟩
        simpa [Nat.zero_add, Function.iterate_succ_apply] using hn
      · obtain ⟨n, hn⟩ := h m
        refine ⟨n, ?_⟩
        rw [show m + 1 + n = m + n + 1 by omega, Function.iterate_succ_apply]
        exact hn
    · intro h m
      obtain ⟨n, hn⟩ := h (m + 1)
      refine ⟨n, ?_⟩
      rw [show m + 1 + n = m + n + 1 by omega, Function.iterate_succ_apply] at hn
      exact hn
  have hBA : ∀ᵐ ω ∂P0, ω ∈ B ↔ ω ∈ A := by
    filter_upwards [hae_iter] with ω hω
    simp only [B, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h 0
      exact (hω (0 + n)).mp hn
    · intro h m
      exact ⟨0, (hω (m + 0)).mpr h⟩
  have hBA_eq : B =ᵐ[P0] A := by
    filter_upwards [hBA] with ω hω
    exact propext hω
  have hconst := herg.aeconst_set hB_meas hB_inv
  rw [Filter.eventuallyConst_set'] at hconst
  rcases hconst with hB_empty | hB_univ
  · left
    rw [← measure_congr hBA_eq, measure_congr hB_empty, measure_empty]
  · right
    rw [← measure_congr hBA_eq.compl, measure_congr hB_univ.compl, Set.compl_univ, measure_empty]

end ErgodicHelpers

end LoynesMaximalProof

open LoynesMaximalProof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {s : ℕ} (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0)
    (hstab : (∫ ω, sig ω ∂P0) < (s : ℝ) * ∫ ω, tau ω ∂P0)
    (Mf : Ω → Fin s → ℝ) (hMf : IsKWLimit P0 shift sig tau Mf) :
    ∃ (Vx : ℝ → Ω → Fin s → ℝ) (V : Ω → Fin s → ℝ),
      (∀ᵐ ω ∂P0, ∀ (x : ℝ) (j : Fin s), 0 ≤ x →
        Tendsto (fun n : ℕ => kwV shift sig tau Mf x n ω j) atTop (𝓝 (Vx x ω j))) ∧
      (∀ᵐ ω ∂P0, ∀ j : Fin s, Tendsto (fun x : ℝ => Vx x ω j) atTop (𝓝 (V ω j))) ∧
      IsKWSolution P0 shift sig tau V ∧
      (∀ Z : Ω → Fin s → ℝ, Measurable Z → IsKWSolution P0 shift sig tau Z →
        ∀ᵐ ω ∂P0, ∀ j : Fin s, Z ω j ≤ V ω j) := by
  have hmp : MeasurePreserving shift P0 P0 := herg.toMeasurePreserving
  have hmpsymm : MeasurePreserving shift.symm P0 P0 := measurePreserving_symm hmp
  -- Basic positivity from hstab
  have hsig_int_nn : 0 ≤ ∫ ω, sig ω ∂P0 := integral_nonneg hsig0
  have htau_int_nn : 0 ≤ ∫ ω, tau ω ∂P0 := integral_nonneg htau0
  have hs_pos : 0 < s := by
    by_contra hs0
    have hsEq : s = 0 := Nat.eq_zero_of_not_pos hs0
    subst hsEq
    simp only [Nat.cast_zero, zero_mul] at hstab
    linarith
  have htau_int_pos : 0 < ∫ ω, tau ω ∂P0 := by
    by_contra hle
    push Not at hle
    have h0 : ∫ ω, tau ω ∂P0 = 0 := le_antisymm hle htau_int_nn
    rw [h0, mul_zero] at hstab
    linarith
  -- Measurability and properties of kwM
  have hkwM_meas : ∀ n : ℕ, Measurable (kwM (s := s) shift sig tau n) := by
    intro n
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have hcomp : Measurable (fun ω => ((sig (shift.symm ω), tau (shift.symm ω)),
          kwM (s := s) shift sig tau n (shift.symm ω))) :=
        ((hsigmeas.comp shift.symm.measurable).prodMk
          (htaumeas.comp shift.symm.measurable)).prodMk (ih.comp shift.symm.measurable)
      exact continuous_kwStep_uncurry.measurable.comp hcomp
  have hkwM_nonneg : ∀ n ω j, 0 ≤ kwM (s := s) shift sig tau n ω j := by
    intro n ω j
    cases n with
    | zero => exact le_refl 0
    | succ n => exact kwStep_nonneg _ _ _ j
  have hkwM_mono_coords : ∀ n ω, Monotone (kwM (s := s) shift sig tau n ω) := by
    intro n ω
    cases n with
    | zero => exact monotone_const
    | succ n => exact kwStep_monotone_coords _ _ _
  -- Properties of Mf
  have hMf_aemeas : AEMeasurable Mf P0 := by
    refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hkwM_meas n).aemeasurable) ?_
    filter_upwards [hMf] with ω hω
    exact tendsto_pi_nhds.mpr hω
  let Mf' : Ω → Fin s → ℝ := hMf_aemeas.mk Mf
  have hMf'_meas : Measurable Mf' := hMf_aemeas.measurable_mk
  have hMf'_eq : Mf =ᵐ[P0] Mf' := hMf_aemeas.ae_eq_mk
  have hMf_sol : IsKWSolution P0 shift sig tau Mf := by
    have hMf_shift : ∀ᵐ ω ∂P0, ∀ j : Fin s,
        Tendsto (fun n : ℕ => kwM shift sig tau n (shift ω) j) atTop (𝓝 (Mf (shift ω) j)) :=
      hmp.quasiMeasurePreserving.ae hMf
    filter_upwards [hMf, hMf_shift] with ω hω hωs
    have hlim1 : Tendsto (fun n : ℕ => kwM shift sig tau (n + 1) (shift ω)) atTop
        (𝓝 (Mf (shift ω))) :=
      (tendsto_pi_nhds.mpr hωs).comp (tendsto_add_atTop_nat 1)
    have hlim2 : Tendsto (fun n : ℕ => kwM (s := s) shift sig tau (n + 1) (shift ω)) atTop
        (𝓝 (kwStep (sig ω) (tau ω) (Mf ω))) := by
      have heq : (fun n : ℕ => kwM (s := s) shift sig tau (n + 1) (shift ω)) =
          (fun n : ℕ => kwStep (sig ω) (tau ω) (kwM (s := s) shift sig tau n ω)) := by
        funext n
        simp [kwM]
      rw [heq]
      exact (continuous_kwStep (sig ω) (tau ω)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hω)
    exact tendsto_nhds_unique hlim1 hlim2
  have hMf_sol_symm : ∀ᵐ ω ∂P0,
      Mf ω = kwStep (sig (shift.symm ω)) (tau (shift.symm ω)) (Mf (shift.symm ω)) := by
    filter_upwards [hmpsymm.quasiMeasurePreserving.ae hMf_sol] with ω hω
    simpa using hω
  have hMf_sol_iter : ∀ᵐ ω ∂P0, ∀ k : ℕ,
      Mf (shift.symm^[k] ω) =
        kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
          (Mf (shift.symm^[k + 1] ω)) := by
    filter_upwards [ae_iterate_of_ae hmpsymm hMf_sol_symm] with ω hω k
    simpa [Function.iterate_succ_apply'] using hω k
  -- Define Vx
  let Vx : ℝ → Ω → Fin s → ℝ :=
    fun x ω j => limUnder atTop (fun n : ℕ => kwV shift sig tau Mf x n ω j)
  -- Convergence of kwV x n to Vx x
  have hkwV_ge_Mf : ∀ ω, (∀ k : ℕ, Mf (shift.symm^[k] ω) =
        kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
          (Mf (shift.symm^[k + 1] ω))) →
      ∀ x : ℝ, 0 ≤ x → ∀ n k : ℕ, ∀ j : Fin s,
        Mf (shift.symm^[k] ω) j ≤ kwV shift sig tau Mf x n (shift.symm^[k] ω) j := by
    intro ω hω x hx n
    induction n with
    | zero =>
      intro k j
      simp [kwV]
      linarith
    | succ n ih =>
      intro k j
      rw [hω k]
      have hstep : kwV shift sig tau Mf x (n + 1) (shift.symm^[k] ω) j =
          kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
            (kwV shift sig tau Mf x n (shift.symm^[k + 1] ω)) j := by
        simp [kwV, Function.iterate_succ_apply']
      rw [hstep]
      exact kwStep_mono _ _ (ih (k + 1)) j
  have hkwV_anti : ∀ ω, (∀ k : ℕ, Mf (shift.symm^[k] ω) =
        kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
          (Mf (shift.symm^[k + 1] ω))) →
      ∀ x : ℝ, 0 ≤ x → ∀ n k : ℕ, ∀ j : Fin s,
        kwV shift sig tau Mf x (n + 1) (shift.symm^[k] ω) j ≤
          kwV shift sig tau Mf x n (shift.symm^[k] ω) j := by
    intro ω hω x hx n
    induction n with
    | zero =>
      intro k j
      have hstep : kwV shift sig tau Mf x 1 (shift.symm^[k] ω) j =
          kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
            (fun i => Mf (shift.symm^[k + 1] ω) i + x) j := by
        simp [kwV, Function.iterate_succ_apply']
      rw [hstep]
      have hle := kwStep_add_const_le (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
        (Mf (shift.symm^[k + 1] ω)) hx j
      rw [← hω k] at hle
      simpa [kwV] using hle
    | succ n ih =>
      intro k j
      have h1 : kwV shift sig tau Mf x (n + 2) (shift.symm^[k] ω) j =
          kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
            (kwV shift sig tau Mf x (n + 1) (shift.symm^[k + 1] ω)) j := by
        simp [kwV, Function.iterate_succ_apply']
      have h2 : kwV shift sig tau Mf x (n + 1) (shift.symm^[k] ω) j =
          kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
            (kwV shift sig tau Mf x n (shift.symm^[k + 1] ω)) j := by
        simp [kwV, Function.iterate_succ_apply']
      rw [h1, h2]
      exact kwStep_mono _ _ (ih (k + 1)) j
  have hVx_tendsto : ∀ᵐ ω ∂P0, ∀ (x : ℝ) (j : Fin s), 0 ≤ x →
      Tendsto (fun n : ℕ => kwV shift sig tau Mf x n ω j) atTop (𝓝 (Vx x ω j)) := by
    filter_upwards [hMf_sol_iter] with ω hω x j hx
    have hanti : Antitone (fun n : ℕ => kwV shift sig tau Mf x n ω j) :=
      antitone_nat_of_succ_le (fun n => by simpa using hkwV_anti ω hω x hx n 0 j)
    have hbdd : BddBelow (Set.range (fun n : ℕ => kwV shift sig tau Mf x n ω j)) :=
      ⟨Mf ω j, by rintro _ ⟨n, rfl⟩; simpa using hkwV_ge_Mf ω hω x hx n 0 j⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hEq : Vx x ω j = ⨅ n, kwV shift sig tau Mf x n ω j := hlim.limUnder_eq
    rwa [hEq]
  -- Properties of Vx
  have hkwV_mono_x : ∀ x y : ℝ, x ≤ y → ∀ n ω j,
      kwV shift sig tau Mf x n ω j ≤ kwV shift sig tau Mf y n ω j := by
    intro x y hxy n
    induction n with
    | zero => intro ω j; simp [kwV]; linarith
    | succ n ih => intro ω j; exact kwStep_mono _ _ (ih (shift.symm ω)) j
  have hVx_mono_x : ∀ᵐ ω ∂P0, ∀ x y : ℝ, 0 ≤ x → x ≤ y → ∀ j, Vx x ω j ≤ Vx y ω j := by
    filter_upwards [hVx_tendsto] with ω hω x y hx hxy j
    exact le_of_tendsto_of_tendsto (hω x j hx) (hω y j (le_trans hx hxy))
      (Eventually.of_forall (fun n => hkwV_mono_x x y hxy n ω j))
  have hVx_nonneg : ∀ᵐ ω ∂P0, ∀ x : ℝ, 0 ≤ x → ∀ j, 0 ≤ Vx x ω j := by
    filter_upwards [hVx_tendsto] with ω hω x hx j
    have h1 := (hω x j hx).comp (tendsto_add_atTop_nat 1)
    exact ge_of_tendsto h1 (Eventually.of_forall (fun n => kwStep_nonneg _ _ _ j))
  have hVx_mono_coords : ∀ᵐ ω ∂P0, ∀ x : ℝ, 0 ≤ x → Monotone (Vx x ω) := by
    filter_upwards [hVx_tendsto] with ω hω x hx i j hij
    have h1 := (hω x i hx).comp (tendsto_add_atTop_nat 1)
    have h2 := (hω x j hx).comp (tendsto_add_atTop_nat 1)
    exact le_of_tendsto_of_tendsto h1 h2
      (Eventually.of_forall (fun n => kwStep_monotone_coords _ _ _ hij))
  have hVx_sol : ∀ᵐ ω ∂P0, ∀ x : ℝ, 0 ≤ x →
      Vx x (shift ω) = kwStep (sig ω) (tau ω) (Vx x ω) := by
    filter_upwards [hVx_tendsto, hmp.quasiMeasurePreserving.ae hVx_tendsto] with ω hω hωs x hx
    have hlim1 : Tendsto (fun n : ℕ => kwV shift sig tau Mf x (n + 1) (shift ω)) atTop
        (𝓝 (Vx x (shift ω))) :=
      (tendsto_pi_nhds.mpr (fun j => hωs x j hx)).comp (tendsto_add_atTop_nat 1)
    have hlim2 : Tendsto (fun n : ℕ => kwV shift sig tau Mf x (n + 1) (shift ω)) atTop
        (𝓝 (kwStep (sig ω) (tau ω) (Vx x ω))) := by
      have heq : (fun n : ℕ => kwV shift sig tau Mf x (n + 1) (shift ω)) =
          (fun n : ℕ => kwStep (sig ω) (tau ω) (kwV shift sig tau Mf x n ω)) := by
        funext n; simp [kwV]
      rw [heq]
      exact (continuous_kwStep (sig ω) (tau ω)).continuousAt.tendsto.comp
        (tendsto_pi_nhds.mpr (fun j => hω x j hx))
    exact tendsto_nhds_unique hlim1 hlim2
  have hkwV_aemeas : ∀ (x : ℝ) (n : ℕ), AEMeasurable (kwV shift sig tau Mf x n) P0 := by
    intro x n
    induction n with
    | zero =>
      have hadd : Continuous (fun v : Fin s → ℝ => fun j => v j + x) :=
        continuous_pi fun j => (continuous_apply j).add continuous_const
      exact hadd.measurable.comp_aemeasurable hMf_aemeas
    | succ n ih =>
      have h1 : AEMeasurable (fun ω => sig (shift.symm ω)) P0 :=
        (hsigmeas.comp shift.symm.measurable).aemeasurable
      have h2 : AEMeasurable (fun ω => tau (shift.symm ω)) P0 :=
        (htaumeas.comp shift.symm.measurable).aemeasurable
      have h3 : AEMeasurable (fun ω => kwV shift sig tau Mf x n (shift.symm ω)) P0 :=
        ih.comp_quasiMeasurePreserving hmpsymm.quasiMeasurePreserving
      exact continuous_kwStep_uncurry.measurable.comp_aemeasurable ((h1.prodMk h2).prodMk h3)
  have hVx_aemeas : ∀ x : ℝ, 0 ≤ x → AEMeasurable (Vx x) P0 := by
    intro x hx
    refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hkwV_aemeas x n) ?_
    filter_upwards [hVx_tendsto] with ω hω
    exact tendsto_pi_nhds.mpr (fun j => hω x j hx)
  -- Measurable versions of Vx (m : ℕ) for defining W'
  let Vxm : ℕ → Ω → Fin s → ℝ := fun m => (hVx_aemeas (m : ℝ) (Nat.cast_nonneg m)).mk (Vx (m : ℝ))
  have hVxm_meas : ∀ m : ℕ, Measurable (Vxm m) :=
    fun m => (hVx_aemeas (m : ℝ) (Nat.cast_nonneg m)).measurable_mk
  have hVxm_eq : ∀ᵐ ω ∂P0, ∀ m : ℕ, Vx (m : ℝ) ω = Vxm m ω := by
    rw [ae_all_iff]
    intro m
    exact (hVx_aemeas (m : ℝ) (Nat.cast_nonneg m)).ae_eq_mk
  -- Define W and W' in EReal
  let W : Ω → Fin s → EReal := fun ω j => ⨆ m : ℕ, ((Vx (m : ℝ) ω j : ℝ) : EReal)
  let W' : Ω → Fin s → EReal := fun ω j => ⨆ m : ℕ, ((Vxm m ω j : ℝ) : EReal)
  have hW'_meas : ∀ j : Fin s, Measurable (fun ω => W' ω j) := fun j =>
    Measurable.iSup fun m =>
      EReal.continuous_coe_iff.mpr continuous_id |>.measurable.comp
        ((measurable_pi_apply j).comp (hVxm_meas m))
  have hW_eq : ∀ᵐ ω ∂P0, ∀ j : Fin s, W ω j = W' ω j := by
    filter_upwards [hVxm_eq] with ω hω j
    simp only [W, W', hω]
  -- Bounds on Vx (shift ω) j - Vx ω j
  have hVx_diff_bounds : ∀ᵐ ω ∂P0, ∀ (x : ℝ) (j : Fin s), 0 ≤ x →
      -tau ω ≤ Vx x (shift ω) j - Vx x ω j ∧ Vx x (shift ω) j - Vx x ω j ≤ sig ω := by
    filter_upwards [hVx_sol, hVx_mono_coords, hVx_nonneg] with ω hsol hmon hnn x j hx
    rw [hsol x hx]
    have h1 := kwStep_ge_sub_tau (tau := tau ω) (hsig0 ω) (hmon x hx) j
    have h2 := kwStep_le_add_sig (hsig0 ω) (htau0 ω) (hmon x hx) (hnn x hx) j
    constructor <;> linarith
  -- Each {W' ω j = ⊤} is shift-invariant a.e., hence has measure 0 or 1
  have hW_zero_or_one : ∀ j : Fin s,
      (∀ᵐ ω ∂P0, W ω j < ⊤) ∨ (∀ᵐ ω ∂P0, W ω j = ⊤) := by
    intro j
    let A : Set Ω := {ω | W' ω j = ⊤}
    have hA_meas : MeasurableSet A := (hW'_meas j) (measurableSet_singleton ⊤)
    have hA_sub : ∀ᵐ ω ∂P0, ω ∈ A → shift ω ∈ A := by
      filter_upwards [hW_eq, hmp.quasiMeasurePreserving.ae hW_eq, hVx_diff_bounds] with
        ω hWeq hWeqs hdiff hω
      simp only [A, Set.mem_ofPred_eq] at hω ⊢
      rw [← hWeqs j]
      rw [← hWeq j] at hω
      rw [eq_top_iff]
      refine le_of_forall_lt_imp_le_of_dense ?_
      -- Actually easier: show ∀ r : ℝ, (r : EReal) ≤ W (shift ω) j
      have hall : ∀ r : ℝ, (r : EReal) ≤ W (shift ω) j := by
        intro r
        have hlt : ((r + tau ω : ℝ) : EReal) < W ω j := by
          rw [hω]; exact EReal.coe_lt_top _
        obtain ⟨m, hm⟩ := lt_iSup_iff.mp hlt
        refine le_trans ?_ (le_iSup (fun m : ℕ => ((Vx (m : ℝ) (shift ω) j : ℝ) : EReal)) m)
        exact_mod_cast (by
          have hm' : r + tau ω < Vx (m : ℝ) ω j := EReal.coe_lt_coe_iff.mp hm
          linarith [(hdiff (m : ℝ) j (Nat.cast_nonneg m)).1] : r ≤ Vx (m : ℝ) (shift ω) j)
      intro x hx
      cases x using EReal.rec with
      | bot => exact bot_le
      | top => exact (lt_irrefl _ hx).elim
      | coe r => exact hall r
    rcases ergodic_ae_subset_shift herg hA_meas hA_sub with h0 | h1
    · left
      have hna : ∀ᵐ ω ∂P0, ω ∉ A := ae_iff.mpr (by simpa using h0)
      filter_upwards [hna, hW_eq] with ω hω hWeq
      rw [hWeq j]
      exact lt_top_iff_ne_top.mpr hω
    · right
      have ha : ∀ᵐ ω ∂P0, ω ∈ A := by rw [ae_iff]; exact h1
      filter_upwards [ha, hW_eq] with ω hω hWeq
      rw [hWeq j]
      exact hω
  -- Prove that ALL coordinates of W are a.s. finite
  have hW_fin : ∀ j : Fin s, ∀ᵐ ω ∂P0, W ω j < ⊤ := by
    by_contra hnot
    rw [not_forall] at hnot
    -- Find the smallest coordinate j0 with W ω j0 = ⊤ a.s.
    have hex : ∃ n : ℕ, ∃ hn : n < s, ∀ᵐ ω ∂P0, W ω ⟨n, hn⟩ = ⊤ := by
      obtain ⟨j, hj⟩ := hnot
      rcases hW_zero_or_one j with hfin | hinf
      · exact (hj hfin).elim
      · exact ⟨j.1, j.2, hinf⟩
    classical
    let j0_nat := Nat.find hex
    have hj0_spec := Nat.find_spec hex
    obtain ⟨hj0_lt, hj0_inf⟩ := hj0_spec
    have hlt_fin : ∀ i : Fin s, i.1 < j0_nat → ∀ᵐ ω ∂P0, W ω i < ⊤ := by
      intro i hi
      rcases hW_zero_or_one i with hfin | hinf
      · exact hfin
      · exact (Nat.find_min hex hi ⟨i.2, hinf⟩).elim
    have hge_inf : ∀ j : Fin s, j0_nat ≤ j.1 → ∀ᵐ ω ∂P0, W ω j = ⊤ := by
      intro j hj
      filter_upwards [hj0_inf, hVx_mono_coords] with ω hω hmon
      have hle : W ω ⟨j0_nat, hj0_lt⟩ ≤ W ω j :=
        iSup_mono fun m => EReal.coe_le_coe_iff.mpr (hmon (m : ℝ) (Nat.cast_nonneg m) hj)
      rw [hω] at hle
      exact top_le_iff.mp hle
    -- Tail sum over j ≥ j0_nat (there are k = s - j0_nat such coordinates)
    let k : ℕ := s - j0_nat
    have hk_pos : 0 < k := by omega
    have hk_le : k ≤ s := by omega
    have hsk : s - k = j0_nat := by omega
    let tailSet : Finset (Fin s) := Finset.univ.filter (fun j : Fin s => s - k ≤ j.1)
    have htail_card : tailSet.card = k := by
      have hbi : tailSet.card = (Finset.range k).card := by
        apply Finset.card_bij (fun j _ => j.1 - (s - k))
        · intro j hj
          simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢
          omega
        · intro j₁ hj₁ j₂ hj₂ hEq
          simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
          exact Fin.ext (by omega)
        · intro n hn
          rw [Finset.mem_range] at hn
          refine ⟨⟨s - k + n, by omega⟩, ?_, by simp⟩
          simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
      rw [hbi, Finset.card_range]
    let Sm : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ tailSet, Vx (m : ℝ) ω j
    let gm : ℕ → Ω → ℝ := fun m ω => Sm m (shift ω) - Sm m ω
    have hSm_aemeas : ∀ m : ℕ, AEMeasurable (Sm m) P0 := fun m =>
      Finset.aemeasurable_fun_sum tailSet (fun j _ =>
        (measurable_pi_apply j).comp_aemeasurable (hVx_aemeas (m : ℝ) (Nat.cast_nonneg m)))
    have hgm_bound : ∀ m : ℕ, ∀ᵐ ω ∂P0,
        ‖gm m ω‖ ≤ (k : ℝ) * (sig ω + tau ω) := by
      intro m
      filter_upwards [hVx_diff_bounds] with ω hdiff
      have hsum : gm m ω = ∑ j ∈ tailSet, (Vx (m : ℝ) (shift ω) j - Vx (m : ℝ) ω j) := by
        simp only [gm, Sm, Finset.sum_sub_distrib]
      rw [hsum, Real.norm_eq_abs, abs_le]
      constructor
      · have hlow : ∑ j ∈ tailSet, (-tau ω) ≤
            ∑ j ∈ tailSet, (Vx (m : ℝ) (shift ω) j - Vx (m : ℝ) ω j) :=
          Finset.sum_le_sum (fun j _ => (hdiff (m : ℝ) j (Nat.cast_nonneg m)).1)
        simp only [Finset.sum_const, htail_card, nsmul_eq_mul] at hlow
        have := hsig0 ω
        nlinarith
      · have hhi : ∑ j ∈ tailSet, (Vx (m : ℝ) (shift ω) j - Vx (m : ℝ) ω j) ≤
            ∑ j ∈ tailSet, sig ω :=
          Finset.sum_le_sum (fun j _ => (hdiff (m : ℝ) j (Nat.cast_nonneg m)).2)
        simp only [Finset.sum_const, htail_card, nsmul_eq_mul] at hhi
        have := htau0 ω
        nlinarith
    have hdom_int : Integrable (fun ω => (k : ℝ) * (sig ω + tau ω)) P0 :=
      (hsigInt.add htauInt).const_mul (k : ℝ)
    have hgm_aemeas : ∀ m : ℕ, AEStronglyMeasurable (gm m) P0 := fun m =>
      ((hSm_aemeas m).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).aestronglyMeasurable.sub
        (hSm_aemeas m).aestronglyMeasurable
    have hgm_int : ∀ m : ℕ, Integrable (gm m) P0 := fun m =>
      hdom_int.mono' (hgm_aemeas m) (hgm_bound m)
    have hgm_zero : ∀ m : ℕ, ∫ ω, gm m ω ∂P0 = 0 := fun m =>
      integral_comp_sub_eq_zero hmp (hSm_aemeas m) (hgm_int m)
    -- Split into j0_nat = 0 (k = s) vs j0_nat > 0 (k < s)
    by_cases hj0_zero : j0_nat = 0
    · -- Case k = s: gm m ω → sig ω - s * tau ω a.e.
      have hall_inf : ∀ᵐ ω ∂P0, ∀ j : Fin s, W ω j = ⊤ := by
        rw [ae_all_iff]
        intro j
        exact hge_inf j (by omega)
      have hgm_tend : ∀ᵐ ω ∂P0, Tendsto (fun m => gm m ω) atTop (𝓝 (sig ω - (s : ℝ) * tau ω)) := by
        filter_upwards [hall_inf, hVx_sol, hVx_mono_x] with ω hinf hsol hmonx
        have hlarge : ∀ j : Fin s, ∃ M : ℕ, tau ω ≤ Vx (M : ℝ) ω j := by
          intro j
          have hlt : ((tau ω : ℝ) : EReal) < W ω j := by rw [hinf j]; exact EReal.coe_lt_top _
          obtain ⟨M, hM⟩ := lt_iSup_iff.mp hlt
          exact ⟨M, le_of_lt (EReal.coe_lt_coe_iff.mp hM)⟩
        choose M hM using hlarge
        let M0 : ℕ := Finset.univ.sup M
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop M0] with m hm
        have hge_tau : ∀ j : Fin s, tau ω ≤ Vx (m : ℝ) ω j := fun j =>
          le_trans (hM j) (hmonx (M j : ℝ) (m : ℝ) (Nat.cast_nonneg _)
            (Nat.cast_le.mpr (le_trans (Finset.le_sup (Finset.mem_univ j)) hm)) j)
        have htail_univ : tailSet = Finset.univ := by
          ext j; simp [tailSet, hsk, hj0_zero]
        have hSm_shift : Sm m (shift ω) =
            ∑ j : Fin s, (Vx (m : ℝ) ω j + sig ω * kwUnit s j - tau ω) := by
          simp only [Sm, htail_univ, hsol (m : ℝ) (Nat.cast_nonneg m), kwStep, sum_order]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hku : 0 ≤ kwUnit s j := by unfold kwUnit; split_ifs <;> norm_num
          have hnn : 0 ≤ Vx (m : ℝ) ω j + sig ω * kwUnit s j - tau ω := by
            have := hge_tau j; have := hsig0 ω; nlinarith
          exact max_eq_left hnn
        have hku_sum : ∑ j : Fin s, sig ω * kwUnit s j = sig ω := by
          rw [← Finset.mul_sum]
          have h1 : ∑ j : Fin s, kwUnit s j = 1 := by
            rw [Finset.sum_eq_single ⟨0, hs_pos⟩]
            · simp [kwUnit]
            · intro j _ hj
              simp [kwUnit, Fin.ext_iff] at hj ⊢
              exact hj
            · intro h; exact (h (Finset.mem_univ _)).elim
          rw [h1, mul_one]
        have hEq : gm m ω = sig ω - (s : ℝ) * tau ω := by
          dsimp only [gm]
          rw [hSm_shift]
          dsimp only [Sm]
          rw [htail_univ, Finset.sum_sub_distrib, Finset.sum_add_distrib, hku_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        exact hEq.symm
      have hlim := tendsto_integral_of_dominated_convergence
        (fun ω => (k : ℝ) * (sig ω + tau ω)) hgm_aemeas hdom_int hgm_bound hgm_tend
      have hlim0 : Tendsto (fun m => ∫ ω, gm m ω ∂P0) atTop (𝓝 0) := by
        simp only [hgm_zero]; exact tendsto_const_nhds
      have hInt_eq : ∫ ω, (sig ω - (s : ℝ) * tau ω) ∂P0 = 0 :=
        tendsto_nhds_unique hlim hlim0
      rw [integral_sub hsigInt (htauInt.const_mul (s : ℝ)), integral_const_mul] at hInt_eq
      linarith
    · -- Case j0_nat > 0 (0 < k < s): gm m ω → -(k : ℝ) * tau ω a.e.
      have hj0_pos : 0 < j0_nat := Nat.pos_of_ne_zero hj0_zero
      have hfin_below : ∀ᵐ ω ∂P0, ∀ i : Fin s, i.1 < j0_nat → W ω i < ⊤ := by
        rw [ae_all_iff]
        intro i
        by_cases hi : i.1 < j0_nat
        · filter_upwards [hlt_fin i hi] with ω hω _; exact hω
        · exact Eventually.of_forall (fun _ h => (hi h).elim)
      have hinf_above : ∀ᵐ ω ∂P0, ∀ j : Fin s, j0_nat ≤ j.1 → W ω j = ⊤ := by
        rw [ae_all_iff]
        intro j
        by_cases hj : j0_nat ≤ j.1
        · filter_upwards [hge_inf j hj] with ω hω _; exact hω
        · exact Eventually.of_forall (fun _ h => (hj h).elim)
      have hgm_tend : ∀ᵐ ω ∂P0, Tendsto (fun m => gm m ω) atTop (𝓝 (-(k : ℝ) * tau ω)) := by
        filter_upwards [hfin_below, hinf_above, hVx_sol, hVx_mono_x, hVx_mono_coords, hVx_nonneg]
          with ω hfin hinf hsol hmonx hmonc hnn
        let iprev : Fin s := ⟨j0_nat - 1, by omega⟩
        have hiprev_fin : W ω iprev < ⊤ := hfin iprev (by show j0_nat - 1 < j0_nat; omega)
        have hiprev_nn : 0 ≤ (W ω iprev).toReal := by
          have h0 : (0 : EReal) ≤ W ω iprev :=
            le_trans (EReal.coe_le_coe_iff.mpr (hnn ((0 : ℕ) : ℝ) (Nat.cast_nonneg 0) iprev))
              (le_iSup (fun m : ℕ => ((Vx (m : ℝ) ω iprev : ℝ) : EReal)) 0)
          exact EReal.toReal_nonneg h0
        let B : ℝ := (W ω iprev).toReal + sig ω
        have hB_nn : 0 ≤ B := add_nonneg hiprev_nn (hsig0 ω)
        have hlarge : ∀ j : Fin s, ∃ M : ℕ, j0_nat ≤ j.1 → B + tau ω < Vx (M : ℝ) ω j := by
          intro j
          by_cases hj : j0_nat ≤ j.1
          · have hlt : ((B + tau ω : ℝ) : EReal) < W ω j := by
              rw [hinf j hj]; exact EReal.coe_lt_top _
            obtain ⟨M, hM⟩ := lt_iSup_iff.mp hlt
            exact ⟨M, fun _ => EReal.coe_lt_coe_iff.mp hM⟩
          · exact ⟨0, fun h => (hj h).elim⟩
        choose M hM using hlarge
        let M0 : ℕ := Finset.univ.sup M
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop M0] with m hm
        let u : Fin s → ℝ := fun j => max (Vx (m : ℝ) ω j + sig ω * kwUnit s j - tau ω) 0
        have hu_below : ∀ i : Fin s, i.1 < s - k → u i ≤ B := by
          intro i hi
          have hile : i ≤ iprev := by show i.1 ≤ j0_nat - 1; omega
          have hle1 : Vx (m : ℝ) ω i ≤ Vx (m : ℝ) ω iprev :=
            hmonc (m : ℝ) (Nat.cast_nonneg m) hile
          have hle2 : ((Vx (m : ℝ) ω iprev : ℝ) : EReal) ≤ W ω iprev :=
            le_iSup (fun m : ℕ => ((Vx (m : ℝ) ω iprev : ℝ) : EReal)) m
          have hle3 : Vx (m : ℝ) ω iprev ≤ (W ω iprev).toReal := by
            have hbot : W ω iprev ≠ ⊥ := by
              intro hbot
              have h0 : (0 : EReal) ≤ W ω iprev :=
                le_trans (EReal.coe_le_coe_iff.mpr (hnn ((0 : ℕ) : ℝ) (Nat.cast_nonneg 0) iprev))
                  (le_iSup (fun m : ℕ => ((Vx (m : ℝ) ω iprev : ℝ) : EReal)) 0)
              rw [hbot] at h0
              exact not_le_of_gt (EReal.bot_lt_coe 0) h0
            rw [← EReal.coe_toReal (ne_of_lt hiprev_fin) hbot] at hle2
            exact EReal.coe_le_coe_iff.mp hle2
          have hku : kwUnit s i ≤ 1 := by unfold kwUnit; split_ifs <;> norm_num
          apply max_le
          · have := hsig0 ω; have := htau0 ω; nlinarith
          · exact hB_nn
        have hu_above : ∀ j : Fin s, s - k ≤ j.1 → u j = Vx (m : ℝ) ω j - tau ω ∧ B < u j := by
          intro j hj
          have hj' : j0_nat ≤ j.1 := by omega
          have hgt : B + tau ω < Vx (m : ℝ) ω j :=
            lt_of_lt_of_le (hM j hj') (hmonx (M j : ℝ) (m : ℝ) (Nat.cast_nonneg _)
              (Nat.cast_le.mpr (le_trans (Finset.le_sup (Finset.mem_univ j)) hm)) j)
          have hku : kwUnit s j = 0 := by
            unfold kwUnit; split_ifs with h0
            · omega
            · rfl
          have hu_eq : u j = Vx (m : ℝ) ω j - tau ω := by
            simp only [u, hku, mul_zero, add_zero]
            exact max_eq_left (by linarith)
          exact ⟨hu_eq, by linarith⟩
        have hsep : ∀ i j : Fin s, i.1 < s - k → s - k ≤ j.1 → u i < u j :=
          fun i j hi hj => lt_of_le_of_lt (hu_below i hi) (hu_above j hj).2
        have hSm_shift : Sm m (shift ω) = ∑ j ∈ tailSet, (Vx (m : ℝ) ω j - tau ω) := by
          simp only [Sm, hsol (m : ℝ) (Nat.cast_nonneg m), kwStep]
          rw [order_tail_sum hsep]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact (hu_above j hj).1
        have hEq : gm m ω = -(k : ℝ) * tau ω := by
          dsimp only [gm]
          rw [hSm_shift]
          dsimp only [Sm]
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, htail_card, nsmul_eq_mul]
          ring
        exact hEq.symm
      have hlim := tendsto_integral_of_dominated_convergence
        (fun ω => (k : ℝ) * (sig ω + tau ω)) hgm_aemeas hdom_int hgm_bound hgm_tend
      have hlim0 : Tendsto (fun m => ∫ ω, gm m ω ∂P0) atTop (𝓝 0) := by
        simp only [hgm_zero]; exact tendsto_const_nhds
      have hInt_eq : ∫ ω, (-(k : ℝ) * tau ω) ∂P0 = 0 :=
        tendsto_nhds_unique hlim hlim0
      rw [integral_const_mul] at hInt_eq
      have hk_pos_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
      nlinarith
  -- Define V and prove all four conclusions!
  let V : Ω → Fin s → ℝ := fun ω j => (W ω j).toReal
  have hW_fin_all : ∀ᵐ ω ∂P0, ∀ j : Fin s, W ω j < ⊤ := ae_all_iff.mpr hW_fin
  have hV_tendsto : ∀ᵐ ω ∂P0, ∀ j : Fin s,
      Tendsto (fun x : ℝ => Vx x ω j) atTop (𝓝 (V ω j)) := by
    filter_upwards [hW_fin_all, hVx_mono_x, hVx_nonneg] with ω hfin hmonx hnn j
    have hbot : W ω j ≠ ⊥ := by
      intro hbot
      have h0 : (0 : EReal) ≤ W ω j :=
        le_trans (EReal.coe_le_coe_iff.mpr (hnn ((0 : ℕ) : ℝ) (Nat.cast_nonneg 0) j))
          (le_iSup (fun m : ℕ => ((Vx (m : ℝ) ω j : ℝ) : EReal)) 0)
      rw [hbot] at h0
      exact not_le_of_gt (EReal.bot_lt_coe 0) h0
    have hW_coe : ((V ω j : ℝ) : EReal) = W ω j := EReal.coe_toReal (ne_of_lt (hfin j)) hbot
    have hle_V : ∀ x : ℝ, 0 ≤ x → Vx x ω j ≤ V ω j := by
      intro x hx
      obtain ⟨m, hm⟩ := exists_nat_ge x
      have h1 : Vx x ω j ≤ Vx (m : ℝ) ω j := hmonx x (m : ℝ) hx hm j
      have h2 : ((Vx (m : ℝ) ω j : ℝ) : EReal) ≤ ((V ω j : ℝ) : EReal) := by
        rw [hW_coe]
        exact le_iSup (fun m : ℕ => ((Vx (m : ℝ) ω j : ℝ) : EReal)) m
      exact le_trans h1 (EReal.coe_le_coe_iff.mp h2)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlt : ((V ω j - ε : ℝ) : EReal) < W ω j := by
      rw [← hW_coe]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨M, hM⟩ := lt_iSup_iff.mp hlt
    refine ⟨(M : ℝ), fun x hx => ?_⟩
    have hMx : Vx (M : ℝ) ω j ≤ Vx x ω j := hmonx (M : ℝ) x (Nat.cast_nonneg M) hx j
    have hxV : Vx x ω j ≤ V ω j := hle_V x (le_trans (Nat.cast_nonneg M) hx)
    have hM' : V ω j - ε < Vx (M : ℝ) ω j := EReal.coe_lt_coe_iff.mp hM
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hV_sol : IsKWSolution P0 shift sig tau V := by
    filter_upwards [hV_tendsto, hmp.quasiMeasurePreserving.ae hV_tendsto, hVx_sol]
      with ω hω hωs hsol
    have hlim1 : Tendsto (fun m : ℕ => Vx (m : ℝ) (shift ω)) atTop (𝓝 (V (shift ω))) :=
      (tendsto_pi_nhds.mpr hωs).comp tendsto_natCast_atTop_atTop
    have hlim2 : Tendsto (fun m : ℕ => Vx (m : ℝ) (shift ω)) atTop
        (𝓝 (kwStep (sig ω) (tau ω) (V ω))) := by
      have heq : (fun m : ℕ => Vx (m : ℝ) (shift ω)) =
          (fun m : ℕ => kwStep (sig ω) (tau ω) (Vx (m : ℝ) ω)) := by
        funext m; exact hsol (m : ℝ) (Nat.cast_nonneg m)
      rw [heq]
      exact (continuous_kwStep (sig ω) (tau ω)).continuousAt.tendsto.comp
        ((tendsto_pi_nhds.mpr hω).comp tendsto_natCast_atTop_atTop)
    exact tendsto_nhds_unique hlim1 hlim2
  have hV_max : ∀ Z : Ω → Fin s → ℝ, Measurable Z → IsKWSolution P0 shift sig tau Z →
      ∀ᵐ ω ∂P0, ∀ j : Fin s, Z ω j ≤ V ω j := by
    intro Z hZmeas hZsol
    let j0 : Fin s := ⟨0, hs_pos⟩
    let U : Ω → ℝ := fun ω =>
      Finset.univ.sup' ⟨j0, Finset.mem_univ j0⟩ (fun j : Fin s => max (Z ω j - Mf' ω j) 0)
    have hU_meas : Measurable U := by
      have hcoord : ∀ j : Fin s, Measurable (fun ω => max (Z ω j - Mf' ω j) 0) := fun j =>
        (((measurable_pi_apply j).comp hZmeas).sub
          ((measurable_pi_apply j).comp hMf'_meas)).max measurable_const
      have hgen : ∀ (S : Finset (Fin s)) (hS : S.Nonempty),
          Measurable (fun ω => S.sup' hS (fun j => max (Z ω j - Mf' ω j) 0)) := by
        intro S hS
        induction hS using Finset.Nonempty.cons_induction with
        | singleton a =>
          simpa using hcoord a
        | cons a t ha ht ih =>
          have : (fun ω => (t.cons a ha).sup' (Finset.cons_nonempty ha)
              (fun j => max (Z ω j - Mf' ω j) 0)) =
              (fun ω => max (Z ω a - Mf' ω a) 0 ⊔
                t.sup' ht (fun j => max (Z ω j - Mf' ω j) 0)) := by
            funext ω
            exact Finset.sup'_cons ht (f := fun j => max (Z ω j - Mf' ω j) 0)
          rw [this]
          exact (hcoord a).sup ih
      exact hgen Finset.univ ⟨j0, Finset.mem_univ j0⟩
    have hU_nn : ∀ ω, 0 ≤ U ω := fun ω =>
      le_trans (le_max_right _ _) (Finset.le_sup' (fun j => max (Z ω j - Mf' ω j) 0)
        (Finset.mem_univ j0))
    have hU_sub : ∀ᵐ ω ∂P0, U (shift ω) ≤ U ω := by
      filter_upwards [hZsol, hMf_sol, hMf'_eq, hmp.quasiMeasurePreserving.ae hMf'_eq]
        with ω hZω hMfω hMeq hMeqs
      refine Finset.sup'_le _ _ (fun j _ => ?_)
      apply max_le _ (hU_nn ω)
      have hZle : ∀ i : Fin s, Z ω i ≤ Mf ω i + U ω := fun i => by
        have h1 : Z ω i - Mf' ω i ≤ U ω :=
          le_trans (le_max_left _ _) (Finset.le_sup' (fun j => max (Z ω j - Mf' ω j) 0)
            (Finset.mem_univ i))
        have h2 : Mf ω i = Mf' ω i := congr_fun hMeq i
        linarith
      have hstep1 : Z (shift ω) j ≤ kwStep (sig ω) (tau ω) (fun i => Mf ω i + U ω) j := by
        rw [hZω]; exact kwStep_mono _ _ hZle j
      have hstep2 : kwStep (sig ω) (tau ω) (fun i => Mf ω i + U ω) j ≤ Mf (shift ω) j + U ω := by
        have := kwStep_add_const_le (sig ω) (tau ω) (Mf ω) (hU_nn ω) j
        rwa [← hMfω] at this
      have h3 : Mf (shift ω) j = Mf' (shift ω) j := congr_fun hMeqs j
      linarith
    -- Ergodicity gives a deterministic n : ℕ with U ω ≤ n a.e.
    have hex_n : ∃ n : ℕ, ∀ᵐ ω ∂P0, U ω ≤ (n : ℝ) := by
      by_contra hnone
      rw [not_exists] at hnone
      have hall0 : ∀ n : ℕ, P0 {ω | U ω ≤ (n : ℝ)} = 0 := by
        intro n
        let Bn : Set Ω := {ω | U ω ≤ (n : ℝ)}
        have hBn_meas : MeasurableSet Bn := hU_meas measurableSet_Iic
        have hBn_sub : ∀ᵐ ω ∂P0, ω ∈ Bn → shift ω ∈ Bn := by
          filter_upwards [hU_sub] with ω hω hmem
          exact le_trans hω hmem
        rcases ergodic_ae_subset_shift herg hBn_meas hBn_sub with h0 | h1
        · exact h0
        · exfalso
          apply hnone n
          rw [ae_iff]
          exact h1
      have huniv : (⋃ n : ℕ, {ω | U ω ≤ (n : ℝ)}) = Set.univ := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact exists_nat_ge (U ω)
      have hP0_univ : P0 Set.univ = 0 := by
        rw [← huniv]
        exact measure_iUnion_null hall0
      have h1 : P0 Set.univ = 1 := measure_univ
      rw [hP0_univ] at h1
      exact zero_ne_one h1
    obtain ⟨n, hn⟩ := hex_n
    have hZ_le_0 : ∀ᵐ ω ∂P0, ∀ j : Fin s, Z ω j ≤ kwV shift sig tau Mf (n : ℝ) 0 ω j := by
      filter_upwards [hn, hMf'_eq] with ω hω hMeq j
      have h1 : Z ω j - Mf' ω j ≤ U ω :=
        le_trans (le_max_left _ _) (Finset.le_sup' (fun j => max (Z ω j - Mf' ω j) 0)
          (Finset.mem_univ j))
      have h2 : Mf ω j = Mf' ω j := congr_fun hMeq j
      simp only [kwV]
      linarith
    have hZ_sol_symm : ∀ᵐ ω ∂P0,
        Z ω = kwStep (sig (shift.symm ω)) (tau (shift.symm ω)) (Z (shift.symm ω)) := by
      filter_upwards [hmpsymm.quasiMeasurePreserving.ae hZsol] with ω hω
      simpa using hω
    have hZ_le_all : ∀ᵐ ω ∂P0, ∀ m : ℕ, ∀ j : Fin s,
        Z ω j ≤ kwV shift sig tau Mf (n : ℝ) m ω j := by
      have h0_iter := ae_iterate_of_ae hmpsymm hZ_le_0
      have hsol_iter := ae_iterate_of_ae hmpsymm hZ_sol_symm
      filter_upwards [h0_iter, hsol_iter] with ω h0 hsol m
      have hgen : ∀ k : ℕ, ∀ j : Fin s,
          Z (shift.symm^[k] ω) j ≤ kwV shift sig tau Mf (n : ℝ) m (shift.symm^[k] ω) j := by
        induction m with
        | zero => intro k j; exact h0 k j
        | succ m ih =>
          intro k j
          have hZstep : Z (shift.symm^[k] ω) =
              kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
                (Z (shift.symm^[k + 1] ω)) := by
            simpa [Function.iterate_succ_apply'] using hsol k
          have hVstep : kwV shift sig tau Mf (n : ℝ) (m + 1) (shift.symm^[k] ω) =
              kwStep (sig (shift.symm^[k + 1] ω)) (tau (shift.symm^[k + 1] ω))
                (kwV shift sig tau Mf (n : ℝ) m (shift.symm^[k + 1] ω)) := by
            simp [kwV, Function.iterate_succ_apply']
          rw [hZstep, hVstep]
          exact kwStep_mono _ _ (ih (k + 1)) j
      simpa using hgen 0
    filter_upwards [hZ_le_all, hVx_tendsto, hV_tendsto, hVx_mono_x] with ω hZle hVx hV hmonx j
    have h1 : Z ω j ≤ Vx (n : ℝ) ω j :=
      ge_of_tendsto (hVx (n : ℝ) j (Nat.cast_nonneg n))
        (Eventually.of_forall (fun m => hZle m j))
    have h2 : Vx (n : ℝ) ω j ≤ V ω j :=
      ge_of_tendsto (hV j) (by
        filter_upwards [Filter.eventually_ge_atTop (n : ℝ)] with x hx
        exact hmonx (n : ℝ) x (Nat.cast_nonneg n) hx j)
    exact le_trans h1 h2
  exact ⟨Vx, V, hVx_tendsto, hV_tendsto, hV_sol, hV_max⟩

#print axioms solution
