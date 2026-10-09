-- Prove2me | solution 1 for TamingMonster.Regret.iloveToConBandits_regret_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T09:49:57.5+00:00
-- url     : https://prove2.me/submissions/e9b45374-b05d-4e20-abe5-de65a82e076a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis
import Theorems.Thm_TamingMonster_Regret_variance_deviation
import Theorems.Thm_TamingMonster_Regret_ips_deviation

set_option autoImplicit false

namespace TamingMonster.Regret

open MeasureTheory

/-! Draft for 2c7e1df6: C3 and C4 proved; C1 (goodEvent_prob) and C2 (Lemma 14) open. -/

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

theorem round_expect_le {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    (Q : Pi → ℝ) (hQ0 : ∀ π, 0 ≤ Q π) (hQ1 : ∑ π, Q π = 1)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : (K : ℝ) * μ ≤ 1)
    (πstar : Pi) (hstar : ∀ π : Pi, expReward D (π : X → Fin K) ≤ expReward D πstar) :
    ∫ w, (w.1.2 ((πstar : X → Fin K) w.1.1)
        - w.1.2 (drawAction (smoothProj Pi Q μ w.1.1) w.2))
      ∂(D.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ≤
      (1 - (K : ℝ) * μ) * ∑ π : Pi, Q π * polRegret Pi D (π : X → Fin K)
        + ((K : ℝ) - 1) * μ := by
  classical
  set ν := volume.restrict (Set.Icc (0 : ℝ) 1) with hν
  have : IsProbabilityMeasure ν := ⟨by simp [hν, Measure.restrict_apply MeasurableSet.univ]⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast NeZero.one_le
  have hRmeas : ∀ π : Pi, Measurable (fun z : X × (Fin K → ℝ) => z.2 ((π : X → Fin K) z.1)) :=
    fun π => measurable_eval_pair.comp
      (measurable_snd.prodMk ((hPiMeas π π.2).comp measurable_fst))
  have hRint : ∀ π : Pi, Integrable (fun z : X × (Fin K → ℝ) => z.2 ((π : X → Fin K) z.1)) D :=
    fun π => Integrable.of_mem_Icc 0 1 (hRmeas π).aemeasurable (hD.mono fun z hz => hz _)
  have hFmeas : Measurable (fun w : (X × (Fin K → ℝ)) × ℝ => w.1.2 ((πstar : X → Fin K) w.1.1)
        - w.1.2 (drawAction (smoothProj Pi Q μ w.1.1) w.2)) := by
    apply Measurable.sub ((hRmeas πstar).comp measurable_fst)
    exact measurable_eval_pair.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_drawAction_comp ((measurable_smoothProj Pi hPiMeas Q μ).comp
        (measurable_fst.comp measurable_fst)) measurable_snd))
  have hDprod : ∀ᵐ w ∂(D.prod ν), ∀ a, w.1.2 a ∈ Set.Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst).ae hD
  have hFint : Integrable (fun w : (X × (Fin K → ℝ)) × ℝ => w.1.2 ((πstar : X → Fin K) w.1.1)
        - w.1.2 (drawAction (smoothProj Pi Q μ w.1.1) w.2)) (D.prod ν) := by
    refine Integrable.of_mem_Icc (-1) 1 hFmeas.aemeasurable (hDprod.mono fun w hw => ?_)
    obtain ⟨h1, h2⟩ := hw ((πstar : X → Fin K) w.1.1)
    obtain ⟨h3, h4⟩ := hw (drawAction (smoothProj Pi Q μ w.1.1) w.2)
    constructor <;> linarith
  have hsup : (⨆ π' : Pi, expReward D (π' : X → Fin K)) = expReward D (πstar : X → Fin K) := by
    have : Nonempty Pi := ⟨πstar⟩
    exact le_antisymm (ciSup_le hstar)
      (le_ciSup (f := fun π' : Pi => expReward D (π' : X → Fin K)) (Set.finite_range _).bddAbove πstar)
  have hHint : Integrable (fun z : X × (Fin K → ℝ) =>
      (1 - (K : ℝ) * μ) * ∑ π : Pi, Q π * (z.2 ((πstar : X → Fin K) z.1)
        - z.2 ((π : X → Fin K) z.1)) + ((K : ℝ) - 1) * μ) D :=
    ((integrable_finset_sum _ (fun π _ => ((hRint πstar).sub (hRint π)).const_mul (Q π))).const_mul
      _).add (integrable_const _)
  calc ∫ w, (w.1.2 ((πstar : X → Fin K) w.1.1)
        - w.1.2 (drawAction (smoothProj Pi Q μ w.1.1) w.2)) ∂(D.prod ν)
      = ∫ z, ∫ u, (z.2 ((πstar : X → Fin K) z.1)
          - z.2 (drawAction (smoothProj Pi Q μ z.1) u)) ∂ν ∂D := integral_prod _ hFint
    _ ≤ ∫ z, ((1 - (K : ℝ) * μ) * ∑ π : Pi, Q π * (z.2 ((πstar : X → Fin K) z.1)
        - z.2 ((π : X → Fin K) z.1)) + ((K : ℝ) - 1) * μ) ∂D := by
      apply integral_mono_ae hFint.integral_prod_left hHint
      filter_upwards [hD] with z hz
      have hp0 := smoothProj_nonneg Pi Q hQ0 hμ0 hμ1 z.1
      have hp1 := smoothProj_sum Pi Q hQ1 μ z.1
      have hi := integral_drawAction (smoothProj Pi Q μ z.1) hp0 hp1
        (fun a => z.2 ((πstar : X → Fin K) z.1) - z.2 a)
      refine le_trans (le_of_eq hi) ?_
      have e1 : ∑ a, smoothProj Pi Q μ z.1 a * (z.2 ((πstar : X → Fin K) z.1) - z.2 a)
          = (1 - (K : ℝ) * μ) * ∑ a, (∑ π ∈ Finset.univ.filter
              (fun π : Pi => (π : X → Fin K) z.1 = a), Q π)
                * (z.2 ((πstar : X → Fin K) z.1) - z.2 a)
            + μ * ∑ a, (z.2 ((πstar : X → Fin K) z.1) - z.2 a) := by
        unfold smoothProj
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [e1, sum_weighted_fiber Pi Q z.1 (fun a => z.2 ((πstar : X → Fin K) z.1) - z.2 a),
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hS : z.2 ((πstar : X → Fin K) z.1) ≤ ∑ a, z.2 a :=
        Finset.single_le_sum (fun a _ => (hz a).1) (Finset.mem_univ _)
      have hr1 := (hz ((πstar : X → Fin K) z.1)).2
      have h1 : μ * ((K : ℝ) * z.2 ((πstar : X → Fin K) z.1) - ∑ a, z.2 a)
          ≤ μ * (((K : ℝ) - 1) * z.2 ((πstar : X → Fin K) z.1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hμ0
      have h2 : μ * (((K : ℝ) - 1) * z.2 ((πstar : X → Fin K) z.1)) ≤ μ * ((K : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hμ0
      linarith
    _ = (1 - (K : ℝ) * μ) * ∑ π : Pi, Q π * polRegret Pi D (π : X → Fin K)
        + ((K : ℝ) - 1) * μ := by
      have hI2 : ∀ π : Pi, Integrable (fun z : X × (Fin K → ℝ) =>
          Q π * (z.2 ((πstar : X → Fin K) z.1) - z.2 ((π : X → Fin K) z.1))) D :=
        fun π => ((hRint πstar).sub (hRint π)).const_mul (Q π)
      have hI1 : Integrable (fun z : X × (Fin K → ℝ) => (1 - (K : ℝ) * μ) * ∑ π : Pi,
          Q π * (z.2 ((πstar : X → Fin K) z.1) - z.2 ((π : X → Fin K) z.1))) D :=
        (integrable_finset_sum _ (fun π _ => hI2 π)).const_mul _
      rw [integral_add hI1 (integrable_const _), integral_const_mul,
        integral_finset_sum _ (fun π _ => hI2 π)]
      rw [integral_const, show D.real Set.univ = 1 by
        rw [measureReal_def, measure_univ, ENNReal.toReal_one], one_smul]
      congr 2
      apply Finset.sum_congr rfl
      intro π _
      rw [integral_const_mul, integral_sub (hRint πstar) (hRint π)]
      unfold polRegret
      rw [hsup]
      rfl

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

theorem hoeffding_shift {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (Xf : E → ℝ) (hX : Measurable Xf) (hb : ∀ᵐ e ∂ν, Xf e ∈ Set.Icc (-1 : ℝ) 1) (B : ℝ)
    (hB : ∫ e, Xf e ∂ν ≤ B) {l : ℝ} (hl : 0 ≤ l) :
    ∫⁻ e, ENNReal.ofReal (Real.exp (l * (Xf e - B))) ∂ν
      ≤ ENNReal.ofReal (Real.exp (l ^ 2 / 2)) := by
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hX.aemeasurable hb
  have h2 : ‖(1 : ℝ) - -1‖₊ = 2 := by
    ext
    simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    norm_num
  have hc : (((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 := by
    rw [h2]
    norm_num
  calc ∫⁻ e, ENNReal.ofReal (Real.exp (l * (Xf e - B))) ∂ν
      ≤ ∫⁻ e, ENNReal.ofReal (Real.exp (l * (Xf e - ∫ x, Xf x ∂ν))) ∂ν := by
        apply lintegral_mono
        intro e
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith) hl
    _ = ENNReal.ofReal (∫ e, Real.exp (l * (Xf e - ∫ x, Xf x ∂ν)) ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_mul l)
          (Filter.Eventually.of_forall (fun e => (Real.exp_pos _).le))).symm
    _ ≤ ENNReal.ofReal (Real.exp (l ^ 2 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have := h.mgf_le l
        rw [hc, one_mul] at this
        exact this

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

theorem mgf_incr_le (A : AlgoParams X K)
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
    (πstar : A.Pi) (hstar : ∀ π : A.Pi, expReward D (π : X → Fin K) ≤ expReward D πstar)
    {l : ℝ} (hl : 0 ≤ l) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
        incr A D (πstar : X → Fin K) Z U ω t)) ∂P
      ≤ ENNReal.ofReal (Real.exp (n * l ^ 2 / 2)) := by
  classical
  have hUnif : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
  have hW : ∀ t, Measurable (fun ω => (Z t ω, U t ω)) := fun t => (hZmeas t).prodMk (hUmeas t)
  have hlaw : ∀ t, P.map (fun ω => (Z t ω, U t ω))
      = D.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro t
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (hZmeas t).aemeasurable
      (hUmeas t).aemeasurable).mp (hZU t), hZlaw t, hUlaw t]
  have hπ : Measurable (πstar : X → Fin K) := hPiMeas _ πstar.2
  have hincrS : ∀ t, 1 ≤ t → Measurable (fun s : ℕ → (X × (Fin K → ℝ)) × ℝ =>
      incr A D (πstar : X → Fin K) seqZ seqU s t) := fun t ht =>
    measurable_incr A hPiMeas hrules hτ0 hτ D _ hπ seqZ seqU measurable_seqZ measurable_seqU t ht
  induction n with
  | zero => simp
  | succ n ih =>
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
  -- the functions on the sequence space
  have hSfM : Measurable (fun s : ℕ → (X × (Fin K → ℝ)) × ℝ =>
      ∑ t ∈ Finset.Icc 1 n, incr A D (πstar : X → Fin K) seqZ seqU s t) :=
    Finset.measurable_sum _ (fun t ht => hincrS t (Finset.mem_Icc.mp ht).1)
  have hYfM : Measurable (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
      incr A D (πstar : X → Fin K) seqZ seqU (Function.update p.1 (n + 1) p.2) (n + 1)) :=
    (hincrS (n + 1) (by omega)).comp measurable_update'
  have hI1 : ∀ ω, ∑ t ∈ Finset.Icc 1 n, incr A D (πstar : X → Fin K) Z U ω t
      = ∑ t ∈ Finset.Icc 1 n, incr A D (πstar : X → Fin K) seqZ seqU (preSeq Z U n ω) t := by
    intro ω
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    apply incr_congr A hτ0 hτ D _ Z U ω seqZ seqU _ t ht.1
    intro s h1 h2
    constructor <;> simp only [seqZ, seqU, preSeq, if_pos (le_trans h2 ht.2)]
  have hI2 : ∀ ω, incr A D (πstar : X → Fin K) Z U ω (n + 1)
      = incr A D (πstar : X → Fin K) seqZ seqU
          (Function.update (preSeq Z U n ω) (n + 1) (Z (n + 1) ω, U (n + 1) ω)) (n + 1) := by
    intro ω
    apply incr_congr A hτ0 hτ D _ Z U ω seqZ seqU _ (n + 1) (by omega)
    intro s h1 h2
    rcases Nat.lt_or_ge s (n + 1) with hs | hs
    · constructor <;> simp only [seqZ, seqU, Function.update_of_ne (show s ≠ n + 1 by omega),
        preSeq, if_pos (show s ≤ n by omega)]
    · obtain rfl : s = n + 1 := by omega
      constructor <;> simp only [seqZ, seqU, Function.update_self]
  -- inner bound
  have hinner : ∀ s : ℕ → (X × (Fin K → ℝ)) × ℝ,
      ∫⁻ e, ENNReal.ofReal (Real.exp (l * incr A D (πstar : X → Fin K) seqZ seqU
          (Function.update s (n + 1) e) (n + 1))) ∂(P.map (fun ω => (Z (n + 1) ω, U (n + 1) ω)))
        ≤ ENNReal.ofReal (Real.exp (l ^ 2 / 2)) := by
    intro s
    rw [hlaw (n + 1)]
    obtain ⟨hQ0, hQ1⟩ := Qtilde_prob A hsel seqZ seqU s (epochOf A.τ (n + 1) - 1)
    obtain ⟨-, hlt, -⟩ := epochOf_spec' hτ0 hτ (t := n + 1) (by omega)
    have hY : ∀ e : (X × (Fin K → ℝ)) × ℝ, incr A D (πstar : X → Fin K) seqZ seqU
        (Function.update s (n + 1) e) (n + 1)
        = (e.1.2 ((πstar : X → Fin K) e.1.1) - e.1.2 (drawAction (smoothProj A.Pi
            (A.Qtilde seqZ seqU s (epochOf A.τ (n + 1) - 1))
            (muM A.Pi A.δ A.τ (epochOf A.τ (n + 1) - 1)) e.1.1) e.2))
          - Bterm A D seqZ seqU s (n + 1) := by
      intro e
      have hag : ∀ s', 1 ≤ s' → s' < n + 1 →
          seqZ s' (Function.update s (n + 1) e) = seqZ s' s ∧
          seqU s' (Function.update s (n + 1) e) = seqU s' s := by
        intro s' _ h2
        constructor <;> simp only [seqZ, seqU, Function.update_of_ne (show s' ≠ n + 1 by omega)]
      unfold incr
      rw [action_succ_eq A hτ0 hτ, Bterm_congr A hτ0 hτ D _ _ _ seqZ seqU s (n + 1) (by omega) hag,
        Qtilde_congr A _ _ _ seqZ seqU s _ (fun s' h1 h2 => hag s' h1 (by omega))]
      simp only [seqZ, seqU, Function.update_self]
    simp_rw [hY]
    have hXf : Measurable (fun e : (X × (Fin K → ℝ)) × ℝ =>
        e.1.2 ((πstar : X → Fin K) e.1.1) - e.1.2 (drawAction (smoothProj A.Pi
          (A.Qtilde seqZ seqU s (epochOf A.τ (n + 1) - 1))
          (muM A.Pi A.δ A.τ (epochOf A.τ (n + 1) - 1)) e.1.1) e.2)) := by
      apply Measurable.sub (measurable_eval_pair.comp ((measurable_snd.comp measurable_fst).prodMk
        (hπ.comp (measurable_fst.comp measurable_fst))))
      exact measurable_eval_pair.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_drawAction_comp ((measurable_smoothProj A.Pi hPiMeas _ _).comp
          (measurable_fst.comp measurable_fst)) measurable_snd))
    have hDprod : ∀ᵐ w ∂(D.prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
        ∀ a, w.1.2 a ∈ Set.Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_fst).ae hD
    apply hoeffding_shift _ _ hXf _ _ _ hl
    · filter_upwards [hDprod] with w hw
      obtain ⟨h1, h2⟩ := hw ((πstar : X → Fin K) w.1.1)
      obtain ⟨h3, h4⟩ := hw (drawAction (smoothProj A.Pi
          (A.Qtilde seqZ seqU s (epochOf A.τ (n + 1) - 1))
          (muM A.Pi A.δ A.τ (epochOf A.τ (n + 1) - 1)) w.1.1) w.2)
      constructor <;> linarith
    · exact round_expect_le A.Pi hPiMeas D hD _ hQ0 hQ1 (muM_nonneg' _ _ _ _)
        (K_muM_le _ _ _ _) πstar hstar
  -- assemble
  have hGM : Measurable (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
      ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
          incr A D (πstar : X → Fin K) seqZ seqU p.1 t))
        * ENNReal.ofReal (Real.exp (l * incr A D (πstar : X → Fin K) seqZ seqU
          (Function.update p.1 (n + 1) p.2) (n + 1)))) :=
    ((measurable_const.mul (hSfM.comp measurable_fst)).exp.ennreal_ofReal).mul
      ((measurable_const.mul hYfM).exp.ennreal_ofReal)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 (n + 1),
        incr A D (πstar : X → Fin K) Z U ω t)) ∂P
      = ∫⁻ ω, (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
          ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) seqZ seqU p.1 t))
          * ENNReal.ofReal (Real.exp (l * incr A D (πstar : X → Fin K) seqZ seqU
            (Function.update p.1 (n + 1) p.2) (n + 1))))
          (preSeq Z U n ω, (Z (n + 1) ω, U (n + 1) ω)) ∂P := by
        apply lintegral_congr
        intro ω
        simp only
        rw [Finset.sum_Icc_succ_top (by omega), hI1, hI2, mul_add, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ s, ∫⁻ e, (fun p : (ℕ → (X × (Fin K → ℝ)) × ℝ) × ((X × (Fin K → ℝ)) × ℝ) =>
          ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) seqZ seqU p.1 t))
          * ENNReal.ofReal (Real.exp (l * incr A D (πstar : X → Fin K) seqZ seqU
            (Function.update p.1 (n + 1) p.2) (n + 1)))) (s, e)
          ∂(P.map (fun ω => (Z (n + 1) ω, U (n + 1) ω))) ∂(P.map (preSeq Z U n)) :=
        lintegral_indep_split P hPreM (hW (n + 1)) hind hGM
    _ ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) seqZ seqU s t))
          * ENNReal.ofReal (Real.exp (l ^ 2 / 2)) ∂(P.map (preSeq Z U n)) := by
        apply lintegral_mono
        intro s
        simp only
        rw [lintegral_const_mul _ (f := fun e => ENNReal.ofReal (Real.exp (l * incr A D
          (πstar : X → Fin K) seqZ seqU (Function.update s (n + 1) e) (n + 1))))
          (by exact (measurable_const.mul (hYfM.comp
            (measurable_const.prodMk measurable_id))).exp.ennreal_ofReal)]
        gcongr
        exact hinner s
    _ = (∫⁻ s, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) seqZ seqU s t)) ∂(P.map (preSeq Z U n)))
          * ENNReal.ofReal (Real.exp (l ^ 2 / 2)) :=
        lintegral_mul_const _ ((measurable_const.mul hSfM).exp.ennreal_ofReal)
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) Z U ω t)) ∂P)
          * ENNReal.ofReal (Real.exp (l ^ 2 / 2)) := by
        rw [lintegral_map (f := fun s => ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.Icc 1 n,
            incr A D (πstar : X → Fin K) seqZ seqU s t)))
          (by exact (measurable_const.mul hSfM).exp.ennreal_ofReal) hPreM]
        congr 1
        apply lintegral_congr
        intro ω
        rw [hI1]
    _ ≤ ENNReal.ofReal (Real.exp (n * l ^ 2 / 2)) * ENNReal.ofReal (Real.exp (l ^ 2 / 2)) :=
        by gcongr
    _ = ENNReal.ofReal (Real.exp (((n + 1 : ℕ) : ℝ) * l ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        push_cast
        ring

end MGF

theorem azuma_regret {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
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
    (πstar : A.Pi) (hstar : ∀ π : A.Pi, expReward D (π : X → Fin K) ≤ expReward D πstar)
    (T : ℕ) :
    P {ω | ∑ t ∈ Finset.Icc 1 T,
            ((1 - (K : ℝ) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) *
                ∑ π : A.Pi, A.Qtilde Z U ω (epochOf A.τ t - 1) π
                  * polRegret A.Pi D (π : X → Fin K)
              + ((K : ℝ) - 1) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1))
          + Real.sqrt (2 * (T : ℝ) * Real.log (2 / A.δ))
        < A.cumRegret Z U (πstar : X → Fin K) ω T} ≤ ENNReal.ofReal (A.δ / 2) := by

  classical
  set ε := Real.sqrt (2 * (T : ℝ) * Real.log (2 / A.δ)) with hε
  have hset : {ω | ∑ t ∈ Finset.Icc 1 T,
            ((1 - (K : ℝ) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) *
                ∑ π : A.Pi, A.Qtilde Z U ω (epochOf A.τ t - 1) π
                  * polRegret A.Pi D (π : X → Fin K)
              + ((K : ℝ) - 1) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1))
          + ε < A.cumRegret Z U (πstar : X → Fin K) ω T}
      = {ω | ε < ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t} := by
    ext ω
    simp only [Set.mem_setOf_eq, incr, Bterm, Finset.sum_sub_distrib, AlgoParams.cumRegret]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hlog : 0 ≤ Real.log (2 / A.δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp [hε]
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set l := ε / T with hldef
  have hl : 0 ≤ l := div_nonneg (Real.sqrt_nonneg _) hTpos.le
  have hmgf := mgf_incr_le A hPiMeas hτ0 hτ hsel hrules D hD P Z U hZmeas hUmeas hindep hZU
    hZlaw hUlaw πstar hstar hl T
  have hmeasS : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 T,
      incr A D (πstar : X → Fin K) Z U ω t) :=
    Finset.measurable_sum _ (fun t ht => measurable_incr A hPiMeas hrules hτ0 hτ D _
      (hPiMeas _ πstar.2) Z U hZmeas hUmeas t (Finset.mem_Icc.mp ht).1)
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := P) (f := fun ω => ENNReal.ofReal (Real.exp
      (l * ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t)))
    (by exact (measurable_const.mul hmeasS).exp.ennreal_ofReal.aemeasurable)
    (ENNReal.ofReal (Real.exp (l * ε)))
  have hsub : {ω | ε < ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t}
      ⊆ {ω | ENNReal.ofReal (Real.exp (l * ε)) ≤ ENNReal.ofReal (Real.exp
          (l * ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.le hl))
  have key : ENNReal.ofReal (Real.exp (l * ε))
      * P {ω | ε < ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t}
      ≤ ENNReal.ofReal (Real.exp (T * l ^ 2 / 2)) := by
    refine le_trans ?_ (le_trans hmarkov hmgf)
    gcongr
  have hone : ENNReal.ofReal (Real.exp (-(l * ε))) * ENNReal.ofReal (Real.exp (l * ε)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hε2 : ε ^ 2 = 2 * T * Real.log (2 / A.δ) :=
    Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hTpos.le) hlog)
  have hexp : -(l * ε) + (T : ℝ) * l ^ 2 / 2 = -Real.log (2 / A.δ) := by
    have h1 : -(l * ε) + (T : ℝ) * l ^ 2 / 2 = -(ε ^ 2) / (2 * T) := by
      rw [hldef]
      field_simp
      ring
    rw [h1, hε2]
    field_simp
  calc P {ω | ε < ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t}
      = ENNReal.ofReal (Real.exp (-(l * ε))) * (ENNReal.ofReal (Real.exp (l * ε))
          * P {ω | ε < ∑ t ∈ Finset.Icc 1 T, incr A D (πstar : X → Fin K) Z U ω t}) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(l * ε))) * ENNReal.ofReal (Real.exp (T * l ^ 2 / 2)) := by
        gcongr
    _ = ENNReal.ofReal (A.δ / 2) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hexp, Real.exp_neg,
          Real.exp_log (by positivity), inv_div]



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

theorem sqrt_step' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 * a) :
    (b - a) * (1 / Real.sqrt a) ≤ (1 + Real.sqrt 2) * (Real.sqrt b - Real.sqrt a) := by
  have hx : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hxx : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hyy : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (by linarith)
  have hxy : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have h2 : Real.sqrt b ≤ Real.sqrt 2 * Real.sqrt a := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hb
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [mul_one_div, div_le_iff₀ hx]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h2)]

theorem tele_sum' {τ : ℕ → ℕ} (hτ : StrictMono τ)
    (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) {n0 : ℕ} (hn0 : 1 ≤ n0) :
    ∀ M, n0 ≤ M → ∑ t ∈ Finset.Ioc (τ n0) (τ M), 1 / Real.sqrt (τ (epochOf τ t - 1) : ℝ)
      ≤ (1 + Real.sqrt 2) * (Real.sqrt (τ M : ℝ) - Real.sqrt (τ n0 : ℝ)) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [← Finset.sum_Ioc_consecutive _ (hτ.monotone hM) (hτ.monotone (Nat.le_succ M))]
    have hc : ∀ t ∈ Finset.Ioc (τ M) (τ (M + 1)),
        1 / Real.sqrt (τ (epochOf τ t - 1) : ℝ) = 1 / Real.sqrt (τ M : ℝ) := by
      intro t ht
      rw [Finset.mem_Ioc] at ht
      rw [epochOf_eq_succ' hτ ht.1 ht.2]
      simp
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
      Nat.cast_sub (hτ.monotone (Nat.le_succ M))]
    have hM1 : 1 ≤ τ M := le_trans (le_trans hn0 hM) (hτ.id_le M : M ≤ τ M)
    have hMpos : (0 : ℝ) < τ M := by exact_mod_cast hM1
    have hs := sqrt_step' hMpos (b := (τ (M + 1) : ℝ))
      (by exact_mod_cast hτ.monotone (Nat.le_succ M))
      (by exact_mod_cast hτ2 M (by omega))
    linarith

theorem small_term' {c S μ K : ℝ} (hK : 0 < K) (hμ : μ = 1 / (2 * K)) (hS : S ≤ c * K * μ)
    (hc : 2 ≤ c) : (1 - K * μ) * S + (K - 1) * μ ≤ c / 2 := by
  subst hμ
  have e0 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
  have e1 : c * K * (1 / (2 * K)) = c / 2 := by field_simp
  have e2 : (K - 1) * (1 / (2 * K)) = 1 / 2 - 1 / (2 * K) := by field_simp
  have hp : 0 < 1 / (2 * K) := by positivity
  rw [e0, e2]
  rw [e1] at hS
  nlinarith

theorem large_term' {c S μ K w : ℝ} (hμ0 : 0 ≤ μ) (hK0 : 0 ≤ K) (hμ1 : K * μ ≤ 1 / 2)
    (hS : S ≤ c * K * μ) (hc : 0 ≤ c) (hw : K * μ ≤ w) :
    (1 - K * μ) * S + (K - 1) * μ ≤ (c + 1) * w := by
  have hy0 : 0 ≤ K * μ := mul_nonneg hK0 hμ0
  have h1 := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 1 - K * μ)
  have h2 : 0 ≤ c * (K * μ) * (K * μ) := mul_nonneg (mul_nonneg hc hy0) hy0
  have h3 := mul_le_mul_of_nonneg_left hw (by linarith : (0 : ℝ) ≤ c + 1)
  nlinarith

theorem expected_regret_sum_le {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (D : Measure (X × (Fin K → ℝ))) {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ))
    (U : ℕ → Ω → ℝ) (ω : Ω)
    (hw : ∀ m, 1 ≤ m →
      ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * polRegret A.Pi D (π : X → Fin K) ≤
        (4 * psi + c0 A.Pi A.δ A.τ) * (K : ℝ) * muM A.Pi A.δ A.τ (m - 1))
    (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T,
        ((1 - (K : ℝ) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) *
            ∑ π : A.Pi, A.Qtilde Z U ω (epochOf A.τ t - 1) π * polRegret A.Pi D (π : X → Fin K)
          + ((K : ℝ) - 1) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) ≤
      C0 A.Pi A.δ A.τ *
        (4 * (K : ℝ) * dT A.Pi A.δ (A.τ (m0 A.Pi A.δ A.τ - 1))
          + Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ (epochOf A.τ T))
              * (A.τ (epochOf A.τ T) : ℝ))) := by
  classical
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hcard : (1 : ℝ) ≤ A.Pi.card := by exact_mod_cast hPi.card_pos
  have hc400 : 400 ≤ C0 A.Pi A.δ A.τ := by
    have : 0 ≤ rho A.Pi A.δ A.τ := Real.iSup_nonneg (fun _ => Real.sqrt_nonneg _)
    simp only [C0, c0, psi, theta1]
    nlinarith
  have hw' : ∀ m, 1 ≤ m →
      ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * polRegret A.Pi D (π : X → Fin K) ≤
        C0 A.Pi A.δ A.τ * (K : ℝ) * muM A.Pi A.δ A.τ (m - 1) := hw
  -- facts on d_t
  have hd_nonneg : ∀ t : ℕ, 1 ≤ t → 0 ≤ dT A.Pi A.δ t := by
    intro t ht
    unfold dT
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h2 : (1 : ℝ) ≤ (t : ℝ) ^ 2 * A.Pi.card :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) hcard
    nlinarith
  have hd_mono : ∀ s t : ℕ, 1 ≤ s → s ≤ t → dT A.Pi A.δ s ≤ dT A.Pi A.δ t := by
    intro s t hs hst
    unfold dT
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hpos : 0 < 16 * (s : ℝ) ^ 2 * A.Pi.card :=
      mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) (by linarith)
    apply Real.log_le_log (div_pos hpos hδ0)
    gcongr
  -- epochs below m₀
  have hbelow : ∀ m, 1 ≤ m → m < m0 A.Pi A.δ A.τ →
      0 < (A.τ m : ℝ) ∧ (A.τ m : ℝ) < 4 * K * dT A.Pi A.δ (A.τ m) := by
    intro m hm1 hm
    have hnot := Nat.notMem_of_lt_sInf hm
    simp only [Set.mem_setOf_eq, not_and, not_le] at hnot
    have hlt := hnot hm1
    have hτpos : 0 < (A.τ m : ℝ) := by
      rcases (Nat.cast_nonneg (A.τ m) : (0 : ℝ) ≤ _).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hlt
        have : 0 < 1 / (4 * (K : ℝ)) := by positivity
        linarith
    refine ⟨hτpos, ?_⟩
    rw [div_lt_div_iff₀ (by positivity) hτpos] at hlt
    linarith
  -- facts on μ
  have hmu_nonneg : ∀ m, 0 ≤ muM A.Pi A.δ A.τ m := by
    intro m
    unfold muM
    split_ifs
    · positivity
    · exact le_min (by positivity) (Real.sqrt_nonneg _)
  have hmu_le : ∀ m, muM A.Pi A.δ A.τ m ≤ 1 / (2 * (K : ℝ)) := by
    intro m
    unfold muM
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hmu_small : ∀ m, m < m0 A.Pi A.δ A.τ → muM A.Pi A.δ A.τ m = 1 / (2 * (K : ℝ)) := by
    intro m hm
    unfold muM
    split_ifs with h0
    · rfl
    · apply min_eq_left
      obtain ⟨hτpos, hd⟩ := hbelow m (by omega) hm
      have hsq : (1 / (2 * (K : ℝ))) ^ 2 ≤ dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)) := by
        rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_lt_mul_of_pos_left hd hK]
      calc 1 / (2 * (K : ℝ)) = Real.sqrt ((1 / (2 * (K : ℝ))) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hsq
  have hmu_sqrt : ∀ m, 1 ≤ m →
      muM A.Pi A.δ A.τ m ≤ Real.sqrt (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ))) := by
    intro m hm
    unfold muM
    rw [if_neg (by omega)]
    exact min_le_right _ _
  have hKmu : ∀ m, (K : ℝ) * muM A.Pi A.δ A.τ m ≤ 1 / 2 := by
    intro m
    have := mul_le_mul_of_nonneg_left (hmu_le m) hK.le
    have e : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by field_simp
    linarith
  -- the split
  set m0' := m0 A.Pi A.δ A.τ with hm0'
  have hc0 : 0 ≤ C0 A.Pi A.δ A.τ := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ (epochOf A.τ T))
      * (A.τ (epochOf A.τ T) : ℝ)) := Real.sqrt_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun t => t ≤ A.τ m0')]
  refine (add_le_add (b := C0 A.Pi A.δ A.τ * (4 * (K : ℝ) * dT A.Pi A.δ (A.τ (m0' - 1))))
    (d := C0 A.Pi A.δ A.τ * Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ (epochOf A.τ T))
              * (A.τ (epochOf A.τ T) : ℝ))) ?_ ?_).trans (le_of_eq (by ring))
  · -- rounds of the first m₀ epochs
    refine (Finset.sum_le_card_nsmul _ _ (C0 A.Pi A.δ A.τ / 2) ?_).trans ?_
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨he1, -, -⟩ := epochOf_spec' hτ0 hτ ht.1.1
      have hle : epochOf A.τ t ≤ m0' := epochOf_le_of' ht.2
      exact small_term' hK (hmu_small _ (by omega)) (hw' _ he1) (by linarith)
    · have hcardle : ((Finset.Icc 1 T).filter (fun t => t ≤ A.τ m0')).card ≤ A.τ m0' := by
        calc _ ≤ (Finset.Icc 1 (A.τ m0')).card := by
              apply Finset.card_le_card
              intro t ht
              rw [Finset.mem_filter, Finset.mem_Icc] at ht
              rw [Finset.mem_Icc]
              exact ⟨ht.1.1, ht.2⟩
          _ = A.τ m0' := by simp
      rw [nsmul_eq_mul]
      have h1 : (((Finset.Icc 1 T).filter (fun t => t ≤ A.τ m0')).card : ℝ) ≤ A.τ m0' := by
        exact_mod_cast hcardle
      have h2 : (A.τ m0' : ℝ) ≤ 2 * A.τ (m0' - 1) := by
        have := hτ2 (m0' - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact_mod_cast this
      obtain ⟨-, h3⟩ := hbelow (m0' - 1) (by omega) (by omega)
      nlinarith [mul_le_mul_of_nonneg_right h1 hc0, mul_le_mul_of_nonneg_left h2 hc0,
        mul_le_mul_of_nonneg_left h3.le hc0]
  · -- later rounds
    by_cases hT : T ≤ A.τ m0'
    · rw [Finset.sum_eq_zero]
      · exact mul_nonneg hc0 hsqrt_nonneg
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_Icc] at ht
        exact (ht.2 (le_trans ht.1.2 hT)).elim
    push_neg at hT
    set M := epochOf A.τ T with hM
    have hT1 : 1 ≤ T := by omega
    obtain ⟨-, -, hTM⟩ := epochOf_spec' hτ0 hτ hT1
    rw [← hM] at hTM
    have hMgt : m0' < M := by
      by_contra h
      push_neg at h
      have := hτ.monotone h
      omega
    have hτM1 : 1 ≤ A.τ M := by omega
    have hdM : 0 ≤ dT A.Pi A.δ (A.τ M) := hd_nonneg _ hτM1
    set W := Real.sqrt ((K : ℝ) * dT A.Pi A.δ (A.τ M)) with hW
    have hW0 : 0 ≤ W := Real.sqrt_nonneg _
    have hterm : ∀ t ∈ (Finset.Icc 1 T).filter (fun t => ¬ t ≤ A.τ m0'),
        ((1 - (K : ℝ) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) *
            ∑ π : A.Pi, A.Qtilde Z U ω (epochOf A.τ t - 1) π * polRegret A.Pi D (π : X → Fin K)
          + ((K : ℝ) - 1) * muM A.Pi A.δ A.τ (epochOf A.τ t - 1)) ≤
        (C0 A.Pi A.δ A.τ + 1) * W * (1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ)) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨he1, -, hte⟩ := epochOf_spec' hτ0 hτ ht.1.1
      have hegt : m0' < epochOf A.τ t := by
        by_contra h
        push_neg at h
        have := hτ.monotone h
        exact ht.2 (le_trans hte this)
      have heM : epochOf A.τ t ≤ M := epochOf_le_of' (le_trans ht.1.2 hTM)
      set m := epochOf A.τ t - 1 with hm
      have hm1 : 1 ≤ m := by omega
      have hτm1 : 1 ≤ A.τ m := le_trans hm1 (hτ.id_le m : m ≤ A.τ m)
      have hτmM : A.τ m ≤ A.τ M := hτ.monotone (by omega)
      have hτpos : (0 : ℝ) < A.τ m := by exact_mod_cast hτm1
      have hdm0 : 0 ≤ dT A.Pi A.δ (A.τ m) := hd_nonneg _ hτm1
      have hdmM : dT A.Pi A.δ (A.τ m) ≤ dT A.Pi A.δ (A.τ M) := hd_mono _ _ hτm1 hτmM
      set μ := muM A.Pi A.δ A.τ m with hμ
      have hμ0 : 0 ≤ μ := hmu_nonneg m
      have hμs := hmu_sqrt m hm1
      rw [← hμ] at hμs
      have hsq : μ * μ ≤ dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)) := by
        calc μ * μ ≤ _ := mul_self_le_mul_self hμ0 hμs
          _ = _ := Real.mul_self_sqrt (by positivity)
      have hKK : (K : ℝ) * μ * ((K : ℝ) * μ) ≤ (K : ℝ) * dT A.Pi A.δ (A.τ M) / (A.τ m : ℝ) := by
        have e : (K : ℝ) * μ * ((K : ℝ) * μ) = (K : ℝ) ^ 2 * (μ * μ) := by ring
        have e2 : (K : ℝ) ^ 2 * (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)))
            = (K : ℝ) * dT A.Pi A.δ (A.τ m) / (A.τ m : ℝ) := by
          field_simp
        rw [e]
        calc (K : ℝ) ^ 2 * (μ * μ)
            ≤ (K : ℝ) ^ 2 * (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ))) :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = _ := e2
          _ ≤ _ := by gcongr
      have hKw : (K : ℝ) * μ ≤ W * (1 / Real.sqrt (A.τ m : ℝ)) := by
        calc (K : ℝ) * μ = Real.sqrt ((K : ℝ) * μ * ((K : ℝ) * μ)) :=
              (Real.sqrt_mul_self (mul_nonneg hK.le hμ0)).symm
          _ ≤ Real.sqrt ((K : ℝ) * dT A.Pi A.δ (A.τ M) / (A.τ m : ℝ)) := Real.sqrt_le_sqrt hKK
          _ = W * (1 / Real.sqrt (A.τ m : ℝ)) := by
              rw [Real.sqrt_div (mul_nonneg hK.le hdM), hW, mul_one_div]
      have := large_term' hμ0 hK.le (hKmu m) (hw' _ he1) hc0 hKw
      rw [mul_assoc]
      exact this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hf0 : ∀ t, 0 ≤ 1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ) := fun t => by positivity
    have hsub1 : ∑ t ∈ (Finset.Icc 1 T).filter (fun t => ¬ t ≤ A.τ m0'),
          1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ)
        ≤ ∑ t ∈ Finset.Ioc (A.τ m0') (A.τ M), 1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_Icc] at ht
        rw [Finset.mem_Ioc]
        exact ⟨by omega, le_trans ht.1.2 hTM⟩
      · intro t _ _
        exact hf0 t
    have htele := tele_sum' hτ hτ2 (n0 := m0') (by omega) M hMgt.le
    have hs2 : 0 ≤ Real.sqrt (A.τ m0' : ℝ) := Real.sqrt_nonneg _
    have hsM : 0 ≤ Real.sqrt (A.τ M : ℝ) := Real.sqrt_nonneg _
    have hsum : ∑ t ∈ (Finset.Icc 1 T).filter (fun t => ¬ t ≤ A.τ m0'),
          1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ)
        ≤ (1 + Real.sqrt 2) * Real.sqrt (A.τ M : ℝ) := by
      have : 0 ≤ (1 + Real.sqrt 2) * Real.sqrt (A.τ m0' : ℝ) :=
        mul_nonneg (by positivity) hs2
      nlinarith
    have hsplit : Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ M) * (A.τ M : ℝ))
        = 2 * Real.sqrt 2 * W * Real.sqrt (A.τ M : ℝ) := by
      have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]
      rw [show 8 * (K : ℝ) * dT A.Pi A.δ (A.τ M) * (A.τ M : ℝ)
          = 8 * ((K : ℝ) * dT A.Pi A.δ (A.τ M)) * (A.τ M : ℝ) by ring,
        Real.sqrt_mul (mul_nonneg (by norm_num) (mul_nonneg hK.le hdM)),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), h8, hW]
    rw [hsplit]
    have hs2a : (14 / 10 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (14 / 10 : ℝ) = Real.sqrt ((14 / 10) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs2b : Real.sqrt 2 ≤ 15 / 10 := by
      rw [show (15 / 10 : ℝ) = Real.sqrt ((15 / 10) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hconst : (C0 A.Pi A.δ A.τ + 1) * (1 + Real.sqrt 2)
        ≤ C0 A.Pi A.δ A.τ * (2 * Real.sqrt 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc400) (sub_nonneg.mpr hs2a)]
    have hWs : 0 ≤ W * Real.sqrt (A.τ M : ℝ) := mul_nonneg hW0 hsM
    have hA : (C0 A.Pi A.δ A.τ + 1) * W * ∑ t ∈ (Finset.Icc 1 T).filter
          (fun t => ¬ t ≤ A.τ m0'), 1 / Real.sqrt (A.τ (epochOf A.τ t - 1) : ℝ)
        ≤ (C0 A.Pi A.δ A.τ + 1) * W * ((1 + Real.sqrt 2) * Real.sqrt (A.τ M : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hW0)
    have hB := mul_le_mul_of_nonneg_right hconst hWs
    nlinarith



/-! Lemmas 12-14 of Agarwal et al. on the event E' = (13) ∧ (Lemma 11 with λ_{m-1} = μ_{m-1}). -/

/-- Part (13) of the event `ℰ`. -/
def Ev13 {X : Type*} [MeasurableSpace X] {K : ℕ} {Ω : Type*} (A : AlgoParams X K)
    (D : Measure (X × (Fin K → ℝ))) (Z : ℕ → Ω → X × (Fin K → ℝ)) (ω : Ω) : Prop :=
  ∀ P : A.Pi → ℝ, (∀ π, 0 ≤ P π) → ∑ π, P π = 1 → ∀ π : A.Pi, ∀ m : ℕ, 1 ≤ m →
    4 * (K : ℝ) * dT A.Pi A.δ (A.τ m) ≤ (A.τ m : ℝ) →
    Vpop (D.map Prod.fst) A.Pi P (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
      64 / 10 * Vhat A.Pi P (π : X → Fin K) (muM A.Pi A.δ A.τ m) (fun i => (Z i ω).1) (A.τ m)
        + 813 / 10 * (K : ℝ)

/-- Lemma 11's conclusion with `λ_{m−1} = μ_{m−1}` and `δ' = δ/4` (so `ln(4t²|Π|/δ') = d_t`). -/
def Ev14 {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (D : Measure (X × (Fin K → ℝ))) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) : Prop :=
  ∀ π : A.Pi, ∀ m : ℕ, 1 ≤ m → ∀ t : ℕ, A.τ (m - 1) < t → t ≤ A.τ m →
    |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)| ≤
      A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * muM A.Pi A.δ A.τ (m - 1)
        + dT A.Pi A.δ t / (t * muM A.Pi A.δ A.τ (m - 1))

lemma l13_hist_len {X : Type*} {K : ℕ} [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ t, (A.history Z U ω t).length = t := by
  intro t
  induction t with
  | zero => simp [AlgoParams.history]
  | succ n ih => simp [AlgoParams.history, ih]

lemma l13_roundRecord_ctx {X : Type*} {K : ℕ} [NeZero K] (A : AlgoParams X K)
    (h : List (Rec X K)) (t : ℕ) (z : X × (Fin K → ℝ)) (u : ℝ) :
    (A.roundRecord h t z u).1 = z.1 := rfl

lemma l13_hist_sum {X : Type*} {K : ℕ} [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (f : X → ℝ) :
    ∀ t, ((A.history Z U ω t).map (fun e => f e.ctx)).sum
      = ∑ i ∈ Finset.Icc 1 t, f (Z i ω).1 := by
  intro t
  induction t with
  | zero => simp [AlgoParams.history]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [AlgoParams.history, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Rec.ctx, l13_roundRecord_ctx]

lemma l13_sp_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (μ : ℝ)
    (hQ : ∀ π, 0 ≤ Q π) (hμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    μ ≤ smoothProj Pi Q μ x a := by
  unfold smoothProj
  have h1 : 0 ≤ ∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π :=
    Finset.sum_nonneg (fun π _ => hQ π)
  have h2 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  nlinarith [mul_nonneg h2 h1]

lemma l13_sp_mono {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q Q' : Pi → ℝ) (μ : ℝ)
    (hQ : ∀ π, Q π ≤ Q' π) (hμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    smoothProj Pi Q μ x a ≤ smoothProj Pi Q' μ x a := by
  unfold smoothProj
  have h2 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  have := Finset.sum_le_sum (s := Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a))
    (fun π _ => hQ π)
  nlinarith [mul_le_mul_of_nonneg_left this h2]

lemma l13_complete_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (πbar : Pi)
    (hs : ∑ π, Q π ≤ 1) (π : Pi) : Q π ≤ complete Pi Q πbar π := by
  classical
  unfold complete
  split_ifs <;> linarith

lemma l13_complete_nonneg {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (πbar : Pi) (hQ : ∀ π, 0 ≤ Q π) (hs : ∑ π, Q π ≤ 1) (π : Pi) :
    0 ≤ complete Pi Q πbar π :=
  le_trans (hQ π) (l13_complete_ge Pi Q πbar hs π)

lemma l13_complete_sum {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (πbar : Pi) : ∑ π, complete Pi Q πbar π = 1 := by
  classical
  unfold complete
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma l13_Vpop_le {X : Type*} [MeasurableSpace X] {K : ℕ} (ν : Measure X)
    [IsProbabilityMeasure ν] (Pi : Finset (X → Fin K)) (P : Pi → ℝ) (π : X → Fin K) (μ : ℝ)
    (hμ : 0 < μ) (hsp : ∀ x a, μ ≤ smoothProj Pi P μ x a) :
    Vpop ν Pi P π μ ≤ 1 / μ := by
  unfold Vpop
  have h := integral_mono_of_nonneg (μ := ν)
    (f := fun x => 1 / smoothProj Pi P μ x (π x)) (g := fun _ => 1 / μ)
    (ae_of_all _ (fun x => by
      have := lt_of_lt_of_le hμ (hsp x (π x))
      show (0 : ℝ) ≤ 1 / smoothProj Pi P μ x (π x)
      positivity))
    (integrable_const _)
    (ae_of_all _ (fun x => one_div_le_one_div_of_le hμ (hsp x (π x))))
  simpa using h

/-- Lemma 12 (calV_le, our proof 1282970b) from part (13) only. -/
lemma l13_lemma12 {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (h13 : Ev13 A D Z ω)
    (π : A.Pi) (m : ℕ) :
    Vpop (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
      if muM A.Pi A.δ A.τ m = 1 / (2 * (K : ℝ)) then 2 * (K : ℝ)
      else theta1 * (K : ℝ)
        + estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K)
          / (theta2 * muM A.Pi A.δ A.τ m) := by
  have : IsProbabilityMeasure (D.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  set H := A.history Z U ω (A.τ m) with hH
  have hHlen : H.length = A.τ m := l13_hist_len A Z U ω _
  set μ := muM A.Pi A.δ A.τ m with hμdef
  by_cases hm0 : m = 0
  · have hμ : μ = 1 / (2 * (K : ℝ)) := by rw [hμdef, hm0]; simp [muM]
    rw [if_pos hμ]
    have hQ : A.Qtilde Z U ω m = complete A.Pi (fun _ => 0) (A.pick H) := by
      simp [AlgoParams.Qtilde, AlgoParams.weights, hm0, hH]
      rfl
    have hμpos : 0 < μ := by rw [hμ]; positivity
    have hKμ : (K : ℝ) * μ ≤ 1 := by
      rw [hμ]; field_simp; linarith
    have hnn : ∀ π', 0 ≤ A.Qtilde Z U ω m π' := by
      intro π'; rw [hQ]
      exact l13_complete_nonneg _ _ _ (fun _ => le_refl _) (by simp) π'
    have := l13_Vpop_le (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ hμpos
      (l13_sp_ge A.Pi _ μ hnn hKμ)
    calc _ ≤ 1 / μ := this
      _ = 2 * (K : ℝ) := by rw [hμ]; field_simp
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hOP : IsOPSolution A.Pi μ H (A.sel m H) := hsel m hm1 H hHlen
    obtain ⟨hQnn, hQs, -, hQv⟩ := hOP
    have hQ : A.Qtilde Z U ω m = complete A.Pi (A.sel m H) (A.pick H) := by
      simp [AlgoParams.Qtilde, AlgoParams.weights, hm0, hH]
    have hτpos : 0 < A.τ m := by
      have := hτ (Nat.pos_of_ne_zero hm0); omega
    have hτR : (0 : ℝ) < (A.τ m : ℝ) := by exact_mod_cast hτpos
    have hcard : (1 : ℝ) ≤ (A.Pi.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hPi
    have hd : 0 < dT A.Pi A.δ (A.τ m) := by
      unfold dT
      apply Real.log_pos
      rw [lt_div_iff₀ hδ0]
      have : (1 : ℝ) ≤ (A.τ m : ℝ) := by exact_mod_cast hτpos
      nlinarith [mul_le_mul this this zero_le_one (by linarith)]
    have hμeq : μ = min (1 / (2 * (K : ℝ)))
        (Real.sqrt (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)))) := by
      rw [hμdef]; simp [muM, hm0]
    have hμpos : 0 < μ := by
      rw [hμeq]
      exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
    have hμle : μ ≤ 1 / (2 * (K : ℝ)) := by rw [hμeq]; exact min_le_left _ _
    have hKμ : (K : ℝ) * μ ≤ 1 := by
      have : (K : ℝ) * μ ≤ (K : ℝ) * (1 / (2 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hμle hK.le
      have e : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by field_simp
      linarith
    have hnn : ∀ π', 0 ≤ A.Qtilde Z U ω m π' := by
      intro π'; rw [hQ]
      exact l13_complete_nonneg _ _ _ hQnn hQs π'
    split_ifs with hc
    · have := l13_Vpop_le (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ hμpos
        (l13_sp_ge A.Pi _ μ hnn hKμ)
      calc _ ≤ 1 / μ := this
        _ = 2 * (K : ℝ) := by rw [hc]; field_simp
    · have hlt : μ < 1 / (2 * (K : ℝ)) := lt_of_le_of_ne hμle hc
      have hsq : Real.sqrt (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)))
          < 1 / (2 * (K : ℝ)) := by
        rw [hμeq] at hlt
        rcases min_lt_iff.mp hlt with h | h
        · exact absurd h (lt_irrefl _)
        · exact h
      have h2 := Real.lt_sq_of_sqrt_lt hsq
      rw [div_lt_iff₀ (by positivity)] at h2
      have e : (1 / (2 * (K : ℝ))) ^ 2 * ((K : ℝ) * (A.τ m : ℝ)) * (4 * (K : ℝ))
          = (A.τ m : ℝ) := by field_simp; ring
      have h4 : 4 * (K : ℝ) * dT A.Pi A.δ (A.τ m) ≤ (A.τ m : ℝ) := by
        nlinarith [mul_lt_mul_of_pos_right h2 (by positivity : (0 : ℝ) < 4 * (K : ℝ))]
      have h13' := h13 (A.Qtilde Z U ω m) hnn (by rw [hQ]; exact l13_complete_sum _ _ _)
        π m hm1 h4
      have hV : Vhat A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ (fun i => (Z i ω).1) (A.τ m)
          ≤ empAvg H (fun x => 1 / smoothProj A.Pi (A.sel m H) μ x ((π : X → Fin K) x)) := by
        unfold Vhat empAvg
        rw [l13_hist_sum A Z U ω (fun x => 1 / smoothProj A.Pi (A.sel m H) μ x
          ((π : X → Fin K) x)) (A.τ m), hHlen]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le
        · exact lt_of_lt_of_le hμpos (l13_sp_ge A.Pi _ μ hQnn hKμ _ _)
        · rw [hQ]
          exact l13_sp_mono A.Pi _ _ μ (l13_complete_ge A.Pi _ _ hQs) hKμ _ _
      have h3 := hQv π
      have eθ : 64 / 10 * (estRegret A.Pi H (π : X → Fin K) / (psi * μ))
          = estRegret A.Pi H (π : X → Fin K) / (theta2 * μ) := by
        unfold theta2 psi; field_simp
      have eθ1 : theta1 = 941 / 10 := rfl
      rw [eθ1]
      nlinarith [h13', hV, h3, eθ]

/-! ### Facts on `d_t`, `μ_m`, `m₀`, `ρ` -/

lemma l13_dT_pos {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {t : ℕ} (ht : 1 ≤ t) : 0 < dT Pi δ t := by
  have hcard : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPi
  unfold dT
  apply Real.log_pos
  rw [lt_div_iff₀ hδ0]
  have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  nlinarith [mul_le_mul this this zero_le_one (by linarith)]

lemma l13_dT_mono {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty)
    {δ : ℝ} (hδ0 : 0 < δ) {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) : dT Pi δ s ≤ dT Pi δ t := by
  have hcard : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPi
  unfold dT
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hpos : 0 < 16 * (s : ℝ) ^ 2 * Pi.card :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) (by linarith)
  apply Real.log_le_log (div_pos hpos hδ0)
  gcongr

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

lemma l13_mu_sqrt (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) :
    muM Pi δ τ m ≤ Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))) := by
  unfold muM
  rw [if_neg (by omega)]
  exact min_le_right _ _

lemma l13_mu_pos (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (m : ℕ) :
    0 < muM Pi δ τ m := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  unfold muM
  split_ifs with h
  · positivity
  · have hτpos : 0 < τ m := by have := hτ (Nat.pos_of_ne_zero h); omega
    have hτR : (0 : ℝ) < (τ m : ℝ) := by exact_mod_cast hτpos
    have hd := l13_dT_pos Pi hPi hδ0 hδ1 (t := τ m) hτpos
    exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))

/-- For `m ≥ m₀`: `4K d_{τ_m} ≤ τ_m`. -/
lemma l13_large (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (hm0 : 2 ≤ m0 Pi δ τ)
    {m : ℕ} (hm : m0 Pi δ τ ≤ m) :
    1 ≤ m ∧ 0 < (τ m : ℝ) ∧ 4 * (K : ℝ) * dT Pi δ (τ m) ≤ (τ m : ℝ) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hne : ({m : ℕ | 1 ≤ m ∧ dT Pi δ (τ m) / (τ m : ℝ) ≤ 1 / (4 * (K : ℝ))} : Set ℕ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : m0 Pi δ τ = 0 := by unfold m0; rw [hemp]; exact Nat.sInf_empty
    omega
  have hmem := Nat.sInf_mem hne
  change 1 ≤ m0 Pi δ τ ∧ dT Pi δ (τ (m0 Pi δ τ)) / (τ (m0 Pi δ τ) : ℝ) ≤ 1 / (4 * (K : ℝ)) at hmem
  obtain ⟨h1, hr⟩ := hmem
  have hτ1 : 1 ≤ τ (m0 Pi δ τ) := by have := hτ (show 0 < m0 Pi δ τ by omega); omega
  have hτmono : τ (m0 Pi δ τ) ≤ τ m := hτ.monotone hm
  have hratio := l13_dT_ratio Pi hPi hδ0 hδ1 hτ1 hτmono
  have hτpos : (0 : ℝ) < (τ m : ℝ) := by
    have : (1 : ℝ) ≤ (τ (m0 Pi δ τ) : ℝ) := by exact_mod_cast hτ1
    have : (τ (m0 Pi δ τ) : ℝ) ≤ (τ m : ℝ) := by exact_mod_cast hτmono
    linarith
  refine ⟨by omega, hτpos, ?_⟩
  have h := le_trans hratio hr
  rw [div_le_div_iff₀ hτpos (by positivity)] at h
  linarith

lemma l13_mu_eq (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (hm0 : 2 ≤ m0 Pi δ τ)
    {m : ℕ} (hm : m0 Pi δ τ ≤ m) :
    muM Pi δ τ m = Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  obtain ⟨h1, hτpos, h4⟩ := l13_large Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm
  unfold muM
  rw [if_neg (by omega)]
  apply min_eq_right
  have hsq : dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ)) ≤ (1 / (2 * (K : ℝ))) ^ 2 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ)))
      ≤ Real.sqrt ((1 / (2 * (K : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 / (2 * (K : ℝ)) := Real.sqrt_sq (by positivity)

/-- For `m ≥ m₀`: `d_{τ_m}/τ_m = K μ_m²`. -/
lemma l13_d_over_t (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (hm0 : 2 ≤ m0 Pi δ τ)
    {m : ℕ} (hm : m0 Pi δ τ ≤ m) :
    dT Pi δ (τ m) / (τ m : ℝ) = (K : ℝ) * muM Pi δ τ m ^ 2 := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  obtain ⟨h1, hτpos, h4⟩ := l13_large Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm
  have hd := l13_dT_pos Pi hPi hδ0 hδ1 (t := τ m) (by exact_mod_cast hτpos)
  rw [l13_mu_eq Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm, Real.sq_sqrt (by positivity)]
  field_simp

lemma l13_mu_small (Pi : Finset (X → Fin K)) {δ : ℝ} {τ : ℕ → ℕ} {m : ℕ}
    (hm : m < m0 Pi δ τ) : muM Pi δ τ m = 1 / (2 * (K : ℝ)) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  unfold muM
  split_ifs with h0
  · rfl
  · apply min_eq_left
    have hnot := Nat.notMem_of_lt_sInf hm
    simp only [Set.mem_setOf_eq, not_and, not_le] at hnot
    have hlt := hnot (by omega)
    have hτpos : 0 < (τ m : ℝ) := by
      rcases (Nat.cast_nonneg (τ m) : (0 : ℝ) ≤ _).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hlt
        have : 0 < 1 / (4 * (K : ℝ)) := by positivity
        linarith
    rw [div_lt_div_iff₀ (by positivity) hτpos] at hlt
    have hsq : (1 / (2 * (K : ℝ))) ^ 2 ≤ dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ)) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hlt hK]
    calc 1 / (2 * (K : ℝ)) = Real.sqrt ((1 / (2 * (K : ℝ))) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq

lemma l13_m0_le_of_ne (Pi : Finset (X → Fin K)) {δ : ℝ} {τ : ℕ → ℕ} {m : ℕ}
    (h : muM Pi δ τ m ≠ 1 / (2 * (K : ℝ))) : m0 Pi δ τ ≤ m := by
  by_contra hlt
  exact h (l13_mu_small Pi (by omega))

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

lemma l13_rho (Pi : Finset (X → Fin K)) {δ : ℝ} {τ : ℕ → ℕ} (hτ0 : τ 0 = 0)
    (hτ : StrictMono τ) (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) (hm0 : 2 ≤ m0 Pi δ τ) :
    1 ≤ rho Pi δ τ ∧ rho Pi δ τ ≤ Real.sqrt 2 ∧
      ∀ m, m0 Pi δ τ ≤ m → Real.sqrt ((τ m : ℝ) / (τ (m - 1) : ℝ)) ≤ rho Pi δ τ := by
  have hterm : ∀ m, m0 Pi δ τ ≤ m →
      1 ≤ Real.sqrt ((τ m : ℝ) / (τ (m - 1) : ℝ)) ∧
        Real.sqrt ((τ m : ℝ) / (τ (m - 1) : ℝ)) ≤ Real.sqrt 2 := by
    intro m hm
    have hpos : 0 < τ (m - 1) := by have := hτ (show 0 < m - 1 by omega); omega
    have hposR : (0 : ℝ) < (τ (m - 1) : ℝ) := by exact_mod_cast hpos
    have hle : τ (m - 1) ≤ τ m := hτ.monotone (by omega)
    have h2 : τ m ≤ 2 * τ (m - 1) := by
      have := hτ2 (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this
    have hleR : (τ (m - 1) : ℝ) ≤ (τ m : ℝ) := by exact_mod_cast hle
    have h2R : (τ m : ℝ) ≤ 2 * (τ (m - 1) : ℝ) := by exact_mod_cast h2
    constructor
    · rw [Real.one_le_sqrt, le_div_iff₀ hposR]; linarith
    · apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hposR]; linarith
  have hbdd : BddAbove (Set.range (fun m : {m : ℕ // m0 Pi δ τ ≤ m} =>
      Real.sqrt ((τ m.1 : ℝ) / (τ (m.1 - 1) : ℝ)))) := by
    refine ⟨Real.sqrt 2, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact (hterm m.1 m.2).2
  have hle : ∀ m, m0 Pi δ τ ≤ m → Real.sqrt ((τ m : ℝ) / (τ (m - 1) : ℝ)) ≤ rho Pi δ τ :=
    fun m hm => le_ciSup (f := fun m : {m : ℕ // m0 Pi δ τ ≤ m} =>
      Real.sqrt ((τ m.1 : ℝ) / (τ (m.1 - 1) : ℝ))) hbdd ⟨m, hm⟩
  refine ⟨le_trans (hterm _ le_rfl).1 (hle _ le_rfl), ?_, hle⟩
  have : Nonempty {m : ℕ // m0 Pi δ τ ≤ m} := ⟨⟨m0 Pi δ τ, le_rfl⟩⟩
  exact ciSup_le (fun m => (hterm m.1 m.2).2)

/-- For `m ≥ m₀`: `μ_{m−1} ≤ ρ μ_m`. -/
lemma l13_mu_prev_le (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) (hm0 : 2 ≤ m0 Pi δ τ)
    {m : ℕ} (hm : m0 Pi δ τ ≤ m) :
    muM Pi δ τ (m - 1) ≤ rho Pi δ τ * muM Pi δ τ m := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  obtain ⟨h1, hτpos, h4⟩ := l13_large Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm
  have hpos : 0 < τ (m - 1) := by have := hτ (show 0 < m - 1 by omega); omega
  have hposR : (0 : ℝ) < (τ (m - 1) : ℝ) := by exact_mod_cast hpos
  have hle : τ (m - 1) ≤ τ m := hτ.monotone (by omega)
  have hd1 := l13_dT_mono Pi hPi hδ0 (s := τ (m - 1)) (t := τ m) hpos hle
  have hdpos := l13_dT_pos Pi hPi hδ0 hδ1 (t := τ (m - 1)) hpos
  obtain ⟨-, -, hρ⟩ := l13_rho Pi hτ0 hτ hτ2 hm0
  calc muM Pi δ τ (m - 1)
      ≤ Real.sqrt (dT Pi δ (τ (m - 1)) / ((K : ℝ) * (τ (m - 1) : ℝ))) :=
        l13_mu_sqrt Pi δ τ (by omega)
    _ ≤ Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ (m - 1) : ℝ))) := by
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_right hd1 (by positivity)
    _ = Real.sqrt ((τ m : ℝ) / (τ (m - 1) : ℝ)) *
          Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ rho Pi δ τ * muM Pi δ τ m := by
        rw [← l13_mu_eq Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm]
        exact mul_le_mul_of_nonneg_right (hρ m hm) (l13_mu_pos Pi hPi hδ0 hδ1 hτ0 hτ m).le

end Params

section Main

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

lemma l13_polRegret_facts (A : AlgoParams X K) (hPi : A.Pi.Nonempty)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ πs : A.Pi, ∀ π : A.Pi, expReward D (π : X → Fin K) ≤ expReward D (πs : X → Fin K) ∧
      polRegret A.Pi D (π : X → Fin K) = expReward D (πs : X → Fin K) - expReward D π ∧
      0 ≤ polRegret A.Pi D (π : X → Fin K) ∧ polRegret A.Pi D (π : X → Fin K) ≤ 1 := by
  have : Nonempty A.Pi := ⟨⟨_, hPi.choose_spec⟩⟩
  obtain ⟨πs, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun π : A.Pi => expReward D (π : X → Fin K)) Finset.univ_nonempty
  have hsup : (⨆ π' : A.Pi, expReward D (π' : X → Fin K)) = expReward D (πs : X → Fin K) :=
    le_antisymm (ciSup_le (fun π => hmax π (Finset.mem_univ _)))
      (le_ciSup (f := fun π' : A.Pi => expReward D (π' : X → Fin K))
        (Set.finite_range _).bddAbove πs)
  refine ⟨πs, fun π => ?_⟩
  have h1 := hmax π (Finset.mem_univ _)
  have hR := l13_expReward_mem D hD (π : X → Fin K)
  have hRs := l13_expReward_mem D hD (πs : X → Fin K)
  have he : polRegret A.Pi D (π : X → Fin K) = expReward D (πs : X → Fin K) - expReward D π := by
    unfold polRegret; rw [hsup]
  refine ⟨h1, he, ?_, ?_⟩ <;> rw [he] <;> linarith

lemma l13_estRegret_facts (A : AlgoParams X K) (hPi : A.Pi.Nonempty)
    (hpick : A.PickIsArgmax) (h : List (Rec X K)) (π : A.Pi) :
    estRegret A.Pi h (π : X → Fin K) =
        ipsEst h ((A.pick h : A.Pi) : X → Fin K) - ipsEst h (π : X → Fin K) ∧
      0 ≤ estRegret A.Pi h (π : X → Fin K) := by
  have : Nonempty A.Pi := ⟨⟨_, hPi.choose_spec⟩⟩
  have hsup : (⨆ π' : A.Pi, ipsEst h (π' : X → Fin K)) = ipsEst h ((A.pick h : A.Pi) : X → Fin K) :=
    le_antisymm (ciSup_le (fun π' => hpick h π'))
      (le_ciSup (f := fun π' : A.Pi => ipsEst h (π' : X → Fin K))
        (Set.finite_range _).bddAbove (A.pick h))
  have he : estRegret A.Pi h (π : X → Fin K) =
      ipsEst h ((A.pick h : A.Pi) : X → Fin K) - ipsEst h (π : X → Fin K) := by
    unfold estRegret; rw [hsup]
  refine ⟨he, ?_⟩
  rw [he]; linarith [hpick h π]

lemma l13_Qtilde_prob (A : AlgoParams X K) (hsel : A.SelSolvesOP) {Ω : Type*}
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (j : ℕ) :
    (∀ π, 0 ≤ A.Qtilde Z U ω j π) ∧ ∑ π, A.Qtilde Z U ω j π = 1 := by
  have hQ : (∀ π, 0 ≤ A.weights j (A.history Z U ω (A.τ j)) π) ∧
      ∑ π, A.weights j (A.history Z U ω (A.τ j)) π ≤ 1 := by
    by_cases hj : j = 0
    · simp [AlgoParams.weights, hj]
    · have hop := hsel j (by omega) _ (l13_hist_len A Z U ω (A.τ j))
      simp only [AlgoParams.weights, hj, if_false]
      exact ⟨hop.1, hop.2.1⟩
  exact ⟨fun π => l13_complete_nonneg _ _ _ hQ.1 hQ.2 π, l13_complete_sum _ _ _⟩

lemma l13_epochOf_tau {τ : ℕ → ℕ} (hτ : StrictMono τ) (m : ℕ) : epochOf τ (τ m) = m := by
  unfold epochOf
  apply le_antisymm (Nat.sInf_le (show m ∈ {k : ℕ | τ m ≤ τ k} from le_refl (τ m)))
  apply le_csInf ⟨m, le_refl (τ m)⟩
  intro k hk
  exact hτ.le_iff_le.mp hk

/-- Lemma 13 (both inequalities) at the epoch ends `t = τ_m`, `m ≥ m₀`, on the event
`(13) ∧ (Lemma 11 with λ = μ)`. -/
theorem l13_lemma13 (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (h13 : Ev13 A D Z ω) (h14 : Ev14 A D Z U ω) :
    ∀ m, m0 A.Pi A.δ A.τ ≤ m → ∀ π : A.Pi,
      polRegret A.Pi D (π : X → Fin K) ≤
          2 * estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K)
            + c0 A.Pi A.δ A.τ * (K : ℝ) * muM A.Pi A.δ A.τ m ∧
        estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K) ≤
          2 * polRegret A.Pi D (π : X → Fin K)
            + c0 A.Pi A.δ A.τ * (K : ℝ) * muM A.Pi A.δ A.τ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  obtain ⟨hm1, hτpos, h4⟩ := l13_large A.Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm
  obtain ⟨hρ1, hρ2, -⟩ := l13_rho A.Pi hτ0 hτ hτ2 hm0
  obtain ⟨πs, hRg⟩ := l13_polRegret_facts A hPi D hD
  have hμpos : 0 < muM A.Pi A.δ A.τ (m - 1) := l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ _
  have hνpos : 0 < muM A.Pi A.δ A.τ m := l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ _
  have hνμ : muM A.Pi A.δ A.τ m ≤ muM A.Pi A.δ A.τ (m - 1) :=
    l13_mu_anti A.Pi hPi hδ0 hδ1 hτ0 hτ (by omega)
  have hμρ : muM A.Pi A.δ A.τ (m - 1) ≤ rho A.Pi A.δ A.τ * muM A.Pi A.δ A.τ m :=
    l13_mu_prev_le A.Pi hPi hδ0 hδ1 hτ0 hτ hτ2 hm0 hm
  have hdt : dT A.Pi A.δ (A.τ m) / (A.τ m : ℝ) = (K : ℝ) * muM A.Pi A.δ A.τ m ^ 2 :=
    l13_d_over_t A.Pi hPi hδ0 hδ1 hτ0 hτ hm0 hm
  have hep : epochOf A.τ (A.τ m) = m := l13_epochOf_tau hτ m
  have eθ1 : theta1 = 941 / 10 := rfl
  have eθ2 : theta2 = 125 / 8 := by unfold theta2 psi; norm_num
  have ec0 : c0 A.Pi A.δ A.τ = 4 * rho A.Pi A.δ A.τ * (1 + 941 / 10) := rfl
  set μ := muM A.Pi A.δ A.τ (m - 1) with hμ
  set ν := muM A.Pi A.δ A.τ m with hν
  set ρ := rho A.Pi A.δ A.τ with hρ
  set H := A.history Z U ω (A.τ m) with hH
  have hρK : 0 ≤ ρ * (K : ℝ) := mul_nonneg (by linarith) hK.le
  -- the variance bound
  have hV : ∀ π : A.Pi, A.calV (D.map Prod.fst) Z U ω (A.τ m) (π : X → Fin K) ≤
      941 / 10 * (K : ℝ) + 15216 / 625 * ρ * (K : ℝ)
        + 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * μ) := by
    intro π
    have hR0 := (hRg π).2.2.1
    have hfrac : 0 ≤ 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * μ) :=
      div_nonneg (by linarith) (by positivity)
    unfold AlgoParams.calV
    split_ifs with hpos
    · apply Finset.sup'_le
      intro m' hm'
      rw [Finset.mem_range, hep] at hm'
      have hb := l13_lemma12 A hPi hδ0 hδ1 hτ0 hτ hsel D Z U ω h13 π m'
      split_ifs at hb with hc
      · linarith
      · have hm0' := l13_m0_le_of_ne A.Pi hc
        have hih := (ih m' hm' hm0' π).2
        rw [ec0] at hih
        rw [eθ1, eθ2] at hb
        have hμ'pos : 0 < muM A.Pi A.δ A.τ m' := l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ _
        have hμμ' : μ ≤ muM A.Pi A.δ A.τ m' := l13_mu_anti A.Pi hPi hδ0 hδ1 hτ0 hτ (by omega)
        have s1 : estRegret A.Pi (A.history Z U ω (A.τ m')) (π : X → Fin K)
              / (125 / 8 * muM A.Pi A.δ A.τ m')
            ≤ (2 * polRegret A.Pi D (π : X → Fin K)
                + 4 * ρ * (1 + 941 / 10) * (K : ℝ) * muM A.Pi A.δ A.τ m')
              / (125 / 8 * muM A.Pi A.δ A.τ m') :=
          div_le_div_of_nonneg_right hih (by positivity)
        have s2 : (2 * polRegret A.Pi D (π : X → Fin K)
                + 4 * ρ * (1 + 941 / 10) * (K : ℝ) * muM A.Pi A.δ A.τ m')
              / (125 / 8 * muM A.Pi A.δ A.τ m')
            = 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * muM A.Pi A.δ A.τ m')
              + 15216 / 625 * ρ * (K : ℝ) := by
          field_simp; ring
        have s3 : 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * muM A.Pi A.δ A.τ m')
            ≤ 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * μ) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
        linarith
    · positivity
  -- the deviation bound
  have hΔ : ∀ π : A.Pi, |ipsEst H (π : X → Fin K) - expReward D (π : X → Fin K)| ≤
      ((941 / 10 + 15216 / 625 * ρ) * ρ + 1) * ((K : ℝ) * ν)
        + 16 / 125 * polRegret A.Pi D (π : X → Fin K) := by
    intro π
    have h := h14 π m hm1 (A.τ m) (hτ (by omega)) le_rfl
    have hcv := hV π
    have e1 : A.calV (D.map Prod.fst) Z U ω (A.τ m) (π : X → Fin K) * μ ≤
        (941 / 10 + 15216 / 625 * ρ) * (K : ℝ) * (ρ * ν)
          + 16 / 125 * polRegret A.Pi D (π : X → Fin K) := by
      calc A.calV (D.map Prod.fst) Z U ω (A.τ m) (π : X → Fin K) * μ
          ≤ (941 / 10 * (K : ℝ) + 15216 / 625 * ρ * (K : ℝ)
              + 2 * polRegret A.Pi D (π : X → Fin K) / (125 / 8 * μ)) * μ :=
            mul_le_mul_of_nonneg_right hcv hμpos.le
        _ = (941 / 10 + 15216 / 625 * ρ) * (K : ℝ) * μ
              + 16 / 125 * polRegret A.Pi D (π : X → Fin K) := by
            field_simp; ring
        _ ≤ (941 / 10 + 15216 / 625 * ρ) * (K : ℝ) * (ρ * ν)
              + 16 / 125 * polRegret A.Pi D (π : X → Fin K) := by
            have hco : 0 ≤ (941 / 10 + 15216 / 625 * ρ) * (K : ℝ) :=
              mul_nonneg (by linarith) hK.le
            linarith [mul_le_mul_of_nonneg_left hμρ hco]
    have e4 : dT A.Pi A.δ (A.τ m) / ((A.τ m : ℝ) * μ) ≤ (K : ℝ) * ν := by
      rw [← div_div, hdt, div_le_iff₀ hμpos]
      nlinarith [mul_le_mul_of_nonneg_left hνμ (le_of_lt (mul_pos hK hνpos))]
    calc |ipsEst H (π : X → Fin K) - expReward D (π : X → Fin K)|
        ≤ A.calV (D.map Prod.fst) Z U ω (A.τ m) (π : X → Fin K) * μ
          + dT A.Pi A.δ (A.τ m) / ((A.τ m : ℝ) * μ) := h
      _ ≤ (941 / 10 + 15216 / 625 * ρ) * (K : ℝ) * (ρ * ν)
          + 16 / 125 * polRegret A.Pi D (π : X → Fin K) + (K : ℝ) * ν := add_le_add e1 e4
      _ = _ := by ring
  -- the numerical condition
  have hρsq : ρ ^ 2 ≤ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hkey : 2 * ((941 / 10 + 15216 / 625 * ρ) * ρ + 1) ≤ 109 / 125 * (4 * ρ * (1 + 941 / 10)) := by
    nlinarith
  have hw : 0 ≤ (K : ℝ) * ν := (mul_pos hK hνpos).le
  have hkeyw := mul_le_mul_of_nonneg_right hkey hw
  intro π
  rw [ec0, show 4 * ρ * (1 + 941 / 10) * (K : ℝ) * ν = 4 * ρ * (1 + 941 / 10) * ((K : ℝ) * ν) by ring]
  set πt := A.pick H with hπt
  obtain ⟨hEg, hEg0⟩ := l13_estRegret_facts A hPi hpick H π
  have hpk := hpick H πs
  obtain ⟨-, hRgπ, hRgπ0, -⟩ := hRg π
  obtain ⟨-, hRgs, -, -⟩ := hRg πs
  obtain ⟨hlt, hRgt, hRgt0, -⟩ := hRg πt
  have hΔπ := abs_le.mp (hΔ π)
  have hΔs := abs_le.mp (hΔ πs)
  have hΔt := abs_le.mp (hΔ πt)
  rw [hRgs, sub_self] at hΔs
  constructor
  · rw [hRgπ] at hΔπ ⊢
    rw [hEg]
    linarith
  · rw [hRgπ] at hΔπ ⊢
    rw [hRgt] at hΔt
    rw [hEg]
    linarith

/-- Lemma 14 on the event `(13) ∧ (Lemma 11 with λ = μ)`. -/
theorem l13_lemma14 (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (h13 : Ev13 A D Z ω) (h14 : Ev14 A D Z U ω)
    (m : ℕ) (hm : 1 ≤ m) :
    ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * polRegret A.Pi D (π : X → Fin K) ≤
      (4 * psi + c0 A.Pi A.δ A.τ) * (K : ℝ) * muM A.Pi A.δ A.τ (m - 1) := by
  classical
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  obtain ⟨πs, hRg⟩ := l13_polRegret_facts A hPi D hD
  obtain ⟨hρ1, -, -⟩ := l13_rho A.Pi hτ0 hτ hτ2 hm0
  have ec0 : c0 A.Pi A.δ A.τ = 4 * rho A.Pi A.δ A.τ * (1 + 941 / 10) := rfl
  have hc0 : 0 ≤ c0 A.Pi A.δ A.τ := by rw [ec0]; nlinarith
  have epsi : psi = 100 := rfl
  by_cases hjm : m - 1 < m0 A.Pi A.δ A.τ
  · have hμ := l13_mu_small A.Pi hjm
    obtain ⟨hQnn, hQs⟩ := l13_Qtilde_prob A hsel Z U ω (m - 1)
    calc ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * polRegret A.Pi D (π : X → Fin K)
        ≤ ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * 1 :=
          Finset.sum_le_sum (fun π _ => mul_le_mul_of_nonneg_left (hRg π).2.2.2 (hQnn π))
      _ = 1 := by simp only [mul_one]; exact hQs
      _ ≤ (4 * psi + c0 A.Pi A.δ A.τ) * (K : ℝ) * muM A.Pi A.δ A.τ (m - 1) := by
          rw [hμ, epsi]
          have e : (4 * 100 + c0 A.Pi A.δ A.τ) * (K : ℝ) * (1 / (2 * (K : ℝ)))
              = (4 * 100 + c0 A.Pi A.δ A.τ) / 2 := by field_simp
          rw [e]; linarith
  · push Not at hjm
    have hj0 : m - 1 ≠ 0 := by omega
    have hL := l13_lemma13 A hPi hδ0 hδ1 hτ0 hτ hτ2 hm0 hpick hsel D hD Z U ω h13 h14 (m - 1) hjm
    set H := A.history Z U ω (A.τ (m - 1)) with hH
    set ν := muM A.Pi A.δ A.τ (m - 1) with hν
    have hνpos : 0 < ν := l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ _
    have hOP := hsel (m - 1) (by omega) H (l13_hist_len A Z U ω _)
    obtain ⟨hQnn, hQs, hQ2, -⟩ := hOP
    have hQt : A.Qtilde Z U ω (m - 1) = complete A.Pi (A.sel (m - 1) H) (A.pick H) := by
      simp [AlgoParams.Qtilde, AlgoParams.weights, hj0, hH]
    rw [hQt]
    unfold complete
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hE : ∑ π, A.sel (m - 1) H π * estRegret A.Pi H (π : X → Fin K) ≤ 2 * (K : ℝ) * (psi * ν) := by
      have e : ∑ π, A.sel (m - 1) H π * (estRegret A.Pi H (π : X → Fin K) / (psi * ν))
          = (∑ π, A.sel (m - 1) H π * estRegret A.Pi H (π : X → Fin K)) / (psi * ν) := by
        rw [Finset.sum_div]
        congr 1; ext π; ring
      rw [e, div_le_iff₀ (by rw [epsi]; positivity)] at hQ2
      linarith
    have h1 : ∑ π, A.sel (m - 1) H π * polRegret A.Pi D (π : X → Fin K)
        ≤ 2 * ∑ π, A.sel (m - 1) H π * estRegret A.Pi H (π : X → Fin K)
          + c0 A.Pi A.δ A.τ * (K : ℝ) * ν * ∑ π, A.sel (m - 1) H π := by
      calc ∑ π, A.sel (m - 1) H π * polRegret A.Pi D (π : X → Fin K)
          ≤ ∑ π, A.sel (m - 1) H π * (2 * estRegret A.Pi H (π : X → Fin K)
              + c0 A.Pi A.δ A.τ * (K : ℝ) * ν) :=
            Finset.sum_le_sum (fun π _ => mul_le_mul_of_nonneg_left (hL π).1 (hQnn π))
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            congr 1; ext π; ring
    have hbar := (hL (A.pick H)).1
    rw [(l13_estRegret_facts A hPi hpick H (A.pick H)).1, sub_self, mul_zero, zero_add] at hbar
    have h2 := mul_le_mul_of_nonneg_left hbar (show 0 ≤ 1 - ∑ π', A.sel (m - 1) H π' by linarith)
    rw [epsi] at hE ⊢
    nlinarith

end Main


/-! ### The event `(13) ∧ (14')` from Lemmas 10 and 11, and the assembly -/

lemma l13_mu_eq' {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K)) {δ : ℝ}
    {τ : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hτpos : 0 < (τ m : ℝ))
    (h4 : 4 * (K : ℝ) * dT Pi δ (τ m) ≤ (τ m : ℝ)) :
    muM Pi δ τ m = Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  unfold muM
  rw [if_neg (by omega)]
  apply min_eq_right
  have hsq : dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ)) ≤ (1 / (2 * (K : ℝ))) ^ 2 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ)))
      ≤ Real.sqrt ((1 / (2 * (K : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 / (2 * (K : ℝ)) := Real.sqrt_sq (by positivity)

/-- On the good event of Lemma 10 (applied with `x_t = (Z t).1`, `μ = μ_m`, failure `δ/4`),
part (13) holds. -/
lemma l13_ev13_of_good {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K) (hPi : A.Pi.Nonempty) (hδ0 : 0 < A.δ) (hτ : StrictMono A.τ)
    (D : Measure (X × (Fin K → ℝ))) {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (ω : Ω)
    (hgood : ∀ Q : A.Pi → ℝ, (∀ π, 0 ≤ Q π) → ∑ π, Q π = 1 → ∀ π : A.Pi, ∀ m : ℕ, 1 ≤ m →
        (Vpop (D.map Prod.fst) A.Pi Q (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
            64 / 10 * Vhat A.Pi Q (π : X → Fin K) (muM A.Pi A.δ A.τ m) (fun i => (Z i ω).1)
              (A.τ m)
            + 75 * (1 - (K : ℝ) * muM A.Pi A.δ A.τ m) * Real.log (A.Pi.card : ℝ)
              / (muM A.Pi A.δ A.τ m ^ 2 * (A.τ m : ℝ))
            + 63 / 10 * Real.log (2 * (A.Pi.card : ℝ) ^ 2 * (m : ℝ) ^ 2 / (A.δ / 4))
              / (muM A.Pi A.δ A.τ m * (A.τ m : ℝ)))
        ∧ (Real.sqrt (Real.log (2 * (A.Pi.card : ℝ) * (m : ℝ) ^ 2 / (A.δ / 4))
              / ((K : ℝ) * (A.τ m : ℝ))) ≤ muM A.Pi A.δ A.τ m →
            4 * (K : ℝ) * Real.log (2 * (A.Pi.card : ℝ) * (m : ℝ) ^ 2 / (A.δ / 4))
              ≤ (A.τ m : ℝ) →
            Vpop (D.map Prod.fst) A.Pi Q (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
              64 / 10 * Vhat A.Pi Q (π : X → Fin K) (muM A.Pi A.δ A.τ m) (fun i => (Z i ω).1)
                (A.τ m)
              + 813 / 10 * (K : ℝ))) :
    Ev13 A D Z ω := by
  intro Q hQ hs π m hm h4
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hcard : (1 : ℝ) ≤ (A.Pi.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPi
  have hmτ : m ≤ A.τ m := hτ.id_le m
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmτR : (m : ℝ) ≤ (A.τ m : ℝ) := by exact_mod_cast hmτ
  have hτpos : (0 : ℝ) < (A.τ m : ℝ) := by linarith
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos (by linarith) 2
  have hx : 0 < 2 * (A.Pi.card : ℝ) * (m : ℝ) ^ 2 / (A.δ / 4) :=
    div_pos (by nlinarith) (by linarith)
  have hL : Real.log (2 * (A.Pi.card : ℝ) * (m : ℝ) ^ 2 / (A.δ / 4)) ≤ dT A.Pi A.δ (A.τ m) := by
    unfold dT
    apply Real.log_le_log hx
    rw [div_le_div_iff₀ (by linarith) hδ0]
    have h1 : (m : ℝ) ^ 2 ≤ (A.τ m : ℝ) ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1
      (le_of_lt (mul_pos (by linarith : (0 : ℝ) < A.Pi.card) hδ0))
    have h3 : 0 ≤ (A.Pi.card : ℝ) * A.δ * (m : ℝ) ^ 2 := by positivity
    nlinarith
  apply (hgood Q hQ hs π m hm).2
  · rw [l13_mu_eq' A.Pi hm hτpos h4]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hL (by positivity))
  · nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 4 * K)]

/-- Off the bad event of Lemma 11 (with `λ_{m−1} = μ_{m−1}`, failure `δ/4`), (14') holds. -/
lemma l13_ev14_of_good {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K) (hδ0 : 0 < A.δ)
    (D : Measure (X × (Fin K → ℝ))) {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ))
    (U : ℕ → Ω → ℝ) (ω : Ω)
    (hgood : ω ∉ {ω | ∃ π : A.Pi, ∃ m : ℕ, 1 ≤ m ∧ ∃ t : ℕ, A.τ (m - 1) < t ∧ t ≤ A.τ m ∧
        A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * muM A.Pi A.δ A.τ (m - 1)
          + Real.log (4 * (t : ℝ) ^ 2 * (A.Pi.card : ℝ) / (A.δ / 4))
            / ((t : ℝ) * muM A.Pi A.δ A.τ (m - 1))
        < |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)|}) :
    Ev14 A D Z U ω := by
  intro π m hm t h1 h2
  by_contra hlt
  push Not at hlt
  have e : Real.log (4 * (t : ℝ) ^ 2 * (A.Pi.card : ℝ) / (A.δ / 4)) = dT A.Pi A.δ t := by
    unfold dT
    congr 1
    field_simp
    ring
  exact hgood ⟨π, m, hm, t, h1, h2, by rw [e]; exact hlt⟩

lemma l13_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B S1 S2 S3 : Set Ω)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsub : ∀ ω, ω ∉ S1 → ω ∉ S2 → ω ∉ S3 → ω ∉ B)
    (h1 : P S1 ≤ ENNReal.ofReal a) (h2 : P S2 ≤ ENNReal.ofReal b)
    (h3 : P S3 ≤ ENNReal.ofReal c) : P B ≤ ENNReal.ofReal (a + b + c) := by
  have hB : B ⊆ S1 ∪ S2 ∪ S3 := fun ω hω => by
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    exact hsub ω hn.1.1 hn.1.2 hn.2 hω
  calc P B ≤ P (S1 ∪ S2 ∪ S3) := measure_mono hB
    _ ≤ P (S1 ∪ S2) + P S3 := measure_union_le _ _
    _ ≤ P S1 + P S2 + P S3 := add_le_add_left (measure_union_le _ _) _
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c :=
        add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (a + b + c) := by
        rw [ENNReal.ofReal_add (by linarith) hc, ENNReal.ofReal_add ha hb]

end TamingMonster.Regret

open TamingMonster.Regret MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
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
    (πstar : A.Pi) (hstar : ∀ π : A.Pi, expReward D (π : X → Fin K) ≤ expReward D πstar)
    (T : ℕ) :
    P {ω | C0 A.Pi A.δ A.τ *
            (4 * (K : ℝ) * dT A.Pi A.δ (A.τ (m0 A.Pi A.δ A.τ - 1))
              + Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ (epochOf A.τ T))
                  * (A.τ (epochOf A.τ T) : ℝ)))
          + Real.sqrt (8 * (T : ℝ) * Real.log (2 / A.δ))
        < A.cumRegret Z U (πstar : X → Fin K) ω T} ≤ ENNReal.ofReal A.δ := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have : IsProbabilityMeasure (D.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hδ4 : 0 < A.δ / 4 := by linarith
  have hδ41 : A.δ / 4 < 1 := by linarith
  have h10 := variance_deviation A.Pi hPi hPiMeas (D.map Prod.fst) P (fun t ω => (Z t ω).1)
    (fun t => measurable_fst.comp (hZmeas t))
    (hindep.comp (fun _ p => p.1.1) (fun _ => measurable_fst.comp measurable_fst))
    (fun t => by rw [← hZlaw t, Measure.map_map measurable_fst (hZmeas t)]; rfl)
    A.τ hτ0 hτ (muM A.Pi A.δ A.τ)
    (fun m _ => ⟨l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ m,
      le_trans (l13_mu_le A.Pi A.δ A.τ m)
        (by rw [div_le_div_iff₀ (by positivity) hK]; linarith)⟩)
    (A.δ / 4) hδ4 hδ41
  have h11 := ips_deviation A hPi hPiMeas hδ0 hδ1 hτ0 hτ hpick hsel hrules D hD P Z U hZmeas
    hUmeas hindep hZU hZlaw hUlaw (A.δ / 4) hδ4 hδ41 (muM A.Pi A.δ A.τ)
    (fun j => ⟨l13_mu_pos A.Pi hPi hδ0 hδ1 hτ0 hτ j, le_rfl⟩)
  have h4 := azuma_regret A hPi hPiMeas hδ0 hδ1 hτ0 hτ hτ2 hpick hsel hrules D hD P Z U
    hZmeas hUmeas hindep hZU hZlaw hUlaw πstar hstar T
  have hlog : 0 ≤ Real.log (2 / A.δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hsq : Real.sqrt (2 * (T : ℝ) * Real.log (2 / A.δ))
      ≤ Real.sqrt (8 * (T : ℝ) * Real.log (2 / A.δ)) :=
    Real.sqrt_le_sqrt (by
      have : (0 : ℝ) ≤ T * Real.log (2 / A.δ) := mul_nonneg (Nat.cast_nonneg _) hlog
      nlinarith)
  refine (l13_three P _ _ _ _ hδ4.le hδ4.le (by linarith : (0 : ℝ) ≤ A.δ / 2) ?_ h10 h11 h4).trans
    (le_of_eq (congrArg ENNReal.ofReal (by ring)))
  intro ω g10 g11 gaz hbad
  have e13 : Ev13 A D Z ω := l13_ev13_of_good A hPi hδ0 hτ D Z ω (Classical.not_not.mp g10)
  have e14 : Ev14 A D Z U ω := l13_ev14_of_good A hδ0 D Z U ω g11
  have h3 := expected_regret_sum_le A hPi hδ0 hδ1 hτ0 hτ hτ2 hm0 D Z U ω
    (fun m hm => l13_lemma14 A hPi hδ0 hδ1 hτ0 hτ hτ2 hm0 hpick hsel D hD Z U ω e13 e14 m hm) T
  simp only [Set.mem_setOf_eq, not_lt] at hbad gaz
  linarith
