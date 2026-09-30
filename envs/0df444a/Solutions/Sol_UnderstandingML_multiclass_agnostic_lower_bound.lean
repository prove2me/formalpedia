-- Prove2me | solution 1 for UnderstandingML.multiclass_agnostic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T22:18:44.693012+00:00
-- url     : https://prove2.me/submissions/aa34922d-a08a-4f8c-930e-eb9540bc8241

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory UnderstandingML

universe u v

namespace AgnosticLowerAux

open Classical

section Generic

variable {K : Type*} [Fintype K] {Z : Type*} [MeasurableSpace Z]

/-- A finitely supported distribution with weights `w` on the points `z k`. -/
noncomputable def wdist (z : K → Z) (w : K → ℝ) : Measure Z :=
  ∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k)

lemma wdist_isProb (z : K → Z) {w : K → ℝ} (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    IsProbabilityMeasure (wdist z w) := by
  constructor
  simp only [wdist, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ hw k), hsum, ENNReal.ofReal_one]

variable [MeasurableSingletonClass Z]

lemma wdist_singleton {z : K → Z} (hz : Function.Injective z) (w : K → ℝ) (k : K) :
    wdist z w {z k} = ENNReal.ofReal (w k) := by
  simp only [wdist, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    have : z k' ∉ ({z k} : Set Z) := fun h ↦ hk' (hz h)
    simp [this]
  · simp

lemma integral_wdist (z : K → Z) {w : K → ℝ} (hw : ∀ k, 0 ≤ w k) (f : Z → ℝ)
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    ∫ x, f x ∂(wdist z w) = ∑ k, w k * f (z k) := by
  unfold wdist
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw k), smul_eq_mul]
  · intro k _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]; exact hb x

/-- The product law charges every finite sample pattern with the product of its weights. -/
lemma iid_ge_sum {z : K → Z} (hz : Function.Injective z) {w : K → ℝ} (hw : ∀ k, 0 ≤ w k)
    (m : ℕ)
    (E : Set (Fin m → Z)) :
    ∑ ω : Fin m → K, (if (fun j ↦ z (ω j)) ∈ E then ENNReal.ofReal (∏ j, w (ω j)) else 0) ≤
      iidLaw (wdist z w) m E := by
  set μ := iidLaw (wdist z w) m with hμ
  have : IsFiniteMeasure (wdist z w) := ⟨by
    simp only [wdist, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.sum_lt_top.2 fun k _ ↦ ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top _ _)⟩
  set S := (Finset.univ : Finset (Fin m → K)).filter (fun ω ↦ (fun j ↦ z (ω j)) ∈ E) with hS
  have hsing : ∀ ω : Fin m → K, μ {fun j ↦ z (ω j)} = ENNReal.ofReal (∏ j, w (ω j)) := by
    intro ω
    rw [← Set.univ_pi_singleton, hμ, iidLaw, Measure.pi_pi]
    simp only [wdist_singleton hz]
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hw _)]
  have hinj : Function.Injective (fun (ω : Fin m → K) (j : Fin m) ↦ z (ω j)) := by
    intro ω ω' h
    funext j
    exact hz (congrFun h j)
  calc ∑ ω : Fin m → K, (if (fun j ↦ z (ω j)) ∈ E then ENNReal.ofReal (∏ j, w (ω j)) else 0)
      = ∑ ω ∈ S, μ {fun j ↦ z (ω j)} := by
        rw [hS, Finset.sum_filter]
        exact Finset.sum_congr rfl fun ω _ ↦ by rw [hsing]
    _ = μ (⋃ ω ∈ S, {fun j ↦ z (ω j)}) := by
        rw [measure_biUnion_finset]
        · intro ω _ ω' _ hne
          simp only [Function.onFun, Set.disjoint_singleton]
          exact fun h ↦ hne (hinj h)
        · intro ω _; exact measurableSet_singleton _
    _ ≤ μ E := by
        apply measure_mono
        intro S' hS'
        simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hS'
        obtain ⟨ω, hω, rfl⟩ := hS'
        exact (Finset.mem_filter.1 hω).2

/-- Two-point testing bound, via the Bhattacharyya coefficient. -/
lemma testing_bound {p q : K → ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hps : ∑ k, p k = 1) (hqs : ∑ k, q k = 1) (m : ℕ) (E : (Fin m → K) → Prop) :
    (1 / 2) * (∑ k, Real.sqrt (p k * q k)) ^ (2 * m) ≤
      ∑ ω : Fin m → K, ((if E ω then ∏ j, p (ω j) else 0) +
        (if E ω then 0 else ∏ j, q (ω j))) := by
  set P : (Fin m → K) → ℝ := fun ω ↦ ∏ j, p (ω j) with hP
  set Q : (Fin m → K) → ℝ := fun ω ↦ ∏ j, q (ω j) with hQ
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω ↦ Finset.prod_nonneg fun j _ ↦ hp _
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω ↦ Finset.prod_nonneg fun j _ ↦ hq _
  have hPs : ∑ ω, P ω = 1 := by
    rw [hP, ← Fintype.prod_sum (fun (_ : Fin m) k ↦ p k)]; simp [hps]
  have hQs : ∑ ω, Q ω = 1 := by
    rw [hQ, ← Fintype.prod_sum (fun (_ : Fin m) k ↦ q k)]; simp [hqs]
  have hBC : ∑ ω, Real.sqrt (P ω * Q ω) = (∑ k, Real.sqrt (p k * q k)) ^ m := by
    have e : (∑ k, Real.sqrt (p k * q k)) ^ m = ∏ _j : Fin m, ∑ k, Real.sqrt (p k * q k) := by
      simp [Finset.prod_const]
    rw [e, Fintype.prod_sum (fun (_ : Fin m) k ↦ Real.sqrt (p k * q k))]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [hP, hQ, ← Finset.prod_mul_distrib, Real.sqrt_prod _ (fun j _ ↦ mul_nonneg (hp _) (hq _))]
  -- each term dominates the minimum
  have hterm : ∀ ω, min (P ω) (Q ω) ≤ (if E ω then P ω else 0) + (if E ω then 0 else Q ω) := by
    intro ω; split_ifs <;> simp
  -- Cauchy–Schwarz
  have hCS : (∑ ω, Real.sqrt (P ω * Q ω)) ^ 2 ≤
      (∑ ω, min (P ω) (Q ω)) * ∑ ω, max (P ω) (Q ω) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun ω ↦ Real.sqrt (min (P ω) (Q ω))) (fun ω ↦ Real.sqrt (max (P ω) (Q ω)))
    have e1 : ∀ ω, Real.sqrt (min (P ω) (Q ω)) * Real.sqrt (max (P ω) (Q ω)) =
        Real.sqrt (P ω * Q ω) := by
      intro ω
      rw [← Real.sqrt_mul (le_min (hP0 ω) (hQ0 ω)), min_mul_max]
    have e2 : ∀ ω, Real.sqrt (min (P ω) (Q ω)) ^ 2 = min (P ω) (Q ω) := fun ω ↦
      Real.sq_sqrt (le_min (hP0 ω) (hQ0 ω))
    have e3 : ∀ ω, Real.sqrt (max (P ω) (Q ω)) ^ 2 = max (P ω) (Q ω) := fun ω ↦
      Real.sq_sqrt (le_trans (hP0 ω) (le_max_left _ _))
    simp only [e1, e2, e3] at h
    exact h
  have hmax : ∑ ω, max (P ω) (Q ω) ≤ 2 := by
    calc ∑ ω, max (P ω) (Q ω) ≤ ∑ ω, (P ω + Q ω) :=
          Finset.sum_le_sum fun ω _ ↦ max_le_add_of_nonneg (hP0 ω) (hQ0 ω)
      _ = 2 := by rw [Finset.sum_add_distrib, hPs, hQs]; norm_num
  have hmin0 : 0 ≤ ∑ ω, min (P ω) (Q ω) :=
    Finset.sum_nonneg fun ω _ ↦ le_min (hP0 ω) (hQ0 ω)
  have key : (1 / 2) * (∑ k, Real.sqrt (p k * q k)) ^ (2 * m) ≤ ∑ ω, min (P ω) (Q ω) := by
    rw [pow_mul', ← hBC]
    nlinarith
  exact key.trans (Finset.sum_le_sum fun ω _ ↦ hterm ω)

lemma testing_bound_ennreal {p q : K → ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hps : ∑ k, p k = 1) (hqs : ∑ k, q k = 1) (m : ℕ) (E : (Fin m → K) → Prop) :
    ENNReal.ofReal ((1 / 2) * (∑ k, Real.sqrt (p k * q k)) ^ (2 * m)) ≤
      ∑ ω : Fin m → K, (if E ω then ENNReal.ofReal (∏ j, p (ω j)) else 0) +
        ∑ ω : Fin m → K, (if E ω then 0 else ENNReal.ofReal (∏ j, q (ω j))) := by
  refine (ENNReal.ofReal_le_ofReal (testing_bound hp hq hps hqs m E)).trans (le_of_eq ?_)
  have ha0 : ∀ ω : Fin m → K, 0 ≤ (if E ω then ∏ j, p (ω j) else 0) := by
    intro ω; split_ifs
    · exact Finset.prod_nonneg fun j _ ↦ hp _
    · exact le_rfl
  have hb0 : ∀ ω : Fin m → K, 0 ≤ (if E ω then 0 else ∏ j, q (ω j)) := by
    intro ω; split_ifs
    · exact le_rfl
    · exact Finset.prod_nonneg fun j _ ↦ hq _
  rw [Finset.sum_add_distrib, ENNReal.ofReal_add (Finset.sum_nonneg fun ω _ ↦ ha0 ω)
    (Finset.sum_nonneg fun ω _ ↦ hb0 ω), ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ ha0 ω),
    ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ hb0 ω)]
  congr 1
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    split_ifs <;> simp
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    split_ifs <;> simp

lemma sum_prod_weights (p : K → ℝ) (m : ℕ) :
    ∑ ω : Fin m → K, ∏ j, p (ω j) = (∑ k, p k) ^ m := by
  rw [← Fintype.prod_sum (fun (_ : Fin m) k ↦ p k)]; simp

/-- Averaging over the flip of one coordinate. -/
lemma pair_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → ℝ) (x : ι) (c : ℝ)
    (h : ∀ b, c ≤ F b + F (Function.update b x (!b x))) :
    (Fintype.card (ι → Bool) : ℝ) * c ≤ 2 * ∑ b, F b := by
  set σ : (ι → Bool) → (ι → Bool) := fun b ↦ Function.update b x (!b x) with hσ
  have hinv : ∀ b, σ (σ b) = b := by
    intro b
    funext y
    by_cases hy : y = x
    · subst hy; simp [hσ]
    · simp [hσ, Function.update_of_ne hy]
  have hswap : ∑ b, F (σ b) = ∑ b, F b :=
    Fintype.sum_equiv ⟨σ, σ, hinv, hinv⟩ _ _ (fun _ ↦ rfl)
  calc (Fintype.card (ι → Bool) : ℝ) * c = ∑ _b : ι → Bool, c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ b, (F b + F (σ b)) := Finset.sum_le_sum fun b _ ↦ h b
    _ = 2 * ∑ b, F b := by rw [Finset.sum_add_distrib, hswap, two_mul]

/-- Reverse Markov inequality for a finite weighted average of a bounded quantity. -/
lemma reverse_markov_sum {Ω : Type*} [Fintype Ω] (P M : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hPs : ∑ ω, P ω = 1) {T N : ℝ} (hT : 0 ≤ T) (hM : ∀ ω, M ω ≤ N)
    (Q : Ω → Prop) (hQ : ∀ ω, T ≤ M ω → Q ω) :
    ∑ ω, P ω * M ω ≤ T + N * ∑ ω, (if Q ω then P ω else 0) := by
  have hpt : ∀ ω, P ω * M ω ≤ T * P ω + N * (if Q ω then P ω else 0) := by
    intro ω
    by_cases hq : Q ω
    · rw [if_pos hq]
      nlinarith [hP ω, hM ω]
    · rw [if_neg hq]
      have : M ω < T := lt_of_not_ge fun h ↦ hq (hQ ω h)
      nlinarith [hP ω]
  calc ∑ ω, P ω * M ω ≤ ∑ ω, (T * P ω + N * (if Q ω then P ω else 0)) :=
        Finset.sum_le_sum fun ω _ ↦ hpt ω
    _ = T + N * ∑ ω, (if Q ω then P ω else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hPs, mul_one]

end Generic

section Shatter

variable {X : Type*} {Y : Type*}

/-- A class of finite Natarajan dimension `d` shatters a set of size exactly `d`. -/
lemma exists_nshatters_card (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d) (hd1 : 1 ≤ d) :
    ∃ C : Finset X, NShatters H C ∧ C.card = d := by
  by_contra hne
  push Not at hne
  have hle : ndim H ≤ ((d - 1 : ℕ) : ℕ∞) := by
    unfold ndim
    refine iSup₂_le fun C hC ↦ ?_
    have h1 : (C.card : ℕ∞) ≤ d := hd ▸
      le_iSup₂_of_le (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) C hC le_rfl
    have h2 := hne C hC
    norm_cast at h1 ⊢
    omega
  rw [hd] at hle
  norm_cast at hle
  omega

end Shatter

section Multiclass

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]

omit [MeasurableSingletonClass X] in
lemma measurable_lossMulti {h : X → Y} (hh : Measurable h) : Measurable (lossMulti h) := by
  have hs : MeasurableSet {z : X × Y | h z.1 = z.2} := by
    have : {z : X × Y | h z.1 = z.2} = ⋃ y : Y, (h ⁻¹' {y}) ×ˢ {y} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
        Set.mem_singleton_iff]
      exact ⟨fun h' ↦ ⟨z.2, h', rfl⟩, fun ⟨y, h1, h2⟩ ↦ h1.trans h2.symm⟩
    rw [this]
    exact MeasurableSet.iUnion fun y ↦ (hh (measurableSet_singleton y)).prod
      (measurableSet_singleton y)
  unfold lossMulti
  exact Measurable.ite hs measurable_const measurable_const

omit [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [Fintype Y] in
lemma abs_lossMulti_le (h : X → Y) (z : X × Y) : |lossMulti h z| ≤ 1 := by
  unfold lossMulti; split_ifs <;> simp

omit [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [Fintype Y] in
lemma lossMulti_nonneg (h : X → Y) (z : X × Y) : 0 ≤ lossMulti h z := by
  unfold lossMulti; split_ifs <;> simp

omit [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [Fintype Y] in
lemma lossMulti_of_eq {h : X → Y} {z : X × Y} (hz : h z.1 = z.2) : lossMulti h z = 0 := by
  unfold lossMulti; simp [hz]

omit [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [Fintype Y] in
lemma lossMulti_of_ne {h : X → Y} {z : X × Y} (hz : h z.1 ≠ z.2) : lossMulti h z = 1 := by
  unfold lossMulti; simp [hz]

lemma risk_wdist {K : Type*} [Fintype K] (z : K → X × Y) {w : K → ℝ} (hw : ∀ k, 0 ≤ w k)
    {h : X → Y} (hh : Measurable h) :
    risk lossMulti (wdist z w) h = ∑ k, w k * lossMulti h (z k) :=
  integral_wdist z hw _ (measurable_lossMulti hh) (abs_lossMulti_le h)

/-- The `log(1/δ)` part of the agnostic lower bound: a two-point testing argument at a single
point `c` where two hypotheses of `H` disagree. -/
lemma part_log (H : Set (X → Y)) (hmeas : ∀ h ∈ H, Measurable h) (c : X) {y₀ y₁ : Y}
    (hy : y₀ ≠ y₁) {h₀ h₁ : X → Y} (h₀H : h₀ ∈ H) (h₁H : h₁ ∈ H) (h₀c : h₀ c = y₀)
    (h₁c : h₁ c = y₁) (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ)
    (hA : IsAgnosticPACWith lossMulti H A mH) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 32)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 16) :
    Real.log (1 / δ) ≤ 16 * ε ^ 2 * mH ε δ := by
  set m := mH ε δ with hm
  set ρ : ℝ := 2 * ε with hρ
  set lab : Bool → Y := fun β ↦ if β then y₀ else y₁ with hlab
  have hlab_inj : Function.Injective lab := by
    intro β β' h
    cases β <;> cases β'
    all_goals first
      | rfl
      | (exfalso; simp only [hlab, Bool.false_eq_true, if_false, if_true] at h
         first | exact hy h | exact hy h.symm)
  set z : Bool → X × Y := fun β ↦ (c, lab β) with hz
  have hz_inj : Function.Injective z := fun β β' h ↦ hlab_inj (Prod.ext_iff.1 h).2
  set w : Bool → Bool → ℝ := fun s β ↦ if β = s then (1 + ρ) / 2 else (1 - ρ) / 2 with hw
  have hw0 : ∀ s β, 0 ≤ w s β := by
    intro s β; simp only [hw]; split_ifs <;> linarith
  have hws : ∀ s, ∑ β, w s β = 1 := by
    intro s; cases s <;> simp [hw] <;> ring
  set D : Bool → Measure (X × Y) := fun s ↦ wdist z (w s) with hD
  have hDp : ∀ s, IsProbabilityMeasure (D s) := fun s ↦ wdist_isProb z (hw0 s) (hws s)
  -- the learner fails whenever it predicts the wrong label at `c`
  set F : Bool → Set (Fin m → X × Y) := fun s ↦
    {S | ∃ h' ∈ H, risk lossMulti (D s) h' + ε < risk lossMulti (D s) (A m S)} with hF
  have hfail : ∀ s (S : Fin m → X × Y), A m S c ≠ lab s → S ∈ F s := by
    intro s S hS
    have hAm : Measurable (A m S) := hmeas _ (hA.1 m S)
    obtain ⟨hs, hsH, hsc⟩ : ∃ hs ∈ H, hs c = lab s := by
      cases s
      · exact ⟨h₁, h₁H, h₁c⟩
      · exact ⟨h₀, h₀H, h₀c⟩
    refine ⟨hs, hsH, ?_⟩
    have hsum2 : ∀ f : Bool → ℝ, ∑ β, f β = f s + f (!s) := by
      intro f; cases s <;> simp [add_comm]
    have hlab_ne : lab s ≠ lab (!s) := by
      intro h; have := hlab_inj h; cases s <;> simp at this
    rw [risk_wdist z (hw0 s) (hmeas _ hsH), risk_wdist z (hw0 s) hAm, hsum2, hsum2]
    have e1 : lossMulti hs (z s) = 0 := lossMulti_of_eq hsc
    have e2 : lossMulti hs (z (!s)) = 1 := by
      refine lossMulti_of_ne ?_
      show hs c ≠ lab (!s)
      rw [hsc]; exact hlab_ne
    have e3 : lossMulti (A m S) (z s) = 1 := lossMulti_of_ne hS
    have e4 := lossMulti_nonneg (A m S) (z (!s))
    have hw1 : w s s = (1 + ρ) / 2 := by simp [hw]
    have hw2 : w s (!s) = (1 - ρ) / 2 := by cases s <;> simp [hw]
    rw [e1, e2, e3, hw1, hw2]
    nlinarith
  -- the two error probabilities
  obtain ⟨E, hE⟩ : ∃ E : (Fin m → Bool) → Prop,
      E = fun ω ↦ A m (fun j ↦ z (ω j)) c ≠ lab true := ⟨_, rfl⟩
  have hPAC : ∀ s, iidLaw (D s) m (F s) ≤ ENNReal.ofReal δ := fun s ↦
    hA.2 ε δ hε (by linarith) hδ (by linarith) (D s) (hDp s) m le_rfl
  have hT : ∑ ω : Fin m → Bool, (if E ω then ENNReal.ofReal (∏ j, w true (ω j)) else 0) ≤
      ENNReal.ofReal δ := by
    refine le_trans ?_ ((iid_ge_sum hz_inj (hw0 true) m (F true)).trans (hPAC true))
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    by_cases h : E ω
    · rw [if_pos h, if_pos (hfail true _ (by rw [hE] at h; exact h))]
    · rw [if_neg h]; simp
  have hFa : ∑ ω : Fin m → Bool, (if E ω then 0 else ENNReal.ofReal (∏ j, w false (ω j))) ≤
      ENNReal.ofReal δ := by
    refine le_trans ?_ ((iid_ge_sum hz_inj (hw0 false) m (F false)).trans (hPAC false))
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    by_cases h : E ω
    · rw [if_pos h]; simp
    · rw [if_neg h, if_pos (hfail false _ ?_)]
      simp only [hE, not_not] at h
      rw [h]
      simpa [hlab] using hy
  have htest := testing_bound_ennreal (hw0 true) (hw0 false) (hws true) (hws false) m E
  have hBC : ∑ β, Real.sqrt (w true β * w false β) = Real.sqrt (1 - ρ ^ 2) := by
    rw [Fintype.sum_bool]
    simp only [hw, if_true]
    simp only [Bool.true_eq_false, if_false, Bool.false_eq_true]
    rw [mul_comm ((1 - ρ) / 2), ← two_mul]
    rw [show (1 + ρ) / 2 * ((1 - ρ) / 2) = (1 - ρ ^ 2) / 4 by ring, Real.sqrt_div' _ (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [hBC, pow_mul, Real.sq_sqrt (by nlinarith)] at htest
  have hsum : ENNReal.ofReal ((1 / 2) * (1 - ρ ^ 2) ^ m) ≤ ENNReal.ofReal (2 * δ) := by
    refine htest.trans ?_
    rw [show (2 : ℝ) * δ = δ + δ by ring, ENNReal.ofReal_add hδ.le hδ.le]
    exact add_le_add hT hFa
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  -- logarithms
  have hx : 0 < 1 - ρ ^ 2 := by nlinarith
  have h1 : (m : ℝ) * Real.log (1 - ρ ^ 2) ≤ Real.log (4 * δ) := by
    rw [← Real.log_pow]
    refine Real.log_le_log (pow_pos hx m) ?_
    linarith
  have h2 : -(2 * ρ ^ 2) ≤ Real.log (1 - ρ ^ 2) := by
    have := Real.one_sub_inv_le_log_of_pos hx
    have e : 1 - (1 - ρ ^ 2)⁻¹ = -(ρ ^ 2 / (1 - ρ ^ 2)) := by field_simp; ring
    rw [e] at this
    have hρs : ρ ^ 2 ≤ 1 / 2 := by nlinarith
    have h3 : ρ ^ 2 / (1 - ρ ^ 2) ≤ 2 * ρ ^ 2 := by
      rw [div_le_iff₀ hx]
      nlinarith [mul_nonneg (sq_nonneg ρ) (by linarith : (0 : ℝ) ≤ 1 - 2 * ρ ^ 2)]
    linarith
  have h4 : Real.log (4 * δ) = Real.log 4 - Real.log (1 / δ) := by
    rw [Real.log_mul (by norm_num) hδ.ne', one_div, Real.log_inv]; ring
  have h5 : 2 * Real.log 4 ≤ Real.log (1 / δ) := by
    rw [← Real.log_rpow (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ hδ]; norm_num; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hρ2 : ρ ^ 2 = 4 * ε ^ 2 := by rw [hρ]; ring
  have hmul : (m : ℝ) * (-(2 * ρ ^ 2)) ≤ m * Real.log (1 - ρ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hm0
  rw [hρ2] at hmul h1
  linarith

/-- The `d` part of the agnostic lower bound: Assouad's cube argument on a shattered set. -/
lemma part_dim (H : Set (X → Y)) (hmeas : ∀ h ∈ H, Measurable h) (C : Finset X)
    {f₀ f₁ : X → Y} (hf : ∀ x ∈ C, f₀ x ≠ f₁ x)
    (hsh : ∀ B ⊆ C, ∃ h ∈ H, (∀ x ∈ B, h x = f₀ x) ∧ ∀ x ∈ C, x ∉ B → h x = f₁ x)
    (hC : C.Nonempty) (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ)
    (hA : IsAgnosticPACWith lossMulti H A mH) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 32)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 16) :
    (C.card : ℝ) ≤ 4096 * ε ^ 2 * mH ε δ := by
  set m := mH ε δ with hm
  set n := C.card with hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hC.card_pos
  by_contra hlt
  rw [not_le] at hlt
  set ρ : ℝ := 32 * ε with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  set lab : X → Bool → Y := fun x β ↦ if β then f₀ x else f₁ x with hlab
  have hlab_ne : ∀ x ∈ C, ∀ β, lab x β ≠ lab x (!β) := by
    intro x hx β
    cases β
    · simpa [hlab] using (hf x hx).symm
    · simpa [hlab] using hf x hx
  have hlab_eq : ∀ x ∈ C, ∀ β β', lab x β = lab x β' → β = β' := by
    intro x hx β β' h
    by_contra hne
    have : β' = !β := by cases β <;> cases β' <;> simp_all
    exact hlab_ne x hx β (this ▸ h)
  set z : ↥C × Bool → X × Y := fun k ↦ (k.1.1, lab k.1.1 k.2) with hz
  have hz_inj : Function.Injective z := by
    rintro ⟨⟨x, hx⟩, β⟩ ⟨⟨x', hx'⟩, β'⟩ h
    simp only [hz, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have := hlab_eq x hx β β' h2
    subst this; rfl
  set w : (↥C → Bool) → ↥C × Bool → ℝ := fun b k ↦
    (1 / n) * (if k.2 = b k.1 then (1 + ρ) / 2 else (1 - ρ) / 2) with hw
  have hw0 : ∀ b k, 0 ≤ w b k := by
    intro b k; simp only [hw]; split_ifs <;> positivity
  have hwb : ∀ b (x : ↥C), w b (x, b x) = (1 / n) * ((1 + ρ) / 2) := by
    intro b x; simp [hw]
  have hwnb : ∀ b (x : ↥C), w b (x, !b x) = (1 / n) * ((1 - ρ) / 2) := by
    intro b x; cases h : b x <;> simp [hw, h]
  have hsumβ : ∀ (b : ↥C → Bool) (x : ↥C) (f : Bool → ℝ), ∑ β, f β = f (b x) + f (!b x) := by
    intro b x f; cases b x <;> simp [add_comm]
  have hpair : ∀ b (x : ↥C), ∑ β, w b (x, β) = 1 / n := by
    intro b x; rw [hsumβ b x, hwb, hwnb]; ring
  have hcardC : Fintype.card ↥C = n := by simp [hn]
  have hws : ∀ b, ∑ k, w b k = 1 := by
    intro b
    rw [Fintype.sum_prod_type]
    simp only [hpair]
    rw [Finset.sum_const, Finset.card_univ, hcardC, nsmul_eq_mul]
    field_simp
  set D : (↥C → Bool) → Measure (X × Y) := fun b ↦ wdist z (w b) with hD
  have hDp : ∀ b, IsProbabilityMeasure (D b) := fun b ↦ wdist_isProb z (hw0 b) (hws b)
  -- the target hypotheses
  have htarget : ∀ b : ↥C → Bool, ∃ h ∈ H, ∀ x : ↥C, h x = lab x (b x) := by
    intro b
    obtain ⟨h, hH, h1, h2⟩ := hsh (C.filter (fun x ↦ ∃ hx : x ∈ C, b ⟨x, hx⟩ = true))
      (Finset.filter_subset _ _)
    refine ⟨h, hH, fun x ↦ ?_⟩
    cases hbx : b x
    · have hx : x.1 ∉ C.filter (fun x ↦ ∃ hx : x ∈ C, b ⟨x, hx⟩ = true) := by
        simp only [Finset.mem_filter, not_and, not_exists]
        intro _ hx'
        have : (⟨x.1, hx'⟩ : ↥C) = x := rfl
        rw [this, hbx]; simp
      simp [hlab, h2 x.1 x.2 hx]
    · have hx : x.1 ∈ C.filter (fun x ↦ ∃ hx : x ∈ C, b ⟨x, hx⟩ = true) :=
        Finset.mem_filter.2 ⟨x.2, x.2, hbx⟩
      simp [hlab, h1 x.1 hx]
  choose t htH htlab using htarget
  -- risks
  set Mis : (↥C → Bool) → (X → Y) → ℕ := fun b g ↦
    (Finset.univ.filter (fun x : ↥C ↦ g x ≠ lab x (b x))).card with hMis
  have hrisk_t : ∀ b, risk lossMulti (D b) (t b) = (1 - ρ) / 2 := by
    intro b
    rw [risk_wdist z (hw0 b) (hmeas _ (htH b)), Fintype.sum_prod_type]
    have : ∀ x : ↥C, ∑ β, w b (x, β) * lossMulti (t b) (z (x, β)) = (1 / n) * ((1 - ρ) / 2) := by
      intro x
      rw [hsumβ b x, hwb, hwnb, lossMulti_of_eq (show t b (z (x, b x)).1 = (z (x, b x)).2 from
        htlab b x), lossMulti_of_ne (show t b (z (x, !b x)).1 ≠ (z (x, !b x)).2 by
          show t b x ≠ lab x (!b x)
          rw [htlab b x]; exact hlab_ne x x.2 _)]
      ring
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, hcardC, nsmul_eq_mul]
    field_simp
  have hrisk_g : ∀ b (g : X → Y), Measurable g →
      (1 - ρ) / 2 + ρ / n * Mis b g ≤ risk lossMulti (D b) g := by
    intro b g hg
    rw [risk_wdist z (hw0 b) hg, Fintype.sum_prod_type]
    have hx : ∀ x : ↥C, (1 / n) * ((1 - ρ) / 2) + ρ / n * (if g x ≠ lab x (b x) then 1 else 0) ≤
        ∑ β, w b (x, β) * lossMulti g (z (x, β)) := by
      intro x
      rw [hsumβ b x, hwb, hwnb]
      have hl0 := lossMulti_nonneg g (z (x, !b x))
      by_cases hgx : g x = lab x (b x)
      · rw [if_neg (not_not.2 hgx), lossMulti_of_eq (show g (z (x, b x)).1 = (z (x, b x)).2 from hgx),
          lossMulti_of_ne (show g (z (x, !b x)).1 ≠ (z (x, !b x)).2 by
            show g x ≠ lab x (!b x)
            rw [hgx]; exact hlab_ne x x.2 _)]
        ring_nf; exact le_refl _
      · rw [if_pos hgx, lossMulti_of_ne (show g (z (x, b x)).1 ≠ (z (x, b x)).2 from hgx)]
        have : 0 ≤ 1 / (n : ℝ) * ((1 - ρ) / 2) * lossMulti g (z (x, !b x)) := by
          have : 0 ≤ 1 / (n : ℝ) * ((1 - ρ) / 2) := by
            apply mul_nonneg <;> [positivity; linarith]
          positivity
        have e : ρ / n = 1 / (n : ℝ) * ρ := by ring
        rw [e]
        nlinarith
    calc (1 - ρ) / 2 + ρ / n * Mis b g
        = ∑ x : ↥C, ((1 / n) * ((1 - ρ) / 2) + ρ / n * (if g x ≠ lab x (b x) then 1 else 0)) := by
          have hb : ∑ x : ↥C, ρ / n * (if g x ≠ lab x (b x) then (1:ℝ) else 0) =
              ρ / n * Mis b g := by
            rw [← Finset.mul_sum]; congr 1; rw [hMis]; dsimp only
            rw [Finset.card_filter]; push_cast; rfl
          rw [Finset.sum_add_distrib, hb, Finset.sum_const,
            Finset.card_univ, hcardC, nsmul_eq_mul]
          field_simp
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ hx x
  -- failure event
  set F : (↥C → Bool) → Set (Fin m → X × Y) := fun b ↦
    {S | ∃ h' ∈ H, risk lossMulti (D b) h' + ε < risk lossMulti (D b) (A m S)} with hF
  have hfail : ∀ b (S : Fin m → X × Y), (n : ℝ) / 16 ≤ Mis b (A m S) → S ∈ F b := by
    intro b S hS
    refine ⟨t b, htH b, ?_⟩
    have h1 := hrisk_g b (A m S) (hmeas _ (hA.1 m S))
    rw [hrisk_t b]
    have h2 : ρ / n * (n / 16) ≤ ρ / n * Mis b (A m S) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h3 : ρ / n * (n / 16) = 2 * ε := by rw [hρ]; field_simp; ring
    linarith
  -- Assouad's argument
  set P : (↥C → Bool) → (Fin m → ↥C × Bool) → ℝ := fun b ω ↦ ∏ j, w b (ω j) with hP
  have hP0 : ∀ b ω, 0 ≤ P b ω := fun b ω ↦ Finset.prod_nonneg fun j _ ↦ hw0 b _
  have hPs : ∀ b, ∑ ω, P b ω = 1 := by
    intro b; rw [hP]; dsimp only; rw [sum_prod_weights, hws, one_pow]
  obtain ⟨W, hW⟩ : ∃ W : (↥C → Bool) → ↥C → (Fin m → ↥C × Bool) → Prop,
      W = fun (b : ↥C → Bool) (x : ↥C) (ω : Fin m → ↥C × Bool) ↦ A m (fun j ↦ z (ω j)) x ≠ lab x (b x) := ⟨_, rfl⟩
  set G : (↥C → Bool) → ↥C → ℝ := fun b x ↦ ∑ ω, if W b x ω then P b ω else 0 with hG
  have hBC : ∀ b (x : ↥C), 1 - ρ ^ 2 / n ≤
      ∑ k, Real.sqrt (w b k * w (Function.update b x (!b x)) k) := by
    intro b x
    set b' := Function.update b x (!b x) with hb'
    have hk : ∀ k : ↥C × Bool, (w b k + w b' k) / 2 - (if k.1 = x then ρ ^ 2 / (2 * n) else 0) ≤
        Real.sqrt (w b k * w b' k) := by
      rintro ⟨y, β⟩
      by_cases hy : y = x
      · subst hy
        rw [if_pos rfl]
        have hb'y : b' y = !b y := by simp [hb']
        have e : w b (y, β) * w b' (y, β) = ((1 / n) / 2) ^ 2 * (1 - ρ ^ 2) := by
          simp only [hw, hb'y]; cases b y <;> cases β <;> simp <;> ring
        have e2 : w b (y, β) + w b' (y, β) = 1 / n := by
          simp only [hw, hb'y]; cases b y <;> cases β <;> simp <;> ring
        rw [e, e2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hs : 1 - ρ ^ 2 ≤ Real.sqrt (1 - ρ ^ 2) := by
          apply Real.le_sqrt_of_sq_le
          have ha : 0 ≤ 1 - ρ ^ 2 := by nlinarith
          nlinarith [mul_nonneg (sq_nonneg ρ) ha]
        have h0 : (0:ℝ) ≤ 1 / n / 2 := by positivity
        have e3 : 1 / (n:ℝ) / 2 - ρ ^ 2 / (2 * n) = 1 / n / 2 * (1 - ρ ^ 2) := by
          field_simp
        rw [e3]; exact mul_le_mul_of_nonneg_left hs h0
      · rw [if_neg hy]
        have : w b' (y, β) = w b (y, β) := by
          simp only [hw, hb', Function.update_of_ne hy]
        rw [this, Real.sqrt_mul_self (hw0 b _)]; linarith
    calc 1 - ρ ^ 2 / n = ∑ k : ↥C × Bool,
          ((w b k + w b' k) / 2 - (if k.1 = x then ρ ^ 2 / (2 * n) else 0)) := by
          have hite : ∑ k : ↥C × Bool, (if k.1 = x then ρ ^ 2 / (2 * n) else 0) = ρ ^ 2 / n := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
            · simp only [if_true, Fintype.sum_bool]
              ring
            · intro y _ hy; simp [hy]
            · simp
          rw [Finset.sum_sub_distrib, hite, ← Finset.sum_div, Finset.sum_add_distrib, hws, hws]
          ring
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦ hk k
  have hpairG : ∀ b (x : ↥C), 1 / 4 ≤ G b x + G (Function.update b x (!b x)) x := by
    intro b x
    set b' := Function.update b x (!b x) with hb'
    have ht := testing_bound (hw0 b) (hw0 b') (hws b) (hws b') m (W b x)
    have hmono : ∀ ω, (if W b x ω then 0 else P b' ω) ≤ (if W b' x ω then P b' ω else 0) := by
      intro ω
      by_cases h : W b x ω
      · rw [if_pos h]; split_ifs
        · exact hP0 _ _
        · exact le_rfl
      · rw [if_neg h, if_pos]
        rw [hW] at h ⊢
        simp only [not_not] at h
        simp only [h, hb', Function.update_self]
        exact hlab_ne x x.2 _
    have hB := hBC b x
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hC.card_pos
    have hρn : ρ ^ 2 / n ≤ ρ ^ 2 := div_le_self (by positivity) hn1
    have hρ2 : ρ ^ 2 < 1 := by nlinarith
    have hBC0 : 0 ≤ 1 - ρ ^ 2 / n := by linarith
    have hpow : 1 / 2 ≤ (1 - ρ ^ 2 / n) ^ (2 * m) := by
      have h1 := one_add_mul_le_pow (a := -(ρ ^ 2 / n)) (by linarith) (2 * m)
      have h2 : (2 * m : ℕ) * (ρ ^ 2 / n) ≤ 1 / 2 := by
        rw [hρ]; push_cast
        rw [show (2 * (m:ℝ)) * ((32 * ε) ^ 2 / n) = 2048 * ε ^ 2 * m / n by ring,
          div_le_iff₀ hn0]
        linarith
      rw [← sub_eq_add_neg] at h1
      linarith
    have h3 : (1 / 2) * (1 - ρ ^ 2 / n) ^ (2 * m) ≤
        (1 / 2) * (∑ k, Real.sqrt (w b k * w b' k)) ^ (2 * m) := by
      gcongr
    calc (1 : ℝ) / 4 ≤ (1 / 2) * (∑ k, Real.sqrt (w b k * w b' k)) ^ (2 * m) := by nlinarith
      _ ≤ ∑ ω, ((if W b x ω then P b ω else 0) + (if W b x ω then 0 else P b' ω)) := ht
      _ ≤ ∑ ω, ((if W b x ω then P b ω else 0) + (if W b' x ω then P b' ω else 0)) :=
          Finset.sum_le_sum fun ω _ ↦ add_le_add le_rfl (hmono ω)
      _ = G b x + G b' x := by rw [Finset.sum_add_distrib]
  have hcard : (Fintype.card (↥C → Bool) : ℝ) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, hcardC]; push_cast; rfl
  have hsumG : ∀ x : ↥C, (2:ℝ) ^ n / 8 ≤ ∑ b, G b x := by
    intro x
    have := pair_sum (fun b ↦ G b x) x (1 / 4) (fun b ↦ hpairG b x)
    rw [hcard] at this; linarith
  set M : (↥C → Bool) → (Fin m → ↥C × Bool) → ℝ := fun b ω ↦
    (Mis b (A m (fun j ↦ z (ω j))) : ℝ) with hM
  have hGM : ∀ b, ∑ x, G b x = ∑ ω, P b ω * M b ω := by
    intro b
    rw [hG]; dsimp only; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [hM]; dsimp only; rw [hMis]; dsimp only; rw [Finset.card_filter]; push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : W b x ω
    · rw [if_pos h, if_pos (by rw [hW] at h; exact h), mul_one]
    · rw [if_neg h, if_neg (by rw [hW] at h; exact h), mul_zero]
  have htot : (n:ℝ) * (2 ^ n / 8) ≤ ∑ b, ∑ ω, P b ω * M b ω := by
    calc (n:ℝ) * (2 ^ n / 8) = ∑ _x : ↥C, (2:ℝ) ^ n / 8 := by
          rw [Finset.sum_const, Finset.card_univ, hcardC, nsmul_eq_mul]
      _ ≤ ∑ x, ∑ b, G b x := Finset.sum_le_sum fun x _ ↦ hsumG x
      _ = ∑ b, ∑ x, G b x := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun b _ ↦ hGM b
  obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset (↥C → Bool)),
      (n:ℝ) / 8 ≤ ∑ ω, P b ω * M b ω := by
    apply Finset.exists_le_of_sum_le Finset.univ_nonempty
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; linarith
  have hMle : ∀ ω, M b ω ≤ n := fun ω ↦ by
    rw [hM]; dsimp only; rw [hMis]
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ.trans hcardC).le
  have hRM := reverse_markov_sum (P b) (M b) (hP0 b) (hPs b) (T := n / 16) (by positivity)
    hMle (fun ω ↦ (n:ℝ) / 16 ≤ M b ω) (fun ω h ↦ h)
  have hQ : 1 / 16 ≤ ∑ ω, (if (n:ℝ) / 16 ≤ M b ω then P b ω else 0) := by
    have := hb.trans hRM
    by_contra hc; push Not at hc; nlinarith
  have hle := iid_ge_sum hz_inj (hw0 b) m (F b)
  have hPAC : iidLaw (D b) m (F b) ≤ ENNReal.ofReal δ :=
    hA.2 ε δ hε (by linarith) hδ (by linarith) (D b) (hDp b) m le_rfl
  have hfin : ENNReal.ofReal (∑ ω, (if (n:ℝ) / 16 ≤ M b ω then P b ω else 0)) ≤
      ENNReal.ofReal δ := by
    refine le_trans ?_ (hle.trans hPAC)
    rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ by
      split_ifs
      · exact hP0 b ω
      · exact le_rfl)]
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    by_cases h : (n:ℝ) / 16 ≤ M b ω
    · rw [if_pos h, if_pos (hfail b _ h)]
    · rw [if_neg h]; simp
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at hfin
  linarith

end Multiclass

end AgnosticLowerAux

open AgnosticLowerAux

theorem solution :
    ∃ C₁ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), (∀ h ∈ H, Measurable h) → ndim H = d → 2 ≤ d →
        ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsAgnosticPACWith lossMulti H A mH →
          ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
            C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mH ε δ := by
  refine ⟨1 / 8192, 1 / 32, 1 / 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro X Y _ _ _ _ _ H d hmeas hdim hd A mH hA ε δ hε hε0 hδ hδ0
  obtain ⟨C, ⟨f₀, f₁, hf, hsh⟩, hC⟩ := exists_nshatters_card H d hdim (by omega)
  obtain ⟨c, hc⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨h₀, h₀H, h₀B, -⟩ := hsh {c} (by simpa using hc)
  obtain ⟨h₁, h₁H, -, h₁B⟩ := hsh ∅ (Finset.empty_subset _)
  have hl := part_log H hmeas c (hf c hc) h₀H h₁H (h₀B c (Finset.mem_singleton_self c))
    (h₁B c hc (Finset.notMem_empty c)) A mH hA hε hε0 hδ hδ0
  have hdm := part_dim H hmeas C hf hsh ⟨c, hc⟩ A mH hA hε hε0 hδ hδ0
  rw [hC] at hdm
  have hm0 : (0 : ℝ) ≤ ε ^ 2 * mH ε δ := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

