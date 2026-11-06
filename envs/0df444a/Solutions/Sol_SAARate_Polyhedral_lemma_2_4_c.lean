-- Prove2me | solution 1 for SAARate.Polyhedral.lemma_2_4_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:14:24.791198+00:00
-- url     : https://prove2.me/submissions/384d13fc-e52d-4f1a-ac91-1dfb50355f1b

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAA3C

open SAARate.Sharp SAARate.Polyhedral

/-- A polyhedron given by a finite set of constraints `⟪a, x⟫ ≤ b`. -/
def HP {m : ℕ} (s : Finset (E m × ℝ)) : Set (E m) := {x | ∀ p ∈ s, inner ℝ p.1 x ≤ p.2}

lemma HP_convex {m : ℕ} (s : Finset (E m × ℝ)) : Convex ℝ (HP s) := by
  intro x hx y hy a b ha hb hab p hp
  have h1 := hx p hp
  have h2 := hy p hp
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  calc a * inner ℝ p.1 x + b * inner ℝ p.1 y ≤ a * p.2 + b * p.2 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = p.2 := by rw [← add_mul, hab, one_mul]

lemma HP_closed {m : ℕ} (s : Finset (E m × ℝ)) : IsClosed (HP s) := by
  have : HP s = ⋂ p ∈ s, {x : E m | inner ℝ p.1 x ≤ p.2} := by
    ext x; simp [HP]
  rw [this]
  exact isClosed_biInter fun p _ => isClosed_le (by fun_prop) continuous_const

lemma HP_union {m : ℕ} (s t : Finset (E m × ℝ)) [DecidableEq (E m × ℝ)] :
    HP (s ∪ t) = HP s ∩ HP t := by
  ext x; simp only [HP, Finset.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

/-- Extreme points of a polyhedron are determined by their active sets, hence finitely many. -/
lemma HP_ext_finite {m : ℕ} (s : Finset (E m × ℝ)) :
    (Set.extremePoints ℝ (HP s)).Finite := by
  classical
  let act : E m → Finset (E m × ℝ) := fun e => s.filter (fun p => inner ℝ p.1 e = p.2)
  have hinj : Set.InjOn act (Set.extremePoints ℝ (HP s)) := by
    intro e he e' he' hact
    have heP : e ∈ HP s := he.1
    have he'P : e' ∈ HP s := he'.1
    set d := e' - e
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < t ∧ t ≤ 1) ∧ ∀ p ∈ s, inner ℝ p.1 (e - t • d) ≤ p.2 := by
      refine ((eventually_mem_nhdsWithin).and
        (nhdsWithin_le_nhds (eventually_le_nhds one_pos))).and ?_
      · rw [Filter.eventually_all_finset]
        intro p hp
        by_cases hpa : inner ℝ p.1 e = p.2
        · have hpa' : inner ℝ p.1 e' = p.2 := by
            have : p ∈ act e := Finset.mem_filter.2 ⟨hp, hpa⟩
            rw [hact] at this
            exact (Finset.mem_filter.1 this).2
          refine Filter.Eventually.of_forall fun t => ?_
          simp only [d, inner_sub_right, inner_smul_right, hpa, hpa', sub_self, mul_zero,
            sub_zero, le_refl]
        · have hlt : inner ℝ p.1 e < p.2 := lt_of_le_of_ne (heP p hp) hpa
          have hc : Continuous fun t : ℝ => inner ℝ p.1 (e - t • d) := by fun_prop
          have : ∀ᶠ t in 𝓝 (0 : ℝ), inner ℝ p.1 (e - t • d) < p.2 := by
            apply hc.continuousAt.eventually_lt continuousAt_const
            simpa using hlt
          exact nhdsWithin_le_nhds (this.mono fun t ht => ht.le)
    obtain ⟨t, ⟨ht0, ht1⟩, htP⟩ := hev.exists
    have hplus : e + t • d ∈ HP s := by
      have : e + t • d = (1 - t) • e + t • e' := by
        simp only [d, smul_sub, sub_smul, one_smul]; abel
      rw [this]
      exact HP_convex s heP he'P (by linarith) ht0.le (by ring)
    have hmid : e ∈ openSegment ℝ (e - t • d) (e + t • d) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [smul_sub, smul_add, smul_smul]; norm_num
      rw [← add_smul]; norm_num
    have h1 := he.2 htP hplus hmid
    have : t • d = 0 := by
      have : e - t • d - e = 0 := by rw [h1, sub_self]
      simpa using this
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h ht0.ne'
    · exact (sub_eq_zero.1 h).symm
  refine Set.Finite.of_finite_image ?_ hinj
  refine (s.powerset.finite_toSet).subset ?_
  rintro _ ⟨e, -, rfl⟩
  exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))

/-- Minkowski: a bounded polyhedron is the convex hull of its (finitely many) extreme points. -/
lemma HP_eq_convexHull {m : ℕ} (s : Finset (E m × ℝ)) (hb : Bornology.IsBounded (HP s)) :
    convexHull ℝ (Set.extremePoints ℝ (HP s)) = HP s := by
  have hcpt : IsCompact (HP s) := Metric.isCompact_of_isClosed_isBounded (HP_closed s) hb
  have h := closure_convexHull_extremePoints hcpt (HP_convex s)
  have hc : IsClosed (convexHull ℝ (Set.extremePoints ℝ (HP s))) :=
    ((HP_ext_finite s).isCompact_convexHull ℝ).isClosed
  rwa [hc.closure_eq] at h

lemma HP_rep {m : ℕ} (s : Finset (E m × ℝ)) (hb : Bornology.IsBounded (HP s)) {y : E m}
    (hy : y ∈ HP s) : ∃ w : E m → ℝ, (∀ v ∈ (HP_ext_finite s).toFinset, 0 ≤ w v) ∧
      ∑ v ∈ (HP_ext_finite s).toFinset, w v = 1 ∧
      ∑ v ∈ (HP_ext_finite s).toFinset, w v • v = y := by
  have hy' : y ∈ convexHull ℝ (((HP_ext_finite s).toFinset : Finset (E m)) : Set (E m)) := by
    rw [Set.Finite.coe_toFinset, HP_eq_convexHull s hb]; exact hy
  exact Finset.mem_convexHull'.1 hy'

lemma saa_affine {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ) {ι : Type*} (F : Finset ι) (w : ι → ℝ)
    (v : ι → E m) (y : E m) (hy : ∀ ω, h y ω = ∑ i ∈ F, w i * h (v i) ω) (s : ℕ → Ω) (N : ℕ) :
    saaObj h s N y = ∑ i ∈ F, w i * saaObj h s N (v i) := by
  simp only [saaObj, hy]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma saa_convex {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω)) (s : ℕ → Ω) (N : ℕ) :
    ConvexOn ℝ Set.univ (saaObj h s N) := by
  refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
  simp only [saaObj, smul_eq_mul]
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 N.cast_nonneg
  have : ∑ j ∈ Finset.range N, h (α • x + β • y) (s j) ≤
      ∑ j ∈ Finset.range N, (α * h x (s j) + β * h y (s j)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := (hconv (s j)).2 (Set.mem_univ x) (Set.mem_univ y) hα hβ hαβ
    simpa only [smul_eq_mul] using this
  calc (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (α • x + β • y) (s j)
      ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (α * h x (s j) + β * h y (s j)) :=
        mul_le_mul_of_nonneg_left this hN
    _ = α * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h x (s j)) +
        β * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h y (s j)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end SAA3C

open SAA3C SAARate.Sharp SAARate.Polyhedral in
theorem solution {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : ∀ ω, P {ω} ≠ 0)
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (hΘp : IsPolyhedral Θ)
    (hA : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ)) :
    ∃ (q ℓ : ℕ), ℓ ≤ q ∧ ∃ x : Fin q → SAARate.Sharp.E m,
      {y | ∃ i : Fin q, i.val < ℓ ∧ x i = y} =
          Set.extremePoints ℝ (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) ∧
        (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
          SAARate.Sharp.expectedObj P h (x i) < SAARate.Sharp.expectedObj P h (x j)) ∧
        ∀ (s : ℕ → Ω) (N : ℕ),
          (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val → SAARate.Sharp.saaObj h s N (x i) < SAARate.Sharp.saaObj h s N (x j)) →
            (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ).Nonempty ∧
              IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ) := by
  classical
  -- piecewise linear data
  choose k a b hrep0 using hpl
  have hrep : ∀ ω x, h x ω = Finset.univ.sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i) := fun ω x => hrep0 ω x
  have hle : ∀ ω i x, inner ℝ (a ω i) x + b ω i ≤ h x ω := fun ω i x => by
    rw [hrep ω x]
    exact Finset.le_sup' (fun i => inner ℝ (a ω i) x + b ω i) (Finset.mem_univ i)
  have hex : ∀ ω x, ∃ i, h x ω = inner ℝ (a ω i) x + b ω i := fun ω x => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i)
    exact ⟨i, by rw [hrep ω x, hi]⟩
  have hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω) := by
    intro ω
    refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
    simp only [smul_eq_mul]
    rw [hrep ω (α • x + β • y)]
    apply Finset.sup'_le
    intro i _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hle ω i x) hα
    have h2 := mul_le_mul_of_nonneg_left (hle ω i y) hβ
    have : b ω i = α * b ω i + β * b ω i := by rw [← add_mul, hαβ, one_mul]
    linarith
  -- the expected value as a finite sum
  set p : Ω → ℝ := fun ω => P.real {ω} with hpdef
  have hp : ∀ ω, 0 < p ω := fun ω => ENNReal.toReal_pos (hP ω) (measure_ne_top P _)
  set f := expectedObj P h with hfdef
  have hf : ∀ x, f x = ∑ ω, p ω * h x ω := fun x => by
    simp only [hfdef, expectedObj]
    rw [integral_fintype Integrable.of_finite]
    simp [hpdef, smul_eq_mul]
  -- Θ as a polyhedron
  obtain ⟨kΘ, aΘ, bΘ, hΘeq⟩ := hΘp
  set TS : Finset (E m × ℝ) := Finset.univ.image (fun i => (aΘ i, bΘ i)) with hTSdef
  have hTS : Θ = HP TS := by
    rw [hΘeq]; ext x; simp [HP, hTSdef]
  -- the optimal set A
  set Aset := argminOn f Θ with hAsetdef
  obtain ⟨⟨a0, ha0⟩, hAb⟩ := hA
  set fstar := f a0 with hfstar
  have hAiff : ∀ x, x ∈ Aset ↔ x ∈ Θ ∧ f x ≤ fstar := by
    intro x
    constructor
    · intro hx; exact ⟨hx.1, hx.2 a0 ha0.1⟩
    · rintro ⟨hx, hfx⟩; exact ⟨hx, fun y hy => hfx.trans (ha0.2 y hy)⟩
  have hfstar_le : ∀ y ∈ Θ, fstar ≤ f y := fun y hy => ha0.2 y hy
  set AS : Finset (E m × ℝ) := (Finset.univ : Finset (∀ ω, Fin (k ω + 1))).image
    (fun σ => (∑ ω, p ω • a ω (σ ω), fstar - ∑ ω, p ω * b ω (σ ω))) with hASdef
  have hAS : Aset = HP (TS ∪ AS) := by
    rw [HP_union, ← hTS]
    ext x
    rw [hAiff, Set.mem_inter_iff]
    refine and_congr_right fun _ => ?_
    simp only [HP, hASdef, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
    have key : ∀ σ : ∀ ω, Fin (k ω + 1), inner ℝ (∑ ω, p ω • a ω (σ ω)) x ≤
        fstar - ∑ ω, p ω * b ω (σ ω) ↔ ∑ ω, p ω * (inner ℝ (a ω (σ ω)) x + b ω (σ ω)) ≤ fstar := by
      intro σ
      rw [sum_inner]
      simp only [real_inner_smul_left, mul_add, Finset.sum_add_distrib]
      constructor <;> intro H <;> linarith
    simp only [key]
    constructor
    · intro H σ
      refine le_trans ?_ ((hf x).symm.le.trans H)
      exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hle ω _ x) (hp ω).le
    · intro H
      have := H (fun ω => Classical.choose (hex ω x))
      rw [hf x]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun ω _ => ?_) this
      rw [← Classical.choose_spec (hex ω x)]
  have hAconv : Convex ℝ Aset := hAS ▸ HP_convex _
  have hAΘ : Aset ⊆ Θ := fun x hx => hx.1
  -- affinity of every `h(·, ω)` on `A`
  have hAaff : ∀ {ι : Type} (F : Finset ι) (w : ι → ℝ) (v : ι → E m), (∀ i ∈ F, 0 ≤ w i) →
      ∑ i ∈ F, w i = 1 → (∀ i ∈ F, v i ∈ Aset) →
      ∀ ω, h (∑ i ∈ F, w i • v i) ω = ∑ i ∈ F, w i * h (v i) ω := by
    intro ι F w v hw0 hw1 hvA
    set y := ∑ i ∈ F, w i • v i
    have hyA : y ∈ Aset := hAconv.sum_mem hw0 hw1 hvA
    have hjen : ∀ ω, h y ω ≤ ∑ i ∈ F, w i * h (v i) ω := fun ω => by
      have := (hconv ω).map_sum_le hw0 hw1 (fun i _ => Set.mem_univ (v i))
      simpa only [smul_eq_mul] using this
    have hD : ∀ ω ∈ (Finset.univ : Finset Ω), 0 ≤ p ω * (∑ i ∈ F, w i * h (v i) ω - h y ω) :=
      fun ω _ => mul_nonneg (hp ω).le (sub_nonneg.2 (hjen ω))
    have hsum : ∑ ω, p ω * (∑ i ∈ F, w i * h (v i) ω - h y ω) =
        ∑ i ∈ F, w i * f (v i) - f y := by
      simp only [hf, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ω _ => by ring
    have hle0 : ∑ i ∈ F, w i * f (v i) - f y ≤ 0 := by
      have h1 : ∑ i ∈ F, w i * f (v i) ≤ ∑ i ∈ F, w i * fstar :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hAiff _).1 (hvA i hi)).2 (hw0 i hi)
      rw [← Finset.sum_mul, hw1, one_mul] at h1
      have h2 := hfstar_le y (hAΘ hyA)
      linarith
    have hzero : ∑ ω, p ω * (∑ i ∈ F, w i * h (v i) ω - h y ω) = 0 :=
      le_antisymm (hsum ▸ hle0) (Finset.sum_nonneg hD)
    intro ω
    have := (Finset.sum_eq_zero_iff_of_nonneg hD).1 hzero ω (Finset.mem_univ ω)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (hp ω).ne'
    · linarith
  -- the box
  obtain ⟨R0', hR0'⟩ := hAb.subset_closedBall (0 : E m)
  set R0 := max R0' 0
  have hR0 : ∀ x ∈ Aset, ‖x‖ ≤ R0 := fun x hx => by
    have := hR0' hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  set R := R0 + 1
  set u : Fin m → E m := fun i => EuclideanSpace.single i (1 : ℝ)
  have hu : ∀ i, ‖u i‖ = 1 := fun i => by simp [u]
  set BS : Finset (E m × ℝ) := Finset.univ.image (fun i => (u i, R)) ∪
    Finset.univ.image (fun i => (-u i, R)) with hBSdef
  have hB1 : ∀ x : E m, ‖x‖ ≤ R → x ∈ HP BS := by
    intro x hx q hq
    simp only [hBSdef, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hq
    rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have := real_inner_le_norm (u i) x
      rw [hu, one_mul] at this
      exact this.trans hx
    · have := real_inner_le_norm (-u i) x
      rw [norm_neg, hu, one_mul] at this
      exact this.trans hx
  have hB2 : Bornology.IsBounded (HP BS) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E m)]
    refine ⟨m * R ^ 2 + 1, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hc : ∀ i, |x i| ≤ R := by
      intro i
      have h1 := hx (u i, R) (by simp [hBSdef])
      have h2 := hx (-u i, R) (by simp [hBSdef])
      simp only [inner_neg_left, u, EuclideanSpace.inner_single_left, map_one, one_mul] at h1 h2
      exact abs_le.2 ⟨by linarith, h1⟩
    have hsq : ‖x‖ ^ 2 ≤ m * R ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              have := hc i
              nlinarith [abs_nonneg (x i), sq_abs (x i)]
        _ = m * R ^ 2 := by simp
    nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  -- the cells
  let PS : (∀ ω, Fin (k ω + 1)) → Finset (E m × ℝ) := fun σ =>
    (Finset.univ : Finset (Σ ω, Fin (k ω + 1))).image
      (fun q => (a q.1 q.2 - a q.1 (σ q.1), b q.1 (σ q.1) - b q.1 q.2))
  let CS : (∀ ω, Fin (k ω + 1)) → Finset (E m × ℝ) := fun σ => TS ∪ BS ∪ PS σ
  have hCS : ∀ σ, HP (CS σ) = (Θ ∩ HP BS) ∩ HP (PS σ) := fun σ => by
    simp only [CS, HP_union, ← hTS]
  have hcell_h : ∀ σ x, x ∈ HP (PS σ) → ∀ ω, h x ω = inner ℝ (a ω (σ ω)) x + b ω (σ ω) := by
    intro σ x hx ω
    refine le_antisymm ?_ (hle ω _ x)
    rw [hrep ω x]
    apply Finset.sup'_le
    intro i _
    have := hx _ (Finset.mem_image_of_mem _ (Finset.mem_univ ⟨ω, i⟩))
    simp only [inner_sub_left] at this
    linarith
  have hcover : ∀ x ∈ Θ, x ∈ HP BS → ∃ σ, x ∈ HP (CS σ) := by
    intro x hxΘ hxB
    refine ⟨fun ω => Classical.choose (hex ω x), ?_⟩
    rw [hCS (fun ω => Classical.choose (hex ω x))]
    refine ⟨⟨hxΘ, hxB⟩, ?_⟩
    intro q hq
    simp only [PS, Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨⟨ω, i⟩, rfl⟩ := hq
    have h1 := hle ω i x
    have h2 := Classical.choose_spec (hex ω x)
    simp only [inner_sub_left]
    linarith
  have hcell_bdd : ∀ σ, Bornology.IsBounded (HP (CS σ)) := fun σ =>
    hB2.subset (fun x hx => by rw [hCS] at hx; exact hx.1.2)
  have hcellΘ : ∀ σ, HP (CS σ) ⊆ Θ := fun σ x hx => by rw [hCS] at hx; exact hx.1.1
  -- the points
  have hX1fin : (Set.extremePoints ℝ Aset).Finite := by rw [hAS]; exact HP_ext_finite _
  set X2 : Set (E m) := ⋃ σ, (Set.extremePoints ℝ (HP (CS σ)) \ Aset) with hX2def
  have hX2fin : X2.Finite :=
    (Set.finite_iUnion fun σ => HP_ext_finite (CS σ)).subset
      (Set.iUnion_mono fun σ => Set.diff_subset)
  have hX2 : ∀ v ∈ X2, v ∈ Θ ∧ v ∉ Aset := by
    intro v hv
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 hv
    exact ⟨hcellΘ σ hσ.1.1, hσ.2⟩
  set L1 := hX1fin.toFinset.toList
  set L2 := hX2fin.toFinset.toList
  set q := L1.length + L2.length
  set ℓ := L1.length
  have hlen : (L1 ++ L2).length = q := List.length_append
  let x : Fin q → E m := fun i => (L1 ++ L2)[i.val]'(by rw [hlen]; exact i.2)
  have T1 : ∀ i : Fin q, i.val < ℓ → x i ∈ Set.extremePoints ℝ Aset := by
    intro i hi
    have : x i = L1[i.val]'hi := List.getElem_append_left hi
    rw [this]
    have := List.getElem_mem (l := L1) hi
    rwa [Finset.mem_toList, Set.Finite.mem_toFinset] at this
  have T2 : ∀ i : Fin q, ℓ ≤ i.val → x i ∈ X2 := by
    intro i hi
    have hi' : i.val - ℓ < L2.length := by have := i.2; omega
    have : x i = L2[i.val - ℓ]'hi' := List.getElem_append_right hi
    rw [this]
    have := List.getElem_mem (l := L2) hi'
    rwa [Finset.mem_toList, Set.Finite.mem_toFinset] at this
  have T3 : ∀ e ∈ Set.extremePoints ℝ Aset, ∃ i : Fin q, i.val < ℓ ∧ x i = e := by
    intro e he
    have : e ∈ L1 := by rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact he
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem this
    exact ⟨⟨n, by omega⟩, hn, List.getElem_append_left hn⟩
  have T4 : ∀ v ∈ X2, ∃ j : Fin q, ℓ ≤ j.val ∧ x j = v := by
    intro v hv
    have : v ∈ L2 := by rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact hv
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem this
    refine ⟨⟨ℓ + n, by omega⟩, Nat.le_add_right ℓ n, ?_⟩
    show (L1 ++ L2)[ℓ + n]'_ = _
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    congr 1; omega
  refine ⟨q, ℓ, by omega, x, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨i, hi, rfl⟩; exact T1 i hi
    · intro hy; exact T3 y hy
  · intro i j hi hj
    have h1 := (hAiff _).1 (extremePoints_subset (T1 i hi))
    have h2 := hX2 _ (T2 j hj)
    have : ¬ f (x j) ≤ fstar := fun H => h2.2 ((hAiff _).2 ⟨h2.1, H⟩)
    push Not at this
    linarith [h1.2]
  -- the main argument for a fixed sample
  intro s N H
  set g := saaObj h s N with hgdef
  have Hc : ∀ e ∈ Set.extremePoints ℝ Aset, ∀ v ∈ X2, g e < g v := by
    intro e he v hv
    obtain ⟨i, hi, rfl⟩ := T3 e he
    obtain ⟨j, hj, rfl⟩ := T4 v hv
    exact H i j hi hj
  have hext_ne : (Set.extremePoints ℝ Aset).Nonempty := by
    have hcpt : IsCompact Aset := Metric.isCompact_of_isClosed_isBounded
      (by rw [hAS]; exact HP_closed _) hAb
    exact hcpt.extremePoints_nonempty ⟨a0, ha0⟩
  obtain ⟨astar, hastar, hamin⟩ := hX1fin.toFinset.exists_min_image g
    (by simpa using hext_ne)
  rw [Set.Finite.mem_toFinset] at hastar
  have hamin' : ∀ e ∈ Set.extremePoints ℝ Aset, g astar ≤ g e := fun e he =>
    hamin e ((Set.Finite.mem_toFinset _).2 he)
  have hastarA : astar ∈ Aset := extremePoints_subset hastar
  have hgconv := saa_convex h hconv s N
  -- (S1) lower bound on A
  have S1 : ∀ y ∈ Aset, g astar ≤ g y := by
    intro y hy
    have hbA : Bornology.IsBounded (HP (TS ∪ AS)) := hAS ▸ hAb
    rw [hAS] at hy
    obtain ⟨w, hw0, hw1, hwy⟩ := HP_rep _ hbA hy
    have hvA : ∀ v ∈ (HP_ext_finite (TS ∪ AS)).toFinset, id v ∈ Aset := fun v hv => by
      rw [Set.Finite.mem_toFinset] at hv
      rw [hAS]; exact extremePoints_subset hv
    have haff := hAaff _ w id hw0 hw1 hvA
    have e : g (∑ v ∈ (HP_ext_finite (TS ∪ AS)).toFinset, w v • id v) =
        ∑ v ∈ (HP_ext_finite (TS ∪ AS)).toFinset, w v * g (id v) :=
      saa_affine h _ w id _ (fun ω => haff ω) s N
    simp only [id] at e
    rw [← hwy, e]
    calc g astar = ∑ v ∈ (HP_ext_finite (TS ∪ AS)).toFinset, w v * g astar := by
          rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (by
          apply hamin'
          rw [Set.Finite.mem_toFinset] at hv
          rw [hAS]; exact hv) (hw0 v hv)
  -- (S2) on Θ ∩ box
  have S2 : ∀ y ∈ Θ, y ∈ HP BS → g astar ≤ g y ∧ (g y ≤ g astar → y ∈ Aset) := by
    intro y hyΘ hyB
    obtain ⟨σ, hσ⟩ := hcover y hyΘ hyB
    obtain ⟨w, hw0, hw1, hwy⟩ := HP_rep _ (hcell_bdd σ) hσ
    set F := (HP_ext_finite (CS σ)).toFinset
    have hvcell : ∀ v ∈ F, v ∈ HP (CS σ) := fun v hv =>
      extremePoints_subset ((Set.Finite.mem_toFinset _).1 hv)
    have hPSy : y ∈ HP (PS σ) := by rw [hCS] at hσ; exact hσ.2
    have haff : ∀ ω, h y ω = ∑ v ∈ F, w v * h (id v) ω := by
      intro ω
      rw [hcell_h σ y hPSy ω, ← hwy, inner_sum]
      simp only [real_inner_smul_right, id]
      rw [show b ω (σ ω) = ∑ v ∈ F, w v * b ω (σ ω) by rw [← Finset.sum_mul, hw1, one_mul],
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv' : v ∈ HP (PS σ) := by have := hvcell v hv; rw [hCS] at this; exact this.2
      rw [hcell_h σ v hv' ω]; ring
    have hgy : g y = ∑ v ∈ F, w v * g v := saa_affine h F w id y haff s N
    have hvlow : ∀ v ∈ F, g astar ≤ g v ∧ (v ∉ Aset → g astar < g v) := by
      intro v hv
      by_cases hvA : v ∈ Aset
      · exact ⟨S1 v hvA, fun h' => absurd hvA h'⟩
      · have hvX2 : v ∈ X2 := Set.mem_iUnion.2 ⟨σ, (Set.Finite.mem_toFinset _).1 hv, hvA⟩
        have := Hc astar hastar v hvX2
        exact ⟨this.le, fun _ => this⟩
    have hsum_eq : g y - g astar = ∑ v ∈ F, w v * (g v - g astar) := by
      rw [hgy]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    have hnn : ∀ v ∈ F, 0 ≤ w v * (g v - g astar) := fun v hv =>
      mul_nonneg (hw0 v hv) (sub_nonneg.2 (hvlow v hv).1)
    refine ⟨by linarith [Finset.sum_nonneg hnn], fun hle' => ?_⟩
    have hz : ∑ v ∈ F, w v * (g v - g astar) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz
    -- every vertex with positive weight lies in A
    set p' : E m → E m := fun v => if v ∈ Aset then v else astar
    have hrepl : ∑ v ∈ F, w v • p' v = y := by
      rw [← hwy]
      refine Finset.sum_congr rfl fun v hv => ?_
      by_cases hvA : v ∈ Aset
      · simp [p', hvA]
      · have hw : w v = 0 := by
          rcases mul_eq_zero.1 (hzero v hv) with h0 | h0
          · exact h0
          · exact absurd (sub_eq_zero.1 h0 ▸ (hvlow v hv).2 hvA) (lt_irrefl _)
        simp [hw]
    rw [← hrepl]
    exact hAconv.sum_mem hw0 hw1 fun v _ => by
      by_cases hvA : v ∈ Aset
      · simp [p', hvA]
      · simp [p', hvA, hastarA]
  -- (S3) global lower bound
  have hseg : ∀ y ∈ Θ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → astar + t • (y - astar) ∈ Θ ∧
      g (astar + t • (y - astar)) ≤ (1 - t) * g astar + t * g y := by
    intro y hy t ht0 ht1
    have heq : astar + t • (y - astar) = (1 - t) • astar + t • y := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq]
    refine ⟨hΘv (hAΘ hastarA) hy (by linarith) ht0 (by ring), ?_⟩
    have := hgconv.2 (Set.mem_univ astar) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - t) ht0
      (by ring)
    simpa only [smul_eq_mul] using this
  have hnorm_step : ∀ y : E m, ∀ t t' : ℝ, |t' - t| ≤ 1 / (‖y - astar‖ + 1) →
      ‖astar + t' • (y - astar)‖ < ‖astar + t • (y - astar)‖ + 1 := by
    intro y t t' htt'
    have hpos : 0 < ‖y - astar‖ + 1 := by positivity
    have : astar + t' • (y - astar) = (astar + t • (y - astar)) + (t' - t) • (y - astar) := by
      rw [sub_smul]; abel
    rw [this]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |t' - t| * ‖y - astar‖ ≤ 1 / (‖y - astar‖ + 1) * ‖y - astar‖ :=
      mul_le_mul_of_nonneg_right htt' (norm_nonneg _)
    have h2 : 1 / (‖y - astar‖ + 1) * ‖y - astar‖ < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hpos]; linarith
    linarith
  have S3 : ∀ y ∈ Θ, g astar ≤ g y := by
    intro y hy
    set t := 1 / (‖y - astar‖ + 1)
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [norm_nonneg (y - astar)]
    obtain ⟨hzΘ, hzg⟩ := hseg y hy t ht0.le ht1
    have hzB : astar + t • (y - astar) ∈ HP BS := by
      apply hB1
      have := hnorm_step y 0 t (by rw [sub_zero, abs_of_pos ht0])
      simp only [zero_smul, add_zero] at this
      have := hR0 astar hastarA
      simp only [R]; linarith
    have := (S2 _ hzΘ hzB).1
    nlinarith
  -- (S4) global equality case
  have S4 : ∀ y ∈ Θ, g y ≤ g astar → y ∈ Aset := by
    intro y hy hgy
    set η := 1 / (‖y - astar‖ + 1)
    have hη0 : 0 < η := by positivity
    have hη1 : η ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [norm_nonneg (y - astar)]
    have claim : ∀ n : ℕ, astar + (min 1 (n * η)) • (y - astar) ∈ Aset := by
      intro n
      induction n with
      | zero => simpa using hastarA
      | succ n ih =>
        set t0 := min 1 (n * η)
        set t1 := min 1 ((n + 1 : ℕ) * η)
        have ht1a : 0 ≤ t1 := le_min zero_le_one (by positivity)
        have ht1b : t1 ≤ 1 := min_le_left _ _
        obtain ⟨hzΘ, hzg⟩ := hseg y hy t1 ht1a ht1b
        have hdiff : |t1 - t0| ≤ η := by
          have h1 : t0 ≤ t1 := min_le_min_left _ (by push_cast; nlinarith)
          have h2 : t1 ≤ t0 + η := by
            simp only [t0, t1]
            push_cast
            rcases le_total 1 (n * η) with hc | hc
            · rw [min_eq_left hc]; exact (min_le_left _ _).trans (by linarith)
            · rw [min_eq_right hc]; exact (min_le_right _ _).trans (by linarith)
          rw [abs_of_nonneg (by linarith)]; linarith
        have hzB : astar + t1 • (y - astar) ∈ HP BS := by
          apply hB1
          have := hnorm_step y t0 t1 hdiff
          have := hR0 _ ih
          simp only [R]; linarith
        apply (S2 _ hzΘ hzB).2
        nlinarith
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / η)
    have hmin : min 1 (n * η) = 1 := by
      apply min_eq_left
      rwa [div_le_iff₀ hη0] at hn
    have := claim n
    rw [hmin, one_smul, add_sub_cancel] at this
    exact this
  -- conclusion
  have hargmin : argminOn g Θ = {y | y ∈ Θ ∧ g y ≤ g astar} := by
    ext y
    constructor
    · intro hy; exact ⟨hy.1, hy.2 astar (hAΘ hastarA)⟩
    · rintro ⟨hy, hgy⟩; exact ⟨hy, fun y' hy' => hgy.trans (S3 y' hy')⟩
  refine ⟨⟨astar, hAΘ hastarA, fun y hy => S3 y hy⟩, ?_, ?_⟩
  · rw [hargmin]
    intro y1 hy1 y2 hy2 α β hα hβ hαβ
    refine ⟨hΘv hy1.1 hy2.1 hα hβ hαβ, ?_⟩
    have := hgconv.2 (Set.mem_univ y1) (Set.mem_univ y2) hα hβ hαβ
    simp only [smul_eq_mul] at this
    have e1 := mul_le_mul_of_nonneg_left hy1.2 hα
    have e2 := mul_le_mul_of_nonneg_left hy2.2 hβ
    have e3 : g astar = α * g astar + β * g astar := by rw [← add_mul, hαβ, one_mul]
    linarith
  · rw [hargmin]
    refine ⟨fun y hy => S4 y hy.1 hy.2, ?_⟩
    intro x1 hx1 x2 hx2 z hz hzseg
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hzseg
    refine ⟨hAΘ hx1, ?_⟩
    have haff := hAaff (Finset.univ : Finset (Fin 2)) ![α, β] ![x1, x2]
      (fun i _ => by fin_cases i <;> simp [hα.le, hβ.le]) (by simp [hαβ])
      (fun i _ => by fin_cases i <;> simp [hx1, hx2])
    have hg : g (∑ i : Fin 2, ![α, β] i • ![x1, x2] i) = ∑ i : Fin 2, ![α, β] i * g (![x1, x2] i) :=
      saa_affine h (Finset.univ : Finset (Fin 2)) ![α, β] ![x1, x2] _ haff s N
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have h1 := S1 x1 hx1
    have h2 := S1 x2 hx2
    have h3 := hz.2
    rw [hg] at h3
    have e2 := mul_le_mul_of_nonneg_left h2 hβ.le
    have e3 : g astar = α * g astar + β * g astar := by rw [← add_mul, hαβ, one_mul]
    have e4 : α * g x1 ≤ α * g astar := by linarith
    exact le_of_mul_le_mul_left e4 hα
