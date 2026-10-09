-- Prove2me | solution 1 for StochasticOrders.Multivariate.multivariate_order_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:32:13.095568+00:00
-- url     : https://prove2.me/submissions/e94c47ed-c8af-4b6f-8df3-3553a96d4b03

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2

set_option autoImplicit false

namespace SO174

open MeasureTheory ProbabilityTheory Filter Topology StochasticOrders.Multivariate

/-- finite-support representation. -/
lemma meas_repr {n : ℕ} (μ : Measure (Fin n → ℝ)) (s : Finset (Fin n → ℝ)) (hs : μ (↑s)ᶜ = 0) :
    μ = ∑ a : ↥s, μ {a.1} • Measure.dirac a.1 := by
  classical
  ext U hU
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hU, smul_eq_mul]
  rw [Finset.sum_coe_sort s (fun a => μ {a} * U.indicator 1 a)]
  rw [← measure_inter_conull (s := U) hs,
    show U ∩ ↑s = ↑(s.filter (· ∈ U)) by ext x; simp [and_comm],
    ← sum_measure_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ U <;> simp [ha]

lemma int_repr {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (s : Finset (Fin n → ℝ))
    (hs : μ (↑s)ᶜ = 0) (φ : (Fin n → ℝ) → ℝ) :
    ∫ x, φ x ∂μ = ∑ a : ↥s, μ.real {a.1} * φ a.1 := by
  conv_lhs => rw [meas_repr μ s hs]
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_smul_measure, integral_dirac, measureReal_def, smul_eq_mul]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure (measure_ne_top _ _)

/-- layer cake: upper-set domination gives integral domination for bounded monotone tests. -/
lemma dom_int {n : ℕ} (μ ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hord : ∀ U : Set (Fin n → ℝ), IsUpperSet U → MeasurableSet U → μ U ≤ ν U)
    (φ : (Fin n → ℝ) → ℝ) (hm : Measurable φ) (hmono : Monotone φ) (C : ℝ)
    (hC : ∀ x, |φ x| ≤ C) : ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν := by
  have hψ0 : ∀ x, 0 ≤ φ x + C := fun x => by have := (abs_le.1 (hC x)).1; linarith
  have hint : ∀ (ρ : Measure (Fin n → ℝ)) [IsProbabilityMeasure ρ], Integrable φ ρ :=
    fun ρ _ => Integrable.of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have key : ∫⁻ x, ENNReal.ofReal (φ x + C) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (φ x + C) ∂ν := by
    rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hψ0) (hm.add_const C).aemeasurable,
      lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hψ0) (hm.add_const C).aemeasurable]
    refine lintegral_mono fun r => hord _ ?_ (measurableSet_lt measurable_const (hm.add_const C))
    intro a b hab ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := hmono hab
    linarith
  have e : ∀ (ρ : Measure (Fin n → ℝ)) [IsProbabilityMeasure ρ],
      ∫ x, φ x ∂ρ + C = (∫⁻ x, ENNReal.ofReal (φ x + C) ∂ρ).toReal := by
    intro ρ _
    rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hψ0)
      (hm.add_const C).aestronglyMeasurable, integral_add (hint ρ) (integrable_const C)]
    simp
  have fin : ∫⁻ x, ENNReal.ofReal (φ x + C) ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal (2 * C) ∂ν) ?_
      (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
    · simp only [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · have := (abs_le.1 (hC x)).2; linarith
  have := ENNReal.toReal_mono fin key
  linarith [e μ, e ν]

/-- S1 finite Strassen for the coordinatewise order. -/
theorem strassen_st_finite {n : ℕ} (μ ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s t : Finset (Fin n → ℝ)) (hs : μ (↑s)ᶜ = 0) (ht : ν (↑t)ᶜ = 0)
    (hord : ∀ U : Set (Fin n → ℝ), IsUpperSet U → MeasurableSet U → μ U ≤ ν U) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ π {p | p.1 ≤ p.2} = 1 := by
  classical
  set Ed : Finset ((Fin n → ℝ) × (Fin n → ℝ)) := (s ×ˢ t).filter (fun p => p.1 ≤ p.2) with hEd
  let L : (↥Ed → ℝ) →ₗ[ℝ] (↥s → ℝ) × (↥t → ℝ) :=
    { toFun := fun x => (fun a => ∑ e, x e * (if (e : (Fin n → ℝ) × (Fin n → ℝ)).1 = a.1 then 1 else 0),
                         fun b => ∑ e, x e * (if (e : (Fin n → ℝ) × (Fin n → ℝ)).2 = b.1 then 1 else 0))
      map_add' := by
        intro x y
        ext i <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hLapp : ∀ x, L x = (fun a => ∑ e, x e * (if (e : (Fin n → ℝ) × (Fin n → ℝ)).1 = a.1 then 1 else 0),
      fun b => ∑ e, x e * (if (e : (Fin n → ℝ) × (Fin n → ℝ)).2 = b.1 then 1 else 0)) := fun x => rfl
  let z0 : (↥s → ℝ) × (↥t → ℝ) := (fun a => μ.real {a.1}, fun b => ν.real {b.1})
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp at hs
  by_cases hz : z0 ∈ L '' stdSimplex ℝ ↥Ed
  · obtain ⟨x, hx, hLx⟩ := hz
    have hx0 : ∀ e, 0 ≤ x e := hx.1
    have hx1 : ∑ e, x e = 1 := hx.2
    let π : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
      ∑ e : ↥Ed, ENNReal.ofReal (x e) • Measure.dirac (e : (Fin n → ℝ) × (Fin n → ℝ))
    have hπS : ∀ S, MeasurableSet S →
        π S = ∑ e : ↥Ed, ENNReal.ofReal (x e) * S.indicator 1 (e : (Fin n → ℝ) × (Fin n → ℝ)) := by
      intro S hS
      simp only [π, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hS, smul_eq_mul]
    have hsum1 : ∑ e : ↥Ed, ENNReal.ofReal (x e) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => hx0 e), hx1, ENNReal.ofReal_one]
    have hπuniv : π Set.univ = 1 := by
      rw [hπS _ MeasurableSet.univ]; simpa using hsum1
    have marg : ∀ (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasure ρ] (r : Finset (Fin n → ℝ)),
        ρ (↑r)ᶜ = 0 → ∀ (pr : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)), Measurable pr →
        (∀ e : ↥Ed, pr e ∈ r) →
        (∀ a : ↥r, ∑ e : ↥Ed, x e * (if pr e = a.1 then 1 else 0) = ρ.real {a.1}) →
        π.map pr = ρ := by
      intro ρ _ r hr pr hpr hmem hrow
      ext U hU
      rw [Measure.map_apply hpr hU, hπS _ (hpr hU)]
      conv_rhs => rw [meas_repr ρ r hr]
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      simp only [Measure.smul_apply, Measure.dirac_apply' _ hU, smul_eq_mul]
      have h1 : ∀ a : ↥r, ρ {a.1} =
          ∑ e : ↥Ed, ENNReal.ofReal (x e * (if pr e = a.1 then 1 else 0)) := by
        intro a
        rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hx0 e) (by split_ifs <;> norm_num)),
          hrow a, ofReal_measureReal]
      simp_rw [h1, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Fintype.sum_eq_single ⟨pr e, hmem e⟩]
      · simp [Set.indicator_apply]
      · intro a ha
        have : pr e ≠ a.1 := fun h => ha (Subtype.ext h.symm)
        simp [this]
    refine ⟨π, ⟨hπuniv⟩, ?_, ?_, ?_⟩
    · refine marg μ s hs Prod.fst measurable_fst ?_ ?_
      · intro e; have := e.2; simp only [hEd, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.1
      · intro a; exact congrFun (congrArg Prod.fst hLx) a
    · refine marg ν t ht Prod.snd measurable_snd ?_ ?_
      · intro e; have := e.2; simp only [hEd, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.2
      · intro a; exact congrFun (congrArg Prod.snd hLx) a
    · rw [hπS _ (measurableSet_le measurable_fst measurable_snd)]
      rw [← hsum1]
      refine Finset.sum_congr rfl fun e _ => ?_
      have := e.2; simp only [hEd, Finset.mem_filter] at this
      have hmem : (e : (Fin n → ℝ) × (Fin n → ℝ)) ∈ {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 ≤ p.2} :=
        this.2
      simp [Set.indicator_of_mem hmem]
  · exfalso
    have hK : IsCompact (L '' stdSimplex ℝ ↥Ed) :=
      (isCompact_stdSimplex ℝ ↥Ed).image L.continuous_of_finiteDimensional
    have hKc : Convex ℝ (L '' stdSimplex ℝ ↥Ed) := (convex_stdSimplex ℝ _).linear_image L
    obtain ⟨f, u0, v0, hfK, huv, hfz⟩ := _root_.geometric_hahn_banach_compact_closed hKc hK
      (convex_singleton z0) isClosed_singleton (Set.disjoint_singleton_right.2 hz)
    have hfz' : ∀ k ∈ L '' stdSimplex ℝ ↥Ed, f k < f z0 :=
      fun k hk => (hfK k hk).trans (huv.trans (hfz z0 rfl))
    have hf : ∀ (y : ↥s → ℝ) (z : ↥t → ℝ), f (y, z) =
        ∑ a, y a * f (Pi.single a 1, 0) + ∑ b, z b * f (0, Pi.single b 1) := by
      intro y z
      have hy : ((y, z) : (↥s → ℝ) × (↥t → ℝ)) =
          ∑ a, y a • ((Pi.single a (1 : ℝ), 0) : (↥s → ℝ) × (↥t → ℝ)) +
            ∑ b, z b • (((0 : ↥s → ℝ), Pi.single b (1 : ℝ)) : (↥s → ℝ) × (↥t → ℝ)) := by
        ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
      rw [hy, map_add, map_sum, map_sum]
      simp only [map_smul, smul_eq_mul]
    set u : ↥s → ℝ := fun a => f (Pi.single a 1, 0) with hu
    set v : ↥t → ℝ := fun b => f (0, Pi.single b 1) with hv
    set c := f z0 with hcdef
    have hc : c = ∑ a, μ.real {a.1} * u a + ∑ b, ν.real {b.1} * v b := hf _ _
    have hedge : ∀ (a : ↥s) (b : ↥t), a.1 ≤ b.1 → u a + v b < c := by
      intro a b hab
      have hmemE : (a.1, b.1) ∈ Ed := by
        simp only [hEd, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨a.2, b.2⟩, hab⟩
      set e0 : ↥Ed := ⟨(a.1, b.1), hmemE⟩
      have hL : L (Pi.single e0 1) = (Pi.single a 1, Pi.single b 1) := by
        rw [hLapp]
        ext a'
        · show ∑ e, (Pi.single e0 1 : ↥Ed → ℝ) e *
              (if (e : (Fin n → ℝ) × (Fin n → ℝ)).1 = a'.1 then 1 else 0) = (Pi.single a 1 : ↥s → ℝ) a'
          rw [Fintype.sum_eq_single e0 (fun e he => by rw [Pi.single_eq_of_ne he, zero_mul]),
            Pi.single_eq_same, one_mul]
          by_cases h : a' = a
          · subst h; simp [e0]
          · rw [Pi.single_eq_of_ne h]
            have : a.1 ≠ a'.1 := fun h' => h (Subtype.ext h'.symm)
            simp [e0, this]
        · show ∑ e, (Pi.single e0 1 : ↥Ed → ℝ) e *
              (if (e : (Fin n → ℝ) × (Fin n → ℝ)).2 = a'.1 then 1 else 0) = (Pi.single b 1 : ↥t → ℝ) a'
          rw [Fintype.sum_eq_single e0 (fun e he => by rw [Pi.single_eq_of_ne he, zero_mul]),
            Pi.single_eq_same, one_mul]
          by_cases h : a' = b
          · subst h; simp [e0]
          · rw [Pi.single_eq_of_ne h]
            have : b.1 ≠ a'.1 := fun h' => h (Subtype.ext h'.symm)
            simp [e0, this]
      have := hfz' _ ⟨Pi.single e0 1, single_mem_stdSimplex _ _, hL⟩
      rw [hf] at this
      simpa [Pi.single_apply, u, v] using this
    set m : ℝ := c - ∑ b, |v b| - 1 with hmdef
    have hm : ∀ b : ↥t, m < c - v b := by
      intro b
      have h1 := Finset.single_le_sum (f := fun b => |v b|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)
      have h2 := le_abs_self (v b)
      linarith
    obtain ⟨a0, ha0⟩ := hsne
    have hsne' : (Finset.univ : Finset ↥s).Nonempty := ⟨⟨a0, ha0⟩, Finset.mem_univ _⟩
    let g : ↥s → (Fin n → ℝ) → ℝ := fun a x => if a.1 ≤ x then max m (u a) else m
    let φ := Finset.univ.sup' hsne' g
    have hφx : ∀ x, φ x = Finset.univ.sup' hsne' (fun a => g a x) :=
      fun x => Finset.sup'_apply _ _ _
    have hφm : Measurable φ :=
      Finset.measurable_sup' hsne' fun a _ => Measurable.ite measurableSet_Ici measurable_const
        measurable_const
    have hφmono : Monotone φ := by
      intro x y hxy
      rw [hφx, hφx]
      apply Finset.sup'_le
      intro a _
      apply Finset.le_sup'_of_le _ (Finset.mem_univ a)
      simp only [g]
      split_ifs with h1 h2 <;>
        first | exact le_rfl | exact le_max_left _ _ | exact absurd (h1.trans hxy) h2
    have hφs : ∀ a : ↥s, u a ≤ φ a.1 := by
      intro a
      rw [hφx]
      exact Finset.le_sup'_of_le _ (Finset.mem_univ a) (by simp [g])
    have hφt : ∀ b : ↥t, φ b.1 < c - v b := by
      intro b
      rw [hφx, Finset.sup'_lt_iff]
      intro a _
      simp only [g]
      split_ifs with h
      · exact max_lt (hm b) (by linarith [hedge a b h])
      · exact hm b
    have hφbd : ∀ x, |φ x| ≤ |m| + ∑ a, |u a| := by
      intro x
      have hS : 0 ≤ ∑ a, |u a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have lo : m ≤ φ x := by
        rw [hφx]
        refine Finset.le_sup'_of_le _ (Finset.mem_univ ⟨a0, ha0⟩) ?_
        simp only [g]; split_ifs <;> simp
      have hi : φ x ≤ |m| + ∑ a, |u a| := by
        rw [hφx]
        apply Finset.sup'_le
        intro a _
        simp only [g]
        have h1 := Finset.single_le_sum (f := fun a => |u a|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ a)
        have h2 := le_abs_self (u a)
        have h3 := le_abs_self m
        split_ifs
        · exact max_le (by linarith) (by linarith [abs_nonneg m])
        · linarith
      rw [abs_le]
      constructor
      · have := neg_abs_le m; linarith
      · exact hi
    have hdom := dom_int μ ν hord φ hφm hφmono _ hφbd
    rw [int_repr μ s hs φ, int_repr ν t ht φ] at hdom
    have hνsum : ∑ b : ↥t, ν.real {b.1} = 1 := by
      have := int_repr ν t ht (fun _ => 1)
      simpa using this.symm
    have h1 : ∑ a : ↥s, μ.real {a.1} * u a ≤ ∑ a : ↥s, μ.real {a.1} * φ a.1 :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hφs a) measureReal_nonneg
    obtain ⟨b0, hb0⟩ : ∃ b : ↥t, 0 < ν.real {b.1} := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      have : ∑ b : ↥t, ν.real {b.1} ≤ 0 := Finset.sum_nonpos fun b _ => hne b
      linarith
    have h2 : ∑ b : ↥t, ν.real {b.1} * φ b.1 < ∑ b : ↥t, ν.real {b.1} * (c - v b) :=
      Finset.sum_lt_sum (fun b _ => mul_le_mul_of_nonneg_left (hφt b).le measureReal_nonneg)
        ⟨b0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hφt b0) hb0⟩
    have h3 : ∑ b : ↥t, ν.real {b.1} * (c - v b) = c - ∑ b : ↥t, ν.real {b.1} * v b := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hνsum, one_mul]
    linarith

/-- clamp to `[-k,k]`. -/
noncomputable def clampK (k : ℕ) (t : ℝ) : ℝ := max (-(k : ℝ)) (min t k)

lemma clampK_mono (k : ℕ) : Monotone (clampK k) := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right _ h)

lemma clampK_mem (k : ℕ) (t : ℝ) : -(k : ℝ) ≤ clampK k t ∧ clampK k t ≤ k := by
  unfold clampK
  refine ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma clampK_eq (k : ℕ) (t : ℝ) (h : |t| ≤ k) : clampK k t = t := by
  unfold clampK
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

noncomputable def floK (k : ℕ) (t : ℝ) : ℝ := (⌊((k : ℝ) + 1) * clampK k t⌋ : ℝ) / ((k : ℝ) + 1)
noncomputable def ceiK (k : ℕ) (t : ℝ) : ℝ := (⌈((k : ℝ) + 1) * clampK k t⌉ : ℝ) / ((k : ℝ) + 1)

lemma floK_mono (k : ℕ) : Monotone (floK k) := fun a b h => by
  unfold floK
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  apply div_le_div_of_nonneg_right _ hk.le
  exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_left (clampK_mono k h) hk.le)

lemma ceiK_mono (k : ℕ) : Monotone (ceiK k) := fun a b h => by
  unfold ceiK
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  apply div_le_div_of_nonneg_right _ hk.le
  exact_mod_cast Int.ceil_mono (mul_le_mul_of_nonneg_left (clampK_mono k h) hk.le)

lemma flo_bounds (k : ℕ) (t : ℝ) :
    t - 1 / ((k : ℝ) + 1) ≤ (⌊((k : ℝ) + 1) * t⌋ : ℝ) / ((k : ℝ) + 1) ∧
      (⌊((k : ℝ) + 1) * t⌋ : ℝ) / ((k : ℝ) + 1) ≤ t := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 := Int.floor_le (((k : ℝ) + 1) * t)
  have h2 := Int.lt_floor_add_one (((k : ℝ) + 1) * t)
  constructor
  · rw [le_div_iff₀ hk, sub_mul, div_mul_cancel₀ _ hk.ne']
    linarith
  · rw [div_le_iff₀ hk]
    linarith

lemma cei_bounds (k : ℕ) (t : ℝ) :
    t ≤ (⌈((k : ℝ) + 1) * t⌉ : ℝ) / ((k : ℝ) + 1) ∧
      (⌈((k : ℝ) + 1) * t⌉ : ℝ) / ((k : ℝ) + 1) ≤ t + 1 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 := Int.le_ceil (((k : ℝ) + 1) * t)
  have h2 := Int.ceil_lt_add_one (((k : ℝ) + 1) * t)
  constructor
  · rw [le_div_iff₀ hk]
    linarith
  · rw [div_le_iff₀ hk]
    have e : (t + 1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = ((k : ℝ) + 1) * t + 1 := by
      rw [add_mul, div_mul_cancel₀ (1 : ℝ) hk.ne', mul_comm]
    rw [e]
    linarith

lemma eventually_clamp (t : ℝ) : ∀ᶠ k : ℕ in atTop, clampK k t = t := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  filter_upwards [eventually_ge_atTop N] with k hk
  exact clampK_eq k t (hN.trans (by exact_mod_cast hk))

lemma tendsto_floK (t : ℝ) : Tendsto (fun k => floK k t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun k : ℕ => t - 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_clamp t] with k hk
    have := (flo_bounds k t).1
    unfold floK; rw [hk]; exact this
  · filter_upwards [eventually_clamp t] with k hk
    have := (flo_bounds k t).2
    unfold floK; rw [hk]; exact this

lemma tendsto_ceiK (t : ℝ) : Tendsto (fun k => ceiK k t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_
  · filter_upwards [eventually_clamp t] with k hk
    have := (cei_bounds k t).1
    unfold ceiK; rw [hk]; exact this
  · filter_upwards [eventually_clamp t] with k hk
    have := (cei_bounds k t).2
    unfold ceiK; rw [hk]; exact this

lemma floK_range_finite (k : ℕ) : (Set.range (floK k)).Finite := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set m : ℤ := ((k : ℤ) + 1) * k
  refine ((Set.finite_Icc (-m - 1) m).image (fun z : ℤ => (z : ℝ) / ((k : ℝ) + 1))).subset ?_
  rintro _ ⟨t, rfl⟩
  refine ⟨⌊((k : ℝ) + 1) * clampK k t⌋, ⟨?_, ?_⟩, rfl⟩
  · have hc := (clampK_mem k t).1
    have : ((-m - 1 : ℤ) : ℝ) ≤ ((k : ℝ) + 1) * clampK k t := by
      push_cast [m]; nlinarith
    exact Int.le_floor.2 this
  · have hc := (clampK_mem k t).2
    have : ((k : ℝ) + 1) * clampK k t ≤ (m : ℝ) := by
      push_cast [m]; nlinarith
    exact Int.floor_le_iff.2 (by linarith)

lemma ceiK_range_finite (k : ℕ) : (Set.range (ceiK k)).Finite := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set m : ℤ := ((k : ℤ) + 1) * k
  refine ((Set.finite_Icc (-m) (m + 1)).image (fun z : ℤ => (z : ℝ) / ((k : ℝ) + 1))).subset ?_
  rintro _ ⟨t, rfl⟩
  refine ⟨⌈((k : ℝ) + 1) * clampK k t⌉, ⟨?_, ?_⟩, rfl⟩
  · have hc := (clampK_mem k t).1
    have : ((-m : ℤ) : ℝ) ≤ ((k : ℝ) + 1) * clampK k t := by
      push_cast [m]; nlinarith
    exact Int.le_ceil_iff.2 (by linarith)
  · have hc := (clampK_mem k t).2
    have : ((k : ℝ) + 1) * clampK k t ≤ (m : ℝ) := by
      push_cast [m]; nlinarith
    exact Int.ceil_le.2 (by push_cast; linarith)

lemma measurable_floK (k : ℕ) : Measurable (floK k) := by
  unfold floK clampK; fun_prop

lemma measurable_ceiK (k : ℕ) : Measurable (ceiK k) := by
  unfold ceiK clampK; fun_prop

/-- S2 monotone finite-range grid maps squeezing the identity. -/
theorem grid_approx (n : ℕ) : ∃ lo hi : ℕ → (Fin n → ℝ) → (Fin n → ℝ),
    (∀ k, Measurable (lo k) ∧ Measurable (hi k) ∧ Monotone (lo k) ∧ Monotone (hi k) ∧
      (Set.range (lo k)).Finite ∧ (Set.range (hi k)).Finite) ∧
    (∀ k x, lo k x ≤ hi k x) ∧
    (∀ x, Tendsto (fun k => lo k x) atTop (𝓝 x)) ∧
    (∀ x, Tendsto (fun k => hi k x) atTop (𝓝 x)) := by
  refine ⟨fun k x i => floK k (x i), fun k x i => ceiK k (x i), fun k => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · exact measurable_pi_lambda _ fun i => (measurable_floK k).comp (measurable_pi_apply i)
  · exact measurable_pi_lambda _ fun i => (measurable_ceiK k).comp (measurable_pi_apply i)
  · exact fun a b h i => floK_mono k (h i)
  · exact fun a b h i => ceiK_mono k (h i)
  · refine (Set.Finite.pi (t := fun _ : Fin n => Set.range (floK k))
      fun _ => floK_range_finite k).subset ?_
    rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
  · refine (Set.Finite.pi (t := fun _ : Fin n => Set.range (ceiK k))
      fun _ => ceiK_range_finite k).subset ?_
    rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
  · intro k x i
    unfold floK ceiK
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    apply div_le_div_of_nonneg_right _ hk.le
    exact_mod_cast Int.floor_le_ceil _
  · exact fun x => tendsto_pi_nhds.2 fun i => tendsto_floK (x i)
  · exact fun x => tendsto_pi_nhds.2 fun i => tendsto_ceiK (x i)

/-- S3 Prokhorov + Portmanteau. -/
theorem coupling_limit {n : ℕ} (μ ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (μk νk : ℕ → Measure (Fin n → ℝ))
    (hμk : ∀ k, IsProbabilityMeasure (μk k)) (hνk : ∀ k, IsProbabilityMeasure (νk k))
    (hμ : ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      Tendsto (fun k => ∫ x, g x ∂(μk k)) atTop (𝓝 (∫ x, g x ∂μ)))
    (hν : ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      Tendsto (fun k => ∫ x, g x ∂(νk k)) atTop (𝓝 (∫ x, g x ∂ν)))
    (πk : ℕ → Measure ((Fin n → ℝ) × (Fin n → ℝ)))
    (hπ : ∀ k, IsProbabilityMeasure (πk k) ∧ (πk k).map Prod.fst = μk k ∧
      (πk k).map Prod.snd = νk k ∧ πk k {p | p.1 ≤ p.2} = 1) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ π {p | p.1 ≤ p.2} = 1 := by
  classical
  let Pk : ℕ → ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ)) := fun k => ⟨πk k, (hπ k).1⟩
  let μP : ProbabilityMeasure (Fin n → ℝ) := ⟨μ, inferInstance⟩
  let νP : ProbabilityMeasure (Fin n → ℝ) := ⟨ν, inferInstance⟩
  let μkP : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun k => ⟨μk k, hμk k⟩
  let νkP : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun k => ⟨νk k, hνk k⟩
  have tμ : Tendsto μkP atTop (𝓝 μP) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hμ
  have tν : Tendsto νkP atTop (𝓝 νP) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hν
  have tight_of : ∀ (Qs : ℕ → ProbabilityMeasure (Fin n → ℝ)) (Q : ProbabilityMeasure (Fin n → ℝ)),
      Tendsto Qs atTop (𝓝 Q) →
      IsTightMeasureSet {((P : ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)) |
        P ∈ Set.range Qs} := by
    intro Qs Q hQ
    apply isTightMeasureSet_of_isCompact_closure
    have hc := hQ.isCompact_insert_range
    exact hc.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert _ _) hc.isClosed)
  have tightπ : IsTightMeasureSet {((P : ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ))) :
      Measure ((Fin n → ℝ) × (Fin n → ℝ))) | P ∈ Set.range Pk} := by
    apply IsTightMeasureSet.prodMk
    · refine (tight_of μkP μP tμ).subset ?_
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨μkP k, ⟨k, rfl⟩, (hπ k).2.1.symm⟩
    · refine (tight_of νkP νP tν).subset ?_
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨νkP k, ⟨k, rfl⟩, (hπ k).2.2.1.symm⟩
  have hK := isCompact_closure_of_isTightMeasureSet tightπ
  obtain ⟨π0, -, hπ0⟩ := hK.exists_clusterPt (f := map Pk atTop)
    (by rw [le_principal_iff]; exact mem_map.2 (Eventually.of_forall fun k => subset_closure ⟨k, rfl⟩))
  have hNe : (𝓝 π0 ⊓ map Pk atTop).NeBot := hπ0
  have hLid : Tendsto (fun P => P) (𝓝 π0 ⊓ map Pk atTop) (𝓝 π0) :=
    tendsto_id.mono_left inf_le_left
  have m1 : π0.map measurable_fst.aemeasurable = μP := by
    refine tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hLid) ?_
    refine (tendsto_map'_iff.2 ?_).mono_left inf_le_right
    convert tμ using 1
    funext k
    apply Subtype.ext
    exact (hπ k).2.1
  have m2 : π0.map measurable_snd.aemeasurable = νP := by
    refine tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_snd).continuousAt.tendsto.comp hLid) ?_
    refine (tendsto_map'_iff.2 ?_).mono_left inf_le_right
    convert tν using 1
    funext k
    apply Subtype.ext
    exact (hπ k).2.2.1
  have hC : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hLid hC
  have hev : ∀ᶠ P in 𝓝 π0 ⊓ map Pk atTop,
      ((P : ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ))) : Measure _)
        {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 ≤ p.2} = 1 :=
    Filter.mem_inf_of_right (mem_map.2 (Eventually.of_forall fun k => (hπ k).2.2.2))
  rw [Filter.limsup_congr hev, limsup_const] at hlim
  refine ⟨(π0 : Measure _), inferInstance, ?_, ?_, le_antisymm prob_le_one hlim⟩
  · have := congrArg (fun P : ProbabilityMeasure (Fin n → ℝ) => (P : Measure (Fin n → ℝ))) m1
    simp only [ProbabilityMeasure.toMeasure_map] at this
    exact this
  · have := congrArg (fun P : ProbabilityMeasure (Fin n → ℝ) => (P : Measure (Fin n → ℝ))) m2
    simp only [ProbabilityMeasure.toMeasure_map] at this
    exact this

/-- Strassen's theorem for laws on `ℝⁿ` (from S1-S3). -/
theorem strassen_st {n : ℕ} (P Q : Measure (Fin n → ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hord : ∀ U : Set (Fin n → ℝ), IsUpperSet U → MeasurableSet U → P U ≤ Q U) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧
      π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧ π {p | p.1 ≤ p.2} = 1 := by
  obtain ⟨lo, hi, hmeas, hlohi, hlo, hhi⟩ := grid_approx n
  have hP : ∀ k, IsProbabilityMeasure (P.map (lo k)) :=
    fun k => Measure.isProbabilityMeasure_map (hmeas k).1.aemeasurable
  have hQ : ∀ k, IsProbabilityMeasure (Q.map (hi k)) :=
    fun k => Measure.isProbabilityMeasure_map (hmeas k).2.1.aemeasurable
  have hπ : ∀ k, ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧
      π.map Prod.fst = P.map (lo k) ∧ π.map Prod.snd = Q.map (hi k) ∧
      π {p | p.1 ≤ p.2} = 1 := by
    intro k
    obtain ⟨hlm, hhm, hlmono, hhmono, hlf, hhf⟩ := hmeas k
    have := hP k
    have := hQ k
    refine strassen_st_finite (P.map (lo k)) (Q.map (hi k)) hlf.toFinset hhf.toFinset ?_ ?_ ?_
    · rw [Measure.map_apply hlm (hlf.toFinset.finite_toSet.measurableSet.compl)]
      have : lo k ⁻¹' (↑hlf.toFinset)ᶜ = ∅ := by
        ext x; simp
      rw [this, measure_empty]
    · rw [Measure.map_apply hhm (hhf.toFinset.finite_toSet.measurableSet.compl)]
      have : hi k ⁻¹' (↑hhf.toFinset)ᶜ = ∅ := by
        ext x; simp
      rw [this, measure_empty]
    · intro U hU hUm
      rw [Measure.map_apply hlm hUm, Measure.map_apply hhm hUm]
      calc P (lo k ⁻¹' U) ≤ Q (lo k ⁻¹' U) :=
            hord _ (fun a b hab ha => hU (hlmono hab) ha) (hlm hUm)
        _ ≤ Q (hi k ⁻¹' U) := measure_mono (fun x hx => hU (hlohi k x) hx)
  choose πk hπk using hπ
  have conv : ∀ (R : Measure (Fin n → ℝ)) [IsProbabilityMeasure R]
      (f : ℕ → (Fin n → ℝ) → (Fin n → ℝ)), (∀ k, Measurable (f k)) →
      (∀ x, Tendsto (fun k => f k x) atTop (𝓝 x)) →
      ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
        Tendsto (fun k => ∫ x, g x ∂(Measure.map (f k) R)) atTop (𝓝 (∫ x, g x ∂(R))) := by
    intro R _ f hf hfx g
    have h1 : ∀ k, ∫ x, g x ∂(Measure.map (f k) R) = ∫ x, g (f k x) ∂(R) := fun k =>
      integral_map (hf k).aemeasurable g.continuous.aestronglyMeasurable
    simp_rw [h1]
    exact tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
      (fun k => (g.continuous.measurable.comp (hf k)).aestronglyMeasurable)
      (integrable_const _)
      (fun k => Eventually.of_forall fun x => g.norm_coe_le_norm _)
      (Eventually.of_forall fun x => (g.continuous.tendsto x).comp (hfx x))
  exact coupling_limit P Q (fun k => P.map (lo k)) (fun k => Q.map (hi k)) hP hQ
    (conv P lo (fun k => (hmeas k).1) hlo) (conv Q hi (fun k => (hmeas k).2.1) hhi) πk hπk

/-- The order dominates on measurable upper sets of the laws. -/
theorem law_upper {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h : MultivariateOrder μ ν X Y) (U : Set (Fin n → ℝ)) (hU : IsUpperSet U)
    (hUm : MeasurableSet U) : μ.map X U ≤ ν.map Y U := by
  set φ : (Fin n → ℝ) → ℝ := U.indicator (fun _ => (1 : ℝ)) with hφdef
  have hφm : Measurable φ := measurable_const.indicator hUm
  have hφmono : Monotone φ := by
    intro a b hab
    by_cases ha : a ∈ U
    · have hb : b ∈ U := hU hab ha
      simp [hφdef, ha, hb]
    · by_cases hb : b ∈ U <;> simp [hφdef, ha, hb]
  have hbd : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x; by_cases hx : x ∈ U <;> simp [hφdef, hx]
  have hiX : Integrable (φ ∘ X) μ :=
    Integrable.of_bound (hφm.comp hX).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => hbd _)
  have hiY : Integrable (φ ∘ Y) ν :=
    Integrable.of_bound (hφm.comp hY).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => hbd _)
  have key := h φ hφm hφmono hiX hiY
  rw [← integral_map hX.aemeasurable hφm.aestronglyMeasurable,
    ← integral_map hY.aemeasurable hφm.aestronglyMeasurable] at key
  have := Measure.isProbabilityMeasure_map (μ := μ) hX.aemeasurable
  have := Measure.isProbabilityMeasure_map (μ := ν) hY.aemeasurable
  have e1 : ∫ x, φ x ∂(μ.map X) = (μ.map X).real U := integral_indicator_one hUm
  have e2 : ∫ x, φ x ∂(ν.map Y) = (ν.map Y).real U := integral_indicator_one hUm
  rw [e1, e2] at key
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 key

/-- S4 the easy direction. -/
theorem order_of_coupling {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace Ω''] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') (ρ : Measure Ω'')
    [IsProbabilityMeasure ρ]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (Xhat Yhat : Ω'' → Fin n → ℝ)
    (hXm : Measurable Xhat) (hYm : Measurable Yhat)
    (hXh : IdentDistrib Xhat X ρ μ) (hYh : IdentDistrib Yhat Y ρ ν)
    (hle : ρ {ω | Xhat ω ≤ Yhat ω} = 1) :
    MultivariateOrder μ ν X Y := by
  intro φ hφm hφmono hiX hiY
  have hs : MeasurableSet {ω | Xhat ω ≤ Yhat ω} := measurableSet_le hXm hYm
  have hae : ∀ᵐ ω ∂ρ, Xhat ω ≤ Yhat ω := by
    rw [ae_iff]
    have : ρ {ω | Xhat ω ≤ Yhat ω}ᶜ = 0 := (prob_compl_eq_zero_iff hs).2 hle
    simpa [Set.compl_ofPred] using this
  have iX : Integrable (φ ∘ Xhat) ρ := ((hXh.comp hφm).integrable_iff).2 hiX
  have iY : Integrable (φ ∘ Yhat) ρ := ((hYh.comp hφm).integrable_iff).2 hiY
  have e1 : ∫ ω, φ (Xhat ω) ∂ρ = ∫ ω, φ (X ω) ∂μ := (hXh.comp hφm).integral_eq
  have e2 : ∫ ω, φ (Yhat ω) ∂ρ = ∫ ω, φ (Y ω) ∂ν := (hYh.comp hφm).integral_eq
  rw [← e1, ← e2]
  exact integral_mono_ae iX iY (hae.mono fun ω hω => hφmono hω)

end SO174

open MeasureTheory ProbabilityTheory StochasticOrders.Multivariate in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    MultivariateOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧ ρ {ω | Xhat ω ≤ Yhat ω} = 1 := by
  constructor
  · intro h
    have := Measure.isProbabilityMeasure_map (μ := μ) hX.aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := ν) hY.aemeasurable
    obtain ⟨π, hπ, h1, h2, h3⟩ := SO174.strassen_st (μ.map X) (ν.map Y)
      (SO174.law_upper μ ν X Y hX hY h)
    exact ⟨(Fin n → ℝ) × (Fin n → ℝ), inferInstance, π, hπ, Prod.fst, Prod.snd,
      measurable_fst, measurable_snd,
      ⟨measurable_fst.aemeasurable, hX.aemeasurable, h1⟩,
      ⟨measurable_snd.aemeasurable, hY.aemeasurable, h2⟩, h3⟩
  · rintro ⟨Ω'', _, ρ, _, Xhat, Yhat, hXm, hYm, hXh, hYh, hle⟩
    exact SO174.order_of_coupling μ ν ρ X Y Xhat Yhat hXm hYm hXh hYh hle
