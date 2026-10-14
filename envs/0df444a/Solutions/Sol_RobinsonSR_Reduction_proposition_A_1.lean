-- Prove2me | solution 1 for RobinsonSR.Reduction.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:00:00.524987+00:00
-- url     : https://prove2.me/submissions/e7ffa289-fccd-4721-8357-5e756d1f5d66

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace


namespace RobinsonSR.Reduction

section Base

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rsrCone {m : ℕ} (v : Fin m → E) : Set E :=
  {x | ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

theorem rsr_sum_ext {m : ℕ} (v : Fin m → E) (J : Finset (Fin m)) (c : Fin m → ℝ)
    (hc : ∀ i ∉ J, c i = 0) : ∑ i, c i • v i = ∑ j : J, c j • v j := by
  rw [Finset.sum_coe_sort J (fun i => c i • v i)]
  exact (Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hc i hi])).symm

theorem rsr_cara {m : ℕ} (v : Fin m → E) :
    ∀ (T : Finset (Fin m)) (c : Fin m → ℝ), (∀ i, 0 ≤ c i) → (∀ i ∉ T, c i = 0) →
    ∃ J : Finset (Fin m), J ⊆ T ∧ LinearIndependent ℝ (fun j : J => v j) ∧
      ∃ c' : Fin m → ℝ, (∀ i, 0 ≤ c' i) ∧ (∀ i ∉ J, c' i = 0) ∧
        ∑ i, c' i • v i = ∑ i, c i • v i := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro c hc hcT
  by_cases hli : LinearIndependent ℝ (fun j : T => v j)
  · exact ⟨T, Finset.Subset.refl _, hli, c, hc, hcT, rfl⟩
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hli
    set g' : Fin m → ℝ := fun i => if h : i ∈ T then g ⟨i, h⟩ else 0 with hg'
    have hg'T : ∀ i ∉ T, g' i = 0 := fun i hi => by simp [hg', hi]
    have hg'sum : ∑ i, g' i • v i = 0 := by
      rw [rsr_sum_ext v T g' hg'T, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hg', j.2]
    have hex : ∃ h : Fin m → ℝ, ∑ i, h i • v i = 0 ∧ (∀ i ∉ T, h i = 0) ∧ ∃ i, 0 < h i := by
      by_cases hp : ∃ i, 0 < g' i
      · exact ⟨g', hg'sum, hg'T, hp⟩
      · refine ⟨fun i => - g' i, ?_, fun i hi => by simp [hg'T i hi], ?_⟩
        · simp only [neg_smul, Finset.sum_neg_distrib, hg'sum, neg_zero]
        · push_neg at hp
          refine ⟨i0, ?_⟩
          have : g' i0 ≠ 0 := by simpa [hg', i0.2] using hi0
          have := lt_of_le_of_ne (hp i0) this
          linarith
    obtain ⟨h, hsum, hhT, i1, hi1⟩ := hex
    have hne : (T.filter (fun i => 0 < h i)).Nonempty :=
      ⟨i1, Finset.mem_filter.2 ⟨by by_contra hh; exact absurd (hhT i1 hh) hi1.ne', hi1⟩⟩
    obtain ⟨j0, hj0P, hmin⟩ := (T.filter (fun i => 0 < h i)).exists_min_image (fun i => c i / h i) hne
    have hj0T : j0 ∈ T := (Finset.mem_filter.1 hj0P).1
    have hj0pos : 0 < h j0 := (Finset.mem_filter.1 hj0P).2
    set θ := c j0 / h j0 with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (hc _) hj0pos.le
    have hc'' : ∀ i, 0 ≤ c i - θ * h i := by
      intro i
      by_cases hpos : 0 < h i
      · have hiT : i ∈ T := by by_contra hh; exact absurd (hhT i hh) hpos.ne'
        have := hmin i (Finset.mem_filter.2 ⟨hiT, hpos⟩)
        rw [le_div_iff₀ hpos] at this
        linarith
      · have : h i ≤ 0 := not_lt.1 hpos
        nlinarith [hc i, mul_nonneg hθ0 (neg_nonneg.2 this)]
    have hj0z : c j0 - θ * h j0 = 0 := by rw [hθ]; field_simp; ring
    have hsupp : ∀ i ∉ T.erase j0, c i - θ * h i = 0 := by
      intro i hi
      by_cases hij : i = j0
      · rw [hij]; exact hj0z
      · have hiT : i ∉ T := fun hh => hi (Finset.mem_erase.2 ⟨hij, hh⟩)
        rw [hcT i hiT, hhT i hiT]; ring
    obtain ⟨J, hJT, hJ, c', hc'0, hc'J, hc'sum⟩ :=
      ih (T.erase j0) (Finset.erase_ssubset hj0T) (fun i => c i - θ * h i) hc'' hsupp
    refine ⟨J, hJT.trans (Finset.erase_subset _ _), hJ, c', hc'0, hc'J, ?_⟩
    rw [hc'sum]
    have : ∑ i, (c i - θ * h i) • v i = ∑ i, c i • v i - θ • ∑ i, h i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_smul, mul_smul]
    rw [this, hsum, smul_zero, sub_zero]

theorem rsr_cone_closed {m : ℕ} (v : Fin m → E) : IsClosed (rsrCone v) := by
  classical
  have key : rsrCone v = ⋃ J : Finset (Fin m), ⋃ (_ : LinearIndependent ℝ (fun j : J => v j)),
      (Fintype.linearCombination ℝ (fun j : J => v j)) '' {d : J → ℝ | ∀ j, 0 ≤ d j} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨J, -, hJ, c', hc'0, hc'J, hc'sum⟩ :=
        rsr_cara v Finset.univ c hc (fun i hi => absurd (Finset.mem_univ i) hi)
      refine ⟨J, hJ, fun j => c' j, fun j => hc'0 _, ?_⟩
      rw [Fintype.linearCombination_apply, ← hc'sum, rsr_sum_ext v J c' hc'J]
    · rintro ⟨J, hJ, d, hd, rfl⟩
      refine ⟨fun i => if h : i ∈ J then d ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · by_cases h : i ∈ J
        · simp [h, hd]
        · simp [h]
      · rw [rsr_sum_ext v J _ (fun i hi => by simp [hi]), Fintype.linearCombination_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [j.2]
  rw [key]
  refine isClosed_iUnion_of_finite fun J => isClosed_iUnion_of_finite fun hJ => ?_
  have hemb := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hJ))
  refine hemb.isClosedMap _ ?_
  have : {d : J → ℝ | ∀ j, 0 ≤ d j} = ⋂ j, {d | 0 ≤ d j} := by ext; simp
  rw [this]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)

theorem rsr_cone_combo {m : ℕ} (v : Fin m → E) {x1 x2 : E}
    (h1 : x1 ∈ rsrCone v) (h2 : x2 ∈ rsrCone v) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x1 + b • x2 ∈ rsrCone v := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  refine ⟨fun i => a * c1 i + b * c2 i, fun i => by have := hc1 i; have := hc2 i; positivity, ?_⟩
  simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

theorem rsr_cone_convex {m : ℕ} (v : Fin m → E) : Convex ℝ (rsrCone v) :=
  fun _ h1 _ h2 _ _ ha hb _ => rsr_cone_combo v h1 h2 ha hb

theorem rsr_zero_mem {m : ℕ} (v : Fin m → E) : (0 : E) ∈ rsrCone v :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem rsr_inner_le {m : ℕ} (v : Fin m → E) {x w : E} (hx : x ∈ rsrCone v)
    (hw : ∀ i, ⟪v i, w⟫ ≤ 0) : ⟪x, w⟫ ≤ 0 := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [sum_inner]
  exact Finset.sum_nonpos fun i _ => by
    rw [real_inner_smul_left]; exact mul_nonpos_of_nonneg_of_nonpos (hc i) (hw i)

theorem rsr_farkas [CompleteSpace E] {m : ℕ} (v : Fin m → E) (x : E)
    (hx : ∀ w : E, (∀ i, ⟪v i, w⟫ ≤ 0) → ⟪x, w⟫ ≤ 0) : x ∈ rsrCone v := by
  by_contra hxC
  have hcl := rsr_cone_closed v
  have hcv := rsr_cone_convex v
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex ⟨0, rsr_zero_mem v⟩
    hcl.isComplete hcv x
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hcv hpK).1 hp
  set w := x - p with hw
  have hwv : ∀ i, ⟪v i, w⟫ ≤ 0 := by
    intro i
    have hpv : p + v i ∈ rsrCone v := by
      have := rsr_cone_combo v hpK (show v i ∈ rsrCone v from
        ⟨fun j => if j = i then 1 else 0, fun j => by dsimp only; split_ifs <;> norm_num, by simp⟩)
        zero_le_one zero_le_one
      simpa using this
    have := hvar _ hpv
    rw [add_sub_cancel_left] at this
    rwa [real_inner_comm]
  have h1 := hx w hwv
  have h2 := hvar 0 (rsr_zero_mem v)
  have h3 := hvar ((2:ℝ) • p) (by rw [two_smul]; simpa using rsr_cone_combo v hpK hpK zero_le_one zero_le_one)
  have hwne : w ≠ 0 := fun h => hxC (by have : x = p := sub_eq_zero.1 h; rw [this]; exact hpK)
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hwne
  have e : x = w + p := by rw [hw]; abel
  rw [e, inner_add_left] at h1
  rw [zero_sub, inner_neg_right] at h2
  have e2 : (2:ℝ) • p - p = p := by rw [two_smul]; abel
  rw [e2] at h3
  have := real_inner_comm w p
  linarith

/-! Polyhedral sets -/

def rsrPoly {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) : Set E := {x | ∀ i, ⟪a i, x⟫ ≤ b i}

def rsrActJ {m : ℕ} (a : Fin m → E) (J : Finset (Fin m)) : Fin m → E :=
  fun i => if i ∈ J then a i else 0

open Classical in
noncomputable def rsrActS {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

theorem rsr_mem_actS {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E) (i : Fin m) :
    i ∈ rsrActS a b x ↔ ⟪a i, x⟫ = b i := by
  classical
  simp [rsrActS]

theorem rsr_poly_convex {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) : Convex ℝ (rsrPoly a b) := by
  intro x hx y hy s t hs ht hst i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := mul_le_mul_of_nonneg_left (hx i) hs
  have h2 := mul_le_mul_of_nonneg_left (hy i) ht
  have : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

theorem rsr_eventually_inactive {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E)
    (hx : x ∈ rsrPoly a b) :
    ∃ ε > 0, ∀ h : E, ‖h‖ < ε → ∀ i, ⟪a i, x⟫ ≠ b i → ⟪a i, x + h⟫ < b i := by
  have hev : ∀ᶠ h in 𝓝 (0 : E), ∀ i, ⟪a i, x⟫ ≠ b i → ⟪a i, x + h⟫ < b i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · have hlt : ⟪a i, x + 0⟫ < b i := by rw [add_zero]; exact lt_of_le_of_ne (hx i) hi
      have hc : Continuous fun h : E => ⟪a i, x + h⟫ := by fun_prop
      exact ((hc.tendsto 0).eventually (gt_mem_nhds hlt)).mono fun _ h _ => h
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨ε, hε, fun h hh => H (by simpa using hh)⟩

theorem rsr_normalCone_iff [CompleteSpace E] {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E)
    (hx : x ∈ rsrPoly a b) (y : E) :
    y ∈ normalCone (rsrPoly a b) x ↔ y ∈ rsrCone (rsrActJ a (rsrActS a b x)) := by
  constructor
  · rintro ⟨-, hy⟩
    apply rsr_farkas
    intro w hw
    obtain ⟨ε, hε, H⟩ := rsr_eventually_inactive a b x hx
    set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
    have ht0 : 0 < t := by positivity
    have htw : ‖t • w‖ < ε := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, ht]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hmem : x + t • w ∈ rsrPoly a b := by
      intro i
      by_cases hi : ⟪a i, x⟫ = b i
      · have := hw i
        simp only [rsrActJ, (rsr_mem_actS a b x i).2 hi, if_true] at this
        rw [inner_add_right, real_inner_smul_right, hi]
        nlinarith
      · exact (H _ htw i hi).le
    have := hy _ hmem
    rw [add_sub_cancel_left, real_inner_smul_right] at this
    by_contra hc
    push_neg at hc
    nlinarith
  · rintro hy
    refine ⟨hx, fun c hc => ?_⟩
    apply rsr_inner_le _ hy
    intro i
    simp only [rsrActJ]
    split_ifs with hi
    · rw [inner_sub_right, (rsr_mem_actS a b x i).1 hi]
      linarith [hc i]
    · simp

theorem rsr_tangentCone_iff [CompleteSpace E] {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E)
    (hx : x ∈ rsrPoly a b) (h : E) :
    h ∈ tangentCone (rsrPoly a b) x ↔ ∀ i, ⟪a i, x⟫ = b i → ⟪a i, h⟫ ≤ 0 := by
  constructor
  · intro hT i hi
    apply hT
    refine ⟨hx, fun c hc => ?_⟩
    rw [inner_sub_right, hi]; linarith [hc i]
  · intro H y hy
    rw [rsr_normalCone_iff a b x hx] at hy
    apply rsr_inner_le _ hy
    intro i
    simp only [rsrActJ]
    split_ifs with hi
    · exact H i ((rsr_mem_actS a b x i).1 hi)
    · simp

/-- Local coincidence of a polyhedron with its tangent cone. -/
theorem rsr_local [CompleteSpace E] {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E)
    (hx : x ∈ rsrPoly a b) :
    ∃ ε > 0, ∀ h : E, ‖h‖ < ε → (x + h ∈ rsrPoly a b ↔ h ∈ tangentCone (rsrPoly a b) x) := by
  obtain ⟨ε, hε, H⟩ := rsr_eventually_inactive a b x hx
  refine ⟨ε, hε, fun h hh => ?_⟩
  rw [rsr_tangentCone_iff a b x hx]
  constructor
  · intro hm i hi
    have := hm i
    rw [inner_add_right, hi] at this
    linarith
  · intro hT i
    by_cases hi : ⟪a i, x⟫ = b i
    · rw [inner_add_right, hi]; linarith [hT i hi]
    · exact (H h hh i hi).le

end Base

theorem rsr_poly_of {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hCp : IsPolyhedral C) :
    ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ), C = rsrPoly a b := by
  obtain ⟨m, a, b, rfl⟩ := hCp
  exact ⟨m, a, b, rfl⟩

theorem proposition_A_1_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ C) :
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ((fun c => c - x0) '' C) ∩ U = tangentCone C x0 ∩ U := by
  obtain ⟨m, a, b, rfl⟩ := rsr_poly_of hCp
  obtain ⟨ε, hε, H⟩ := rsr_local a b x0 hx0
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  ext h
  simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hh⟩
    refine ⟨(H _ hh).1 ?_, hh⟩
    simpa using hc
  · rintro ⟨hT, hh⟩
    exact ⟨⟨x0 + h, (H _ hh).2 hT, by simp⟩, hh⟩

end RobinsonSR.Reduction

open RobinsonSR.Reduction


theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ C) :
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ((fun c => c - x0) '' C) ∩ U = tangentCone C x0 ∩ U := by
  exact proposition_A_1_core C hCp hCne x0 hx0
