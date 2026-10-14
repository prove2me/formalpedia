-- Prove2me | solution 1 for RobinsonSR.Reduction.proposition_A_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:03:56.797053+00:00
-- url     : https://prove2.me/submissions/e7d3f60b-f361-4a42-ac8b-ed292b333199

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


section Face

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rsr_exposed_iff (C : Set E) (y z : E) : z ∈ exposedFace C y ↔ -y ∈ normalCone C z := by
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun c hc => by rw [inner_sub_right]; linarith [h c hc]⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun c hc => by have := h c hc; rw [inner_sub_right] at this; linarith⟩

theorem rsr_face_inner_eq (C : Set E) (y0 c x : E) (hc : c ∈ exposedFace C y0)
    (hx : x ∈ exposedFace C y0) : ⟪y0, c - x⟫ = 0 := by
  have h1 := hx.2 c hc.1
  have h2 := hc.2 x hx.1
  rw [inner_neg_left, inner_neg_left] at h1 h2
  rw [inner_sub_right]; linarith

theorem rsr_face_repr (C : Set E) (y0 x1 z : E) (hx1 : x1 ∈ exposedFace C y0) :
    z ∈ exposedFace C y0 ↔ z ∈ C ∧ ⟪y0, z⟫ ≤ ⟪y0, x1⟫ := by
  constructor
  · rintro ⟨hz, h⟩
    have := h x1 hx1.1
    rw [inner_neg_left, inner_neg_left] at this
    exact ⟨hz, by linarith⟩
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun c hc => ?_⟩
    have := hx1.2 c hc
    rw [inner_neg_left, inner_neg_left] at this ⊢
    linarith

theorem rsr_face_poly {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (y0 x1 : E)
    (hx1 : x1 ∈ exposedFace (rsrPoly a b) y0) :
    exposedFace (rsrPoly a b) y0 =
      rsrPoly (Fin.cons y0 a : Fin (m+1) → E) (Fin.cons ⟪y0, x1⟫ b : Fin (m+1) → ℝ) := by
  ext z
  rw [rsr_face_repr _ y0 x1 z hx1]
  simp only [rsrPoly, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  tauto

theorem rsr_face_convex {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (y0 : E) :
    Convex ℝ (exposedFace (rsrPoly a b) y0) := by
  by_cases hne : (exposedFace (rsrPoly a b) y0).Nonempty
  · obtain ⟨x1, hx1⟩ := hne
    rw [rsr_face_poly a b y0 x1 hx1]
    exact rsr_poly_convex _ _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact convex_empty

theorem rsr_face_normal [CompleteSpace E] {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (y0 x : E)
    (hx : x ∈ exposedFace (rsrPoly a b) y0) :
    normalCone (exposedFace (rsrPoly a b) y0) x =
        {v | ∃ y ∈ normalCone (rsrPoly a b) x, ∃ α : ℝ, 0 ≤ α ∧ v = y + α • y0} := by
  ext v
  constructor
  · intro hv
    rw [rsr_face_poly a b y0 x hx] at hv
    have hxP : x ∈ rsrPoly (Fin.cons y0 a : Fin (m+1) → E) (Fin.cons ⟪y0, x⟫ b : Fin (m+1) → ℝ) := by
      rw [← rsr_face_poly a b y0 x hx]; exact hx
    rw [rsr_normalCone_iff _ _ x hxP] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [Fin.sum_univ_succ]
    have h0 : rsrActJ (Fin.cons y0 a : Fin (m+1) → E)
        (rsrActS (Fin.cons y0 a : Fin (m+1) → E) (Fin.cons ⟪y0, x⟫ b : Fin (m+1) → ℝ) x) 0 = y0 := by
      simp [rsrActJ, rsr_mem_actS]
    have hs : ∀ i : Fin m, rsrActJ (Fin.cons y0 a : Fin (m+1) → E)
        (rsrActS (Fin.cons y0 a : Fin (m+1) → E) (Fin.cons ⟪y0, x⟫ b : Fin (m+1) → ℝ) x) i.succ =
        rsrActJ a (rsrActS a b x) i := by
      intro i
      simp [rsrActJ, rsr_mem_actS]
    simp only [h0, hs]
    refine ⟨∑ i : Fin m, c i.succ • rsrActJ a (rsrActS a b x) i, ?_, c 0, hc 0, by rw [add_comm]⟩
    rw [rsr_normalCone_iff a b x hx.1]
    exact ⟨fun i => c i.succ, fun i => hc _, rfl⟩
  · rintro ⟨y, ⟨-, hy⟩, α, hα, rfl⟩
    refine ⟨hx, fun c hc => ?_⟩
    rw [inner_add_left, real_inner_smul_left, rsr_face_inner_eq _ y0 c x hc hx, mul_zero, add_zero]
    exact hy c hc.1

theorem rsr_face_stable [CompleteSpace E] {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (y0 : E) :
    ∀ᶠ y in 𝓝 y0, exposedFace (rsrPoly a b) y ⊆ exposedFace (rsrPoly a b) y0 := by
  have hev : ∀ᶠ y in 𝓝 y0, ∀ J : Finset (Fin m),
      -y0 ∉ rsrCone (rsrActJ a J) → -y ∉ rsrCone (rsrActJ a J) := by
    rw [Filter.eventually_all]
    intro J
    by_cases hJ : -y0 ∈ rsrCone (rsrActJ a J)
    · exact Filter.Eventually.of_forall fun y h => absurd hJ h
    · have := (continuous_neg.tendsto y0).eventually
        ((rsr_cone_closed (rsrActJ a J)).isOpen_compl.mem_nhds hJ)
      exact this.mono fun y hy _ => hy
  refine hev.mono fun y hy z hz => ?_
  rw [rsr_exposed_iff] at hz ⊢
  have hzC := hz.1
  rw [rsr_normalCone_iff a b z hzC] at hz ⊢
  by_contra hc
  exact hy _ hc hz

end Face

theorem proposition_A_2_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 : EuclideanSpace ℝ (Fin n)) :
    (∀ x ∈ exposedFace C y0, normalCone (exposedFace C y0) x =
        {v | ∃ y ∈ normalCone C x, ∃ α : ℝ, 0 ≤ α ∧ v = y + α • y0}) ∧
    ∀ᶠ y in 𝓝 y0, exposedFace C y ⊆ exposedFace C y0 := by
  obtain ⟨m, a, b, rfl⟩ := rsr_poly_of hCp
  exact ⟨fun x hx => rsr_face_normal a b y0 x hx, rsr_face_stable a b y0⟩


section Red

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Near `-q`, adding a nonnegative multiple of `q` cannot leave a finitely generated cone. -/
theorem rsr_kc {m : ℕ} (v : Fin m → E) (q : E) :
    ∀ᶠ w in 𝓝 (-q), ∀ y ∈ rsrCone v, ∀ α : ℝ, 0 ≤ α → w = y + α • q → w ∈ rsrCone v := by
  classical
  set u : Fin (m+1) → E := Fin.cons q v with hu
  set S : Set E := ⋃ J : Finset (Fin (m+1)), ⋃ (_ : (0 : Fin (m+1)) ∈ J),
      ⋃ (_ : LinearIndependent ℝ (fun j : J => u j)),
      (Fintype.linearCombination ℝ (fun j : J => u j)) '' {d : J → ℝ | ∀ j, 0 ≤ d j} with hS
  have hSc : IsClosed S := by
    refine isClosed_iUnion_of_finite fun J => isClosed_iUnion_of_finite fun _ =>
      isClosed_iUnion_of_finite fun hJ => ?_
    have hemb := LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hJ))
    refine hemb.isClosedMap _ ?_
    have : {d : J → ℝ | ∀ j, 0 ≤ d j} = ⋂ j, {d | 0 ≤ d j} := by ext; simp
    rw [this]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have hpS : -q ∉ S := by
    intro hmem
    simp only [hS, Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hmem
    obtain ⟨J, h0J, hli, d, hd, hpd⟩ := hmem
    rw [Fintype.linearCombination_apply] at hpd
    set g : J → ℝ := fun j => d j + if (j : Fin (m+1)) = 0 then 1 else 0 with hg
    have hsum : ∑ j, g j • u j = 0 := by
      simp only [hg, add_smul, Finset.sum_add_distrib, hpd]
      have : ∑ j : J, (if (j : Fin (m+1)) = 0 then (1:ℝ) else 0) • u j = u 0 := by
        rw [Finset.sum_coe_sort J (fun i => (if i = 0 then (1:ℝ) else 0) • u i)]
        simp [ite_smul, h0J]
      rw [this, hu, Fin.cons_zero]; abel
    have := Fintype.linearIndependent_iff.1 hli g hsum ⟨0, h0J⟩
    simp only [hg, if_true] at this
    linarith [hd ⟨0, h0J⟩]
  filter_upwards [hSc.isOpen_compl.mem_nhds hpS] with w hwS
  rintro y ⟨c, hc, rfl⟩ α hα hw
  set c' : Fin (m+1) → ℝ := Fin.cons α c with hc'
  have hc'0 : ∀ i, 0 ≤ c' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hc'] using hα
    · simpa [hc'] using hc j
  have hc'sum : ∑ i, c' i • u i = w := by
    rw [Fin.sum_univ_succ, hw]
    simp [hc', hu, add_comm]
  obtain ⟨J, -, hli, c'', hc''0, hc''J, hsum⟩ :=
    rsr_cara u Finset.univ c' hc'0 (fun i hi => absurd (Finset.mem_univ i) hi)
  by_cases h0 : (0 : Fin (m+1)) ∈ J
  · exfalso
    apply hwS
    simp only [hS, Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    refine ⟨J, h0, hli, fun j => c'' j, fun j => hc''0 _, ?_⟩
    rw [Fintype.linearCombination_apply, ← rsr_sum_ext u J c'' hc''J, hsum, hc'sum]
  · have hz : c'' 0 = 0 := hc''J 0 h0
    refine ⟨fun i => c'' i.succ, fun i => hc''0 _, ?_⟩
    rw [← hc'sum, ← hsum, Fin.sum_univ_succ, hz, zero_smul, zero_add]
    simp [hu]

theorem rsr_loc {S S' U : Set E} (hS' : Convex ℝ S') (hU : IsOpen U) {p v : E} (hp : p ∈ U)
    (hpS' : p ∈ S') (hiff : ∀ q ∈ U, q ∈ S' → q ∈ S) (hv : ∀ t ∈ S, ⟪v, t - p⟫ ≤ 0) :
    ∀ t ∈ S', ⟪v, t - p⟫ ≤ 0 := by
  intro t ht
  have hc : Continuous fun s : ℝ => p + s • (t - p) := by fun_prop
  have h1 := (hc.tendsto' 0 p (by simp)).eventually (hU.mem_nhds hp)
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.1 h1
  set s : ℝ := min (ε/2) 1 with hsdef
  have hs0 : 0 < s := lt_min (by positivity) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsε : dist s 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    have := min_le_left (ε/2) 1
    linarith
  have hq : p + s • (t - p) ∈ S' := hS'.add_smul_sub_mem hpS' ht ⟨hs0.le, hs1⟩
  have := hv _ (hiff _ (H hsε) hq)
  rw [add_sub_cancel_left, real_inner_smul_right] at this
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos hs0 hcon]

theorem rsr_polar_convex (S : Set E) : Convex ℝ (polar S) := by
  intro u hu w hw s t hs ht _ y hy
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs (hu y hy))
    (mul_nonpos_of_nonneg_of_nonpos ht (hw y hy))

end Red

theorem rsr_A3_aux {n : ℕ} {m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (y0 x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ exposedFace (rsrPoly a b) y0) :
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ h ∈ U, ∀ k ∈ V,
        (-(y0 + k) ∈ normalCone (rsrPoly a b) (x0 + h) ↔
          -((parallelSubspace (exposedFace (rsrPoly a b) y0)).starProjection k) ∈
            normalCone (tangentCone (exposedFace (rsrPoly a b) y0) x0) h) := by
  set P := rsrPoly a b with hP
  set F := exposedFace P y0 with hF
  set L := parallelSubspace F with hL
  set T := tangentCone F x0 with hT
  have hx0P : x0 ∈ rsrPoly (Fin.cons y0 a : Fin (m+1) → _) (Fin.cons ⟪y0, x0⟫ b : Fin (m+1) → ℝ) := by
    rw [← rsr_face_poly a b y0 x0 hx0]; exact hx0
  obtain ⟨ε1, hε1, H1⟩ := rsr_local _ _ x0 hx0P
  have H1' : ∀ h, ‖h‖ < ε1 → (x0 + h ∈ F ↔ h ∈ T) := by
    rw [hT, hF, rsr_face_poly a b y0 x0 hx0]; exact H1
  have hVa : ∀ᶠ k in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), exposedFace P (y0 + k) ⊆ F := by
    have ht : Filter.Tendsto (fun k : EuclideanSpace ℝ (Fin n) => y0 + k) (𝓝 0) (𝓝 y0) :=
      (continuous_const.add continuous_id).tendsto' 0 y0 (by simp)
    exact ht.eventually (rsr_face_stable a b y0)
  have hVb : ∀ᶠ k in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∀ J : Finset (Fin m),
      ∀ y ∈ rsrCone (rsrActJ a J), ∀ α : ℝ, 0 ≤ α → -(y0 + k) = y + α • y0 →
        -(y0 + k) ∈ rsrCone (rsrActJ a J) := by
    have ht : Filter.Tendsto (fun k : EuclideanSpace ℝ (Fin n) => -(y0 + k)) (𝓝 0) (𝓝 (-y0)) :=
      (continuous_const.add continuous_id).neg.tendsto' 0 (-y0) (by simp)
    rw [Filter.eventually_all]
    intro J
    exact ht.eventually (rsr_kc (rsrActJ a J) y0)
  have hFconv : Convex ℝ {h' : EuclideanSpace ℝ (Fin n) | x0 + h' ∈ F} := by
    intro u hu w hw s t hs ht hst
    have := rsr_face_convex a b y0 hu hw hs ht hst
    show x0 + (s • u + t • w) ∈ F
    have e : x0 + (s • u + t • w) = s • (x0 + u) + t • (x0 + w) := by
      calc x0 + (s • u + t • w) = (s + t) • x0 + (s • u + t • w) := by rw [hst, one_smul]
        _ = s • (x0 + u) + t • (x0 + w) := by simp only [add_smul, smul_add]; abel
    rw [e]; exact this
  have hTconv : Convex ℝ T := rsr_polar_convex _
  have hkey : ∀ k c z, c ∈ F → z ∈ F → ⟪-(L.starProjection k), c - z⟫ = ⟪-(y0 + k), c - z⟫ := by
    intro k c z hc hz
    have hmem : c - z ∈ L := by
      show c - z ∈ (affineSpan ℝ F).direction
      rw [direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ hc hz
    have h1 : ⟪L.starProjection k, c - z⟫ = ⟪k, c - z⟫ := by
      rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hmem]
    have h2 := rsr_face_inner_eq P y0 c z hc hz
    rw [inner_neg_left, inner_neg_left, inner_add_left, h1, h2]; ring
  refine ⟨Metric.ball 0 ε1, Metric.ball_mem_nhds 0 hε1, _, hVa.and hVb, ?_⟩
  intro h hh k hk
  obtain ⟨hka, hkb⟩ := hk
  have hh' : ‖h‖ < ε1 := mem_ball_zero_iff.1 hh
  constructor
  · intro hN
    have hz : x0 + h ∈ exposedFace P (y0 + k) := (rsr_exposed_iff _ _ _).2 hN
    have hzF : x0 + h ∈ F := hka hz
    have hTh : h ∈ T := (H1' h hh').1 hzF
    refine ⟨hTh, ?_⟩
    refine rsr_loc (S := {h' | x0 + h' ∈ F}) hTconv Metric.isOpen_ball hh hTh
      (fun q hq hqT => (H1' q (mem_ball_zero_iff.1 hq)).2 hqT) ?_
    intro t ht
    have e : t - h = (x0 + t) - (x0 + h) := by abel
    rw [e, hkey k _ _ ht hzF]
    exact hN.2 _ ht.1
  · rintro ⟨hTh, hNT⟩
    have hzF : x0 + h ∈ F := (H1' h hh').2 hTh
    have hloc := rsr_loc (S := T) hFconv Metric.isOpen_ball hh hzF
      (fun q hq hqF => (H1' q (mem_ball_zero_iff.1 hq)).1 hqF) hNT
    have hNF : -(y0 + k) ∈ normalCone F (x0 + h) := by
      refine ⟨hzF, fun c hc => ?_⟩
      rw [← hkey k c _ hc hzF]
      have := hloc (c - x0) (by simpa using hc)
      have e : c - x0 - h = c - (x0 + h) := by abel
      rwa [e] at this
    rw [hF, rsr_face_normal a b y0 _ hzF] at hNF
    obtain ⟨y, hy, α, hα, hyeq⟩ := hNF
    have hzP : x0 + h ∈ P := hzF.1
    rw [rsr_normalCone_iff a b _ hzP] at hy ⊢
    exact hkb _ y hy α hα hyeq

theorem proposition_A_3_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ exposedFace C y0) :
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ h ∈ U, ∀ k ∈ V,
        (-(y0 + k) ∈ normalCone C (x0 + h) ↔ -(L.starProjection k) ∈ normalCone T h) := by
  obtain ⟨m, a, b, rfl⟩ := rsr_poly_of hCp
  exact rsr_A3_aux a b y0 x0 hx0

end RobinsonSR.Reduction

open RobinsonSR.Reduction


theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ exposedFace C y0) :
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ h ∈ U, ∀ k ∈ V,
        (-(y0 + k) ∈ normalCone C (x0 + h) ↔ -(L.starProjection k) ∈ normalCone T h) := by
  exact proposition_A_3_core C hCp hCne y0 x0 hx0
