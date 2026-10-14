-- Prove2me | solution 1 for RobinsonSR.Reduction.theorem_A_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:18:39.322061+00:00
-- url     : https://prove2.me/submissions/841e1f1d-3bc4-45b1-9723-024a6be8fb2e

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


theorem rsr_corr_aux {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    ∃ N ∈ 𝓝 x0, ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∀ x ∈ N, ∀ y ∈ W,
      (y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x ↔
        (parallelSubspace (exposedFace C (Matrix.toEuclideanLin A x0 + a))).starProjection y -
          (parallelSubspace (exposedFace C (Matrix.toEuclideanLin A x0 + a))).starProjection
            (Matrix.toEuclideanLin A (x - x0)) ∈
          normalCone (tangentCone (exposedFace C (Matrix.toEuclideanLin A x0 + a)) x0)
            (x - x0)) := by
  obtain ⟨mm, aa, bb, rfl⟩ := rsr_poly_of hCp
  set M := Matrix.toEuclideanLin A with hM
  set y0 := M x0 + a with hy0
  set L := parallelSubspace (exposedFace (rsrPoly aa bb) y0) with hL
  have hx0 : x0 ∈ exposedFace (rsrPoly aa bb) y0 := (rsr_exposed_iff _ _ _).2 hsol
  obtain ⟨U, hU, V, hV, H⟩ := rsr_A3_aux aa bb y0 x0 hx0
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV
  have hMc : Continuous fun x : EuclideanSpace ℝ (Fin n) => M (x - x0) :=
    (LinearMap.continuous_of_finiteDimensional M).comp (continuous_id.sub continuous_const)
  have hN1 : ∀ᶠ x in 𝓝 x0, x - x0 ∈ U :=
    ((continuous_id.sub continuous_const).tendsto' x0 0 (by simp)).eventually hU
  have hN2 : ∀ᶠ x in 𝓝 x0, ‖M (x - x0)‖ < δ / 2 := by
    have := (hMc.tendsto' x0 0 (by simp)).eventually (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) (half_pos hδ))
    exact this.mono fun x hx => by simpa using hx
  refine ⟨_, hN1.and hN2, Metric.ball 0 (δ / 2), Metric.ball_mem_nhds 0 (half_pos hδ), ?_⟩
  rintro x ⟨hxU, hxM⟩ y hy
  have hy' : ‖y‖ < δ / 2 := mem_ball_zero_iff.1 hy
  set k := M (x - x0) - y with hk
  have hkV : k ∈ V := by
    apply hδV
    rw [mem_ball_zero_iff]
    calc ‖k‖ ≤ ‖M (x - x0)‖ + ‖y‖ := norm_sub_le _ _
      _ < δ := by linarith
  have HH := H (x - x0) hxU k hkV
  have e1 : y - (M x + a) = -(y0 + k) := by
    rw [hk, hy0, map_sub]; abel
  have e2 : x0 + (x - x0) = x := by abel
  have e3 : L.starProjection y - L.starProjection (M (x - x0)) = -(L.starProjection k) := by
    rw [hk]; simp only [map_sub]; abel
  rw [e2] at HH
  rw [e1, e3]
  exact HH

theorem correspondence_A_4_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ N ∈ 𝓝 x0, ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∀ x ∈ N, ∀ y ∈ W,
      (y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x ↔
        L.starProjection y - L.starProjection (Matrix.toEuclideanLin A (x - x0)) ∈
          normalCone T (x - x0)) :=
  rsr_corr_aux C hCp A a x0 hsol


section Goal

variable {n : ℕ}

def rsrPiece {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (J : Finset (Fin p)) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {q | q.1 ∈ L ∧ q.2 ∈ rsrPoly g (fun _ => 0) ∧ (∀ i ∈ J, ⟪g i, q.2⟫ = 0) ∧
    q.1 - B q.2 ∈ rsrCone (rsrActJ g J)}

theorem rsr_piece_sol {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (J : Finset (Fin p)) {q}
    (hq : q ∈ rsrPiece g B L J) : q.1 - B q.2 ∈ normalCone (rsrPoly g (fun _ => 0)) q.2 := by
  obtain ⟨-, hT, hJ, hc⟩ := hq
  refine ⟨hT, fun c hc' => rsr_inner_le _ hc fun i => ?_⟩
  simp only [rsrActJ]
  split_ifs with hi
  · rw [inner_sub_right, hJ i hi, sub_zero]; exact hc' i
  · simp

theorem rsr_sol_piece {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {z w : EuclideanSpace ℝ (Fin n)} (hz : z ∈ L)
    (hN : z - B w ∈ normalCone (rsrPoly g (fun _ => 0)) w) :
    (z, w) ∈ rsrPiece g B L (rsrActS g (fun _ => 0) w) := by
  refine ⟨hz, hN.1, fun i hi => (rsr_mem_actS _ _ _ i).1 hi, ?_⟩
  exact (rsr_normalCone_iff g _ w hN.1 _).1 hN

theorem rsr_piece_add {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (J : Finset (Fin p)) {q r}
    (hq : q ∈ rsrPiece g B L J) (hr : r ∈ rsrPiece g B L J) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s • q + t • r ∈ rsrPiece g B L J := by
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  refine ⟨L.add_mem (L.smul_mem s hq1) (L.smul_mem t hr1), fun i => ?_, fun i hi => ?_, ?_⟩
  · simp only [Prod.snd_add, Prod.smul_snd, inner_add_right, real_inner_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs (hq2 i))
      (mul_nonpos_of_nonneg_of_nonpos ht (hr2 i))
  · simp only [Prod.snd_add, Prod.smul_snd, inner_add_right, real_inner_smul_right, hq3 i hi,
      hr3 i hi, mul_zero, add_zero]
  · have := rsr_cone_combo _ hq4 hr4 hs ht
    convert this using 1
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, map_add, map_smul,
      smul_sub]
    abel

theorem rsr_piece_closed {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (J : Finset (Fin p)) :
    IsClosed (rsrPiece g B L J) := by
  have hB : Continuous B := LinearMap.continuous_of_finiteDimensional B
  have h1 : IsClosed {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | q.1 ∈ L} :=
    L.closed_of_finiteDimensional.preimage continuous_fst
  have hT : IsClosed (rsrPoly g (fun _ => (0:ℝ))) := by
    have : rsrPoly g (fun _ => (0:ℝ)) = ⋂ i, {x | ⟪g i, x⟫ ≤ 0} := by ext; simp [rsrPoly]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      q.2 ∈ rsrPoly g (fun _ => 0)} := hT.preimage continuous_snd
  have h3 : IsClosed {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      ∀ i ∈ J, ⟪g i, q.2⟫ = 0} := by
    have : {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | ∀ i ∈ J, ⟪g i, q.2⟫ = 0}
        = ⋂ i, ⋂ (_ : i ∈ J), {q | ⟪g i, q.2⟫ = 0} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (by fun_prop)
      continuous_const
  have h4 : IsClosed {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      q.1 - B q.2 ∈ rsrCone (rsrActJ g J)} :=
    (rsr_cone_closed _).preimage (continuous_fst.sub (hB.comp continuous_snd))
  exact h1.inter (h2.inter (h3.inter h4))

theorem rsr_piece_lip {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hu : ∀ z ∈ L, ∃! w, z - B w ∈ normalCone (rsrPoly g (fun _ => 0)) w) (J : Finset (Fin p)) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ q ∈ rsrPiece g B L J, ∀ r ∈ rsrPiece g B L J,
      ‖q.2 - r.2‖ ≤ K * ‖q.1 - r.1‖) ∧ IsClosed (Prod.fst '' rsrPiece g B L J) := by
  set P := rsrPiece g B L J with hP
  set G := Submodule.span ℝ P with hG
  have h0P : (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈ P :=
    ⟨L.zero_mem, fun i => by simp, fun i _ => by simp, by simpa using rsr_zero_mem _⟩
  have hdiff : ∀ x ∈ G, ∃ q ∈ P, ∃ r ∈ P, x = q - r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨x, hx, 0, h0P, by simp⟩
    | zero => exact ⟨0, h0P, 0, h0P, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨q1, hq1, r1, hr1, rfl⟩ := ihx
      obtain ⟨q2, hq2, r2, hr2, rfl⟩ := ihy
      refine ⟨q1 + q2, by simpa using rsr_piece_add g B L J hq1 hq2 zero_le_one zero_le_one,
        r1 + r2, by simpa using rsr_piece_add g B L J hr1 hr2 zero_le_one zero_le_one, by abel⟩
    | smul c x _ ihx =>
      obtain ⟨q, hq, r, hr, rfl⟩ := ihx
      rcases le_or_gt 0 c with hc | hc
      · refine ⟨c • q, by simpa using rsr_piece_add g B L J hq hq hc le_rfl,
          c • r, by simpa using rsr_piece_add g B L J hr hr hc le_rfl, by rw [smul_sub]⟩
      · refine ⟨(-c) • r, by simpa using rsr_piece_add g B L J hr hr (s := -c) (t := 0) (by linarith) le_rfl,
          (-c) • q, by simpa using rsr_piece_add g B L J hq hq (s := -c) (t := 0) (by linarith) le_rfl, ?_⟩
        rw [smul_sub, neg_smul, neg_smul]; abel
  set f : G →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (LinearMap.fst ℝ _ _).comp G.subtype with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨q, hq, r, hr, hqr⟩ := hdiff x x.2
    have h1 : (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).1 = 0 := hx
    rw [hqr, Prod.fst_sub, sub_eq_zero] at h1
    have hs1 := rsr_piece_sol g B L J hq
    have hs2 := rsr_piece_sol g B L J hr
    rw [h1] at hs1
    have h2 : q.2 = r.2 := (hu r.1 hr.1).unique hs1 hs2
    apply Subtype.ext
    rw [hqr]
    exact Prod.ext (by simp [h1]) (by simp [h2])
  obtain ⟨K, -, hA⟩ := f.exists_antilipschitzWith hker
  refine ⟨K, K.2, ?_, ?_⟩
  · intro q hq r hr
    have hmem : q - r ∈ G := G.sub_mem (Submodule.subset_span hq) (Submodule.subset_span hr)
    have := hA.le_mul_norm (map_zero f) ⟨q - r, hmem⟩
    have e : ‖(⟨q - r, hmem⟩ : G)‖ = ‖q - r‖ := rfl
    have e2 : f ⟨q - r, hmem⟩ = q.1 - r.1 := rfl
    rw [e, e2] at this
    calc ‖q.2 - r.2‖ = ‖(q - r).2‖ := rfl
      _ ≤ ‖q - r‖ := norm_snd_le _
      _ ≤ K * ‖q.1 - r.1‖ := this
  · have hemb := LinearMap.isClosedEmbedding_of_injective hker
    have hS : IsClosed {x : G | (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈ P} :=
      (rsr_piece_closed g B L J).preimage continuous_subtype_val
    have := hemb.isClosedMap _ hS
    convert this using 1
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, Submodule.subset_span hq⟩, hq, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩

theorem rsr_lipsol {p : ℕ} (g : Fin p → EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hu : ∀ z ∈ L, ∃! w, z - B w ∈ normalCone (rsrPoly g (fun _ => 0)) w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z1 ∈ L, ∀ z2 ∈ L, ∀ w1 w2,
      z1 - B w1 ∈ normalCone (rsrPoly g (fun _ => 0)) w1 →
      z2 - B w2 ∈ normalCone (rsrPoly g (fun _ => 0)) w2 → ‖w1 - w2‖ ≤ K * ‖z1 - z2‖ := by
  choose Kf hK0 hKlip hDc using rsr_piece_lip g B L hu
  set K := ∑ J, Kf J with hK
  have hKJ : ∀ J, Kf J ≤ K := fun J =>
    Finset.single_le_sum (f := Kf) (fun J _ => hK0 J) (Finset.mem_univ J)
  have hK0' : 0 ≤ K := Finset.sum_nonneg fun J _ => hK0 J
  refine ⟨K, hK0', ?_⟩
  intro z1 hz1 z2 hz2 w1 w2 hw1 hw2
  have hex : ∀ z, ∃ w, z ∈ L → z - B w ∈ normalCone (rsrPoly g (fun _ => 0)) w := by
    intro z
    by_cases hz : z ∈ L
    · obtain ⟨w, hw, -⟩ := hu z hz
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose sol hsol using hex
  set zt : ℝ → EuclideanSpace ℝ (Fin n) := fun t => z1 + t • (z2 - z1) with hzt
  have hztL : ∀ t, zt t ∈ L := fun t => L.add_mem hz1 (L.smul_mem t (L.sub_mem hz2 hz1))
  have hztc : Continuous zt := by fun_prop
  set φ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => sol (zt t) with hφ
  set K' := K * ‖z2 - z1‖ with hK'
  have hK'0 : 0 ≤ K' := mul_nonneg hK0' (norm_nonneg _)
  have hloc : ∀ t, ∀ᶠ t' in 𝓝 t, ‖φ t' - φ t‖ ≤ K' * |t' - t| := by
    intro t
    have hev : ∀ᶠ t' in 𝓝 t, ∀ J, zt t ∉ Prod.fst '' rsrPiece g B L J →
        zt t' ∉ Prod.fst '' rsrPiece g B L J := by
      rw [Filter.eventually_all]
      intro J
      by_cases hJ : zt t ∈ Prod.fst '' rsrPiece g B L J
      · exact Filter.Eventually.of_forall fun _ h => absurd hJ h
      · exact ((hztc.tendsto t).eventually ((hDc J).isOpen_compl.mem_nhds hJ)).mono
          fun _ h _ => h
    filter_upwards [hev] with t' ht'
    set J' := rsrActS g (fun _ => 0) (φ t') with hJ'
    have hp' : (zt t', φ t') ∈ rsrPiece g B L J' := rsr_sol_piece g B L (hztL t') (hsol _ (hztL t'))
    have hzt : zt t ∈ Prod.fst '' rsrPiece g B L J' := by
      by_contra h
      exact ht' J' h ⟨_, hp', rfl⟩
    obtain ⟨q, hq, hq1⟩ := hzt
    have hqs := rsr_piece_sol g B L J' hq
    rw [hq1] at hqs
    have hq2 : q.2 = φ t := (hu (zt t) (hztL t)).unique hqs (hsol _ (hztL t))
    have := hKlip J' _ hp' q hq
    simp only [hq1, hq2] at this
    have e : zt t' - zt t = (t' - t) • (z2 - z1) := by
      simp only [hzt, sub_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs] at this
    calc ‖φ t' - φ t‖ ≤ Kf J' * (|t' - t| * ‖z2 - z1‖) := this
      _ ≤ K * (|t' - t| * ‖z2 - z1‖) :=
          mul_le_mul_of_nonneg_right (hKJ J') (by positivity)
      _ = K' * |t' - t| := by rw [hK']; ring
  have hφc : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Filter.Tendsto (fun t' : ℝ => K' * |t' - t|) (𝓝 t) (𝓝 0) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto' t 0 (by simp)
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hloc t) hlim
  set s : Set ℝ := {t | ‖φ t - φ 0‖ ≤ K' * t} with hs
  have hsc : IsClosed s :=
    isClosed_le (continuous_norm.comp (hφc.sub continuous_const)) (continuous_const.mul continuous_id)
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (a := (0:ℝ)) (b := 1) (s := s)
    (hsc.inter isClosed_Icc) (by simp [hs]) (by
      rintro x ⟨hx, hx01⟩
      filter_upwards [nhdsWithin_le_nhds (hloc x), self_mem_nhdsWithin] with t' h1 h2
      have h2' : x < t' := h2
      have hx' : ‖φ x - φ 0‖ ≤ K' * x := hx
      show ‖φ t' - φ 0‖ ≤ K' * t'
      rw [abs_of_pos (by linarith)] at h1
      calc ‖φ t' - φ 0‖ = ‖(φ t' - φ x) + (φ x - φ 0)‖ := by congr 1; abel
        _ ≤ ‖φ t' - φ x‖ + ‖φ x - φ 0‖ := norm_add_le _ _
        _ ≤ K' * (t' - x) + K' * x := add_le_add h1 hx'
        _ = K' * t' := by ring)
  have h1 : (1:ℝ) ∈ s := hsub ⟨zero_le_one, le_rfl⟩
  have hφ0 : φ 0 = w1 := by
    have e : zt 0 = z1 := by simp [hzt]
    have := hsol (zt 0) (hztL 0)
    show sol (zt 0) = w1
    rw [e] at this ⊢
    exact (hu z1 hz1).unique this hw1
  have hφ1 : φ 1 = w2 := by
    have e : zt 1 = z2 := by simp [hzt]
    have := hsol (zt 1) (hztL 1)
    show sol (zt 1) = w2
    rw [e] at this ⊢
    exact (hu z2 hz2).unique this hw2
  have h1' : ‖φ 1 - φ 0‖ ≤ K' * 1 := h1
  rw [hφ0, hφ1, mul_one, hK', norm_sub_rev z2 z1] at h1'
  rw [norm_sub_rev]; exact h1'

end Goal


theorem rsr_polar_scale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) {t : ℝ} (ht : 0 < t) {v w : E}
    (h : v ∈ normalCone (polar S) w) : t • v ∈ normalCone (polar S) (t • w) := by
  obtain ⟨hw, hv⟩ := h
  refine ⟨fun y hy => by
    rw [real_inner_smul_right]; exact mul_nonpos_of_nonneg_of_nonpos ht.le (hw y hy),
    fun c hc => ?_⟩
  have hc' : t⁻¹ • c ∈ polar S := fun y hy => by
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.le) (hc y hy)
  have := hv _ hc'
  have e : c - t • w = t • (t⁻¹ • c - w) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [e, real_inner_smul_left, real_inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos ht.le (mul_nonpos_of_nonneg_of_nonpos ht.le this)

theorem rsr_small {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) {D : ℝ}
    (hD : ‖v‖ < D) : ‖(ρ / D) • v‖ < ρ := by
  have hD0 : 0 < D := lt_of_le_of_lt (norm_nonneg _) hD
  rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hD0]
  exact mul_lt_mul_of_pos_left hD hρ

theorem rsr_A4_aux {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0)
    (F T : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hF : F = exposedFace C (Matrix.toEuclideanLin A x0 + a)) (hT : T = tangentCone F x0)
    (hL : L = parallelSubspace F) :
    (∃ lam : ℝ, StronglyRegularLin C A a x0 lam) ↔
      (L = ⊥ ∨ ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (Matrix.toEuclideanLin A w) ∈ normalCone T w) := by
  obtain ⟨N, hN, W, hW, Hc⟩ := rsr_corr_aux C hCp A a x0 hsol
  rw [← hF, ← hT, ← hL] at Hc
  obtain ⟨m, aa, bb, rfl⟩ := rsr_poly_of hCp
  set M := Matrix.toEuclideanLin A with hM
  set y0 := M x0 + a with hy0
  have hx0F : x0 ∈ exposedFace (rsrPoly aa bb) y0 := (rsr_exposed_iff _ _ _).2 hsol
  have hx0P : x0 ∈ rsrPoly (Fin.cons y0 aa : Fin (m+1) → _) (Fin.cons ⟪y0, x0⟫ bb : Fin (m+1) → ℝ) := by
    rw [← rsr_face_poly aa bb y0 x0 hx0F]; exact hx0F
  set g := rsrActJ (Fin.cons y0 aa : Fin (m+1) → _)
    (rsrActS (Fin.cons y0 aa : Fin (m+1) → _) (Fin.cons ⟪y0, x0⟫ bb : Fin (m+1) → ℝ) x0) with hg
  have hTg : T = rsrPoly g (fun _ => 0) := by
    rw [hT, hF, rsr_face_poly aa bb y0 x0 hx0F]
    ext h
    rw [rsr_tangentCone_iff _ _ x0 hx0P]
    constructor
    · intro H i
      show ⟪g i, h⟫ ≤ 0
      simp only [hg, rsrActJ]
      split_ifs with hi
      · exact H i ((rsr_mem_actS _ _ _ i).1 hi)
      · simp
    · intro H i hi
      have := H i
      simp only [hg, rsrActJ, (rsr_mem_actS _ _ _ i).2 hi, if_true] at this
      exact this
  have hTpol : T = polar (normalCone F x0) := hT
  have h00 : (0 : EuclideanSpace ℝ (Fin n)) ∈ normalCone T 0 := by
    rw [hTpol]; exact ⟨fun y _ => by simp, fun c _ => by simp⟩
  have hscale : ∀ t : ℝ, 0 < t → ∀ z w : EuclideanSpace ℝ (Fin n),
      (t • z - L.starProjection (M (t • w)) ∈ normalCone T (t • w) ↔
        z - L.starProjection (M w) ∈ normalCone T w) := by
    intro t ht z w
    rw [hTpol]
    constructor
    · intro h
      have := rsr_polar_scale _ (inv_pos.2 ht) h
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, map_smul, map_smul, ← smul_sub,
        smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
    · intro h
      have := rsr_polar_scale _ ht h
      rwa [smul_sub, ← map_smul, ← map_smul] at this
  have hxF : ∀ c ∈ F, c - x0 ∈ L := by
    intro c hc
    rw [hL]
    show c - x0 ∈ (affineSpan ℝ F).direction
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ hc (hF ▸ hx0F)
  constructor
  · rintro ⟨lam, -, U, hU, V, hV, s, hs, hlip⟩
    right
    intro z hz
    obtain ⟨r1, hr1, hr1s⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hW)
    obtain ⟨r2, hr2, hr2s⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN hV)
    have hs0 : s 0 = x0 :=
      ((hs 0 (mem_of_mem_nhds hU)).2.2 x0 (mem_of_mem_nhds hV) (by rw [zero_sub]; exact hsol)).symm
    -- correspondence at scaled points
    have hA : ∀ t : ℝ, ‖t • z‖ < r1 → ∀ x ∈ N,
        (t • z - (M x + a) ∈ normalCone (rsrPoly aa bb) x ↔
          t • z - L.starProjection (M (x - x0)) ∈ normalCone T (x - x0)) := by
      intro t ht x hx
      have hy : t • z ∈ W := (hr1s (mem_ball_zero_iff.2 ht)).2
      have := Hc x hx (t • z) hy
      rwa [Submodule.starProjection_eq_self_iff.2 (L.smul_mem t hz)] at this
    set ρ := min r1 (r2 / (|lam| + 1)) with hρ
    have hρ0 : 0 < ρ := lt_min hr1 (by positivity)
    set t := ρ / (‖z‖ + 1) with ht
    have ht0 : 0 < t := by positivity
    have htz : ‖t • z‖ < ρ := rsr_small hρ0 z (by linarith)
    have htz1 : ‖t • z‖ < r1 := lt_of_lt_of_le htz (min_le_left _ _)
    have hyU : t • z ∈ U := (hr1s (mem_ball_zero_iff.2 htz1)).1
    obtain ⟨hsV, hssol, -⟩ := hs (t • z) hyU
    have hdist : ‖s (t • z) - x0‖ < r2 := by
      have h1 := hlip (t • z) hyU 0 (mem_of_mem_nhds hU)
      rw [hs0, sub_zero] at h1
      have h2 : lam * ‖t • z‖ ≤ |lam| * ‖t • z‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      have h3 : (|lam| + 1) * ρ ≤ r2 := by
        have := min_le_right r1 (r2 / (|lam| + 1))
        rw [← hρ] at this
        have hpos : 0 < |lam| + 1 := by positivity
        calc (|lam| + 1) * ρ ≤ (|lam| + 1) * (r2 / (|lam| + 1)) :=
              mul_le_mul_of_nonneg_left this hpos.le
          _ = r2 := by field_simp
      nlinarith [abs_nonneg lam, norm_nonneg (t • z)]
    have hsN : s (t • z) ∈ N := (hr2s (by rw [Metric.mem_ball, dist_eq_norm]; exact hdist)).1
    have hred := (hA t htz1 _ hsN).1 hssol
    have hsolv0 : z - L.starProjection (M (t⁻¹ • (s (t • z) - x0))) ∈
        normalCone T (t⁻¹ • (s (t • z) - x0)) := by
      rw [← hscale t ht0, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      exact hred
    refine ⟨t⁻¹ • (s (t • z) - x0), hsolv0, ?_⟩
    · intro w hw
      -- uniqueness argument reused below
      set D := ‖z‖ + ‖w‖ + ‖t⁻¹ • (s (t • z) - x0)‖ + 1 with hD
      set ρ' := min r1 r2 with hρ'
      have hρ'0 : 0 < ρ' := lt_min hr1 hr2
      set τ := ρ' / D with hτ
      have hτ0 : 0 < τ := by positivity
      have hτz : ‖τ • z‖ < r1 := lt_of_lt_of_le (rsr_small hρ'0 z (by
        have := norm_nonneg w; have := norm_nonneg (t⁻¹ • (s (t • z) - x0)); linarith))
        (min_le_left _ _)
      have huniq : ∀ v, z - L.starProjection (M v) ∈ normalCone T v → ‖v‖ < D →
          x0 + τ • v = s (τ • z) := by
        intro v hv hvD
        have hτv : ‖τ • v‖ < r2 := lt_of_lt_of_le (rsr_small hρ'0 v hvD) (min_le_right _ _)
        have hmem : x0 + τ • v ∈ N ∩ V :=
          hr2s (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hτv)
        have hyU : τ • z ∈ U := (hr1s (mem_ball_zero_iff.2 hτz)).1
        refine (hs (τ • z) hyU).2.2 _ hmem.2 ?_
        rw [hA τ hτz _ hmem.1, add_sub_cancel_left, hscale τ hτ0]
        exact hv
      have hw0 : ‖w‖ < D := by
        have := norm_nonneg z; have := norm_nonneg (t⁻¹ • (s (t • z) - x0)); linarith
      have hv0 : ‖t⁻¹ • (s (t • z) - x0)‖ < D := by
        have := norm_nonneg z; have := norm_nonneg w; linarith
      have e1 := huniq w hw hw0
      have hsolv : z - L.starProjection (M (t⁻¹ • (s (t • z) - x0))) ∈
          normalCone T (t⁻¹ • (s (t • z) - x0)) := by
        rw [← hscale t ht0, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
        exact hred
      have e2 := huniq _ hsolv hv0
      rw [← e2] at e1
      have := add_left_cancel e1
      exact smul_right_injective _ hτ0.ne' this
  · intro hcase
    have hu : ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (M w) ∈ normalCone T w := by
      rcases hcase with hbot | hu
      · have hmem0 : ∀ u ∈ L, u = 0 := fun u hu => by
          rw [hbot] at hu; exact (Submodule.mem_bot ℝ).1 hu
        have hT0 : ∀ h ∈ T, h = 0 := by
          intro h hh
          rw [hTpol] at hh
          have hN : h ∈ normalCone F x0 := ⟨hF ▸ hx0F, fun c hc => by
            rw [hmem0 _ (hxF c hc), inner_zero_right]⟩
          have := hh h hN
          exact real_inner_self_nonpos.1 this
        intro z hz
        refine ⟨0, ?_, fun w hw => hT0 w hw.1⟩
        show z - L.starProjection (M 0) ∈ normalCone T 0
        rw [hmem0 z hz, hmem0 (L.starProjection (M 0)) (L.starProjection_apply_mem _), sub_zero]
        exact h00
      · exact hu
    set B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (L.starProjection : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap ∘ₗ M
      with hB
    have hBw : ∀ w, B w = L.starProjection (M w) := fun w => rfl
    have hu' : ∀ z ∈ L, ∃! w, z - B w ∈ normalCone (rsrPoly g (fun _ => 0)) w := by
      intro z hz
      simp only [hBw, ← hTg]
      exact hu z hz
    obtain ⟨K, hK0, hK⟩ := rsr_lipsol g B L hu'
    have hex : ∀ z, ∃ w, z ∈ L → z - L.starProjection (M w) ∈ normalCone T w := by
      intro z
      by_cases hz : z ∈ L
      · obtain ⟨w, hw, -⟩ := hu z hz
        exact ⟨w, fun _ => hw⟩
      · exact ⟨0, fun h => absurd h hz⟩
    choose sol hsolv using hex
    have hK' : ∀ z1 ∈ L, ∀ z2 ∈ L, ‖sol z1 - sol z2‖ ≤ K * ‖z1 - z2‖ := by
      intro z1 hz1 z2 hz2
      have h1 := hsolv z1 hz1
      have h2 := hsolv z2 hz2
      rw [← hBw, hTg] at h1 h2
      exact hK z1 hz1 z2 hz2 _ _ h1 h2
    have hsol0 : sol 0 = 0 := by
      have := hsolv 0 L.zero_mem
      refine (hu 0 L.zero_mem).unique this ?_
      simpa using h00
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
    refine ⟨K, hsol, W ∩ Metric.ball 0 (ε / (K + 1)),
      Filter.inter_mem hW (Metric.ball_mem_nhds 0 (by positivity)), N, hN,
      fun y => x0 + sol (L.starProjection y), ?_, ?_⟩
    · rintro y ⟨hyW, hyB⟩
      have hPy : L.starProjection y ∈ L := L.starProjection_apply_mem y
      have hbound : ‖sol (L.starProjection y)‖ ≤ K * ‖y‖ := by
        have := hK' _ hPy 0 L.zero_mem
        rw [hsol0, sub_zero, sub_zero] at this
        exact this.trans (mul_le_mul_of_nonneg_left (L.norm_starProjection_apply_le y) hK0)
      have hy' : ‖y‖ < ε / (K + 1) := mem_ball_zero_iff.1 hyB
      have hsN : x0 + sol (L.starProjection y) ∈ N := by
        apply hεN
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        have h1 : K * ‖y‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hy'.le hK0
        have h2 : K * (ε / (K + 1)) < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
        linarith
      refine ⟨hsN, ?_, ?_⟩
      · rw [Hc _ hsN y hyW, add_sub_cancel_left]
        exact hsolv _ hPy
      · intro x hxN hxs
        have h1 := (Hc x hxN y hyW).1 hxs
        have := (hu _ hPy).unique h1 (hsolv _ hPy)
        show x = x0 + sol (L.starProjection y)
        rw [← this]; abel
    · rintro y1 - y2 -
      show ‖x0 + sol (L.starProjection y1) - (x0 + sol (L.starProjection y2))‖ ≤ K * ‖y1 - y2‖
      rw [add_sub_add_left_eq_sub]
      refine (hK' _ (L.starProjection_apply_mem _) _ (L.starProjection_apply_mem _)).trans ?_
      rw [← map_sub]
      exact mul_le_mul_of_nonneg_left (L.norm_starProjection_apply_le _) hK0

theorem theorem_A_4_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    (∃ lam : ℝ, StronglyRegularLin C A a x0 lam) ↔
      (L = ⊥ ∨ ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (Matrix.toEuclideanLin A w) ∈ normalCone T w) := by
  intro y0 F T L
  exact rsr_A4_aux C hCp A a x0 hsol F T L rfl rfl rfl

end RobinsonSR.Reduction

open RobinsonSR.Reduction


theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    (∃ lam : ℝ, StronglyRegularLin C A a x0 lam) ↔
      (L = ⊥ ∨ ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (Matrix.toEuclideanLin A w) ∈ normalCone T w) := by
  exact theorem_A_4_core C hCp hCne A a x0 hsol
