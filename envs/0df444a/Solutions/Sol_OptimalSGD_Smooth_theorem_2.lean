-- Prove2me | solution 1 for OptimalSGD.Smooth.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T05:18:37.647353+00:00
-- url     : https://prove2.me/submissions/5c5ad57e-7a56-417e-b5f7-c9bfddcdea42

import Mathlib
import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

set_option autoImplicit false

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace SGD2

section Proj

variable {d : ℕ}

lemma proj_isProj {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (v : Vec d) : IsProjection W v (projOnto W v) := by
  have hex : ∃ p, IsProjection W v p := by
    obtain ⟨p, hp, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hW v
    refine ⟨p, hp, fun x hx => ?_⟩
    rw [norm_sub_rev p v, heq, norm_sub_rev x v]
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨x, hx⟩ : W)
  unfold projOnto
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma proj_mem {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (v : Vec d) : projOnto W v ∈ W := (proj_isProj hW hclosed hne v).1

lemma proj_inner {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (v x : Vec d) (hx : x ∈ W) : ⟪v - projOnto W v, x - projOnto W v⟫_ℝ ≤ 0 := by
  have hP := proj_isProj hW hclosed hne v
  have : Nonempty W := ⟨⟨_, hP.1⟩⟩
  have heq : ‖v - projOnto W v‖ = ⨅ w : W, ‖v - w‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => by rw [norm_sub_rev, norm_sub_rev v]; exact hP.2 w w.2
    · exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨_, hP.1⟩ : W)
  exact (norm_eq_iInf_iff_real_inner_le_zero hW hP.1).1 heq x hx

lemma proj_lip {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (u v : Vec d) : ‖projOnto W u - projOnto W v‖ ≤ ‖u - v‖ := by
  have h1 := proj_inner hW hclosed hne u (projOnto W v) (proj_mem hW hclosed hne v)
  have h2 := proj_inner hW hclosed hne v (projOnto W u) (proj_mem hW hclosed hne u)
  set p := projOnto W u
  set q := projOnto W v
  have key : ‖p - q‖ ^ 2 ≤ ⟪u - v, p - q⟫_ℝ := by
    have e : ⟪u - v, p - q⟫_ℝ - ‖p - q‖ ^ 2 = -⟪u - p, q - p⟫_ℝ - ⟪v - q, p - q⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  have h3 := real_inner_le_norm (u - v) (p - q)
  by_cases h0 : ‖p - q‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma proj_self {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    {x : Vec d} (hx : x ∈ W) : projOnto W x = x := by
  have h := (proj_isProj hW hclosed hne x).2 x hx
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

lemma proj_cont {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty) :
    Continuous (projOnto W) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact proj_lip hW hclosed hne x y).continuous

end Proj

section Det

variable {d : ℕ}

/-- strong convexity + relative subgradient + minimality: `λ‖w − w*‖² ≤ ⟪m, w − w*⟫`. -/
lemma sc_ineq {W : Set (Vec d)} (hW : Convex ℝ W) {F : Vec d → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hF : StrongConvexOn W lam F) {wstar : Vec d} (hwstar : wstar ∈ W)
    (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {w m : Vec d} (hw : w ∈ W) (hsub : ∀ u ∈ W, F w + ⟪u - w, m⟫_ℝ ≤ F u) :
    lam * ‖w - wstar‖ ^ 2 ≤ ⟪m, w - wstar⟫_ℝ := by
  set Q := ‖w - wstar‖ ^ 2 with hQdef
  set X := ⟪m, w - wstar⟫_ℝ with hXdef
  have key : ∀ s : ℝ, 0 < s → s < 1 → (1 - s) * (lam * Q) ≤ X := by
    intro s hs0 hs1
    have ha : 0 ≤ 1 - s := by linarith
    have h1 := hF.2 hw hwstar ha hs0.le (by ring)
    have h2 := hF.2 hwstar hw ha hs0.le (by ring)
    have hu : (1 - s) • w + s • wstar ∈ W := hW hw hwstar ha hs0.le (by ring)
    have hv : (1 - s) • wstar + s • w ∈ W := hW hwstar hw ha hs0.le (by ring)
    have h3 := hsub _ hu
    have h4 := hmin _ hv
    have e1 : (1 - s) • w + s • wstar - w = s • (wstar - w) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e1, real_inner_smul_left] at h3
    have e2 : ⟪wstar - w, m⟫_ℝ = -X := by
      rw [hXdef, real_inner_comm, ← inner_neg_right, neg_sub]
    rw [e2] at h3
    have e3 : ‖wstar - w‖ = ‖w - wstar‖ := norm_sub_rev _ _
    simp only [smul_eq_mul] at h1 h2
    rw [e3] at h2
    have h5 : s * ((1 - s) * (lam * Q)) ≤ s * X := by nlinarith
    exact le_of_mul_le_mul_left h5 hs0
  have hQ : 0 ≤ lam * Q := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  set p := lam * Q
  have hs0 : 0 < ε / (2 * ε + p) := by positivity
  have hs1 : ε / (2 * ε + p) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h := key _ hs0 hs1
  have e : (1 - ε / (2 * ε + p)) * p = p * (ε + p) / (2 * ε + p) := by field_simp; ring
  rw [e] at h
  have h' : p - ε ≤ p * (ε + p) / (2 * ε + p) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

lemma dist_bound {lam G : ℝ} (hlam : 0 < lam) {a m : Vec d} (hm : ‖m‖ ^ 2 ≤ G ^ 2)
    (h : lam * ‖a‖ ^ 2 ≤ ⟪m, a⟫_ℝ) : ‖a‖ ^ 2 ≤ G ^ 2 / lam ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 := real_inner_le_norm m a
  by_cases h0 : ‖a‖ = 0
  · rw [h0]; nlinarith
  · have hpos : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h2 : lam * ‖a‖ ≤ ‖m‖ := by nlinarith
    have h3 : 0 ≤ lam * ‖a‖ := by positivity
    nlinarith

/-- `2⟪a, b⟫ ≤ ε‖a‖² + ‖b‖²/ε`, in the averaged form used for the recursion. -/
lemma young_avg (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 < ε) (X Y : Vec d) :
    ‖α • X + β • Y‖ ^ 2 ≤ (1 + ε) * α ^ 2 * ‖X‖ ^ 2 + (1 + 1 / ε) * β ^ 2 * ‖Y‖ ^ 2 := by
  have h0 : 0 ≤ ‖(ε * α) • X - β • Y‖ ^ 2 := by positivity
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hβ] at h0
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hβ]
  have e : (1 + 1 / ε) * β ^ 2 * ‖Y‖ ^ 2 = β ^ 2 * ‖Y‖ ^ 2 + (β * ‖Y‖) ^ 2 / ε := by
    field_simp
  rw [e]
  have h1 : 2 * (α * (β * ⟪X, Y⟫_ℝ)) ≤ ε * α ^ 2 * ‖X‖ ^ 2 + (β * ‖Y‖) ^ 2 / ε := by
    rw [← sub_nonneg]
    have : ε * α ^ 2 * ‖X‖ ^ 2 + (β * ‖Y‖) ^ 2 / ε - 2 * (α * (β * ⟪X, Y⟫_ℝ)) =
        ((ε * α * ‖X‖) ^ 2 - 2 * (ε * α * (β * ⟪X, Y⟫_ℝ)) + (β * ‖Y‖) ^ 2) / ε := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ hε.le
    nlinarith
  nlinarith

end Det

section Iter

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

lemma iter_succ (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z)
    (t : ℕ) (ht : t < T) :
    sgdStrongIterates lam W g S (t + 1) =
      projOnto W (sgdStrongIterates lam W g S t -
        (1 / (lam * ((t : ℝ) + 1))) • g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)) := by
  simp only [sgdStrongIterates, dif_pos ht]

lemma iter_succ_ge (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z)
    (t : ℕ) (ht : ¬ t < T) :
    sgdStrongIterates lam W g S (t + 1) = projOnto W (sgdStrongIterates lam W g S t) := by
  simp only [sgdStrongIterates, dif_neg ht, smul_zero, sub_zero]

lemma iter_mem {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (lam : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) :
    ∀ t, sgdStrongIterates lam W g S t ∈ W
  | 0 => by simpa [sgdStrongIterates] using hzero
  | t + 1 => by simp only [sgdStrongIterates]; exact proj_mem hW hclosed ⟨0, hzero⟩ _

lemma iter_update (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z)
    (i : Fin T) (z : Z) :
    ∀ t, t ≤ i.val → sgdStrongIterates lam W g (Function.update S i z) t =
      sgdStrongIterates lam W g S t
  | 0, _ => by simp [sgdStrongIterates]
  | t + 1, h => by
    have ih := iter_update lam W g S i z t (by omega)
    by_cases ht : t < T
    · rw [iter_succ _ _ _ _ _ ht, iter_succ _ _ _ _ _ ht, ih]
      have hne : (⟨t, ht⟩ : Fin T) ≠ i := by
        intro e; rw [← e] at h; simp at h
      rw [Function.update_of_ne hne]
    · rw [iter_succ_ge _ _ _ _ _ ht, iter_succ_ge _ _ _ _ _ ht, ih]

lemma iter_meas {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (lam : ℝ) {g : Vec d → Z → Vec d} (hg : Measurable (Function.uncurry g)) {T : ℕ} :
    ∀ t, Measurable (fun S : Fin T → Z => sgdStrongIterates lam W g S t)
  | 0 => by simp only [sgdStrongIterates]; exact measurable_const
  | t + 1 => by
    have ih := iter_meas hW hclosed hne lam hg (T := T) t
    have hP := (proj_cont hW hclosed hne).measurable
    by_cases ht : t < T
    · have e : (fun S : Fin T → Z => sgdStrongIterates lam W g S (t + 1)) = fun S =>
          projOnto W (sgdStrongIterates lam W g S t -
            (1 / (lam * ((t : ℝ) + 1))) • g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)) :=
        funext fun S => iter_succ lam W g S t ht
      rw [e]
      have hgm : Measurable fun S : Fin T → Z => g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩) :=
        hg.comp (ih.prodMk (measurable_pi_apply _))
      exact hP.comp (ih.sub (hgm.const_smul (1 / (lam * ((t : ℝ) + 1)))))
    · have e : (fun S : Fin T → Z => sgdStrongIterates lam W g S (t + 1)) = fun S =>
          projOnto W (sgdStrongIterates lam W g S t) :=
        funext fun S => iter_succ_ge lam W g S t ht
      rw [e]; exact hP.comp ih

lemma one_step {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) {wstar : Vec d}
    (hwstar : wstar ∈ W) (lam : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) (t : ℕ)
    (ht : t < T) :
    ‖sgdStrongIterates lam W g S (t + 1) - wstar‖ ^ 2 ≤
      ‖sgdStrongIterates lam W g S t - wstar‖ ^ 2
      - 2 * (1 / (lam * ((t : ℝ) + 1))) *
          ⟪g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩), sgdStrongIterates lam W g S t - wstar⟫_ℝ
      + (1 / (lam * ((t : ℝ) + 1))) ^ 2 * ‖g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)‖ ^ 2 := by
  have hne : W.Nonempty := ⟨wstar, hwstar⟩
  rw [iter_succ lam W g S t ht]
  set w := sgdStrongIterates lam W g S t
  set v := g w (S ⟨t, ht⟩)
  set η := 1 / (lam * ((t : ℝ) + 1))
  have h1 : ‖projOnto W (w - η • v) - wstar‖ ≤ ‖w - η • v - wstar‖ := by
    have := proj_lip hW hclosed hne (w - η • v) wstar
    rwa [proj_self hW hclosed hne hwstar] at this
  have h2 : ‖projOnto W (w - η • v) - wstar‖ ^ 2 ≤ ‖w - η • v - wstar‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : w - η • v - wstar = (w - wstar) - η • v := by abel
  rw [e, norm_sub_sq_real (w - wstar) (η • v), real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_comm] at h2
  linarith

end Iter

section Meas

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

lemma iid_prob (D : Measure Z) [IsProbabilityMeasure D] (T : ℕ) :
    IsProbabilityMeasure (iidLaw D T) := by
  unfold iidLaw; infer_instance

lemma upd_mp (D : Measure Z) [IsProbabilityMeasure D] (T : ℕ) (i : Fin T) :
    MeasurePreserving (fun p : (Fin T → Z) × Z => Function.update p.1 i p.2)
      ((iidLaw D T).prod D) (iidLaw D T) := by
  haveI := iid_prob D T
  refine ⟨measurable_update', ?_⟩
  unfold iidLaw
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin T → Z) × Z => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ (s i) := by
    ext ⟨S, z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => D (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => D (Function.update s i Set.univ j))
      (Finset.mem_univ i)]
  have hc : ∏ j ∈ Finset.univ.erase i, D (Function.update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, D (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hc]
  simp only [Function.update_self, measure_univ, one_mul]
  ring

lemma int_upd (D : Measure Z) [IsProbabilityMeasure D] {T : ℕ} (i : Fin T)
    {f : (Fin T → Z) → ℝ} (hf : AEStronglyMeasurable f (iidLaw D T)) :
    ∫ S, f S ∂(iidLaw D T) = ∫ p, f (Function.update p.1 i p.2) ∂((iidLaw D T).prod D) := by
  have h := upd_mp D T i
  rw [← integral_map h.measurable.aemeasurable (by rwa [h.map_eq]), h.map_eq]

lemma lint_upd (D : Measure Z) [IsProbabilityMeasure D] {T : ℕ} (i : Fin T)
    {f : (Fin T → Z) → ENNReal} (hf : Measurable f) :
    ∫⁻ S, f S ∂(iidLaw D T) = ∫⁻ p, f (Function.update p.1 i p.2) ∂((iidLaw D T).prod D) := by
  have h := upd_mp D T i
  rw [← lintegral_map hf h.measurable, h.map_eq]

lemma sq_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hnn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ C := by
  have hnn' : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hnn
  have hint : Integrable f μ :=
    ⟨hf, (hasFiniteIntegral_iff_ofReal hnn').2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn'] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 h

lemma mean_sq_le (D : Measure Z) [IsProbabilityMeasure D] {f : Z → Vec d} (hf : Integrable f D)
    (h2 : Integrable (fun z => ‖f z‖ ^ 2) D) :
    ‖∫ z, f z ∂D‖ ^ 2 ≤ ∫ z, ‖f z‖ ^ 2 ∂D := by
  set m := ∫ z, f z ∂D
  have h1 : ‖m‖ ^ 2 = ∫ z, ⟪m, f z⟫_ℝ ∂D := by
    rw [integral_inner hf, real_inner_self_eq_norm_sq]
  have hb : Integrable (fun z => (‖m‖ ^ 2 + ‖f z‖ ^ 2) / 2) D :=
    ((integrable_const _).add h2).div_const 2
  have h3 : ∫ z, ⟪m, f z⟫_ℝ ∂D ≤ ∫ z, (‖m‖ ^ 2 + ‖f z‖ ^ 2) / 2 ∂D := by
    apply integral_mono (hf.const_inner m) hb
    intro z
    have := real_inner_le_norm m (f z)
    nlinarith [sq_nonneg (‖m‖ - ‖f z‖)]
  rw [integral_div, integral_add (integrable_const _) h2, integral_const] at h3
  simp only [probReal_univ, one_smul] at h3
  linarith

lemma sq_int {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → Vec d} (hu : Measurable u) {wstar : Vec d} {R2 : ℝ}
    (hb : ∀ x, ‖u x - wstar‖ ^ 2 ≤ R2) : Integrable (fun x => ‖u x - wstar‖ ^ 2) μ :=
  Integrable.mono' (integrable_const R2)
    ((hu.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb x)

lemma exp_step (D : Measure Z) [IsProbabilityMeasure D] {g : Vec d → Z → Vec d}
    (hg : Measurable (Function.uncurry g)) {W : Set (Vec d)}
    (hint : ∀ v ∈ W, Integrable (g v) D) {G : ℝ}
    (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    {wstar : Vec d} {lam R2 : ℝ}
    (hsc : ∀ v ∈ W, lam * ‖v - wstar‖ ^ 2 ≤ ⟪OptimalSGD.Suffix.oracleMean D g v, v - wstar⟫_ℝ)
    (hR : ∀ v ∈ W, ‖v - wstar‖ ^ 2 ≤ R2)
    {T : ℕ} (i : Fin T) (w : (Fin T → Z) → Vec d) (hw : Measurable w) (hwW : ∀ S, w S ∈ W)
    (hdep : ∀ S z, w (Function.update S i z) = w S) :
    (Integrable (fun S => ‖g (w S) (S i)‖ ^ 2) (iidLaw D T) ∧
      ∫ S, ‖g (w S) (S i)‖ ^ 2 ∂(iidLaw D T) ≤ G ^ 2) ∧
    (Integrable (fun S => ⟪g (w S) (S i), w S - wstar⟫_ℝ) (iidLaw D T) ∧
      lam * ∫ S, ‖w S - wstar‖ ^ 2 ∂(iidLaw D T) ≤
        ∫ S, ⟪g (w S) (S i), w S - wstar⟫_ℝ ∂(iidLaw D T)) := by
  haveI := iid_prob D T
  have hmp := upd_mp D T i
  have hgw : Measurable fun p : (Fin T → Z) × Z => g (w p.1) p.2 :=
    hg.comp ((hw.comp measurable_fst).prodMk measurable_snd)
  have hlprod : ∫⁻ p, ENNReal.ofReal (‖g (w p.1) p.2‖ ^ 2) ∂((iidLaw D T).prod D) ≤
      ENNReal.ofReal (G ^ 2) := by
    rw [lintegral_prod _ (hgw.norm.pow_const 2).ennreal_ofReal.aemeasurable]
    calc ∫⁻ S, ∫⁻ z, ENNReal.ofReal (‖g (w S) z‖ ^ 2) ∂D ∂(iidLaw D T)
        ≤ ∫⁻ S, ENNReal.ofReal (G ^ 2) ∂(iidLaw D T) :=
          lintegral_mono fun S => hmoment _ (hwW S)
      _ = ENNReal.ofReal (G ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
  have h2prod := sq_lint (hgw.norm.pow_const 2).aestronglyMeasurable (fun _ => by positivity)
    (sq_nonneg G) hlprod
  have hφm : Measurable fun S : Fin T → Z => g (w S) (S i) :=
    hg.comp (hw.prodMk (measurable_pi_apply i))
  have part1 : Integrable (fun S => ‖g (w S) (S i)‖ ^ 2) (iidLaw D T) ∧
      ∫ S, ‖g (w S) (S i)‖ ^ 2 ∂(iidLaw D T) ≤ G ^ 2 := by
    apply sq_lint (hφm.norm.pow_const 2).aestronglyMeasurable (fun _ => by positivity) (sq_nonneg G)
    rw [lint_upd D i (hφm.norm.pow_const 2).ennreal_ofReal]
    simp only [hdep, Function.update_self]
    exact hlprod
  have hΦm : Measurable fun p : (Fin T → Z) × Z => ⟪g (w p.1) p.2, w p.1 - wstar⟫_ℝ :=
    hgw.inner ((hw.comp measurable_fst).sub measurable_const)
  have hΦint : Integrable (fun p : (Fin T → Z) × Z => ⟪g (w p.1) p.2, w p.1 - wstar⟫_ℝ)
      ((iidLaw D T).prod D) := by
    refine Integrable.mono' ((h2prod.1.add (integrable_const R2)).div_const 2)
      hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hb := hR _ (hwW p.1)
    have h1 := abs_real_inner_le_norm (g (w p.1) p.2) (w p.1 - wstar)
    show |⟪g (w p.1) p.2, w p.1 - wstar⟫_ℝ| ≤ (‖g (w p.1) p.2‖ ^ 2 + R2) / 2
    nlinarith [sq_nonneg (‖g (w p.1) p.2‖ - ‖w p.1 - wstar‖), norm_nonneg (g (w p.1) p.2),
      norm_nonneg (w p.1 - wstar)]
  have hinner : ∀ S, ∫ z, ⟪g (w S) z, w S - wstar⟫_ℝ ∂D =
      ⟪OptimalSGD.Suffix.oracleMean D g (w S), w S - wstar⟫_ℝ := by
    intro S
    simp only [OptimalSGD.Suffix.oracleMean]
    simp_rw [real_inner_comm (w S - wstar)]
    exact integral_inner (hint _ (hwW S)) _
  have hmeanint : Integrable
      (fun S => ⟪OptimalSGD.Suffix.oracleMean D g (w S), w S - wstar⟫_ℝ) (iidLaw D T) :=
    hΦint.integral_prod_left.congr (Filter.Eventually.of_forall hinner)
  have hφm' : Measurable fun S : Fin T → Z => ⟪g (w S) (S i), w S - wstar⟫_ℝ :=
    hφm.inner (hw.sub measurable_const)
  have hφint : Integrable (fun S : Fin T → Z => ⟪g (w S) (S i), w S - wstar⟫_ℝ) (iidLaw D T) := by
    rw [← hmp.integrable_comp hφm'.aestronglyMeasurable]
    have e : (fun S : Fin T → Z => ⟪g (w S) (S i), w S - wstar⟫_ℝ) ∘
        (fun p : (Fin T → Z) × Z => Function.update p.1 i p.2) =
        fun p => ⟪g (w p.1) p.2, w p.1 - wstar⟫_ℝ := by
      funext p; simp only [Function.comp, hdep, Function.update_self]
    rw [e]; exact hΦint
  have hsqint : Integrable (fun S => ‖w S - wstar‖ ^ 2) (iidLaw D T) :=
    sq_int hw fun S => hR _ (hwW S)
  refine ⟨part1, hφint, ?_⟩
  have e1 : ∫ S, ⟪g (w S) (S i), w S - wstar⟫_ℝ ∂(iidLaw D T) =
      ∫ S, ⟪OptimalSGD.Suffix.oracleMean D g (w S), w S - wstar⟫_ℝ ∂(iidLaw D T) := by
    rw [int_upd D i hφm'.aestronglyMeasurable]
    simp only [hdep, Function.update_self]
    rw [integral_prod _ hΦint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [e1, ← integral_const_mul]
  exact integral_mono (hsqint.const_mul lam) hmeanint fun S => hsc _ (hwW S)

end Meas

section Main

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

lemma num1 (n x R : ℝ) (hn : 1 ≤ n) (hx0 : 0 ≤ x) (hx : x ≤ 4 * R / n) (hR : 0 ≤ R) :
    (1 - 2 / n) * x + R / n ^ 2 ≤ 4 * R / (n + 1) := by
  have hn0 : 0 < n := by linarith
  have key : x * n ≤ 4 * R := by rwa [le_div_iff₀ hn0] at hx
  have e : (1 - 2 / n) * x + R / n ^ 2 = ((n - 2) * (x * n) + R) / n ^ 2 := by
    field_simp; try ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_or_gt 2 n with h2 | h2
  · have h3 : (n - 2) * (x * n) ≤ (n - 2) * (4 * R) := mul_le_mul_of_nonneg_left key (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0:ℝ) ≤ n + 1)
    nlinarith [mul_nonneg hR hn0.le]
  · have h3 : (n - 2) * (x * n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0:ℝ) ≤ n + 1)
    nlinarith [mul_nonneg hR (by linarith : (0:ℝ) ≤ n - 1),
      mul_nonneg (mul_nonneg hR hn0.le) (by linarith : (0:ℝ) ≤ n - 1)]

lemma num2 (k a b c : ℝ) (hk : 1 ≤ k) (ha : a ≤ c / (k + 1)) (hb : b ≤ 8 * c / k) (hc : 0 ≤ c) :
    (1 + 1 / (2 * k)) * (k / (k + 1)) ^ 2 * b + (1 + 1 / (1 / (2 * k))) * (1 / (k + 1)) ^ 2 * a ≤
      8 * c / (k + 1) := by
  have hk0 : 0 < k := by linarith
  have h1 := mul_le_mul_of_nonneg_left hb
    (by positivity : (0:ℝ) ≤ (1 + 1 / (2 * k)) * (k / (k + 1)) ^ 2)
  have h2 := mul_le_mul_of_nonneg_left ha
    (by positivity : (0:ℝ) ≤ (1 + 1 / (1 / (2 * k))) * (1 / (k + 1)) ^ 2)
  have e : (1 + 1 / (2 * k)) * (k / (k + 1)) ^ 2 * (8 * c / k) +
      (1 + 1 / (1 / (2 * k))) * (1 / (k + 1)) ^ 2 * (c / (k + 1)) =
      c * (8 * k ^ 2 + 14 * k + 5) / (k + 1) ^ 3 := by
    field_simp; ring
  have h3 : c * (8 * k ^ 2 + 14 * k + 5) / (k + 1) ^ 3 ≤ 8 * c / (k + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hc (by linarith : (0:ℝ) ≤ k + 1))
      (by linarith : (0:ℝ) ≤ 2 * k + 3)]
  linarith

lemma lemma1 {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    {lam : ℝ} (hlam : 0 < lam) (D : Measure Z) [IsProbabilityMeasure D] {g : Vec d → Z → Vec d}
    (hg : Measurable (Function.uncurry g)) (hint : ∀ v ∈ W, Integrable (g v) D) {G : ℝ}
    (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    {wstar : Vec d} (hwstar : wstar ∈ W)
    (hsc : ∀ v ∈ W, lam * ‖v - wstar‖ ^ 2 ≤ ⟪OptimalSGD.Suffix.oracleMean D g v, v - wstar⟫_ℝ)
    (hR : ∀ v ∈ W, ‖v - wstar‖ ^ 2 ≤ G ^ 2 / lam ^ 2) (T : ℕ) :
    ∀ t, t ≤ T → ∫ S, ‖sgdStrongIterates lam W g S t - wstar‖ ^ 2 ∂(iidLaw D T) ≤
      4 * (G ^ 2 / lam ^ 2) / ((t : ℝ) + 1) := by
  haveI := iid_prob D T
  have hne : W.Nonempty := ⟨0, hzero⟩
  have hR0 : 0 ≤ G ^ 2 / lam ^ 2 := by positivity
  intro t
  induction t with
  | zero =>
    intro _
    have h := integral_mono (sq_int (μ := iidLaw D T) (iter_meas hW hclosed hne lam hg 0)
      fun S => hR _ (iter_mem hW hclosed hzero lam g S 0)) (integrable_const (G ^ 2 / lam ^ 2))
      (fun S => hR _ (iter_mem hW hclosed hzero lam g S 0))
    simp only [integral_const, probReal_univ, one_smul] at h
    simp only [Nat.cast_zero, zero_add, div_one]
    linarith
  | succ t ih =>
    intro htT
    have ht : t < T := by omega
    have iht := ih (by omega)
    obtain ⟨⟨h2i, h2⟩, ⟨hii, hi⟩⟩ := exp_step D hg hint hmoment hsc hR ⟨t, ht⟩
      (fun S => sgdStrongIterates lam W g S t) (iter_meas hW hclosed hne lam hg t)
      (fun S => iter_mem hW hclosed hzero lam g S t)
      (fun S z => iter_update lam W g S ⟨t, ht⟩ z t le_rfl)
    beta_reduce at h2i h2 hii hi
    have hsqt := sq_int (μ := iidLaw D T) (iter_meas hW hclosed hne lam hg t)
      fun S => hR _ (iter_mem hW hclosed hzero lam g S t)
    have hsqt1 := sq_int (μ := iidLaw D T) (iter_meas hW hclosed hne lam hg (t + 1))
      fun S => hR _ (iter_mem hW hclosed hzero lam g S (t + 1))
    set η := 1 / (lam * ((t : ℝ) + 1)) with hη
    have hC : Integrable (fun S : Fin T → Z => 2 * η *
        ⟪g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩), sgdStrongIterates lam W g S t - wstar⟫_ℝ)
        (iidLaw D T) := hii.const_mul _
    have hB : Integrable (fun S : Fin T → Z =>
        η ^ 2 * ‖g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)‖ ^ 2) (iidLaw D T) :=
      h2i.const_mul _
    have hA : Integrable (fun S : Fin T → Z => ‖sgdStrongIterates lam W g S t - wstar‖ ^ 2 - 2 * η *
        ⟪g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩), sgdStrongIterates lam W g S t - wstar⟫_ℝ)
        (iidLaw D T) := hsqt.sub hC
    have hstep : ∫ S, ‖sgdStrongIterates lam W g S (t + 1) - wstar‖ ^ 2 ∂(iidLaw D T) ≤
        ∫ S, (‖sgdStrongIterates lam W g S t - wstar‖ ^ 2 - 2 * η *
          ⟪g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩), sgdStrongIterates lam W g S t - wstar⟫_ℝ
          + η ^ 2 * ‖g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)‖ ^ 2) ∂(iidLaw D T) :=
      integral_mono hsqt1 (hA.add hB) (fun S => one_step hW hclosed hwstar lam g S t ht)
    rw [integral_add hA hB, integral_sub hsqt hC, integral_const_mul, integral_const_mul] at hstep
    set a := ∫ S, ‖sgdStrongIterates lam W g S t - wstar‖ ^ 2 ∂(iidLaw D T)
    have hstep2 : ∫ S, ‖sgdStrongIterates lam W g S (t + 1) - wstar‖ ^ 2 ∂(iidLaw D T) ≤
        (1 - 2 / ((t : ℝ) + 1)) * a + (G ^ 2 / lam ^ 2) / ((t : ℝ) + 1) ^ 2 := by
      have e1 : 2 * η * (lam * a) = 2 / ((t : ℝ) + 1) * a := by rw [hη]; field_simp
      have e2 : η ^ 2 * G ^ 2 = (G ^ 2 / lam ^ 2) / ((t : ℝ) + 1) ^ 2 := by rw [hη]; field_simp
      have h5 := mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ) ≤ 2 * η)
      have h6 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ η ^ 2)
      nlinarith
    have ha0 : 0 ≤ a := integral_nonneg fun S => by positivity
    have := num1 ((t : ℝ) + 1) a (G ^ 2 / lam ^ 2)
      (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]) ha0 iht hR0
    push_cast
    linarith

/-- the running average `w̄_k = (w_0 + … + w_{k-1})/k`. -/
noncomputable def avgK (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ}
    (S : Fin T → Z) (k : ℕ) : Vec d :=
  ((k : ℝ))⁻¹ • ∑ t ∈ Finset.range k, sgdStrongIterates lam W g S t

lemma avg_mem {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (lam : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) {k : ℕ} (hk : 1 ≤ k) :
    avgK lam W g S k ∈ W := by
  unfold avgK
  rw [Finset.smul_sum]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  apply hW.sum_mem (fun _ _ => by positivity)
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; exact mul_inv_cancel₀ hk0
  · intro t _; exact iter_mem hW hclosed hzero lam g S t

lemma avg_meas {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W) (hne : W.Nonempty)
    (lam : ℝ) {g : Vec d → Z → Vec d} (hg : Measurable (Function.uncurry g)) {T : ℕ} (k : ℕ) :
    Measurable (fun S : Fin T → Z => avgK lam W g S k) := by
  unfold avgK
  exact (Finset.measurable_sum _ fun t _ => iter_meas hW hclosed hne lam hg t).const_smul
    ((k : ℝ))⁻¹

lemma avg_succ (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z)
    {k : ℕ} (hk : 1 ≤ k) (wstar : Vec d) :
    avgK lam W g S (k + 1) - wstar = ((k : ℝ) / (k + 1)) • (avgK lam W g S k - wstar) +
      (1 / ((k : ℝ) + 1)) • (sgdStrongIterates lam W g S k - wstar) := by
  unfold avgK
  rw [Finset.sum_range_succ]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  rw [smul_sub, smul_sub, smul_smul, smul_add]
  have e1 : (k : ℝ) / (k + 1) * (k : ℝ)⁻¹ = ((k : ℝ) + 1)⁻¹ := by field_simp
  rw [e1]
  have e2 : wstar = ((k : ℝ) / (k + 1)) • wstar + (1 / ((k : ℝ) + 1)) • wstar := by
    rw [← add_smul, show (k : ℝ) / (k + 1) + 1 / (k + 1) = 1 by field_simp, one_smul]
  conv_lhs => rw [e2]
  rw [one_div]
  abel

lemma avg_bound {W : Set (Vec d)} (hW : Convex ℝ W) (hclosed : IsClosed W)
    (hzero : (0 : Vec d) ∈ W)
    {lam : ℝ} (hlam : 0 < lam) (D : Measure Z) [IsProbabilityMeasure D] {g : Vec d → Z → Vec d}
    (hg : Measurable (Function.uncurry g)) (hint : ∀ v ∈ W, Integrable (g v) D) {G : ℝ}
    (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    {wstar : Vec d} (hwstar : wstar ∈ W)
    (hsc : ∀ v ∈ W, lam * ‖v - wstar‖ ^ 2 ≤ ⟪OptimalSGD.Suffix.oracleMean D g v, v - wstar⟫_ℝ)
    (hR : ∀ v ∈ W, ‖v - wstar‖ ^ 2 ≤ G ^ 2 / lam ^ 2) (T : ℕ) :
    ∀ k, 1 ≤ k → k ≤ T → ∫ S, ‖avgK lam W g S k - wstar‖ ^ 2 ∂(iidLaw D T) ≤
      8 * (4 * (G ^ 2 / lam ^ 2)) / (k : ℝ) := by
  haveI := iid_prob D T
  have hne : W.Nonempty := ⟨0, hzero⟩
  have hR0 : 0 ≤ G ^ 2 / lam ^ 2 := by positivity
  have L1 := lemma1 hW hclosed hzero hlam D hg hint hmoment hwstar hsc hR T
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk1 hkT
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have e : ∀ S : Fin T → Z, avgK lam W g S (0 + 1) = sgdStrongIterates lam W g S 0 := by
        intro S; simp [avgK]
      simp only [e]
      have := L1 0 (by omega)
      norm_num at this ⊢
      linarith
    · have ihk := ih hk0 (by omega)
      have hak := L1 k (by omega)
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have hYoung : ∀ S : Fin T → Z, ‖avgK lam W g S (k + 1) - wstar‖ ^ 2 ≤
          (1 + 1 / (2 * (k : ℝ))) * ((k : ℝ) / (k + 1)) ^ 2 * ‖avgK lam W g S k - wstar‖ ^ 2 +
          (1 + 1 / (1 / (2 * (k : ℝ)))) * (1 / ((k : ℝ) + 1)) ^ 2 *
            ‖sgdStrongIterates lam W g S k - wstar‖ ^ 2 := by
        intro S
        rw [avg_succ lam W g S hk0 wstar]
        exact young_avg _ _ _ (by positivity) (by positivity) (by positivity) _ _
      have hI1 := sq_int (μ := iidLaw D T) (avg_meas hW hclosed hne lam hg k)
        fun S => hR _ (avg_mem hW hclosed hzero lam g S hk0)
      have hI2 := sq_int (μ := iidLaw D T) (iter_meas hW hclosed hne lam hg k)
        fun S => hR _ (iter_mem hW hclosed hzero lam g S k)
      have hI3 := sq_int (μ := iidLaw D T) (avg_meas hW hclosed hne lam hg (k + 1))
        fun S => hR _ (avg_mem hW hclosed hzero lam g S (by omega))
      have hA : Integrable (fun S : Fin T → Z => (1 + 1 / (2 * (k : ℝ))) * ((k : ℝ) / (k + 1)) ^ 2 *
          ‖avgK lam W g S k - wstar‖ ^ 2) (iidLaw D T) := hI1.const_mul _
      have hB : Integrable (fun S : Fin T → Z => (1 + 1 / (1 / (2 * (k : ℝ)))) *
          (1 / ((k : ℝ) + 1)) ^ 2 * ‖sgdStrongIterates lam W g S k - wstar‖ ^ 2) (iidLaw D T) :=
        hI2.const_mul _
      have hm : ∫ S, ‖avgK lam W g S (k + 1) - wstar‖ ^ 2 ∂(iidLaw D T) ≤
          ∫ S, ((1 + 1 / (2 * (k : ℝ))) * ((k : ℝ) / (k + 1)) ^ 2 * ‖avgK lam W g S k - wstar‖ ^ 2 +
          (1 + 1 / (1 / (2 * (k : ℝ)))) * (1 / ((k : ℝ) + 1)) ^ 2 *
            ‖sgdStrongIterates lam W g S k - wstar‖ ^ 2) ∂(iidLaw D T) :=
        integral_mono hI3 (hA.add hB) hYoung
      rw [integral_add hA hB, integral_const_mul, integral_const_mul] at hm
      have := num2 (k : ℝ) _ _ (4 * (G ^ 2 / lam ^ 2)) hk1' hak ihk (by positivity)
      push_cast
      linarith

lemma F_meas {α : Type*} [MeasurableSpace α] {W : Set (Vec d)} {F : Vec d → ℝ}
    {m : Vec d → Vec d} (hsub : ∀ w ∈ W, ∀ u ∈ W, F w + ⟪u - w, m w⟫_ℝ ≤ F u)
    {A : α → Vec d} (hA : Measurable A) (hAW : ∀ x, A x ∈ W) : Measurable fun x => F (A x) := by
  apply measurable_of_Ioi
  intro c
  set U : Set (Vec d) := ⋃ w ∈ {w | w ∈ W ∧ c < F w}, {u | c < F w + ⟪u - w, m w⟫_ℝ} with hUdef
  have hU : IsOpen U := isOpen_biUnion fun w _ => isOpen_lt continuous_const
    (continuous_const.add ((continuous_id.sub continuous_const).inner continuous_const))
  have e : (fun x => F (A x)) ⁻¹' Set.Ioi c = A ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, hUdef, Set.mem_iUnion, Set.mem_ofPred_eq,
      exists_prop]
    constructor
    · intro h; exact ⟨A x, ⟨hAW x, h⟩, by simpa using h⟩
    · rintro ⟨w, ⟨hw, _⟩, h⟩; exact lt_of_lt_of_le h (hsub w hw _ (hAW x))
  rw [e]; exact hA hU.measurableSet

theorem main {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g))
    (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {μ : ℝ} (hμ : 0 ≤ μ) (hsmooth : OptimalSGD.Smooth.IsSmoothWrt W F μ wstar)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun S : Fin T → Z => F (sgdStrongAverage lam W g S)) (iidLaw D T) ∧
      (∫ S : Fin T → Z, F (sgdStrongAverage lam W g S) ∂(iidLaw D T)) - F wstar ≤
        16 * μ * G ^ 2 / (lam ^ 2 * T) := by
  have hne : W.Nonempty := ⟨0, hzero⟩
  haveI := iid_prob D T
  have hsub : ∀ w ∈ W, ∀ u ∈ W,
      F w + ⟪u - w, OptimalSGD.Suffix.oracleMean D g w⟫_ℝ ≤ F u := fun w hw => (horacle w hw).2
  have hint : ∀ v ∈ W, Integrable (g v) D := fun v hv => (horacle v hv).1
  have hsc : ∀ v ∈ W, lam * ‖v - wstar‖ ^ 2 ≤
      ⟪OptimalSGD.Suffix.oracleMean D g v, v - wstar⟫_ℝ :=
    fun v hv => sc_ineq hW hlam hF hwstar hmin hv (hsub v hv)
  have hmean : ∀ v ∈ W, ‖OptimalSGD.Suffix.oracleMean D g v‖ ^ 2 ≤ G ^ 2 := by
    intro v hv
    have hm2 : AEStronglyMeasurable (fun z => ‖g v z‖ ^ 2) D :=
      (hint v hv).aestronglyMeasurable.norm.pow 2
    have h2 := sq_lint hm2 (fun _ => by positivity) (sq_nonneg G) (hmoment v hv)
    exact (mean_sq_le D (hint v hv) h2.1).trans h2.2
  have hR : ∀ v ∈ W, ‖v - wstar‖ ^ 2 ≤ G ^ 2 / lam ^ 2 :=
    fun v hv => dist_bound hlam (hmean v hv) (hsc v hv)
  have hR0 : 0 ≤ G ^ 2 / lam ^ 2 := by positivity
  have hAm : Measurable fun S : Fin T → Z => sgdStrongAverage lam W g S :=
    avg_meas hW hclosed hne lam hg T
  have hAW : ∀ S : Fin T → Z, sgdStrongAverage lam W g S ∈ W :=
    fun S => avg_mem hW hclosed hzero lam g S hT
  have hFm := F_meas hsub hAm hAW
  have hFlo : ∀ S : Fin T → Z, F wstar ≤ F (sgdStrongAverage lam W g S) :=
    fun S => hmin _ (hAW S)
  have hFhi : ∀ S : Fin T → Z, F (sgdStrongAverage lam W g S) - F wstar ≤
      μ / 2 * ‖sgdStrongAverage lam W g S - wstar‖ ^ 2 := fun S => hsmooth _ (hAW S)
  have hFint : Integrable (fun S : Fin T → Z => F (sgdStrongAverage lam W g S)) (iidLaw D T) := by
    refine Integrable.mono' (integrable_const (|F wstar| + μ / 2 * (G ^ 2 / lam ^ 2)))
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun S => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hFlo S
    have h2 := hFhi S
    have h4 : μ / 2 * ‖sgdStrongAverage lam W g S - wstar‖ ^ 2 ≤ μ / 2 * (G ^ 2 / lam ^ 2) :=
      mul_le_mul_of_nonneg_left (hR _ (hAW S)) (by positivity)
    have h5 : 0 ≤ μ / 2 * (G ^ 2 / lam ^ 2) := by positivity
    constructor
    · have := neg_abs_le (F wstar); linarith
    · have := le_abs_self (F wstar); linarith
  refine ⟨hFint, ?_⟩
  have hsqA := sq_int (μ := iidLaw D T) hAm fun S => hR _ (hAW S)
  have hb : ∫ S, ‖sgdStrongAverage lam W g S - wstar‖ ^ 2 ∂(iidLaw D T) ≤
      8 * (4 * (G ^ 2 / lam ^ 2)) / (T : ℝ) :=
    avg_bound hW hclosed hzero hlam D hg hint hmoment hwstar hsc hR T T hT le_rfl
  have hm : ∫ S, (F (sgdStrongAverage lam W g S) - F wstar) ∂(iidLaw D T) ≤
      ∫ S, μ / 2 * ‖sgdStrongAverage lam W g S - wstar‖ ^ 2 ∂(iidLaw D T) :=
    integral_mono (hFint.sub (integrable_const _)) (hsqA.const_mul _) hFhi
  rw [integral_sub hFint (integrable_const _), integral_const, integral_const_mul] at hm
  simp only [probReal_univ, one_smul] at hm
  have hb' := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ μ / 2)
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : μ / 2 * (8 * (4 * (G ^ 2 / lam ^ 2)) / (T : ℝ)) = 16 * μ * G ^ 2 / (lam ^ 2 * T) := by
    field_simp; ring
  linarith

end Main

end SGD2

open MeasureTheory UnderstandingML OptimalSGD.Smooth in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {μ : ℝ} (hμ : 0 ≤ μ) (hsmooth : IsSmoothWrt W F μ wstar)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun S : Fin T → Z => F (sgdStrongAverage lam W g S)) (iidLaw D T) ∧
      (∫ S : Fin T → Z, F (sgdStrongAverage lam W g S) ∂(iidLaw D T)) - F wstar ≤
        16 * μ * G ^ 2 / (lam ^ 2 * T) := by
  exact SGD2.main W hW hclosed hzero F hlam hF D g hg horacle G hmoment wstar hwstar hmin hμ
    hsmooth T hT
