-- Prove2me | solution 1 for Viterbo.cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T15:04:21.460628+00:00
-- url     : https://prove2.me/submissions/aa13eb20-e286-4fec-b81a-a92e4e4355e7

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
section
/-!
Blueprint, Part M: elementary properties of `cEHZ` on convex domains, and monotonicity under
inclusion from Clarke's dual action principle in length form
(`Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`).
-/

open MeasureTheory Set OAI.SymmetricPolar
open scoped ENNReal Pointwise

namespace Viterbo.CM

variable {n : ℕ}

/-- The `K`-length `∫₀¹ h_K(-J ż)` of a loop. -/
noncomputable def ell (K : Set (Phase n)) (z : ℝ → Phase n) : ℝ :=
  ∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)

/-- Absolutely continuous (as in `IsGeneralizedClosedCharacteristic`). -/
def IsAC (z : ℝ → Phase n) : Prop :=
  ∃ v : ℝ → Phase n, LocallyIntegrable v volume ∧ ∀ a b, z b - z a = ∫ s in a..b, v s

/-! ## Helpers -/

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

lemma pI_sub_left (x y w : Phase n) :
    phaseInner (x - y) w = phaseInner x w - phaseInner y w := by
  simp [phaseInner, inner_sub_left]; ring

lemma pI_sub_right (w x y : Phase n) :
    phaseInner w (x - y) = phaseInner w x - phaseInner w y := by
  simp [phaseInner, inner_sub_right]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_zero_right (x : Phase n) : phaseInner x 0 = 0 := by simp [phaseInner]

lemma pI_self (z : Phase n) : phaseInner z z = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp [phaseInner]

lemma norm_sq_le_pI (u : Phase n) : ‖u‖ ^ 2 ≤ phaseInner u u := by
  rw [pI_self, Prod.norm_def]
  rcases max_cases ‖u.1‖ ‖u.2‖ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg ‖u.1‖, sq_nonneg ‖u.2‖]

lemma J_sub (x y : Phase n) : J (x - y) = J x - J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_neg (x : Phase n) : J (-x) = -J x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_J (x : Phase n) : J (J x) = -x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_eq_zero {z : Phase n} (h : J z = 0) : z = 0 := by
  simp only [J, Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

lemma norm_negJ (x : Phase n) : ‖-J x‖ = ‖x‖ := by
  rw [norm_neg]; simp [J, Prod.norm_def, max_comm]

lemma continuous_J : Continuous (J : Phase n → Phase n) := by
  show Continuous fun z : Phase n => ((-z.2, z.1) : Phase n)
  fun_prop

lemma abs_pI_le (x y : Phase n) : |phaseInner x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold phaseInner
  have h1 := abs_real_inner_le_norm x.1 y.1
  have h2 := abs_real_inner_le_norm x.2 y.2
  have a1 := norm_fst_le x
  have a2 := norm_snd_le x
  have b1 := norm_fst_le y
  have b2 := norm_snd_le y
  calc |inner ℝ x.1 y.1 + inner ℝ x.2 y.2| ≤ |inner ℝ x.1 y.1| + |inner ℝ x.2 y.2| := abs_add_le _ _
    _ ≤ ‖x.1‖ * ‖y.1‖ + ‖x.2‖ * ‖y.2‖ := add_le_add h1 h2
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- `phaseInner · w` as a continuous linear functional. -/
noncomputable def pIL (w : Phase n) : Phase n →L[ℝ] ℝ :=
  (innerSL ℝ w.1).comp (ContinuousLinearMap.fst ℝ (Position n) (Position n)) +
    (innerSL ℝ w.2).comp (ContinuousLinearMap.snd ℝ (Position n) (Position n))

lemma pIL_apply (w z : Phase n) : pIL w z = phaseInner z w := by
  simp [pIL, phaseInner, real_inner_comm]

lemma continuous_pI : Continuous (fun p : Phase n × Phase n => phaseInner p.1 p.2) := by
  unfold phaseInner; fun_prop

/-! ### Absolutely continuous loops -/

lemma ii_of_li {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable v volume a b :=
  (hv.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

lemma eq_prim {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
  funext x; rw [← hf 0 x]; abel

lemma cont_of_ac {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : Continuous γ := by
  rw [eq_prim hf]
  exact continuous_const.add (intervalIntegral.continuous_primitive (ii_of_li hv) 0)

lemma hasDeriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, HasDerivAt γ (v x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hv] with x hx
  rw [eq_prim hf]
  simpa using (hx 0).const_add (γ 0)

lemma deriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, deriv γ x = v x :=
  (hasDeriv_ae hv hf).mono fun _ hx => hx.deriv

lemma ii_pI {w v : ℝ → Phase n} (hw : Continuous w) (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => phaseInner (w t) (v t)) volume a b := by
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hw.continuousOn
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => phaseInner (w t) (v t)) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * C)) ?_ ?_
    · have hm : AEStronglyMeasurable (fun t => (w t, v t)) (volume.restrict (uIcc a b)) :=
        hw.aestronglyMeasurable.prodMk hvi.aestronglyMeasurable
      have h4 := continuous_pI.comp_aestronglyMeasurable hm
      simpa only [Function.comp_def] using h4
    · refine (ae_restrict_iff' measurableSet_uIcc).2 (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      have hCt : 2 * ‖w t‖ ≤ 2 * C := by linarith [hC t ht]
      calc _ ≤ 2 * ‖w t‖ * ‖v t‖ := abs_pI_le _ _
        _ ≤ 2 * C * ‖v t‖ := mul_le_mul_of_nonneg_right hCt (norm_nonneg _)
  exact this.intervalIntegrable

lemma integral_pI_const {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (c : Phase n)
    (a b : ℝ) : ∫ t in a..b, phaseInner c (v t) = phaseInner c (∫ t in a..b, v t) := by
  have h : ∀ x, phaseInner c x = pIL c x := fun x => by rw [pIL_apply, pI_comm]
  simp only [h]
  exact (pIL c).intervalIntegral_comp_comm (ii_of_li hv a b)

lemma action_eq {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    action γ = 1 / 2 * ∫ t in (0 : ℝ)..1, phaseInner (J (γ t)) (v t) := by
  unfold action; congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]

/-! ### Support functions -/

/-- The support function `h_K(w)`. -/
noncomputable def supp (K : Set (Phase n)) (w : Phase n) : ℝ :=
  sSup ((fun x => phaseInner x w) '' K)

lemma bdd_supp {S : Set (Phase n)} (hS : Bornology.IsBounded S) (u : Phase n) :
    BddAbove ((fun y => phaseInner y u) '' S) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨2 * R * ‖u‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  calc phaseInner y u ≤ |phaseInner y u| := le_abs_self _
    _ ≤ 2 * ‖y‖ * ‖u‖ := abs_pI_le _ _
    _ ≤ 2 * R * ‖u‖ := by gcongr; exact hR y hy

lemma supp_eq {S : Set (Phase n)} (hS : Bornology.IsBounded S) {x u : Phase n}
    (hx : x ∈ closure S) (hu : u ∈ normalCone phaseInner S x) :
    supp S u = phaseInner x u := by
  have hne : S.Nonempty := closure_nonempty_iff.1 ⟨x, hx⟩
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have := hu y hy
    rw [pI_sub_right, pI_comm u y, pI_comm u x] at this
    linarith
  · have hsub : S ⊆ {y | phaseInner y u ≤ supp S u} :=
      fun y hy => le_csSup (bdd_supp hS u) (mem_image_of_mem _ hy)
    have hcl : IsClosed {y | phaseInner y u ≤ supp S u} :=
      isClosed_le (continuous_pI.comp (continuous_id.prodMk continuous_const)) continuous_const
    exact hcl.closure_subset_iff.2 hsub hx

lemma supp_le_add {K : Set (Phase n)} (hK : Bornology.IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (w w' : Phase n) :
    supp K w ≤ supp K w' + 2 * R * ‖w - w'‖ := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : phaseInner x w' ≤ supp K w' := le_csSup (bdd_supp hK w') (mem_image_of_mem _ hx)
  have h2 : phaseInner x (w - w') ≤ 2 * R * ‖w - w'‖ :=
    (le_abs_self _).trans ((abs_pI_le _ _).trans (by gcongr; exact hR x hx))
  rw [pI_sub_right] at h2
  simp only
  linarith

lemma supp_zero {K : Set (Phase n)} (hne : K.Nonempty) : supp K 0 = 0 := by
  unfold supp
  simp only [pI_zero_right]
  rw [hne.image_const, csSup_singleton]

lemma ii_supp {K : Set (Phase n)} (hK : IsConvexDomain K) {v : ℝ → Phase n}
    (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => supp K (-J (v t))) volume a b := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨k0, hk0⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hK.1 ⟨k0, hk0⟩ hR x y
  have hbd : ∀ w, |supp K w| ≤ 2 * R * ‖w‖ := fun w => by
    have h1 := supp_le_add hK.1 ⟨k0, hk0⟩ hR w 0
    have h2 := supp_le_add hK.1 ⟨k0, hk0⟩ hR 0 w
    rw [supp_zero ⟨k0, hk0⟩, sub_zero] at h1
    rw [supp_zero ⟨k0, hk0⟩, zero_sub, norm_neg] at h2
    rw [abs_le]; constructor <;> linarith
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => supp K (-J (v t))) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * R)) ?_ ?_
    · exact (hlip.continuous.comp continuous_J.neg).comp_aestronglyMeasurable
        hvi.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      calc _ ≤ 2 * R * ‖-J (v t)‖ := hbd _
        _ = 2 * R * ‖v t‖ := by rw [norm_negJ]
  exact this.intervalIntegrable

lemma ell_eq {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (K : Set (Phase n)) :
    ell K z = ∫ t in (0 : ℝ)..1, supp K (-J (v t)) := by
  unfold ell
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]; rfl

/-! ### Translation -/

/-! ### Scaling -/

/-! ### Positivity of the action -/

lemma cone_lower {S : Set (Phase n)} {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ S) {y u : Phase n} (hu : u ∈ normalCone phaseInner S y) :
    r / 2 * ‖u‖ ≤ phaseInner (y - x0) u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [pI_zero_right]
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : x0 + s • u ∈ S := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, hsu]
    linarith)
  have h1 := hu _ hz
  have h2 := norm_sq_le_pI u
  have e : phaseInner u (x0 + s • u - y) = s * phaseInner u u - phaseInner (y - x0) u := by
    rw [show x0 + s • u - y = s • u - (y - x0) by abel, pI_sub_right, pI_smul_right,
      pI_comm u (y - x0)]
  rw [e] at h1
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma isAC_of_char {S : Set (Phase n)} {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) : IsAC γ := by
  obtain ⟨-, -, v, hv, hf, -⟩ := hγ
  exact ⟨v, hv, hf⟩

lemma ell_char {S : Set (Phase n)} (hS : IsConvexDomain S) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) : ell S γ = 2 * action γ := by
  obtain ⟨hper, hfr, v, hv, hf, hae⟩ := hγ
  rw [action_eq hv hf, ell_eq hv hf,
    show ∀ x : ℝ, 2 * (1 / 2 * x) = x from fun x => by ring]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with t ⟨u, hu, hvu⟩ _
  rw [← hvu, J_J, neg_neg, supp_eq hS.1 (frontier_subset_closure (hfr t)) hu, pI_J_J]

lemma action_pos_of_char {S : Set (Phase n)} (hS : IsConvexDomain S) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) (hnc : ∃ s t, γ s ≠ γ t) : 0 < action γ := by
  obtain ⟨hper, hfr, v, hv, hf, hae⟩ := hγ
  obtain ⟨x0, hx0⟩ := hS.2.2
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
  have hγc := cont_of_ac hv hf
  set f : ℝ → ℝ := fun t => phaseInner (J (γ t - x0)) (v t) with hfdef
  have hfi : IntervalIntegrable f volume 0 1 :=
    ii_pI (continuous_J.comp (hγc.sub continuous_const)) hv 0 1
  have h2A : 2 * action γ = ∫ t in (0 : ℝ)..1, f t := by
    rw [action_eq hv hf]
    have e : ∀ t, f t = phaseInner (J (γ t)) (v t) - phaseInner (J x0) (v t) := fun t => by
      simp only [f, J_sub, pI_sub_left]
    simp only [e]
    rw [intervalIntegral.integral_sub (ii_pI (w := fun t => J (γ t)) (continuous_J.comp hγc) hv 0 1)
      (ii_pI (w := fun _ => J x0) continuous_const hv 0 1), integral_pI_const hv, ← hf 0 1,
      show γ 1 = γ 0 by simpa using hper 0, sub_self, pI_zero_right]
    ring
  have hpos : ∀ᵐ t, r / 2 * ‖-J (v t)‖ ≤ f t := by
    filter_upwards [hae] with t ⟨u, hu, hvu⟩
    have := cone_lower hr hball hu
    simp only [f]
    rw [← hvu, J_J, neg_neg, pI_J_J]
    exact this
  have hnn : ∀ᵐ t, 0 ≤ f t := hpos.mono fun t ht => le_trans (by positivity) ht
  by_contra hA
  push Not at hA
  have hint0 : ∫ t in (0 : ℝ)..1, f t = 0 := by
    have := intervalIntegral.integral_nonneg_of_ae zero_le_one hnn
    linarith
  have hf0 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hnn) hfi).1
    hint0
  have hv0 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1 ∪ Ioc 1 0)), v t = 0 := by
    filter_upwards [hf0, ae_restrict_of_ae hpos] with t h1 h2
    have h3 : r / 2 * ‖-J (v t)‖ ≤ 0 := by simpa [h1] using h2
    have h4 : ‖-J (v t)‖ ≤ 0 := by
      by_contra h5; push Not at h5
      have : 0 < r / 2 * ‖-J (v t)‖ := by positivity
      linarith
    have h6 : -J (v t) = 0 := norm_le_zero_iff.1 h4
    exact J_eq_zero (neg_eq_zero.1 h6)
  have hv0' := (ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioc)).1 hv0
  have hconst : ∀ s, γ s = γ 0 := by
    intro s
    have hfs := Int.fract_nonneg s
    have hfs1 := Int.fract_lt_one s
    have hper' : γ (Int.fract s) = γ s := by
      rw [← Int.self_sub_floor]
      simpa using hper.sub_int_mul_eq (x := s) ⌊s⌋
    rw [← hper']
    have := hf 0 (Int.fract s)
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : Phase n)) ?_,
      intervalIntegral.integral_zero] at this
    · exact sub_eq_zero.1 this
    · filter_upwards [hv0'] with t ht ht'
      rw [Set.uIoc_of_le hfs] at ht'
      exact ht (Or.inl ⟨ht'.1, ht'.2.trans hfs1.le⟩)
  obtain ⟨s, t, hst⟩ := hnc
  exact hst (by rw [hconst s, hconst t])

lemma ell_nonneg {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n}
    (hz : Function.Periodic z 1) (hac : IsAC z) : 0 ≤ ell K z := by
  obtain ⟨v, hv, hf⟩ := hac
  rw [ell_eq hv hf]
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hlow : ∀ t, phaseInner (J k0) (v t) ≤ supp K (-J (v t)) := fun t => by
    have := le_csSup (bdd_supp hK.1 (-J (v t))) (mem_image_of_mem _ hk0)
    rw [show phaseInner k0 (-J (v t)) = phaseInner (J k0) (v t) by
      rw [← pI_J_J, J_neg, J_J, neg_neg]] at this
    exact this
  have h0 : ∫ t in (0 : ℝ)..1, phaseInner (J k0) (v t) = 0 := by
    rw [integral_pI_const hv, ← hf 0 1, show z 1 = z 0 by simpa using hz 0, sub_self,
      pI_zero_right]
  have hm := intervalIntegral.integral_mono_on zero_le_one
    (ii_pI (w := fun _ => J k0) continuous_const hv 0 1) (ii_supp hK hv 0 1) (fun t _ => hlow t)
  linarith

/-- From Clarke's principle: the minimal action is attained, and positive. -/
theorem exists_char_cEHZ_eq (hn : 1 ≤ n) {S : Set (Phase n)} (hS : IsConvexDomain S) :
    ∃ γ : ℝ → Phase n, IsGeneralizedClosedCharacteristic S γ ∧ (∃ s t, γ s ≠ γ t) ∧
      0 < action γ ∧ cEHZ S = ENNReal.ofReal (action γ) ∧
      ∀ z : ℝ → Phase n, Function.Periodic z 1 → IsAC z → 0 < action z →
        4 * action γ * action z ≤ ell S z ^ 2 := by
  obtain ⟨γ, hγ, hnc, hkey⟩ :=
    exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq n hn S hS
  have hA := action_pos_of_char hS hγ hnc
  refine ⟨γ, hγ, hnc, hA, le_antisymm ?_ ?_, fun z hz hac hpos => hkey z hz hac hpos⟩
  · refine (iInf₂_le γ ⟨hγ, hnc⟩).trans ?_
    rw [abs_of_pos hA]
  · refine le_iInf₂ fun γ' hγ' => ?_
    have hA' := action_pos_of_char hS hγ'.1 hγ'.2
    rw [abs_of_pos hA']
    apply ENNReal.ofReal_le_ofReal
    have h1 : 4 * action γ * action γ' ≤ ell S γ' ^ 2 :=
      hkey γ' hγ'.1.1 (isAC_of_char hγ'.1) hA'
    rw [ell_char hS hγ'.1] at h1
    nlinarith

end Viterbo.CM
end

section
/-!
# HKO Theorem 2.2, part B: a closed billiard lifts to a generalized closed characteristic

A closed `T`-billiard trajectory `q` in `K` (with bounce points `p` on `∂T`) gives a piecewise affine
loop on `∂(K × T)` with `2m` legs, traversed backwards: alternately `p` moves from `p_j` to `p_{j-1}`
with `q = q_j` fixed, and `q` moves from `q_j` to `q_{j-1}` with `p = p_{j-1}` fixed.  Its action is
`∑ ⟨p_j, q_{j+1} - q_j⟩ = ∑ h_T(q_{j+1} - q_j)`, the `T°`-length of `q`.
-/

namespace Viterbo.Thm22.PartB

open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise

/-! ## Piecewise affine interpolation through `v : ℤ → E` -/

section PL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The piecewise affine function with `pl v k = v k` at the integers. -/
noncomputable def pl (v : ℤ → E) (s : ℝ) : E :=
  v ⌊s⌋ + Int.fract s • (v (⌊s⌋ + 1) - v ⌊s⌋)

lemma pl_eqOn (v : ℤ → E) (k : ℤ) :
    EqOn (pl v) (fun s => v k + (s - k) • (v (k + 1) - v k)) (Icc (k : ℝ) (k + 1)) := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with h | h
  · have e : s = ((k + 1 : ℤ) : ℝ) := by rw [h]; push_cast; ring
    rw [e]
    simp only [pl, Int.floor_intCast, Int.fract_intCast, zero_smul, add_zero]
    push_cast
    simp
  · have hf : ⌊s⌋ = k := Int.floor_eq_iff.2 ⟨hs.1, h⟩
    simp only [pl, ← Int.self_sub_floor, hf]

lemma pl_affine_cont (v : ℤ → E) (k : ℤ) :
    Continuous (fun s : ℝ => v k + (s - k) • (v (k + 1) - v k)) := by fun_prop

lemma pl_cont (v : ℤ → E) : Continuous (pl v) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · have hk1 : ((⌈s⌉ - 1 : ℤ) : ℝ) < s := by
      have := Int.ceil_lt_add_one s; push_cast; linarith
    have hk2 : s ≤ ((⌈s⌉ - 1 : ℤ) : ℝ) + 1 := by
      have := Int.le_ceil s; push_cast; linarith
    have hmem : Ioc ((⌈s⌉ - 1 : ℤ) : ℝ) (((⌈s⌉ - 1 : ℤ) : ℝ) + 1) ∈ 𝓝[≤] s :=
      Ioc_mem_nhdsLE_of_mem ⟨hk1, hk2⟩
    refine ((pl_affine_cont v (⌈s⌉ - 1)).continuousWithinAt).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hmem] with x hx using pl_eqOn v _ ⟨hx.1.le, hx.2⟩
    · exact pl_eqOn v _ ⟨hk1.le, hk2⟩
  · have hk1 : ((⌊s⌋ : ℤ) : ℝ) ≤ s := Int.floor_le s
    have hk2 : s < ((⌊s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one s
    have hmem : Ico ((⌊s⌋ : ℤ) : ℝ) (((⌊s⌋ : ℤ) : ℝ) + 1) ∈ 𝓝[≥] s :=
      Ico_mem_nhdsGE_of_mem ⟨hk1, hk2⟩
    refine ((pl_affine_cont v ⌊s⌋).continuousWithinAt).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hmem] with x hx using pl_eqOn v _ ⟨hx.1, hx.2.le⟩
    · exact pl_eqOn v _ ⟨hk1, hk2.le⟩

lemma pl_hasDerivAt (v : ℤ → E) {s : ℝ} (hs : Int.fract s ≠ 0) :
    HasDerivAt (pl v) (v (⌊s⌋ + 1) - v ⌊s⌋) s := by
  have h1 : ((⌊s⌋ : ℤ) : ℝ) < s := by
    refine lt_of_le_of_ne (Int.floor_le s) (fun h => hs ?_)
    rw [← h, Int.fract_intCast]
  have h2 : s < ((⌊s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one s
  obtain ⟨k, hk⟩ : ∃ k, ⌊s⌋ = k := ⟨_, rfl⟩
  rw [hk] at h1 h2 ⊢
  have hd : HasDerivAt (fun x : ℝ => v k + (x - k) • (v (k + 1) - v k)) (v (k + 1) - v k) s := by
    have := ((hasDerivAt_id s).sub_const (k : ℝ)).smul_const (v (k + 1) - v k)
    simpa using this.const_add (v k)
  exact hd.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds h1 h2] with x hx using pl_eqOn v k ⟨hx.1.le, hx.2.le⟩)

lemma pl_intCast (v : ℤ → E) (k : ℤ) : pl v (k : ℝ) = v k := by
  simp [pl]

lemma pl_add_int (v : ℤ → E) (P : ℤ) (hv : ∀ k, v (k + P) = v k) (s : ℝ) :
    pl v (s + P) = pl v s := by
  simp only [pl, Int.floor_add_intCast, Int.fract_add_intCast]
  rw [hv, show ⌊s⌋ + P + 1 = (⌊s⌋ + 1) + P by ring, hv]

end PL

/-! ## The vertices of the lifted loop -/

section Vertices

open Fin.CommRing

variable {n M : ℕ} [NeZero M]

/-- The `k`-th vertex of the loop: `(q_{-⌊k/2⌋}, p_{-⌊(k+1)/2⌋})`. -/
noncomputable def vtx (q p : Fin M → Position n) (k : ℤ) : Phase n :=
  (q (-((k / 2 : ℤ) : Fin M)), p (-(((k + 1) / 2 : ℤ) : Fin M)))

variable (q p : Fin M → Position n)

lemma vtx_even (i : ℤ) : vtx q p (2 * i) = (q (-(i : Fin M)), p (-(i : Fin M))) := by
  have h1 : 2 * i / 2 = i := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [vtx, h1, h2]

lemma vtx_odd (i : ℤ) :
    vtx q p (2 * i + 1) = (q (-(i : Fin M)), p (-(i : Fin M) - 1)) := by
  have h1 : (2 * i + 1) / 2 = i := by omega
  have h2 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
  simp only [vtx, h1, h2]
  congr 2
  push_cast; ring

lemma vtx_cases (k : ℤ) : ∃ j : Fin M,
    (vtx q p k = (q j, p j) ∧ vtx q p (k + 1) = (q j, p (j - 1))) ∨
    (vtx q p k = (q j, p (j - 1)) ∧ vtx q p (k + 1) = (q (j - 1), p (j - 1))) := by
  obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' k
  · exact ⟨-(i : Fin M), Or.inl ⟨vtx_even q p i, vtx_odd q p i⟩⟩
  · refine ⟨-(i : Fin M), Or.inr ⟨vtx_odd q p i, ?_⟩⟩
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, vtx_even]
    push_cast
    congr 2 <;> ring

lemma vtx_periodic (k : ℤ) : vtx q p (k + (2 * M : ℕ)) = vtx q p k := by
  have h1 : (k + ((2 * M : ℕ) : ℤ)) / 2 = k / 2 + (M : ℤ) := by push_cast; omega
  have h2 : (k + ((2 * M : ℕ) : ℤ) + 1) / 2 = (k + 1) / 2 + (M : ℤ) := by push_cast; omega
  have hM : (((M : ℕ) : ℤ) : Fin M) = 0 := by simp
  simp only [vtx, h1, h2, Int.cast_add, hM, add_zero]

lemma vtx_norm (k : ℤ) : ‖vtx q p k‖ ≤ ∑ j, ‖q j‖ + ∑ j, ‖p j‖ := by
  have hq : ∀ a, ‖q a‖ ≤ ∑ j, ‖q j‖ := fun a =>
    Finset.single_le_sum (f := fun j => ‖q j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hp : ∀ a, ‖p a‖ ≤ ∑ j, ‖p j‖ := fun a =>
    Finset.single_le_sum (f := fun j => ‖p j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h0 : 0 ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h0' : 0 ≤ ∑ j, ‖p j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [vtx, norm_prod_le_iff]
  exact ⟨(hq _).trans (by linarith), (hp _).trans (by linarith)⟩

end Vertices

/-! ## The loop -/

section Loop

open Fin.CommRing

variable {n M : ℕ} [NeZero M] {K T : Set (Position n)} {q p : Fin M → Position n}

/-- The billiard data, with indices in the ring `Fin M`. -/
structure Bil (K T : Set (Position n)) (q p : Fin M → Position n) : Prop where
  cK : Convex ℝ K
  cT : Convex ℝ T
  bT : Bornology.IsBounded T
  neT : T.Nonempty
  hq : ∀ j, q j ∈ frontier K
  hne : ∀ j, q (j + 1) ≠ q j
  hp : ∀ j, p j ∈ frontier T
  hd : ∀ j, q (j + 1) - q j ∈ normalConeE T (p j)
  he : ∀ j, p (j + 1) - p j ∈ -normalConeE K (q (j + 1))

/-- `2M` legs per period. -/
noncomputable abbrev NN (M : ℕ) : ℝ := ((2 * M : ℕ) : ℝ)

lemma NN_pos : 0 < NN M := by
  have := NeZero.pos M
  unfold NN; positivity

/-- The loop. -/
noncomputable def gam (q p : Fin M → Position n) (t : ℝ) : Phase n :=
  pl (vtx q p) (NN M * t)

/-- Its velocity. -/
noncomputable def vel (q p : Fin M → Position n) (t : ℝ) : Phase n :=
  NN M • (vtx q p (⌊NN M * t⌋ + 1) - vtx q p ⌊NN M * t⌋)

/-- The break points. -/
def Dset (M : ℕ) : Set ℝ := {t | Int.fract (NN M * t) = 0}

lemma Dset_countable : (Dset M).Countable := by
  refine (Set.countable_range (fun k : ℤ => (k : ℝ) / NN M)).mono ?_
  intro t ht
  refine ⟨⌊NN M * t⌋, ?_⟩
  have h := Int.floor_add_fract (NN M * t)
  rw [show Int.fract (NN M * t) = 0 from ht, add_zero] at h
  have := (NN_pos (M := M)).ne'
  simp only
  rw [h]; field_simp

lemma gam_cont (q p : Fin M → Position n) : Continuous (gam q p) :=
  (pl_cont _).comp (continuous_const.mul continuous_id)

lemma gam_periodic (q p : Fin M → Position n) : Function.Periodic (gam q p) 1 := by
  intro t
  have e : NN M * (t + 1) = NN M * t + (((2 * M : ℕ) : ℤ) : ℝ) := by
    unfold NN; push_cast; ring
  rw [gam, e, pl_add_int _ _ (vtx_periodic q p)]
  rfl

lemma gam_hasDerivAt (q p : Fin M → Position n) {t : ℝ} (ht : t ∉ Dset M) :
    HasDerivAt (gam q p) (vel q p t) t := by
  have h1 := pl_hasDerivAt (vtx q p) (s := NN M * t) ht
  have h2 : HasDerivAt (fun t : ℝ => NN M * t) (NN M) t := by
    simpa using (hasDerivAt_id t).const_mul (NN M)
  exact h1.scomp t h2

lemma gam_eq (q p : Fin M → Position n) (t : ℝ) :
    gam q p t = vtx q p ⌊NN M * t⌋ +
      Int.fract (NN M * t) • (vtx q p (⌊NN M * t⌋ + 1) - vtx q p ⌊NN M * t⌋) := rfl

lemma Bil.mem_frontier (H : Bil K T q p) (t : ℝ) : gam q p t ∈ frontier (K ×ˢ T) := by
  have hl : Int.fract (NN M * t) ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [frontier_prod_eq, gam_eq]
  obtain ⟨j, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := vtx_cases q p ⌊NN M * t⌋
  · right
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · simpa using H.hq j
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub]
      exact H.cT.closure.add_smul_sub_mem (frontier_subset_closure (H.hp j))
        (frontier_subset_closure (H.hp _)) hl
  · left
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub]
      exact H.cK.closure.add_smul_sub_mem (frontier_subset_closure (H.hq j))
        (frontier_subset_closure (H.hq _)) hl
    · simpa using H.hp (j - 1)

lemma normalConeE_smul {S : Set (Position n)} {x u : Position n} (hu : u ∈ normalConeE S x)
    {c : ℝ} (hc : 0 ≤ c) : c • u ∈ normalConeE S x := by
  intro y hy
  have := hu y hy
  simp only at this ⊢
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hc this

lemma mem_J_q {x : Phase n} {u : Position n} (hu : u ∈ normalConeE K x.1) :
    ((0 : Position n), u) ∈ J '' normalCone phaseInner (K ×ˢ T) x := by
  refine ⟨(u, 0), fun y hy => ?_, by simp [J]⟩
  have := hu y.1 hy.1
  simpa [phaseInner] using this

lemma mem_J_p {x : Phase n} {w : Position n} (hw : w ∈ normalConeE T x.2) :
    (-w, (0 : Position n)) ∈ J '' normalCone phaseInner (K ×ˢ T) x := by
  refine ⟨(0, w), fun y hy => ?_, by simp [J]⟩
  have := hw y.2 hy.2
  simpa [phaseInner] using this

lemma Bil.normal (H : Bil K T q p) (t : ℝ) :
    vel q p t ∈ J '' normalCone phaseInner (K ×ˢ T) (gam q p t) := by
  have hN : (0 : ℝ) ≤ NN M := NN_pos.le
  obtain ⟨j, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := vtx_cases q p ⌊NN M * t⌋
  · have hv : vel q p t = (0, NN M • (p (j - 1) - p j)) := by
      rw [vel, e1, e2]; ext <;> simp
    have hx : (gam q p t).1 = q j := by rw [gam_eq, e1, e2]; simp
    rw [hv]
    apply mem_J_q
    rw [hx]
    apply normalConeE_smul _ hN
    have := H.he (j - 1)
    rw [sub_add_cancel] at this
    have := Set.mem_neg.1 this
    simpa using this
  · have hv : vel q p t = (-(NN M • (q j - q (j - 1))), 0) := by
      rw [vel, e1, e2]; ext <;> simp; ring
    have hx : (gam q p t).2 = p (j - 1) := by rw [gam_eq, e1, e2]; simp
    rw [hv]
    apply mem_J_p
    rw [hx]
    apply normalConeE_smul _ hN
    have := H.hd (j - 1)
    rwa [sub_add_cancel] at this

lemma vel_loc (q p : Fin M → Position n) : LocallyIntegrable (vel q p) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  set R := ∑ j, ‖q j‖ + ∑ j, ‖p j‖
  have hmeas : Measurable (vel q p) := by
    have : vel q p = (fun k : ℤ => NN M • (vtx q p (k + 1) - vtx q p k)) ∘
        (fun t => ⌊NN M * t⌋) := rfl
    rw [this]
    exact measurable_from_top.comp (Int.measurable_floor.comp (measurable_const.mul measurable_id))
  refine Measure.integrableOn_of_bounded (M := NN M * (R + R)) hk.measure_lt_top.ne
    hmeas.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [vel, norm_smul, Real.norm_eq_abs, abs_of_pos NN_pos]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add (vtx_norm q p _) (vtx_norm q p _))

lemma Bil.gcc (H : Bil K T q p) : IsGeneralizedClosedCharacteristic (K ×ˢ T) (gam q p) := by
  refine ⟨gam_periodic q p, H.mem_frontier, vel q p, vel_loc q p, ?_, ae_of_all _ H.normal⟩
  intro a b
  rw [integral_eq_of_hasDerivAt_off_countable _ _ Dset_countable (gam_cont q p).continuousOn
    (fun t ht => gam_hasDerivAt q p ht.2)
    ((vel_loc q p).integrableOn_isCompact isCompact_uIcc).intervalIntegrable]

lemma Bil.nonconst (H : Bil K T q p) : ∃ s t, gam q p s ≠ gam q p t := by
  refine ⟨1 / NN M, 2 / NN M, fun h => ?_⟩
  have hN := (NN_pos (M := M)).ne'
  have e1 : NN M * (1 / NN M) = ((2 * 0 + 1 : ℤ) : ℝ) := by field_simp; norm_num
  have e2 : NN M * (2 / NN M) = ((2 * 1 : ℤ) : ℝ) := by field_simp; norm_num
  rw [gam, gam, e1, e2, pl_intCast, pl_intCast, vtx_odd, vtx_even] at h
  have h1 := congrArg Prod.fst h
  simp only at h1
  apply H.hne (-1)
  rw [neg_add_cancel]
  simpa using h1

end Loop

/-! ## The action -/

section Action

open Fin.CommRing

variable {n M : ℕ} [NeZero M] {K T : Set (Position n)} {q p : Fin M → Position n}

lemma phaseInner_J_affine (a d : Phase n) (l c : ℝ) :
    phaseInner (J (a + l • d)) (c • d) = c * phaseInner (J a) d := by
  simp only [phaseInner, J, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    inner_add_left, inner_neg_left, inner_smul_left, inner_smul_right, neg_add, conj_trivial]
  rw [real_inner_comm d.1 d.2]
  ring

/-- The contribution of the `k`-th leg. -/
noncomputable def om (q p : Fin M → Position n) (k : ℤ) : ℝ :=
  phaseInner (J (vtx q p k)) (vtx q p (k + 1) - vtx q p k)

lemma integrand_ae (q p : Fin M → Position n) {t : ℝ} (ht : t ∉ Dset M) :
    phaseInner (J (gam q p t)) (deriv (gam q p) t) = NN M * om q p ⌊NN M * t⌋ := by
  rw [(gam_hasDerivAt q p ht).deriv, gam_eq, vel]
  exact phaseInner_J_affine _ _ _ _

lemma piece (q p : Fin M → Position n) (k : ℕ) :
    EqOn (fun _ => NN M * om q p k) (fun t => NN M * om q p ⌊NN M * t⌋)
      (uIoo ((k : ℝ) / NN M) (((k + 1 : ℕ) : ℝ) / NN M)) := by
  have hN := NN_pos (M := M)
  have hle : (k : ℝ) / NN M ≤ ((k + 1 : ℕ) : ℝ) / NN M := by gcongr; exact_mod_cast Nat.le_succ k
  intro t ht
  rw [uIoo_of_le hle] at ht
  obtain ⟨h1, h2⟩ := ht
  rw [div_lt_iff₀ hN, mul_comm] at h1
  rw [lt_div_iff₀ hN, mul_comm] at h2
  have : ⌊NN M * t⌋ = (k : ℤ) :=
    Int.floor_eq_iff.2 ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  simp only [this]

lemma integral_steps (q p : Fin M → Position n) (L : ℕ) :
    IntervalIntegrable (fun t => NN M * om q p ⌊NN M * t⌋) volume 0 ((L : ℝ) / NN M) ∧
    ∫ t in (0 : ℝ)..((L : ℝ) / NN M), NN M * om q p ⌊NN M * t⌋ =
      ∑ k ∈ Finset.range L, om q p k := by
  have hN := NN_pos (M := M)
  induction L with
  | zero => simp
  | succ L ih =>
    have hi : IntervalIntegrable (fun t => NN M * om q p ⌊NN M * t⌋) volume
        ((L : ℝ) / NN M) (((L + 1 : ℕ) : ℝ) / NN M) :=
      intervalIntegrable_const.congr_uIoo (piece q p L)
    refine ⟨ih.1.trans hi, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hi, ih.2, Finset.sum_range_succ,
      ← intervalIntegral.integral_congr_uIoo (piece q p L), intervalIntegral.integral_const,
      smul_eq_mul]
    congr 1
    have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
    push_cast
    field_simp
    ring

lemma integral_loop (q p : Fin M → Position n) :
    ∫ t in (0 : ℝ)..1, phaseInner (J (gam q p t)) (deriv (gam q p) t) =
      ∑ k ∈ Finset.range (2 * M), om q p k := by
  have h1 : ((2 * M : ℕ) : ℝ) / NN M = 1 := div_self (NN_pos (M := M)).ne'
  rw [← (integral_steps q p (2 * M)).2, h1]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Dset_countable (M := M)).ae_notMem volume] with t ht _
  exact integrand_ae q p ht

lemma sum_range_two_mul (f : ℕ → ℝ) (L : ℕ) :
    ∑ k ∈ Finset.range (2 * L), f k = ∑ i ∈ Finset.range L, (f (2 * i) + f (2 * i + 1)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 2 * (L + 1) = 2 * L + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The two legs at `q_j`. -/
noncomputable def G (q p : Fin M → Position n) (j : Fin M) : ℝ :=
  inner ℝ (q j) (p (j - 1) - p j) - inner ℝ (p (j - 1)) (q (j - 1) - q j)

lemma vtx_odd_succ (i : ℤ) :
    vtx q p (2 * i + 1 + 1) = (q (-(i : Fin M) - 1), p (-(i : Fin M) - 1)) := by
  rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, vtx_even]
  push_cast
  congr 2 <;> ring

lemma om_pair (i : ℤ) : om q p (2 * i) + om q p (2 * i + 1) = G q p (-(i : Fin M)) := by
  simp only [om, vtx_even, vtx_odd, vtx_odd_succ, G, phaseInner, J, Prod.fst_sub, Prod.snd_sub,
    sub_self, inner_zero_right, inner_neg_left]
  ring

lemma sum_om (q p : Fin M → Position n) :
    ∑ k ∈ Finset.range (2 * M), om q p k = 2 * ∑ j, inner ℝ (p j) (q (j + 1) - q j) := by
  rw [sum_range_two_mul (fun k => om q p k)]
  have h1 : ∑ i ∈ Finset.range M, (om q p ((2 * i : ℕ) : ℤ) + om q p ((2 * i + 1 : ℕ) : ℤ)) =
      ∑ j : Fin M, G q p (-j) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [om_pair]
    simp
  rw [h1, Fintype.sum_equiv (Equiv.neg (Fin M)) (fun j => G q p (-j)) (G q p) (fun j => rfl)]
  have h2 : ∑ j : Fin M, G q p j = ∑ j : Fin M, G q p (j + 1) :=
    (Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => rfl)).symm
  have h3 : ∑ j : Fin M, inner ℝ (q (j + 1)) (p (j + 1)) = ∑ j : Fin M, inner ℝ (q j) (p j) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => rfl)
  rw [h2]
  simp only [G, add_sub_cancel_right, inner_sub_right, Finset.sum_sub_distrib] at h3 ⊢
  rw [h3]
  have h4 : ∀ j : Fin M, inner ℝ (q (j + 1)) (p j) = inner ℝ (p j) (q (j + 1)) :=
    fun j => real_inner_comm _ _
  have h5 : ∀ j : Fin M, inner ℝ (p j) (q j) = inner ℝ (q j) (p j) :=
    fun j => real_inner_comm _ _
  simp only [h4, h5]
  ring

end Action

/-! ## The main statement -/

section Main

open Fin.CommRing

variable {n : ℕ}

lemma bddAbove_inner {T : Set (Position n)} (hT : IsConvexDomain T) (d : Position n) :
    BddAbove ((fun x => inner ℝ x d) '' T) := by
  obtain ⟨R, hR⟩ := hT.1.subset_closedBall 0
  refine ⟨R * ‖d‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm _ _).trans (by gcongr)

lemma supp_eq {T : Set (Position n)} (hT : IsConvexDomain T) {x d : Position n}
    (hx : x ∈ closure T) (hd : d ∈ normalConeE T x) : supportFunction T d = inner ℝ x d := by
  have hne : T.Nonempty := hT.2.2.mono interior_subset
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨y, hy, rfl⟩
    have := hd y hy
    simp only at this
    rw [inner_sub_right] at this
    show inner ℝ y d ≤ inner ℝ x d
    rw [real_inner_comm d y, real_inner_comm d x]
    linarith
  · have : closure T ⊆ {y | inner ℝ y d ≤ supportFunction T d} :=
      closure_minimal (fun y hy => le_csSup (bddAbove_inner hT d) ⟨y, hy, rfl⟩)
        (isClosed_le (by fun_prop) continuous_const)
    exact this hx

lemma polygonLength_nonneg' {T : Set (Position n)} (hT : IsConvexDomain T)
    (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (q : Fin m → Position n) :
    0 ≤ polygonLength T q := by
  unfold polygonLength
  refine Finset.sum_nonneg fun i _ => ?_
  unfold supportFunction
  exact le_csSup_of_le (bddAbove_inner hT _) ⟨0, interior_subset h0, rfl⟩ (by simp)

theorem cEHZ_le_billiard {n : ℕ} {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (q : Fin m → Position n)
    (hq : IsClosedBilliard K T q) :
    cEHZ (K ×ˢ T) ≤ ENNReal.ofReal (polygonLength T q) := by
  obtain ⟨hm, hqK, hqne, p, hp⟩ := hq
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have H : Bil K T q p :=
    { cK := hK.2.1
      cT := hT.2.1
      bT := hT.1
      neT := hT.2.2.mono interior_subset
      hq := hqK
      hne := fun j => by simpa [finRotate_apply] using hqne j
      hp := fun j => (hp j).1
      hd := fun j => by simpa [finRotate_apply] using (hp j).2.1
      he := fun j => by simpa [finRotate_apply] using (hp j).2.2 }
  have hact : action (gam q p) = polygonLength T q := by
    rw [action, integral_loop, sum_om, polygonLength]
    simp only [finRotate_apply]
    rw [Finset.sum_congr rfl
      (fun j _ => supp_eq hT (frontier_subset_closure (hp j).1) (H.hd j))]
    ring
  refine (iInf₂_le (gam q p) ⟨H.gcc, H.nonconst⟩).trans ?_
  rw [hact, abs_of_nonneg (polygonLength_nonneg' hT h0 q)]

end Main

end Viterbo.Thm22.PartB
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# Blueprint (q166): HKO Theorem 2.2 (Artstein-Avidan–Ostrover Thm 2.13, Rudolf Thm 1)

Route (all finite-dimensional except Part C):
* Part F: a polygon `q ∈ P(K)` has a separation certificate `u` (`∑ u = 0`, `u ≠ 0`,
  `∑ h_K(u_j) ≤ ∑ ⟨u_j, q_j⟩`, supporting hyperplane of the open convex set of translatable polygons
  at `q`), and conversely.
* Part A: `c_EHZ(K × T) ≤ ℓ_T(q)` for `q ∈ P(K)`: Clarke's principle applied to the PartB loop
  `gam q p` with `p_{j-1} - p_j = λ u_j`.
* Part H: Helly reduction to `≤ n + 1` vertices; a minimizer of `ℓ_T` over `P_{≤ n+1}(K)` with the least
  number of vertices exists.
* Part K: such a minimizer, translated, is a closed billiard (KKT by separation).
* Part C: every nonconstant generalized closed characteristic of `K × T` has action at least
  `inf_{P(K)} ℓ_T` (Riemann sums for `∫⟨Q, Ṗ⟩` and `∫⟨P, Q̇⟩`).
-/
lemma isConvexDomain_prod {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T) :
    IsConvexDomain (K ×ˢ T) := by
  refine ⟨hK.1.prod hT.1, hK.2.1.prod hT.2.1, ?_⟩
  rw [interior_prod_eq]
  exact hK.2.2.prod hT.2.2

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartF
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# HKO Theorem 2.2, part F: separation certificates for `P(K)`
-/
lemma bddAbove_inner {K : Set (Position n)} (hK : IsConvexDomain K) (d : Position n) :
    BddAbove ((fun x => inner ℝ x d) '' K) := by
  obtain ⟨R, hR⟩ := hK.1.subset_closedBall 0
  refine ⟨R * ‖d‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm _ _).trans (by gcongr)

lemma inner_le_supp {K : Set (Position n)} (hK : IsConvexDomain K) {x : Position n} (hx : x ∈ K)
    (u : Position n) : inner ℝ u x ≤ supportFunction K u := by
  rw [real_inner_comm]
  exact le_csSup (bddAbove_inner hK u) ⟨x, hx, rfl⟩

/-- An interior point is strictly below the support function in a nonzero direction. -/
lemma inner_lt_supp {K : Set (Position n)} (hK : IsConvexDomain K) {x : Position n}
    (hx : x ∈ interior K) {u : Position n} (hu : u ≠ 0) : inner ℝ u x < supportFunction K u := by
  have ht : Tendsto (fun δ : ℝ => x + δ • u) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun δ : ℝ => x + δ • u) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x + δ • u ∈ interior K ∧ 0 < δ :=
    ((ht.mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds hx)).and
      self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  have := inner_le_supp hK (interior_subset h1) u
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have : 0 < δ * ‖u‖ ^ 2 := by positivity
  linarith

lemma mem_add_singleton_iff {S : Set (Position n)} {x t : Position n} :
    x ∈ S + {t} ↔ x - t ∈ S := by
  rw [Set.add_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - t, h, by simp⟩

lemma notTranslatable_iff {K : Set (Position n)} {m : ℕ} {y : Fin m → Position n} :
    NotTranslatableIntoInterior K y ↔ ∀ t, ¬ ∀ j, y j - t ∈ interior K := by
  simp only [NotTranslatableIntoInterior, mem_add_singleton_iff]

/-- Points of `K` approximating the support function from the interior. -/
lemma exists_interior_gt {K : Set (Position n)} (hK : IsConvexDomain K) (u : Position n)
    {ε : ℝ} (hε : 0 < ε) : ∃ k ∈ interior K, supportFunction K u - ε < inner ℝ u k := by
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup (hne.image _) (show supportFunction K u - ε < supportFunction K u by
      linarith)
  have hxc : x ∈ closure (interior K) := by
    rw [hK.2.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2]
    exact subset_closure hx
  have hU : IsOpen {y : Position n | supportFunction K u - ε < inner ℝ y u} :=
    isOpen_lt continuous_const (by fun_prop)
  obtain ⟨k, hk1, hk2⟩ := mem_closure_iff.1 hxc _ hU hlt
  exact ⟨k, hk2, by rw [real_inner_comm]; exact hk1⟩

/-- The set of translatable polygons. -/
def Dset (K : Set (Position n)) (m : ℕ) : Set (Fin m → Position n) :=
  {x | ∃ t, ∀ j, x j - t ∈ interior K}

lemma Dset_open (K : Set (Position n)) (m : ℕ) : IsOpen (Dset K m) := by
  have : Dset K m = ⋃ t : Position n, ⋂ j : Fin m, (fun x : Fin m → Position n => x j - t) ⁻¹'
      interior K := by
    ext x; simp [Dset]
  rw [this]
  exact isOpen_iUnion fun t => isOpen_iInter_of_finite fun j =>
    isOpen_interior.preimage (by fun_prop)

lemma Dset_convex {K : Set (Position n)} (hK : IsConvexDomain K) (m : ℕ) :
    Convex ℝ (Dset K m) := by
  rintro x ⟨t, ht⟩ y ⟨s, hs⟩ a b ha hb hab
  refine ⟨a • t + b • s, fun j => ?_⟩
  have := hK.2.1.interior (ht j) (hs j) ha hb hab
  convert this using 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_sub]
  abel

theorem exists_cert {K : Set (Position n)} (hK : IsConvexDomain K) {m : ℕ}
    {q : Fin m → Position n} (hq : NotTranslatableIntoInterior K q) :
    ∃ u : Fin m → Position n, ∑ j, u j = 0 ∧ (∃ j, u j ≠ 0) ∧
      ∑ j, supportFunction K (u j) ≤ ∑ j, inner ℝ (u j) (q j) ∧
      ∀ y : Fin m → Position n, ∑ j, inner ℝ (u j) (q j) ≤ ∑ j, inner ℝ (u j) (y j) →
        NotTranslatableIntoInterior K y := by
  rw [notTranslatable_iff] at hq
  have hqD : q ∉ Dset K m := fun ⟨t, ht⟩ => hq t ht
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (Dset_convex hK m) (Dset_open K m) hqD
  set u : Fin m → Position n := fun j =>
    (InnerProductSpace.toDual ℝ (Position n)).symm (f.comp (ContinuousLinearMap.single ℝ (fun _ : Fin m => Position n) j))
    with hu_def
  have hfu : ∀ x : Fin m → Position n, f x = ∑ j, inner ℝ (u j) (x j) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu_def, InnerProductSpace.toDual_symm_apply]
    rfl
  obtain ⟨k0, hk0⟩ := hK.2.2
  have hx0 : ∀ t : Position n, (fun _ : Fin m => k0 + t) ∈ Dset K m :=
    fun t => ⟨t, fun j => by simpa using hk0⟩
  -- `∑ u = 0`
  have hsum : ∑ j, u j = 0 := by
    set S := ∑ j, u j with hS_def
    have key : ∀ t : Position n, f (fun _ => k0) + inner ℝ S t < f q := by
      intro t
      have := hf _ (hx0 t)
      rw [hfu] at this ⊢
      simp only [inner_add_right, Finset.sum_add_distrib] at this
      rwa [hS_def, sum_inner]
    by_contra hS
    have ha : 0 < inner ℝ S S := real_inner_self_pos.2 hS
    have := key (((f q - f (fun _ => k0)) / inner ℝ S S) • S)
    rw [real_inner_smul_right, div_mul_cancel₀ _ ha.ne'] at this
    linarith
  refine ⟨u, hsum, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := hf _ (hx0 0)
    simp only [hfu, h, inner_zero_left, Finset.sum_const_zero] at this
    exact lt_irrefl _ this
  · -- the support function bound
    have hm : ∀ ε > 0, ∑ j, supportFunction K (u j) ≤ f q + m * ε := by
      intro ε hε
      choose k hk hlt using fun j => exists_interior_gt hK (u j) hε
      have hkD : k ∈ Dset K m := ⟨0, fun j => by simpa using hk j⟩
      have h1 := hf _ hkD
      rw [hfu] at h1
      have h2 : ∑ j, (supportFunction K (u j) - ε) ≤ ∑ j, inner ℝ (u j) (k j) :=
        Finset.sum_le_sum fun j _ => (hlt j).le
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h2
      linarith
    rw [← hfu]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hm (ε / (m + 1)) (by positivity)
    have h3 : (m : ℝ) * (ε / (m + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · intro y hy
    rw [notTranslatable_iff]
    intro t ht
    have hyD : y ∈ Dset K m := ⟨t, ht⟩
    have := hf _ hyD
    rw [hfu, hfu] at this
    linarith

end Viterbo.Thm22.PartF
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part F: separation certificates for `P(K)` -/
alias exists_cert := Viterbo.Thm22.PartF.exists_cert

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartF
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem notTranslatable_of_cert {K : Set (Position n)} (hK : IsConvexDomain K) {m : ℕ}
    {u y : Fin m → Position n} (hsum : ∑ j, u j = 0) (hne : ∃ j, u j ≠ 0)
    (hle : ∑ j, supportFunction K (u j) ≤ ∑ j, inner ℝ (u j) (y j)) :
    NotTranslatableIntoInterior K y := by
  rw [notTranslatable_iff]
  intro t ht
  obtain ⟨j0, hj0⟩ := hne
  have e : ∑ j, inner ℝ (u j) (y j) = ∑ j, inner ℝ (u j) (y j - t) := by
    simp only [inner_sub_right, Finset.sum_sub_distrib]
    rw [← sum_inner, hsum, inner_zero_left, sub_zero]
  have hlt : ∑ j, inner ℝ (u j) (y j - t) < ∑ j, supportFunction K (u j) := by
    refine Finset.sum_lt_sum (fun j _ => inner_le_supp hK (interior_subset (ht j)) _)
      ⟨j0, Finset.mem_univ _, inner_lt_supp hK (ht j0) hj0⟩
  linarith

end Viterbo.Thm22.PartF
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias notTranslatable_of_cert := Viterbo.Thm22.PartF.notTranslatable_of_cert

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# HKO Theorem 2.2, part A: the Clarke upper bound `c_EHZ(K × T) ≤ ℓ_T(q)` for `q ∈ P(K)`

Take a certificate `u` for `q` (`exists_cert`), `p` with `p (j-1) - p j = λ u j`, and the PartB loop
`z = gam q p`: `A(z) = λ ∑ ⟨u j, q j⟩ ≥ λ ∑ h_K(u j)` and `ℓ_{K×T}(z) ≤ λ ∑ h_K(u j) + ℓ_T(q)`; with
`λ = ℓ_T(q) / ∑ h_K(u j)` Clarke's inequality `4 A(γ) A(z) ≤ ℓ(z)²` gives `A(γ) ≤ ℓ_T(q)`.
-/
/-! ## Support functions -/
lemma bddAbove_inner {K : Set (Position n)} (hK : IsConvexDomain K) (d : Position n) :
    BddAbove ((fun x => inner ℝ x d) '' K) := by
  obtain ⟨R, hR⟩ := hK.1.subset_closedBall 0
  refine ⟨R * ‖d‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm _ _).trans (by gcongr)

lemma inner_le_supp {K : Set (Position n)} (hK : IsConvexDomain K) {x : Position n} (hx : x ∈ K)
    (u : Position n) : inner ℝ u x ≤ supportFunction K u := by
  rw [real_inner_comm]
  exact le_csSup (bddAbove_inner hK u) ⟨x, hx, rfl⟩

lemma inner_lt_supp {K : Set (Position n)} (hK : IsConvexDomain K) {x : Position n}
    (hx : x ∈ interior K) {u : Position n} (hu : u ≠ 0) : inner ℝ u x < supportFunction K u := by
  have ht : Tendsto (fun δ : ℝ => x + δ • u) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun δ : ℝ => x + δ • u) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x + δ • u ∈ interior K ∧ 0 < δ :=
    ((ht.mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds hx)).and
      self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  have := inner_le_supp hK (interior_subset h1) u
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have : 0 < δ * ‖u‖ ^ 2 := by positivity
  linarith

lemma supp_zero' {K : Set (Position n)} (hK : IsConvexDomain K) : supportFunction K 0 = 0 := by
  unfold supportFunction
  simp only [inner_zero_right]
  rw [(hK.2.2.mono interior_subset).image_const, csSup_singleton]

lemma supp_smul_le {K : Set (Position n)} (hK : IsConvexDomain K) {c : ℝ} (hc : 0 ≤ c)
    (u : Position n) : supportFunction K (c • u) ≤ c * supportFunction K u := by
  refine csSup_le ((hK.2.2.mono interior_subset).image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [real_inner_smul_right]
  exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_inner hK u) ⟨x, hx, rfl⟩) hc

lemma supp_prod_le {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (a b : Position n) :
    CM.supp (K ×ˢ T) (a, b) ≤ supportFunction K a + supportFunction T b := by
  have hne : (K ×ˢ T).Nonempty :=
    (hK.2.2.mono interior_subset).prod (hT.2.2.mono interior_subset)
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [phaseInner]
  exact add_le_add (le_csSup (bddAbove_inner hK a) ⟨x.1, hx.1, rfl⟩)
    (le_csSup (bddAbove_inner hT b) ⟨x.2, hx.2, rfl⟩)

lemma supp_smul_le' {S : Set (Phase n)} (hS : IsConvexDomain S) {c : ℝ} (hc : 0 ≤ c)
    (w : Phase n) : CM.supp S (c • w) ≤ c * CM.supp S w := by
  refine csSup_le ((hS.2.2.mono interior_subset).image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have e : phaseInner x (c • w) = c * phaseInner x w := by
    simp only [phaseInner, Prod.smul_fst, Prod.smul_snd, real_inner_smul_right]; ring
  simp only [e]
  exact mul_le_mul_of_nonneg_left (le_csSup (CM.bdd_supp hS.1 w) ⟨x, hx, rfl⟩) hc

lemma negJ_eq (w : Phase n) : -J w = (w.2, -w.1) := by
  simp [J]

lemma negJ_smul (c : ℝ) (w : Phase n) : -J (c • w) = c • (-J w) := by
  ext <;> simp [J]

lemma mem_add_singleton_iff {S : Set (Position n)} {x t : Position n} :
    x ∈ S + {t} ↔ x - t ∈ S := by
  rw [Set.add_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - t, h, by simp⟩

end Viterbo.Thm22.PartA
end

section
namespace Viterbo.Thm22.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
variable {M : ℕ} [NeZero M]
/-! ## Step functions -/
lemma piece (f : ℤ → ℝ) (k : ℕ) :
    EqOn (fun _ => PartB.NN M * f k) (fun t => PartB.NN M * f ⌊PartB.NN M * t⌋)
      (uIoo ((k : ℝ) / PartB.NN M) (((k + 1 : ℕ) : ℝ) / PartB.NN M)) := by
  have hN := PartB.NN_pos (M := M)
  have hle : (k : ℝ) / PartB.NN M ≤ ((k + 1 : ℕ) : ℝ) / PartB.NN M := by
    gcongr; exact_mod_cast Nat.le_succ k
  intro t ht
  rw [uIoo_of_le hle] at ht
  obtain ⟨h1, h2⟩ := ht
  rw [div_lt_iff₀ hN, mul_comm] at h1
  rw [lt_div_iff₀ hN, mul_comm] at h2
  have : ⌊PartB.NN M * t⌋ = (k : ℤ) :=
    Int.floor_eq_iff.2 ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  simp only [this]

lemma integral_steps (f : ℤ → ℝ) (L : ℕ) :
    IntervalIntegrable (fun t => PartB.NN M * f ⌊PartB.NN M * t⌋) volume 0
        ((L : ℝ) / PartB.NN M) ∧
    ∫ t in (0 : ℝ)..((L : ℝ) / PartB.NN M), PartB.NN M * f ⌊PartB.NN M * t⌋ =
      ∑ k ∈ Finset.range L, f k := by
  have hN := PartB.NN_pos (M := M)
  induction L with
  | zero => simp
  | succ L ih =>
    have hi : IntervalIntegrable (fun t => PartB.NN M * f ⌊PartB.NN M * t⌋) volume
        ((L : ℝ) / PartB.NN M) (((L + 1 : ℕ) : ℝ) / PartB.NN M) :=
      intervalIntegrable_const.congr_uIoo (piece (M := M) f L)
    refine ⟨ih.1.trans hi, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hi, ih.2, Finset.sum_range_succ,
      ← intervalIntegral.integral_congr_uIoo (piece (M := M) f L),
      intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
    push_cast
    field_simp
    ring

end Viterbo.Thm22.PartA
end

section
namespace Viterbo.Thm22.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
open Fin.CommRing
variable {M : ℕ} [NeZero M]
/-! ## The loop `gam q p` -/
lemma gam_ac (q p : Fin M → Position n) (a b : ℝ) :
    PartB.gam q p b - PartB.gam q p a = ∫ s in a..b, PartB.vel q p s := by
  rw [integral_eq_of_hasDerivAt_off_countable _ _ PartB.Dset_countable
    (PartB.gam_cont q p).continuousOn (fun t ht => PartB.gam_hasDerivAt q p ht.2)
    ((PartB.vel_loc q p).integrableOn_isCompact isCompact_uIcc).intervalIntegrable]

lemma action_gam (q p : Fin M → Position n) :
    action (PartB.gam q p) = ∑ j, inner ℝ (p (j - 1) - p j) (q j) := by
  rw [action, PartB.integral_loop, PartB.sum_om]
  have h : ∑ j : Fin M, inner ℝ (p j) (q (j + 1)) = ∑ j : Fin M, inner ℝ (p (j - 1)) (q j) :=
    (Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun j => by simp)).symm
  simp only [inner_sub_right, inner_sub_left, Finset.sum_sub_distrib]
  rw [h]
  ring

/-- The `K × T`-length of the loop, leg by leg. -/
noncomputable def F' (q p : Fin M → Position n) (K T : Set (Position n)) (k : ℤ) : ℝ :=
  supportFunction K (PartB.vtx q p (k + 1) - PartB.vtx q p k).2 +
    supportFunction T (-(PartB.vtx q p (k + 1) - PartB.vtx q p k).1)

lemma F'_pair {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (q p : Fin M → Position n) (i : ℤ) :
    F' q p K T (2 * i) + F' q p K T (2 * i + 1) =
      supportFunction K (p (-(i : Fin M) - 1) - p (-(i : Fin M))) +
        supportFunction T (q (-(i : Fin M)) - q (-(i : Fin M) - 1)) := by
  simp only [F', PartB.vtx_even, PartB.vtx_odd, PartB.vtx_odd_succ, Prod.fst_sub, Prod.snd_sub,
    sub_self, neg_zero, neg_sub, supp_zero' hK, supp_zero' hT]
  ring

lemma ell_gam_le {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (q p : Fin M → Position n) :
    CM.ell (K ×ˢ T) (PartB.gam q p) ≤
      ∑ j, supportFunction K (p (j - 1) - p j) + ∑ j, supportFunction T (q j - q (j - 1)) := by
  have hKT := isConvexDomain_prod hK hT
  rw [CM.ell_eq (PartB.vel_loc q p) (gam_ac q p)]
  have hN := PartB.NN_pos (M := M)
  have h1 : ((2 * M : ℕ) : ℝ) / PartB.NN M = 1 := div_self hN.ne'
  obtain ⟨hint, hval⟩ := integral_steps (M := M) (F' q p K T) (2 * M)
  rw [h1] at hint hval
  have hle : ∫ t in (0 : ℝ)..1, CM.supp (K ×ˢ T) (-J (PartB.vel q p t)) ≤
      ∫ t in (0 : ℝ)..1, PartB.NN M * F' q p K T ⌊PartB.NN M * t⌋ := by
    refine intervalIntegral.integral_mono_on zero_le_one (CM.ii_supp hKT (PartB.vel_loc q p) 0 1)
      hint (fun t _ => ?_)
    rw [PartB.vel, negJ_smul]
    refine (supp_smul_le' hKT hN.le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hN.le
    rw [negJ_eq]
    exact supp_prod_le hK hT _ _
  refine hle.trans (le_of_eq ?_)
  rw [hval, PartB.sum_range_two_mul (fun k => F' q p K T k)]
  have e : ∑ i ∈ Finset.range M, (F' q p K T ((2 * i : ℕ) : ℤ) + F' q p K T ((2 * i + 1 : ℕ) : ℤ)) =
      ∑ j : Fin M, (supportFunction K (p (-j - 1) - p (-j)) +
        supportFunction T (q (-j) - q (-j - 1))) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [F'_pair hK hT]
    simp
  rw [e, ← Finset.sum_add_distrib]
  exact Fintype.sum_equiv (Equiv.neg (Fin M)) _ _ (fun j => rfl)

/-- A primitive of a zero-sum sequence. -/
lemma exists_prim (u : Fin M → Position n) (hu : ∑ j, u j = 0) :
    ∃ p : Fin M → Position n, ∀ j, p (j - 1) - p j = u j := by
  set P : ℕ → Position n := fun k => ∑ i ∈ Finset.range k, u (i : Fin M) with hP
  have hper : ∀ k, P (k + M) = P k := by
    intro k
    simp only [hP, Finset.sum_range_add]
    have : ∑ x ∈ Finset.range M, u ((k + x : ℕ) : Fin M) = 0 := by
      rw [Finset.sum_range (fun x => u ((k + x : ℕ) : Fin M))]
      simp only [Nat.cast_add, Fin.cast_val_eq_self]
      exact (Fintype.sum_equiv (Equiv.addLeft (k : Fin M)) (fun x => u ((k : Fin M) + x)) u
        (fun j => rfl)).trans hu
    rw [this, add_zero]
  have hper' : ∀ c k, P (k + M * c) = P k := by
    intro c; induction c with
    | zero => simp
    | succ c ih => intro k; rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hmod : ∀ k, P k = P (k % M) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k M]
    rw [hper']
  have hcast : ∀ a b : ℕ, (a : Fin M) = (b : Fin M) → P a = P b := by
    intro a b h
    have := congrArg Fin.val h
    simp only [Fin.val_natCast] at this
    rw [hmod a, hmod b, this]
  refine ⟨fun j => -P (j.val + 1), fun j => ?_⟩
  have h1 : P ((j - 1).val + 1) = P j.val := hcast _ _ (by simp)
  show -P ((j - 1).val + 1) - -P (j.val + 1) = u j
  rw [h1]
  simp only [hP, Finset.sum_range_succ, Fin.cast_val_eq_self]
  abel

end Viterbo.Thm22.PartA
end

section
namespace Viterbo.Thm22.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## The theorem -/
open Fin.CommRing in
theorem cEHZ_le_notTranslatable (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) {m : ℕ}
    (q : Fin m → Position n) (hq : NotTranslatableIntoInterior K q) :
    cEHZ (K ×ˢ T) ≤ ENNReal.ofReal (polygonLength T q) := by
  obtain ⟨x0, hx0⟩ := hK.2.2
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := by
    rcases m with _ | M
    · exact absurd (fun j => j.elim0) (hq 0)
    · exact ⟨M, rfl⟩
  obtain ⟨u, hsum, hne, hle, -⟩ := exists_cert hK hq
  set a := ∑ j, supportFunction K (u j) with ha_def
  set α := ∑ j, inner ℝ (u j) (q j) with hα_def
  set ℓ := polygonLength T q with hℓ_def
  -- `a > 0`
  have ha : 0 < a := by
    obtain ⟨j0, hj0⟩ := hne
    have h := Finset.sum_lt_sum (s := Finset.univ) (f := fun j => inner ℝ (u j) x0)
      (g := fun j => supportFunction K (u j))
      (fun j _ => inner_le_supp hK (interior_subset hx0) _)
      ⟨j0, Finset.mem_univ _, inner_lt_supp hK hx0 hj0⟩
    rw [← sum_inner, hsum, inner_zero_left] at h
    exact h
  -- `ℓ` in ring indexing
  have hℓ : ℓ = ∑ j, supportFunction T (q (j + 1) - q j) := by
    rw [hℓ_def, polygonLength]
    simp only [finRotate_apply]
  have hℓ' : ℓ = ∑ j, supportFunction T (q j - q (j - 1)) := by
    rw [hℓ]
    exact (Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun j => by simp)).symm
  -- `ℓ > 0`
  have hℓpos : 0 < ℓ := by
    have hex : ∃ j, q (j + 1) - q j ≠ 0 := by
      by_contra h
      push Not at h
      have hc : ∀ k : ℕ, q (k : Fin (M + 1)) = q 0 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [Nat.cast_succ, ← ih]; exact sub_eq_zero.1 (h _)
      apply hq (q 0 - x0)
      intro j
      rw [mem_add_singleton_iff, show j = ((j.val : ℕ) : Fin (M + 1)) by simp, hc]
      simpa using hx0
    obtain ⟨j0, hj0⟩ := hex
    rw [hℓ]
    have h := Finset.sum_lt_sum (s := Finset.univ) (f := fun j => inner ℝ (q (j + 1) - q j) 0)
      (g := fun j => supportFunction T (q (j + 1) - q j))
      (fun j _ => inner_le_supp hT (interior_subset h0) _)
      ⟨j0, Finset.mem_univ _, inner_lt_supp hT h0 hj0⟩
    simpa using h
  set c := ℓ / a with hc_def
  have hc : 0 < c := div_pos hℓpos ha
  have hca : c * a = ℓ := div_mul_cancel₀ _ ha.ne'
  obtain ⟨p, hp⟩ := exists_prim (c • u) (by simp only [Pi.smul_apply]; rw [← Finset.smul_sum, hsum, smul_zero])
  set z := PartB.gam q p
  have hAz : action z = c * α := by
    rw [action_gam]
    simp only [hp, Pi.smul_apply, real_inner_smul_left, hα_def, Finset.mul_sum]
  have hell : CM.ell (K ×ˢ T) z ≤ 2 * ℓ := by
    refine (ell_gam_le hK hT q p).trans ?_
    rw [← hℓ']
    have : ∑ j, supportFunction K (p (j - 1) - p j) ≤ c * a := by
      rw [ha_def, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by rw [hp]; exact supp_smul_le hK hc.le _
    linarith
  have hKT := isConvexDomain_prod hK hT
  have hac : CM.IsAC z := ⟨_, PartB.vel_loc q p, gam_ac q p⟩
  have hell0 := CM.ell_nonneg hKT (PartB.gam_periodic q p) hac
  obtain ⟨γ, -, -, hAγ, hcγ, hClarke⟩ := CM.exists_char_cEHZ_eq hn hKT
  have hαa : a ≤ α := hle
  have hAzpos : 0 < action z := by rw [hAz]; exact mul_pos hc (ha.trans_le hαa)
  have hcl := hClarke z (PartB.gam_periodic q p) hac hAzpos
  have hsq : CM.ell (K ×ˢ T) z ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ hell0 hell 2
  have hzℓ : ℓ ≤ action z := by rw [hAz, ← hca]; exact mul_le_mul_of_nonneg_left hαa hc.le
  have h1 : action γ * ℓ ≤ ℓ * ℓ := by nlinarith
  have h2 : action γ ≤ ℓ := le_of_mul_le_mul_right (by linarith) hℓpos
  rw [hcγ]
  exact ENNReal.ofReal_le_ofReal h2

end Viterbo.Thm22.PartA
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part A: the Clarke upper bound -/
alias cEHZ_le_notTranslatable := Viterbo.Thm22.PartA.cEHZ_le_notTranslatable

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartH
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# HKO Theorem 2.2, part H: Helly reduction and existence of a minimizer
-/
/-! ## Support-function helpers (copied from `PProdPartAB`) -/
lemma bddAbove_inner {T : Set (Position n)} (hT : Bornology.IsBounded T) (u : Position n) :
    BddAbove ((fun x => inner ℝ x u) '' T) := by
  obtain ⟨R, hR⟩ := hT.subset_closedBall 0
  refine ⟨R * ‖u‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm x u).trans (by gcongr)

lemma supportFunction_add_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (u v : Position n) :
    supportFunction T (u + v) ≤ supportFunction T u + supportFunction T v := by
  unfold supportFunction
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [inner_add_right]
  exact add_le_add (le_csSup (bddAbove_inner hT u) ⟨x, hx, rfl⟩)
    (le_csSup (bddAbove_inner hT v) ⟨x, hx, rfl⟩)

lemma polygonLength_comp_perm (T : Set (Position n)) {m : ℕ} (q : Fin m → Position n)
    (e : Equiv.Perm (Fin m)) (he : ∀ i, e (finRotate m i) = finRotate m (e i)) :
    polygonLength T (q ∘ e) = polygonLength T q := by
  unfold polygonLength
  simp only [Function.comp_apply, he]
  exact Equiv.sum_comp e (fun i => supportFunction T (q (finRotate m i) - q i))

lemma finRotate_pow_val (k r : ℕ) (x : Fin (k + 1)) :
    ((finRotate (k + 1) ^ r) x).val = (x.val + r) % (k + 1) := by
  induction r generalizing x with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, finRotate_apply, Fin.val_add, Fin.val_one',
      Nat.mod_add_mod, add_right_comm, Nat.add_mod_mod, add_assoc]

lemma rot_castSucc (k : ℕ) (i : Fin k) :
    finRotate (k + 1) i.castSucc = i.succ := by
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

lemma polygonLength_castSucc_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) {k : ℕ} (q : Fin (k + 2) → Position n) :
    polygonLength T (q ∘ Fin.castSucc) ≤ polygonLength T q := by
  unfold polygonLength
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Function.comp_apply, rot_castSucc, finRotate_last, Fin.succ_last,
    Fin.castSucc_zero, Fin.succ_castSucc]
  have htri := supportFunction_add_le hT hne (q (Fin.last (k + 1)) - q (Fin.last k).castSucc)
    (q 0 - q (Fin.last (k + 1)))
  rw [show q (Fin.last (k + 1)) - q (Fin.last k).castSucc + (q 0 - q (Fin.last (k + 1))) =
    q 0 - q (Fin.last k).castSucc by abel] at htri
  linarith

lemma mem_shift_iff (K : Set (Position n)) (x t : Position n) :
    x ∈ interior K + {t} ↔ x - t ∈ interior K := by
  rw [Set.add_singleton, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - t, h, sub_add_cancel x t⟩

/-- Helly reduction by one vertex. -/
lemma step {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) {k : ℕ} (hk : n + 1 < k + 1) (q : Fin (k + 1) → Position n)
    (hq : NotTranslatableIntoInterior K q) :
    ∃ q' : Fin k → Position n, NotTranslatableIntoInterior K q' ∧
      polygonLength T q' ≤ polygonLength T q := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  let C : Fin (k + 2) → Set (Position n) := fun j => {t | q j - t ∈ interior K}
  have hconv : ∀ j ∈ (Finset.univ : Finset (Fin (k + 2))), Convex ℝ (C j) := by
    intro j _ t1 ht1 t2 ht2 a b ha hb hab
    have := hK.2.1.interior ht1 ht2 ha hb hab
    show q j - (a • t1 + b • t2) ∈ interior K
    convert this using 1
    calc q j - (a • t1 + b • t2) = (a + b) • q j - (a • t1 + b • t2) := by rw [hab, one_smul]
      _ = a • (q j - t1) + b • (q j - t2) := by rw [add_smul, smul_sub, smul_sub]; abel
  have hempty : ¬ (⋂ j ∈ (Finset.univ : Finset (Fin (k + 2))), C j).Nonempty := by
    rintro ⟨t, ht⟩
    apply hq t
    intro j
    rw [mem_shift_iff]
    simp only [Finset.mem_univ, iInter_true, mem_iInter] at ht
    exact ht j
  have hI : ∃ I : Finset (Fin (k + 2)), I.card ≤ Module.finrank ℝ (Position n) + 1 ∧
      ¬ (⋂ i ∈ I, C i).Nonempty := by
    by_contra hcon
    push Not at hcon
    exact hempty (Convex.helly_theorem' hconv (fun I _ hc => hcon I hc))
  obtain ⟨I, hIc, hIe⟩ := hI
  rw [finrank_euclideanSpace_fin] at hIc
  obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
    by_contra h
    push Not at h
    have : I = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, Fintype.card_fin] at hIc
    omega
  let e : Equiv.Perm (Fin (k + 2)) := finRotate (k + 2) ^ (j.val + 1)
  have he_last : e (Fin.last (k + 1)) = j := by
    apply Fin.ext
    show ((finRotate (k + 1 + 1) ^ (j.val + 1)) (Fin.last (k + 1))).val = j.val
    rw [finRotate_pow_val, Fin.val_last,
      show k + 1 + (j.val + 1) = j.val + (k + 1 + 1) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.isLt]
  have he : ∀ i, e (finRotate (k + 2) i) = finRotate (k + 2) (e i) := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, pow_mul_comm']
  refine ⟨(q ∘ e) ∘ Fin.castSucc, ?_, ?_⟩
  · intro t ht
    apply hIe
    refine ⟨t, ?_⟩
    simp only [mem_iInter]
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    have hne' : e.symm i ≠ Fin.last (k + 1) := by
      intro h
      apply hij
      rw [← he_last, ← h, Equiv.apply_symm_apply]
    obtain ⟨i', hi'⟩ := Fin.exists_castSucc_eq.2 hne'
    have := ht i'
    rw [mem_shift_iff] at this
    simp only [Function.comp_apply, hi', Equiv.apply_symm_apply] at this
    exact this
  · rw [← polygonLength_comp_perm T q e he]
    exact polygonLength_castSucc_le hT hne (q ∘ e)

theorem exists_small {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    {m : ℕ} (q : Fin m → Position n) (hq : NotTranslatableIntoInterior K q) :
    ∃ (m' : ℕ) (q' : Fin m' → Position n), m' ≤ n + 1 ∧ NotTranslatableIntoInterior K q' ∧
      polygonLength T q' ≤ polygonLength T q := by
  have hne : T.Nonempty := hT.2.2.mono interior_subset
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ n + 1
    · exact ⟨m, q, hm, hq, le_rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      obtain ⟨q', hq', hle⟩ := step hK hT.1 hne (by omega) q hq
      obtain ⟨m', q'', hm', hq'', hle'⟩ := ih k (by omega) q' hq'
      exact ⟨m', q'', hm', hq'', hle'.trans hle⟩

end Viterbo.Thm22.PartH
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part H: Helly reduction and existence of a minimizer -/
alias exists_small := Viterbo.Thm22.PartH.exists_small

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartH
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Existence of a minimizer -/
lemma notTranslatable_iff {K : Set (Position n)} {m : ℕ} {y : Fin m → Position n} :
    NotTranslatableIntoInterior K y ↔ ∀ t, ¬ ∀ j, y j - t ∈ interior K := by
  simp only [NotTranslatableIntoInterior, mem_shift_iff]

/-- The set of translatable polygons. -/
def Dset (K : Set (Position n)) (m : ℕ) : Set (Fin m → Position n) :=
  {x | ∃ t, ∀ j, x j - t ∈ interior K}

lemma Dset_open (K : Set (Position n)) (m : ℕ) : IsOpen (Dset K m) := by
  have : Dset K m = ⋃ t : Position n, ⋂ j : Fin m, (fun x : Fin m → Position n => x j - t) ⁻¹'
      interior K := by
    ext x; simp [Dset]
  rw [this]
  exact isOpen_iUnion fun t => isOpen_iInter_of_finite fun j =>
    isOpen_interior.preimage (by fun_prop)

lemma isClosed_notTranslatable (K : Set (Position n)) (m : ℕ) :
    IsClosed {q : Fin m → Position n | NotTranslatableIntoInterior K q} := by
  have : {q : Fin m → Position n | NotTranslatableIntoInterior K q} = (Dset K m)ᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_compl_iff, Dset, notTranslatable_iff, not_exists]
  rw [this]
  exact (Dset_open K m).isClosed_compl

lemma notTranslatable_sub {K : Set (Position n)} {m : ℕ} {q : Fin m → Position n}
    (hq : NotTranslatableIntoInterior K q) (c : Position n) :
    NotTranslatableIntoInterior K (fun j => q j - c) := by
  rw [notTranslatable_iff] at hq ⊢
  intro t ht
  exact hq (c + t) fun j => by simpa [sub_sub] using ht j

lemma polygonLength_sub (T : Set (Position n)) {m : ℕ} (q : Fin m → Position n) (c : Position n) :
    polygonLength T (fun j => q j - c) = polygonLength T q := by
  unfold polygonLength
  simp only [sub_sub_sub_cancel_right]

lemma supp_le_norm {T : Set (Position n)} {R : ℝ} (hR : T ⊆ Metric.closedBall 0 R)
    (hne : T.Nonempty) (u : Position n) : supportFunction T u ≤ R * ‖u‖ := by
  unfold supportFunction
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm x u).trans (by gcongr)

lemma continuous_supp {T : Set (Position n)} (hT : IsConvexDomain T) :
    Continuous (supportFunction T) := by
  have hne : T.Nonempty := hT.2.2.mono interior_subset
  obtain ⟨R, hR⟩ := hT.1.subset_closedBall 0
  have hR0 : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hne
    exact dist_nonneg.trans (Metric.mem_closedBall.1 (hR hx))
  have key : ∀ u v : Position n, supportFunction T u - supportFunction T v ≤ R * ‖u - v‖ := by
    intro u v
    have h1 := supportFunction_add_le hT.1 hne v (u - v)
    rw [add_sub_cancel] at h1
    have h2 := supp_le_norm hR hne (u - v)
    linarith
  refine (LipschitzWith.of_dist_le_mul (K := R.toNNReal) fun u v => ?_).continuous
  rw [Real.coe_toNNReal R hR0, Real.dist_eq, dist_eq_norm, abs_le]
  constructor
  · have := key v u
    rw [norm_sub_rev] at this
    linarith
  · exact key u v

lemma continuous_polygonLength {T : Set (Position n)} (hT : IsConvexDomain T) (m : ℕ) :
    Continuous (fun q : Fin m → Position n => polygonLength T q) := by
  unfold polygonLength
  have := continuous_supp hT
  fun_prop

lemma supp_ge_norm {T : Set (Position n)} (hT : IsConvexDomain T) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall 0 r ⊆ T) (d : Position n) : r * ‖d‖ ≤ supportFunction T d := by
  set x : Position n := (r / ‖d‖) • d
  have hx : x ∈ T := by
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hd : d = 0
    · simp [x, hd, hr.le]
    · have : ‖d‖ ≠ 0 := norm_ne_zero_iff.2 hd
      simp only [x, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hr]
      rw [div_mul_cancel₀ _ this]
  have hle : inner ℝ x d ≤ supportFunction T d := le_csSup (bddAbove_inner hT.1 d) ⟨x, hx, rfl⟩
  have : inner ℝ x d = r * ‖d‖ := by
    by_cases hd : d = 0
    · simp [x, hd]
    · have : ‖d‖ ≠ 0 := norm_ne_zero_iff.2 hd
      simp only [x, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
  linarith

lemma norm_sub_zero_le {M : ℕ} (q : Fin (M + 1) → Position n) (j : Fin (M + 1)) :
    ‖q j - q 0‖ ≤ ∑ i, ‖q (finRotate (M + 1) i) - q i‖ := by
  classical
  set D : ℕ → ℝ := fun i => if h : i < M + 1 then ‖q (finRotate (M + 1) ⟨i, h⟩) - q ⟨i, h⟩‖
    else 0 with hD
  have hD0 : ∀ i, 0 ≤ D i := fun i => by
    simp only [hD]; split_ifs <;> positivity
  have key : ∀ k (hk : k < M + 1), ‖q ⟨k, hk⟩ - q 0‖ ≤ ∑ i ∈ Finset.range k, D i := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < M + 1 := by omega
      have hrot : finRotate (M + 1) ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      rw [Finset.sum_range_succ]
      have hDk : D k = ‖q ⟨k + 1, hk⟩ - q ⟨k, hk'⟩‖ := by
        simp only [hD, dif_pos hk', hrot]
      calc ‖q ⟨k + 1, hk⟩ - q 0‖ ≤ ‖q ⟨k + 1, hk⟩ - q ⟨k, hk'⟩‖ + ‖q ⟨k, hk'⟩ - q 0‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ∑ i ∈ Finset.range k, D i + D k := by rw [hDk]; linarith [ih hk']
  have hfull : ∑ i ∈ Finset.range (M + 1), D i = ∑ i, ‖q (finRotate (M + 1) i) - q i‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hD, dif_pos i.isLt]
  calc ‖q j - q 0‖ = ‖q ⟨j.val, j.isLt⟩ - q 0‖ := rfl
    _ ≤ ∑ i ∈ Finset.range j.val, D i := key j.val j.isLt
    _ ≤ ∑ i ∈ Finset.range (M + 1), D i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun i _ _ => hD0 i)
    _ = _ := hfull

/-- For a fixed number of vertices, `ℓ_T` attains its infimum on `P_m(K)` (if nonempty). -/
lemma exists_min_fixed {K T : Set (Position n)} (hT : IsConvexDomain T)
    (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (hP : ∃ q : Fin m → Position n,
      NotTranslatableIntoInterior K q) :
    ∃ q : Fin m → Position n, NotTranslatableIntoInterior K q ∧
      ∀ q' : Fin m → Position n, NotTranslatableIntoInterior K q' →
        polygonLength T q ≤ polygonLength T q' := by
  obtain ⟨q1, hq1⟩ := hP
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := by
    rcases m with _ | M
    · exfalso
      exact hq1 0 (fun j => j.elim0)
    · exact ⟨M, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  set r := ε / 2
  have hr : 0 < r := by positivity
  have hcb : Metric.closedBall (0 : Position n) r ⊆ T :=
    (Metric.closedBall_subset_ball (by simp only [r]; linarith)).trans hball
  set C := polygonLength T q1
  set A : Set (Fin (M + 1) → Position n) :=
    {q | NotTranslatableIntoInterior K q} ∩ {q | q 0 = 0} ∩ {q | polygonLength T q ≤ C}
  have hcont := continuous_polygonLength hT (M + 1)
  have hAc : IsClosed A :=
    ((isClosed_notTranslatable K _).inter (isClosed_eq (continuous_apply 0) continuous_const)).inter
      (isClosed_le hcont continuous_const)
  have hAb : Bornology.IsBounded A := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨C / r, ?_⟩
    rintro q ⟨⟨-, hq0⟩, hqC⟩
    simp only [mem_ofPred_eq] at hq0 hqC
    have hC0 : 0 ≤ C / r := by
      have : 0 ≤ polygonLength T q := Finset.sum_nonneg fun i _ =>
        (mul_nonneg hr.le (norm_nonneg _)).trans (supp_ge_norm hT hr hcb _)
      exact div_nonneg (this.trans hqC) hr.le
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hC0]
    intro j
    have h1 := norm_sub_zero_le q j
    rw [hq0, sub_zero] at h1
    have h2 : r * ∑ i, ‖q (finRotate (M + 1) i) - q i‖ ≤ polygonLength T q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => supp_ge_norm hT hr hcb _
    rw [le_div_iff₀ hr]
    nlinarith
  have hAk : IsCompact A := Metric.isCompact_of_isClosed_isBounded hAc hAb
  have hAne : A.Nonempty :=
    ⟨fun j => q1 j - q1 0, ⟨⟨notTranslatable_sub hq1 _, by simp⟩, by
      simp only [mem_ofPred_eq, polygonLength_sub]; rfl⟩⟩
  obtain ⟨q, hqA, hqmin⟩ := hAk.exists_isMinOn hAne hcont.continuousOn
  refine ⟨q, hqA.1.1, fun q' hq' => ?_⟩
  by_cases hC : polygonLength T q' ≤ C
  · have hmem : (fun j => q' j - q' 0) ∈ A :=
      ⟨⟨notTranslatable_sub hq' _, by simp⟩, by simpa only [mem_ofPred_eq, polygonLength_sub]⟩
    have := hqmin hmem
    simp only [mem_ofPred_eq, polygonLength_sub] at this
    exact this
  · exact (hqA.2 : polygonLength T q ≤ C).trans (le_of_not_ge hC)

lemma exists_two (hn : 1 ≤ n) {K : Set (Position n)} (hK : IsConvexDomain K) :
    ∃ q : Fin 2 → Position n, NotTranslatableIntoInterior K q := by
  obtain ⟨R, hR⟩ := hK.1.subset_closedBall 0
  set e : Position n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  refine ⟨![0, (2 * |R| + 1) • e], ?_⟩
  rw [notTranslatable_iff]
  intro t ht
  have h0 := interior_subset (ht 0)
  have h1 := interior_subset (ht 1)
  have h0' := hR h0
  have h1' := hR h1
  rw [Metric.mem_closedBall, dist_zero_right] at h0' h1'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0' h1'
  have : ‖(2 * |R| + 1) • e‖ ≤ 2 * R := by
    calc ‖(2 * |R| + 1) • e‖ = ‖((2 * |R| + 1) • e - t) - (0 - t)‖ := by
          congr 1; abel
      _ ≤ ‖(2 * |R| + 1) • e - t‖ + ‖0 - t‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  have := le_abs_self R
  linarith

theorem exists_minimizer (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) :
    ∃ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 ∧ NotTranslatableIntoInterior K q ∧
      (∀ (m' : ℕ) (q' : Fin m' → Position n), m' ≤ n + 1 → NotTranslatableIntoInterior K q' →
        polygonLength T q ≤ polygonLength T q') ∧
      (∀ (m' : ℕ) (q' : Fin m' → Position n), m' < m → NotTranslatableIntoInterior K q' →
        polygonLength T q < polygonLength T q') := by
  classical
  -- a global minimizer over `P_{≤ n+1}(K)`
  have hglob : ∃ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 ∧ NotTranslatableIntoInterior K q ∧
      ∀ (m' : ℕ) (q' : Fin m' → Position n), m' ≤ n + 1 → NotTranslatableIntoInterior K q' →
        polygonLength T q ≤ polygonLength T q' := by
    have hfix := fun m (h : ∃ q : Fin m → Position n, NotTranslatableIntoInterior K q) =>
      exists_min_fixed (K := K) hT h0 h
    choose qm hqm hmin using hfix
    set S := (Finset.range (n + 2)).filter
      (fun m => ∃ q : Fin m → Position n, NotTranslatableIntoInterior K q)
    let g : ℕ → ℝ := fun m =>
      if h : ∃ q : Fin m → Position n, NotTranslatableIntoInterior K q then
        polygonLength T (qm m h) else 0
    have h2 : 2 ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), exists_two hn hK⟩
    obtain ⟨m0, hm0S, hm0⟩ := S.exists_min_image g ⟨2, h2⟩
    obtain ⟨hm0r, hP0⟩ := Finset.mem_filter.1 hm0S
    refine ⟨m0, qm m0 hP0, by rw [Finset.mem_range] at hm0r; omega, hqm m0 hP0, ?_⟩
    intro m' q' hm' hq'
    have hm'S : m' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨q', hq'⟩⟩
    have := hm0 m' hm'S
    simp only [g, dif_pos hP0, dif_pos (⟨q', hq'⟩ : ∃ q : Fin m' → Position n,
      NotTranslatableIntoInterior K q)] at this
    exact this.trans (hmin m' _ q' hq')
  let P : ℕ → Prop := fun m => ∃ q : Fin m → Position n, m ≤ n + 1 ∧
    NotTranslatableIntoInterior K q ∧
      ∀ (m' : ℕ) (q' : Fin m' → Position n), m' ≤ n + 1 → NotTranslatableIntoInterior K q' →
        polygonLength T q ≤ polygonLength T q'
  have hP : ∃ m, P m := by
    obtain ⟨m, q, h1, h2, h3⟩ := hglob
    exact ⟨m, q, h1, h2, h3⟩
  obtain ⟨q, hm, hq, hmin⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, q, hm, hq, hmin, fun m' q' hm' hq' => ?_⟩
  have hle := hmin m' q' (by omega) hq'
  refine lt_of_le_of_ne hle fun heq => Nat.find_min hP hm' ⟨q', by omega, hq', ?_⟩
  intro m'' q'' hm'' hq''
  rw [← heq]
  exact hmin m'' q'' hm'' hq''

end Viterbo.Thm22.PartH
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias exists_minimizer := Viterbo.Thm22.PartH.exists_minimizer

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartK
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# HKO Theorem 2.2, part K: a minimizer is a closed billiard

Vertex deletion against `hmin'` (vertices distinct, certificate entries nonzero), Lagrange multipliers
by separating `μ • u` from the compact convex set `W = {(p (j-1) - p j)_j : p ∈ (closure T)^m}`, and a
translation obtained as a subsequence limit.
-/
/-! ## Support functions -/
lemma bddAbove_inner {T : Set (Position n)} (hT : Bornology.IsBounded T) (u : Position n) :
    BddAbove ((fun x => inner ℝ x u) '' T) := by
  obtain ⟨R, hR⟩ := hT.subset_closedBall 0
  refine ⟨R * ‖u‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm x u).trans (by gcongr)

lemma supportFunction_add_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (u v : Position n) :
    supportFunction T (u + v) ≤ supportFunction T u + supportFunction T v := by
  unfold supportFunction
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [inner_add_right]
  exact add_le_add (le_csSup (bddAbove_inner hT u) ⟨x, hx, rfl⟩)
    (le_csSup (bddAbove_inner hT v) ⟨x, hx, rfl⟩)

lemma inner_le_supp_closure {T : Set (Position n)} (hT : IsConvexDomain T) {x : Position n}
    (hx : x ∈ closure T) (d : Position n) : inner ℝ x d ≤ supportFunction T d := by
  have : closure T ⊆ {y | inner ℝ y d ≤ supportFunction T d} :=
    closure_minimal (fun y hy => le_csSup (bddAbove_inner hT.1 d) ⟨y, hy, rfl⟩)
      (isClosed_le (by fun_prop) continuous_const)
  exact this hx

/-- An interior point is strictly below the support function in a nonzero direction. -/
lemma inner_lt_supp {K : Set (Position n)} (hK : IsConvexDomain K) {x : Position n}
    (hx : x ∈ interior K) {u : Position n} (hu : u ≠ 0) : inner ℝ u x < supportFunction K u := by
  have ht : Tendsto (fun δ : ℝ => x + δ • u) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun δ : ℝ => x + δ • u) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x + δ • u ∈ interior K ∧ 0 < δ :=
    ((ht.mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds hx)).and
      self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  have := inner_le_supp_closure hK (subset_closure (interior_subset h1)) u
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm] at this
  have : 0 < δ * ‖u‖ ^ 2 := by positivity
  linarith

lemma supp_zero {T : Set (Position n)} (hne : T.Nonempty) : supportFunction T 0 = 0 := by
  unfold supportFunction
  simp only [inner_zero_right]
  rw [hne.image_const, csSup_singleton]

lemma supp_smul {T : Set (Position n)} {c : ℝ} (hc : 0 ≤ c) (d : Position n) :
    supportFunction T (c • d) = c * supportFunction T d := by
  unfold supportFunction
  have : (fun x => inner ℝ x (c • d)) '' T = c • ((fun x => inner ℝ x d) '' T) := by
    rw [← Set.image_smul, Set.image_image]
    simp [real_inner_smul_right, smul_eq_mul]
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

lemma polygonLength_smul (T : Set (Position n)) {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (q : Fin m → Position n) :
    polygonLength T (fun j => c • q j) = c * polygonLength T q := by
  unfold polygonLength
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, supp_smul hc]

/-! ## Polygons, rotations, deletion -/
lemma mem_add_singleton_iff {S : Set (Position n)} {x t : Position n} :
    x ∈ S + {t} ↔ x - t ∈ S := by
  rw [Set.add_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - t, h, by simp⟩

lemma notTranslatable_iff {K : Set (Position n)} {m : ℕ} {y : Fin m → Position n} :
    NotTranslatableIntoInterior K y ↔ ∀ t, ¬ ∀ j, y j - t ∈ interior K := by
  simp only [NotTranslatableIntoInterior, mem_add_singleton_iff]

lemma polygonLength_comp_perm (T : Set (Position n)) {m : ℕ} (q : Fin m → Position n)
    (e : Equiv.Perm (Fin m)) (he : ∀ i, e (finRotate m i) = finRotate m (e i)) :
    polygonLength T (q ∘ e) = polygonLength T q := by
  unfold polygonLength
  simp only [Function.comp_apply, he]
  exact Equiv.sum_comp e (fun i => supportFunction T (q (finRotate m i) - q i))

lemma finRotate_pow_val (k r : ℕ) (x : Fin (k + 1)) :
    ((finRotate (k + 1) ^ r) x).val = (x.val + r) % (k + 1) := by
  induction r generalizing x with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, finRotate_apply, Fin.val_add, Fin.val_one',
      Nat.mod_add_mod, add_right_comm, Nat.add_mod_mod, add_assoc]

lemma rot_castSucc (k : ℕ) (i : Fin k) :
    finRotate (k + 1) i.castSucc = i.succ := by
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

lemma polygonLength_castSucc_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) {k : ℕ} (q : Fin (k + 2) → Position n) :
    polygonLength T (q ∘ Fin.castSucc) ≤ polygonLength T q := by
  unfold polygonLength
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Function.comp_apply, rot_castSucc, finRotate_last, Fin.succ_last,
    Fin.castSucc_zero, Fin.succ_castSucc]
  have htri := supportFunction_add_le hT hne (q (Fin.last (k + 1)) - q (Fin.last k).castSucc)
    (q 0 - q (Fin.last (k + 1)))
  rw [show q (Fin.last (k + 1)) - q (Fin.last k).castSucc + (q 0 - q (Fin.last (k + 1))) =
    q 0 - q (Fin.last k).castSucc by abel] at htri
  linarith

/-- The rotation bringing the last index to `j`. -/
def rot (k : ℕ) (j : Fin (k + 2)) : Equiv.Perm (Fin (k + 2)) := finRotate (k + 2) ^ (j.val + 1)

lemma rot_last (k : ℕ) (j : Fin (k + 2)) : rot k j (Fin.last (k + 1)) = j := by
  apply Fin.ext
  show ((finRotate (k + 1 + 1) ^ (j.val + 1)) (Fin.last (k + 1))).val = j.val
  rw [finRotate_pow_val, Fin.val_last,
    show k + 1 + (j.val + 1) = j.val + (k + 1 + 1) by ring, Nat.add_mod_right,
    Nat.mod_eq_of_lt j.isLt]

lemma rot_comm (k : ℕ) (j : Fin (k + 2)) (i : Fin (k + 2)) :
    rot k j (finRotate (k + 2) i) = finRotate (k + 2) (rot k j i) := by
  unfold rot
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, pow_mul_comm']

lemma sum_del {β : Type*} [AddCommGroup β] (k : ℕ) (j : Fin (k + 2)) (F : Fin (k + 2) → β) :
    ∑ i : Fin (k + 1), F (rot k j i.castSucc) = ∑ i, F i - F j := by
  have h1 := Equiv.sum_comp (rot k j) F
  rw [Fin.sum_univ_castSucc, rot_last] at h1
  rw [← h1]
  abel

lemma length_del {T : Set (Position n)} (hT : Bornology.IsBounded T) (hne : T.Nonempty)
    (k : ℕ) (j : Fin (k + 2)) (q : Fin (k + 2) → Position n) :
    polygonLength T (fun i : Fin (k + 1) => q (rot k j i.castSucc)) ≤ polygonLength T q := by
  rw [← polygonLength_comp_perm T q (rot k j) (rot_comm k j)]
  exact polygonLength_castSucc_le hT hne (q ∘ rot k j)

lemma cover (k : ℕ) (j i : Fin (k + 2)) (hi : i ≠ j) : ∃ i' : Fin (k + 1), rot k j i'.castSucc = i := by
  have hne : (rot k j).symm i ≠ Fin.last (k + 1) := by
    intro h; apply hi; rw [← rot_last k j, ← h, Equiv.apply_symm_apply]
  obtain ⟨i', hi'⟩ := Fin.exists_castSucc_eq.2 hne
  exact ⟨i', by rw [hi', Equiv.apply_symm_apply]⟩

lemma finRotate_ne (k : ℕ) (i : Fin (k + 2)) : finRotate (k + 2) i ≠ i := by
  rw [finRotate_apply]
  intro h
  have : (1 : Fin (k + 2)) = 0 := by simp at h
  exact absurd (congrArg Fin.val this) (by simp)

/-! ## Summation by parts and multipliers -/
lemma by_parts {m : ℕ} (x p : Fin m → Position n) :
    ∑ j, inner ℝ (x j) (p ((finRotate m).symm j) - p j) =
      ∑ j, inner ℝ (p j) (x (finRotate m j) - x j) := by
  simp only [inner_sub_right, Finset.sum_sub_distrib]
  have : ∑ j, inner ℝ (x j) (p ((finRotate m).symm j)) = ∑ j, inner ℝ (p j) (x (finRotate m j)) := by
    rw [← Equiv.sum_comp (finRotate m)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply, real_inner_comm]
  rw [this]
  congr 1
  simp [real_inner_comm]

/-- Lagrange multipliers: a linear functional below `ℓ_T` is `∑ ⟨p (j-1) - p j, ·⟩` with
`p j ∈ closure T`. -/
lemma exists_mult {T : Set (Position n)} (hT : IsConvexDomain T) {m : ℕ}
    (v : Fin m → Position n)
    (hv : ∀ x : Fin m → Position n, ∑ j, inner ℝ (v j) (x j) ≤ polygonLength T x) :
    ∃ p : Fin m → Position n, (∀ j, p j ∈ closure T) ∧
      ∀ j, v j = p ((finRotate m).symm j) - p j := by
  by_contra hcon
  have hTne : T.Nonempty := hT.2.2.mono interior_subset
  let L : (Fin m → Position n) → (Fin m → Position n) := fun p j => p ((finRotate m).symm j) - p j
  have hL : IsLinearMap ℝ L :=
    ⟨fun x y => by funext j; simp only [L, Pi.add_apply]; abel,
     fun c x => by funext j; simp only [L, Pi.smul_apply, smul_sub]⟩
  have hLc : Continuous L := continuous_pi fun j => (continuous_apply _).sub (continuous_apply _)
  set W := L '' (univ.pi fun _ => closure T) with hW
  have hWc : IsCompact W := (isCompact_univ_pi fun _ => hT.1.isCompact_closure).image hLc
  have hWconv : Convex ℝ W := (convex_pi fun _ _ => hT.2.1.closure).is_linear_image hL
  have hvW : v ∉ W := by
    rintro ⟨p, hp, hpv⟩
    exact hcon ⟨p, fun j => hp j (mem_univ _), fun j => (congrFun hpv j).symm⟩
  obtain ⟨φ, c, hφW, hφv⟩ := geometric_hahn_banach_closed_point hWconv hWc.isClosed hvW
  set x : Fin m → Position n := fun j =>
    (InnerProductSpace.toDual ℝ (Position n)).symm
      (φ.comp (ContinuousLinearMap.single ℝ (fun _ : Fin m => Position n) j)) with hx_def
  have hφ : ∀ w : Fin m → Position n, φ w = ∑ j, inner ℝ (x j) (w j) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hx_def, InnerProductSpace.toDual_symm_apply]
    rfl
  have hsum : ∀ p : Fin m → Position n, (∀ j, p j ∈ T) →
      ∑ j, inner ℝ (p j) (x (finRotate m j) - x j) < c := by
    intro p hp
    have := hφW (L p) ⟨p, fun j _ => subset_closure (hp j), rfl⟩
    rwa [hφ, by_parts] at this
  have hle : polygonLength T x ≤ c := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / (m + 1) := by positivity
    choose p hp hlt using fun j : Fin m =>
      (show ∃ y ∈ T, supportFunction T (x (finRotate m j) - x j) - ε / (m + 1) <
          inner ℝ y (x (finRotate m j) - x j) by
        obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_lt_csSup (hTne.image _)
          (show supportFunction T (x (finRotate m j) - x j) - ε / (m + 1) <
            supportFunction T (x (finRotate m j) - x j) by linarith)
        exact ⟨y, hy, h⟩)
    have h1 := hsum p hp
    have h2 : ∑ j, (supportFunction T (x (finRotate m j) - x j) - ε / (m + 1)) ≤
        ∑ j, inner ℝ (p j) (x (finRotate m j) - x j) :=
      Finset.sum_le_sum fun j _ => (hlt j).le
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h2
    have h3 : (m : ℝ) * (ε / (m + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    unfold polygonLength
    linarith
  have h4 := hv x
  rw [hφ] at hφv
  have h5 : ∑ j, inner ℝ (x j) (v j) = ∑ j, inner ℝ (v j) (x j) :=
    Finset.sum_congr rfl fun j _ => real_inner_comm _ _
  linarith

/-! ## Translation into `closure K` -/
lemma exists_translate {K : Set (Position n)} (hK : IsConvexDomain K) {m : ℕ}
    (q : Fin m → Position n) (hD : ∀ s : ℝ, 0 < s → s < 1 → ∃ t, ∀ j, s • q j - t ∈ interior K)
    (hm : 0 < m) : ∃ t, ∀ j, q j - t ∈ closure K := by
  obtain ⟨R0, hR0⟩ := hK.1.subset_closedBall 0
  let s : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 1) / 2
  have hpos : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) / 2 := fun k => by positivity
  have hle1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) / 2 ≤ 1 / 2 := fun k => by
    gcongr
    rw [div_le_one (by positivity)]
    have := k.cast_nonneg (α := ℝ)
    linarith
  have hs0 : ∀ k, 0 < s k := fun k => by have := hle1 k; simp only [s]; linarith
  have hs1 : ∀ k, s k < 1 := fun k => by have := hpos k; simp only [s]; linarith
  choose τ hτ using fun k => hD (s k) (hs0 k) (hs1 k)
  let i0 : Fin m := ⟨0, hm⟩
  have hbd : ∀ k, τ k ∈ Metric.closedBall (0 : Position n) (‖q i0‖ + R0) := by
    intro k
    rw [mem_closedBall_zero_iff]
    have h1 := hR0 (interior_subset (hτ k i0))
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖s k • q i0‖ ≤ ‖q i0‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hs0 k).le]
      exact mul_le_of_le_one_left (norm_nonneg _) (hs1 k).le
    calc ‖τ k‖ = ‖s k • q i0 - (s k • q i0 - τ k)‖ := by congr 1; abel
      _ ≤ ‖s k • q i0‖ + ‖s k • q i0 - τ k‖ := norm_sub_le _ _
      _ ≤ ‖q i0‖ + R0 := by linarith
  obtain ⟨t, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hs : Tendsto s atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)).const_sub (1 : ℝ)
    simp only [zero_div, sub_zero] at this
    exact this
  refine ⟨t, fun j => ?_⟩
  have hconv : Tendsto (fun k => s (φ k) • q j - τ (φ k)) atTop (𝓝 (q j - t)) := by
    have := ((hs.comp hφ.tendsto_atTop).smul_const (q j)).sub hlim
    simpa using this
  exact isClosed_closure.mem_of_tendsto hconv
    (Eventually.of_forall fun k => subset_closure (interior_subset (hτ (φ k) j)))

/-! ## The theorem -/
theorem billiard_of_minimizer {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (hm : m ≤ n + 1)
    (q : Fin m → Position n) (hq : NotTranslatableIntoInterior K q)
    (hmin : ∀ (m' : ℕ) (q' : Fin m' → Position n), m' ≤ n + 1 → NotTranslatableIntoInterior K q' →
      polygonLength T q ≤ polygonLength T q')
    (hmin' : ∀ (m' : ℕ) (q' : Fin m' → Position n), m' < m → NotTranslatableIntoInterior K q' →
      polygonLength T q < polygonLength T q') :
    ∃ t : Position n, IsClosedBilliard K T (fun j => q j - t) ∧
      polygonLength T (fun j => q j - t) = polygonLength T q := by
  classical
  have hKne : K.Nonempty := hK.2.2.mono interior_subset
  have hTne : T.Nonempty := hT.2.2.mono interior_subset
  obtain ⟨u, hsum, ⟨j0, hj0⟩, hcert, hlast⟩ := exists_cert hK hq
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := by
    rcases m with _ | _ | k
    · exact j0.elim0
    · exfalso; apply hj0
      rw [Fin.sum_univ_one] at hsum
      have : j0 = 0 := Subsingleton.elim (α := Fin 1) _ _
      rwa [this]
    · exact ⟨k, rfl⟩
  set R := finRotate (k + 2) with hR
  -- Step 1: consecutive vertices are distinct, certificate entries are nonzero.
  have hd : ∀ j, q (R j) ≠ q j := by
    intro j hj
    have hq' : NotTranslatableIntoInterior K (fun i : Fin (k + 1) => q (rot k j i.castSucc)) := by
      rw [notTranslatable_iff] at hq ⊢
      intro t ht
      apply hq t
      intro i
      by_cases hij : i = j
      · subst hij
        rw [← hj]
        obtain ⟨i', hi'⟩ := cover k i (R i) (finRotate_ne k i)
        rw [← hi']
        exact ht i'
      · obtain ⟨i', hi'⟩ := cover k j i hij
        rw [← hi']
        exact ht i'
    exact absurd (hmin' _ _ (by omega) hq') (not_lt.2 (length_del hT.1 hTne k j q))
  have hu : ∀ j, u j ≠ 0 := by
    intro j hj
    have hq' : NotTranslatableIntoInterior K (fun i : Fin (k + 1) => q (rot k j i.castSucc)) := by
      refine notTranslatable_of_cert hK (u := fun i => u (rot k j i.castSucc)) ?_ ?_ ?_
      · rw [sum_del k j u, hsum, hj, sub_zero]
      · by_contra h
        push Not at h
        have h1 : ∑ i : Fin (k + 1), ‖u (rot k j i.castSucc)‖ = 0 := by simp [h]
        rw [sum_del k j (fun i => ‖u i‖), hj, norm_zero, sub_zero] at h1
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg (u i))).1 h1 j0
          (Finset.mem_univ _)
        exact hj0 (norm_eq_zero.1 this)
      · rw [sum_del k j (fun i => supportFunction K (u i)),
          sum_del k j (fun i => inner ℝ (u i) (q i)), hj, supp_zero hKne, inner_zero_left]
        simpa using hcert
    exact absurd (hmin' _ _ (by omega) hq') (not_lt.2 (length_del hT.1 hTne k j q))
  -- positivity
  obtain ⟨x0, hx0⟩ := hK.2.2
  have hgpos : 0 < ∑ j, supportFunction K (u j) := by
    have : ∑ j, inner ℝ (u j) x0 < ∑ j, supportFunction K (u j) :=
      Finset.sum_lt_sum (fun j _ => (inner_lt_supp hK hx0 (hu j)).le)
        ⟨j0, Finset.mem_univ _, inner_lt_supp hK hx0 hj0⟩
    rwa [← sum_inner, hsum, inner_zero_left] at this
  set gstar := ∑ j, inner ℝ (u j) (q j) with hgstar
  set fstar := polygonLength T q with hfstar
  have hg : 0 < gstar := lt_of_lt_of_le hgpos hcert
  have hf : 0 < fstar := by
    rw [hfstar]
    unfold polygonLength
    refine Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty
    have := inner_lt_supp hT h0 (sub_ne_zero.2 (hd j))
    simp only [inner_zero_right] at this
    exact this
  set μ := fstar / gstar with hμ
  have hμ0 : 0 ≤ μ := by positivity
  -- Step 2: multipliers.
  have hfx : ∀ x : Fin (k + 2) → Position n,
      μ * ∑ j, inner ℝ (u j) (x j) ≤ polygonLength T x := by
    intro x
    by_cases hx : ∑ j, inner ℝ (u j) (x j) ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos hμ0 hx).trans (PartB.polygonLength_nonneg' hT h0 x)
    · push Not at hx
      set gx := ∑ j, inner ℝ (u j) (x j) with hgx
      have hy := hlast (fun j => (gstar / gx) • x j) (by
        simp only [real_inner_smul_right, ← Finset.mul_sum, ← hgx]
        rw [div_mul_cancel₀ _ hx.ne'])
      have h1 := hmin _ _ hm hy
      rw [polygonLength_smul T (by positivity)] at h1
      rw [hμ, div_mul_eq_mul_div, div_le_iff₀ hg]
      rw [div_mul_eq_mul_div, le_div_iff₀ hx] at h1
      linarith
  obtain ⟨p, hpT, hpv⟩ := exists_mult hT (fun j => μ • u j) (fun x => by
    simpa [real_inner_smul_left, ← Finset.mul_sum] using hfx x)
  have hpe : ∀ j, inner ℝ (p j) (q (R j) - q j) = supportFunction T (q (R j) - q j) := by
    have hs : ∑ j, inner ℝ (p j) (q (R j) - q j) = ∑ j, supportFunction T (q (R j) - q j) := by
      rw [← by_parts]
      simp_rw [← hpv]
      simp only [real_inner_smul_right, ← Finset.mul_sum]
      have : ∑ j, inner ℝ (q j) (u j) = gstar :=
        Finset.sum_congr rfl fun j _ => real_inner_comm _ _
      rw [this, hμ, div_mul_cancel₀ _ hg.ne']
      rfl
    intro j
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => inner_le_supp_closure hT (hpT j) _)).1 hs j
      (Finset.mem_univ _)
  -- Step 3: translation.
  have hD : ∀ s : ℝ, 0 < s → s < 1 → ∃ t, ∀ j, s • q j - t ∈ interior K := by
    intro s hs0 hs1
    by_contra h
    have hnt : NotTranslatableIntoInterior K (fun j => s • q j) := by
      rw [notTranslatable_iff]
      intro t ht
      exact h ⟨t, ht⟩
    have := hmin _ _ hm hnt
    rw [polygonLength_smul T hs0.le] at this
    nlinarith
  obtain ⟨t, ht⟩ := exists_translate hK q hD (by omega)
  have hye : ∀ j, inner ℝ (u j) (q j - t) = supportFunction K (u j) := by
    have hs : ∑ j, inner ℝ (u j) (q j - t) = gstar := by
      simp only [inner_sub_right, Finset.sum_sub_distrib]
      rw [← sum_inner, hsum, inner_zero_left, sub_zero]
    have hle : ∀ j ∈ Finset.univ, inner ℝ (u j) (q j - t) ≤ supportFunction K (u j) :=
      fun j _ => by rw [real_inner_comm]; exact inner_le_supp_closure hK (ht j) _
    have : ∑ j, inner ℝ (u j) (q j - t) = ∑ j, supportFunction K (u j) :=
      le_antisymm (Finset.sum_le_sum hle) (hs ▸ hcert)
    intro j
    exact (Finset.sum_eq_sum_iff_of_le hle).1 this j (Finset.mem_univ _)
  -- Step 4: assembly.
  refine ⟨t, ⟨by omega, fun j => ?_, fun j => ?_, p, fun j => ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · rw [frontier, Set.mem_sdiff]
    refine ⟨ht j, fun hint => ?_⟩
    have := inner_lt_supp hK hint (hu j)
    rw [hye j] at this
    exact lt_irrefl _ this
  · intro h
    exact hd j (sub_left_injective h)
  · rw [frontier, Set.mem_sdiff]
    refine ⟨hpT j, fun hint => ?_⟩
    have := inner_lt_supp hT hint (sub_ne_zero.2 (hd j))
    rw [real_inner_comm, hpe j] at this
    exact lt_irrefl _ this
  · show ∀ y ∈ T, inner ℝ (q (R j) - t - (q j - t)) (y - p j) ≤ 0
    intro y hy
    rw [sub_sub_sub_cancel_right, inner_sub_right, real_inner_comm (p j), hpe j,
      real_inner_comm y]
    have := le_csSup (bddAbove_inner hT.1 (q (R j) - q j)) ⟨y, hy, rfl⟩
    unfold supportFunction
    linarith
  · rw [Set.mem_neg]
    have e : -(p (R j) - p j) = μ • u (R j) := by
      have := hpv (R j)
      rw [hR, Equiv.symm_apply_apply] at this
      rw [this]; abel
    rw [e]
    show ∀ y ∈ K, inner ℝ (μ • u (R j)) (y - (q (R j) - t)) ≤ 0
    intro y hy
    rw [real_inner_smul_left, inner_sub_right, hye (R j)]
    have := le_csSup (bddAbove_inner hK.1 (u (R j))) ⟨y, hy, rfl⟩
    have h2 : inner ℝ (u (R j)) y ≤ supportFunction K (u (R j)) := by
      rw [real_inner_comm]; exact this
    exact mul_nonpos_of_nonneg_of_nonpos hμ0 (by linarith)
  · show polygonLength T (fun j => q j - t) = polygonLength T q
    unfold polygonLength
    simp only [sub_sub_sub_cancel_right]

end Viterbo.Thm22.PartK
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part K: a minimizer is a closed billiard -/
alias billiard_of_minimizer := Viterbo.Thm22.PartK.billiard_of_minimizer

end Viterbo.Thm22
end

section
namespace Viterbo.Thm22.PartC
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# HKO Theorem 2.2, part C: characteristics are no shorter than `inf_{P(K)} ℓ_T`

`γ = (Q, P)` with velocity `v`; a.e. `v = J (a, b)` with `(a, b)` normal to `K × T`, so
`⟨x, a⟩ ≤ ⟨Q, a⟩` on `K` and `⟨y, b⟩ ≤ ⟨P, b⟩` on `T` (here `a = v.2`, `b = -v.1`).
With `B = ∫₀¹ ⟨P, b⟩`, `C = ∫₀¹ ⟨Q, a⟩`: `2 A(γ) = B + C`, and `B = C` (Riemann sums plus a
periodic discrete summation by parts). The polygon: cells `[s'_j, s_j]`, `s_j = 1 - j/N`,
`u_j = P(s_j) - P(s'_j)`, vertices `Y_j = λ Q(s_j)` with `λ = C / ∑ ⟨Q(s_j), u_j⟩`.
-/
/-! ## Cells -/
/-- The right end `s_j = 1 - j / N` of the `j`-th cell; its left end is `sR N (j + 1)`. -/
noncomputable def sR (N : ℕ) (j : ℕ) : ℝ := 1 - (j : ℝ) / N

lemma tele {E : Type*} [AddCommGroup E] (F : ℝ → E) (N : ℕ) (hN : N ≠ 0) :
    ∑ j : Fin N, (F (sR N (j : ℕ)) - F (sR N ((j : ℕ) + 1))) = F 1 - F 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => F (sR N j) - F (sR N (j + 1))) N,
    Finset.sum_range_sub']
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp [sR, hN']

lemma sum_cells (f : ℝ → ℝ) (hf : ∀ a b, IntervalIntegrable f volume a b) (N : ℕ) (hN : N ≠ 0) :
    ∑ j : Fin N, ∫ t in sR N ((j : ℕ) + 1)..sR N (j : ℕ), f t = ∫ t in (0 : ℝ)..1, f t := by
  have h := tele (fun x => ∫ t in (0 : ℝ)..x, f t) N hN
  simp only [intervalIntegral.integral_same, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_interval_sub_left (hf _ _) (hf _ _)]

lemma cell_le (N : ℕ) (j : ℕ) : sR N (j + 1) ≤ sR N j := by
  unfold sR
  push_cast
  have : (0 : ℝ) ≤ 1 / N := by positivity
  rw [add_div]
  linarith

lemma cell_bounds (N : ℕ) (hN : N ≠ 0) (j : Fin N) :
    0 ≤ sR N ((j : ℕ) + 1) ∧ sR N (j : ℕ) ≤ 1 ∧ sR N (j : ℕ) - sR N ((j : ℕ) + 1) = 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  refine ⟨?_, ?_, ?_⟩
  · unfold sR
    rw [sub_nonneg, div_le_one hN']
    exact_mod_cast hj
  · unfold sR
    have : (0 : ℝ) ≤ (j : ℝ) / N := by positivity
    linarith
  · unfold sR
    push_cast
    field_simp
    ring

/-! ## Riemann sums -/
lemma unif {F : ℝ → Phase n} (hF : Continuous F) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ ρ → ‖F x - F y‖ ≤ η := by
  obtain ⟨ρ, hρ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn) η hη
  refine ⟨ρ / 2, by positivity, fun x hx y hy hxy => ?_⟩
  have := h x hx y hy (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at this
  exact this.le

lemma riemann {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) {F : ℝ → Phase n} (hF : Continuous F)
    {η ρ : ℝ} (hρ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ ρ → ‖F x - F y‖ ≤ η)
    {N : ℕ} (hN : N ≠ 0) (hNρ : 1 / (N : ℝ) ≤ ρ) (τ : Fin N → ℝ)
    (hτ : ∀ j : Fin N, τ j ∈ Icc (sR N ((j : ℕ) + 1)) (sR N (j : ℕ))) :
    |∑ j, phaseInner (F (τ j)) (γ (sR N (j : ℕ)) - γ (sR N ((j : ℕ) + 1))) -
        ∫ t in (0 : ℝ)..1, phaseInner (F t) (v t)| ≤ 2 * η * ∫ t in (0 : ℝ)..1, ‖v t‖ := by
  have hii : ∀ a b, IntervalIntegrable (fun t => phaseInner (F t) (v t)) volume a b :=
    CM.ii_pI hF hv
  have hni : ∀ a b, IntervalIntegrable (fun t => 2 * η * ‖v t‖) volume a b :=
    fun a b => ((CM.ii_of_li hv a b).norm).const_mul _
  rw [← intervalIntegral.integral_const_mul, ← sum_cells _ hii N hN, ← sum_cells _ hni N hN, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  obtain ⟨h0, h1, hlen⟩ := cell_bounds N hN j
  have hle := cell_le N (j : ℕ)
  rw [hf, ← CM.integral_pI_const hv,
    ← intervalIntegral.integral_sub (CM.ii_pI continuous_const hv _ _) (hii _ _),
    ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hle (ae_of_all _ fun t ht => ?_) (hni _ _)
  rw [← CM.pI_sub_left, Real.norm_eq_abs]
  refine (CM.abs_pI_le _ _).trans ?_
  have hτj := hτ j
  have hb : ‖F (τ j) - F t‖ ≤ η := hρ _ ⟨h0.trans hτj.1, hτj.2.trans h1⟩ _
    ⟨h0.trans ht.1.le, ht.2.trans h1⟩ (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hτj.1, hτj.2])
  have := mul_le_mul_of_nonneg_right hb (norm_nonneg (v t))
  linarith

/-! ## The normal cone of the product -/
lemma normal_prod {K T : Set (Position n)} {z : Phase n} (hz : z ∈ closure (K ×ˢ T)) {w : Phase n}
    (hw : w ∈ J '' normalCone phaseInner (K ×ˢ T) z) :
    (∀ x ∈ K, phaseInner ((0 : Position n), x) w ≤ phaseInner ((0 : Position n), z.1) w) ∧
    (∀ y ∈ T, phaseInner (-y, (0 : Position n)) w ≤ phaseInner (-z.2, (0 : Position n)) w) := by
  obtain ⟨⟨α, β⟩, hN, rfl⟩ := hw
  rw [closure_prod_eq] at hz
  have key : ∀ x ∈ K, ∀ y ∈ T, inner ℝ α (x - z.1) + inner ℝ β (y - z.2) ≤ 0 := by
    intro x hx y hy
    have := hN (x, y) ⟨hx, hy⟩
    simpa [phaseInner] using this
  have hc : ∀ (c : ℝ) (g : Position n → ℝ), Continuous g → IsClosed {y | c + g y ≤ 0} :=
    fun c g hg => isClosed_le (continuous_const.add hg) continuous_const
  constructor
  · intro x hx
    have hS : T ⊆ {y | inner ℝ α (x - z.1) + inner ℝ β (y - z.2) ≤ 0} := fun y hy => key x hx y hy
    have h2 := (hc _ _ (by fun_prop)).closure_subset_iff.2 hS hz.2
    simp only [mem_ofPred_eq, sub_self, inner_zero_right, add_zero] at h2
    simp only [phaseInner, J, inner_zero_left, zero_add]
    rw [inner_sub_right] at h2
    rw [real_inner_comm α x, real_inner_comm α z.1]
    linarith
  · intro y hy
    have hS : K ⊆ {x | inner ℝ β (y - z.2) + inner ℝ α (x - z.1) ≤ 0} := fun x hx => by
      have := key x hx y hy; simp only [mem_ofPred_eq]; linarith
    have h2 := (hc _ _ (by fun_prop)).closure_subset_iff.2 hS hz.1
    simp only [mem_ofPred_eq, sub_self, inner_zero_right, add_zero] at h2
    simp only [phaseInner, J, inner_zero_left, add_zero, inner_neg_neg]
    rw [inner_sub_right] at h2
    rw [real_inner_comm β y, real_inner_comm β z.2]
    linarith

/-- One cell: an a.e. pointwise bound integrates. -/
lemma cell_int {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) {W : ℝ → Phase n} (hW : Continuous W)
    (c : Phase n) (hae : ∀ᵐ t, phaseInner c (v t) ≤ phaseInner (W t) (v t)) {a b : ℝ}
    (hab : a ≤ b) : phaseInner c (γ b - γ a) ≤ ∫ t in a..b, phaseInner (W t) (v t) := by
  rw [hf, ← CM.integral_pI_const hv]
  exact intervalIntegral.integral_mono_ae hab (CM.ii_pI continuous_const hv _ _)
    (CM.ii_pI hW hv _ _) hae

/-! ## Small lemmas -/
lemma eq_of_forall_small {x M : ℝ} (hM : 0 ≤ M) (h : ∀ η > 0, |x| ≤ η * M) : x = 0 := by
  by_contra hx
  have hx' : 0 < |x| := abs_pos.2 hx
  have h1 := h (|x| / (2 * (M + 1))) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h1
  nlinarith

lemma rot_eq {γ : ℝ → Phase n} (hper : Function.Periodic γ 1) (M : ℕ) (j : Fin (M + 1)) :
    γ (sR (M + 1) (finRotate (M + 1) j : ℕ)) = γ (sR (M + 1) ((j : ℕ) + 1)) := by
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    have hM : (M : ℝ) + 1 ≠ 0 := by positivity
    have e1 : sR (M + 1) 0 = 0 + 1 := by simp [sR]
    have e2 : sR (M + 1) ((Fin.last M : ℕ) + 1) = 0 := by simp [sR, hM]
    rw [e1, e2, hper 0]
  · rfl

lemma disc_id (z z' : Phase n) :
    phaseInner ((0 : Position n), z'.1) (z - z') - phaseInner (-z.2, (0 : Position n)) (z - z') =
      inner ℝ z.2 z.1 - inner ℝ z'.2 z'.1 := by
  simp only [phaseInner, Prod.fst_sub, Prod.snd_sub, inner_zero_left,
    inner_neg_left, inner_sub_right]
  rw [real_inner_comm z.2 z'.1, real_inner_comm z'.2 z'.1]
  ring

lemma nat_bound {ρ : ℝ} (hρ : 0 < ρ) {k : ℕ} (hk : 1 / ρ < k) : 1 / ((k + 1 : ℕ) : ℝ) ≤ ρ := by
  rw [div_lt_iff₀ hρ] at hk
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

/-! ## The main statement -/
theorem exists_notTranslatable_le_action {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic (K ×ˢ T) γ) (hnc : ∃ s t, γ s ≠ γ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (q : Fin m → Position n), NotTranslatableIntoInterior K q ∧
      polygonLength T q ≤ action γ + ε := by
  have hApos := CM.action_pos_of_char (isConvexDomain_prod hK hT) hγ hnc
  obtain ⟨hper, hfr, v, hv, hf, hae⟩ := hγ
  have hγc : Continuous γ := CM.cont_of_ac hv hf
  set FC : ℝ → Phase n := fun t => ((0 : Position n), (γ t).1) with hFC
  set FB : ℝ → Phase n := fun t => (-(γ t).2, (0 : Position n)) with hFB
  have hFCc : Continuous FC := continuous_const.prodMk (continuous_fst.comp hγc)
  have hFBc : Continuous FB := (continuous_snd.comp hγc).neg.prodMk continuous_const
  set C := ∫ t in (0 : ℝ)..1, phaseInner (FC t) (v t) with hCdef
  set B := ∫ t in (0 : ℝ)..1, phaseInner (FB t) (v t) with hBdef
  set Mv := ∫ t in (0 : ℝ)..1, ‖v t‖ with hMv
  have hMv0 : 0 ≤ Mv := intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  have hA : action γ = (B + C) / 2 := by
    rw [CM.action_eq hv hf]
    have e : ∀ t, phaseInner (J (γ t)) (v t) =
        phaseInner (FB t) (v t) + phaseInner (FC t) (v t) := by
      intro t
      rw [← CM.pI_add_left]
      congr 1
      ext <;> simp [J, FB, FC]
    simp only [e]
    rw [intervalIntegral.integral_add (CM.ii_pI hFBc hv 0 1) (CM.ii_pI hFCc hv 0 1)]
    ring
  have hper1 : γ 1 = γ 0 := by simpa using hper 0
  -- `B = C`
  have hBC : C - B = 0 := by
    refine eq_of_forall_small (M := 4 * Mv) (by positivity) fun η hη => ?_
    obtain ⟨ρ1, hρ1, h1⟩ := unif hFCc hη
    obtain ⟨ρ2, hρ2, h2⟩ := unif hFBc hη
    have hm : 0 < min ρ1 ρ2 := lt_min hρ1 hρ2
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / min ρ1 ρ2)
    have hN : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hNρ := nat_bound hm hk
    have r1 := riemann hv hf hFCc h1 hN (hNρ.trans (min_le_left _ _))
      (fun j => sR (k + 1) ((j : ℕ) + 1)) (fun j => ⟨le_rfl, cell_le _ _⟩)
    have r2 := riemann hv hf hFBc h2 hN (hNρ.trans (min_le_right _ _))
      (fun j => sR (k + 1) (j : ℕ)) (fun j => ⟨cell_le _ _, le_rfl⟩)
    have hdisc : ∑ j : Fin (k + 1), phaseInner (FC (sR (k + 1) ((j : ℕ) + 1)))
          (γ (sR (k + 1) (j : ℕ)) - γ (sR (k + 1) ((j : ℕ) + 1))) -
        ∑ j : Fin (k + 1), phaseInner (FB (sR (k + 1) (j : ℕ)))
          (γ (sR (k + 1) (j : ℕ)) - γ (sR (k + 1) ((j : ℕ) + 1))) = 0 := by
      rw [← Finset.sum_sub_distrib]
      have := tele (fun x => inner ℝ (γ x).2 (γ x).1) (k + 1) hN
      rw [hper1, sub_self] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => disc_id _ _
    rw [abs_le] at r1 r2 ⊢
    constructor <;> linarith [r1.1, r1.2, r2.1, r2.2]
  have hCB : B = C := by linarith
  have hCA : action γ = C := by rw [hA, hCB]; ring
  have hCpos : 0 < C := hCA ▸ hApos
  -- the tolerance
  set δ := C * ε / (C + ε) with hδ
  have hδpos : 0 < δ := by positivity
  have hδC : (C + ε) * δ = C * ε := by rw [hδ]; field_simp
  set η := δ / (2 * Mv + 1) with hη
  have hηpos : 0 < η := by positivity
  have hηM : 2 * η * Mv ≤ δ := by
    have : η * (2 * Mv + 1) = δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨ρ, hρ, hu⟩ := unif hFCc hηpos
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ρ)
  have hN : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have r := riemann hv hf hFCc hu hN (nat_bound hρ hk) (fun j => sR (k + 1) (j : ℕ))
    (fun j => ⟨cell_le _ _, le_rfl⟩)
  set Δ : Fin (k + 1) → Phase n := fun j => γ (sR (k + 1) (j : ℕ)) - γ (sR (k + 1) ((j : ℕ) + 1))
    with hΔ
  set u : Fin (k + 1) → Position n := fun j => (Δ j).2 with hudef
  set D := ∑ j : Fin (k + 1), phaseInner (FC (sR (k + 1) (j : ℕ))) (Δ j) with hD
  have hDC : |D - C| ≤ δ := r.trans hηM
  have hDlow : C - δ ≤ D := by rw [abs_le] at hDC; linarith [hDC.1]
  have hδltC : δ < C := by nlinarith
  have hDpos : 0 < D := by linarith
  have hD' : D = ∑ j, inner ℝ (u j) (γ (sR (k + 1) (j : ℕ))).1 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [FC, phaseInner, inner_zero_left, zero_add, u]
    exact real_inner_comm _ _
  -- the pointwise normal-cone facts
  have hN2 : ∀ᵐ t, (∀ x ∈ K, phaseInner ((0 : Position n), x) (v t) ≤ phaseInner (FC t) (v t)) ∧
      (∀ y ∈ T, phaseInner (-y, (0 : Position n)) (v t) ≤ phaseInner (FB t) (v t)) := by
    filter_upwards [hae] with t ht
    exact normal_prod (frontier_subset_closure (hfr t)) ht
  have hKne : K.Nonempty := hK.2.2.mono interior_subset
  have hTne : T.Nonempty := hT.2.2.mono interior_subset
  -- cells
  have hcK : ∀ j : Fin (k + 1), supportFunction K (u j) ≤
      ∫ t in sR (k + 1) ((j : ℕ) + 1)..sR (k + 1) (j : ℕ), phaseInner (FC t) (v t) := by
    intro j
    unfold supportFunction
    refine csSup_le (hKne.image _) (forall_mem_image.2 fun x hx => ?_)
    have := cell_int hv hf hFCc ((0 : Position n), x) (hN2.mono fun t ht => ht.1 x hx)
      (cell_le (k + 1) (j : ℕ))
    simpa [phaseInner, u, Δ] using this
  set lam := C / D with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hcT : ∀ j : Fin (k + 1), supportFunction T
      (lam • (γ (sR (k + 1) ((j : ℕ) + 1))).1 - lam • (γ (sR (k + 1) (j : ℕ))).1) ≤
      lam * ∫ t in sR (k + 1) ((j : ℕ) + 1)..sR (k + 1) (j : ℕ), phaseInner (FB t) (v t) := by
    intro j
    unfold supportFunction
    refine csSup_le (hTne.image _) (forall_mem_image.2 fun y hy => ?_)
    have := cell_int hv hf hFBc (-y, (0 : Position n)) (hN2.mono fun t ht => ht.2 y hy)
      (cell_le (k + 1) (j : ℕ))
    have e : inner ℝ y (lam • (γ (sR (k + 1) ((j : ℕ) + 1))).1 - lam • (γ (sR (k + 1) (j : ℕ))).1)
        = lam * phaseInner (-y, (0 : Position n))
          (γ (sR (k + 1) (j : ℕ)) - γ (sR (k + 1) ((j : ℕ) + 1))) := by
      simp only [phaseInner, ← smul_sub, real_inner_smul_right, inner_zero_left, add_zero,
        inner_neg_left, Prod.fst_sub, inner_sub_right]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this hlam0
  set Y : Fin (k + 1) → Position n := fun j => lam • (γ (sR (k + 1) (j : ℕ))).1 with hY
  refine ⟨k + 1, Y, ?_, ?_⟩
  · have hsum : ∑ j, u j = 0 := by
      have := tele (fun x => (γ x).2) (k + 1) hN
      rw [hper1, sub_self] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => Prod.snd_sub _ _
    have hne : ∃ j, u j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : D = 0 := by rw [hD']; simp [hcon]
      linarith
    have hYsum : ∑ j, inner ℝ (u j) (Y j) = C := by
      simp only [Y, real_inner_smul_right]
      rw [← Finset.mul_sum, ← hD', hlam, div_mul_cancel₀ _ hDpos.ne']
    refine notTranslatable_of_cert hK hsum hne ?_
    rw [hYsum]
    refine (Finset.sum_le_sum fun j _ => hcK j).trans (le_of_eq ?_)
    exact sum_cells _ (CM.ii_pI hFCc hv) _ hN
  · unfold polygonLength
    have hrot : ∀ j : Fin (k + 1), Y (finRotate (k + 1) j) =
        lam • (γ (sR (k + 1) ((j : ℕ) + 1))).1 := fun j => by
      simp only [Y]; rw [rot_eq hper k j]
    simp only [hrot]
    refine (Finset.sum_le_sum fun j _ => hcT j).trans ?_
    rw [← Finset.mul_sum, sum_cells _ (CM.ii_pI hFBc hv) _ hN, ← hBdef, hCB, hCA, hlam,
      div_mul_eq_mul_div, div_le_iff₀ hDpos]
    nlinarith

end Viterbo.Thm22.PartC
end

section
namespace Viterbo.Thm22
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part C: characteristics are no shorter than `inf_{P(K)} ℓ_T` -/
alias exists_notTranslatable_le_action := Viterbo.Thm22.PartC.exists_notTranslatable_le_action

/-! ## Assembly -/
theorem cEHZ_le_billiard {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (q : Fin m → Position n)
    (hq : IsClosedBilliard K T q) :
    cEHZ (K ×ˢ T) ≤ ENNReal.ofReal (polygonLength T q) :=
  PartB.cEHZ_le_billiard hK hT h0 q hq

/-- The minimizer over `P_{≤ n+1}(K)` realizes `c_EHZ(K × T)` and, translated, is a closed billiard. -/
theorem key (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) :
    ∃ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 ∧ NotTranslatableIntoInterior K q ∧
      cEHZ (K ×ˢ T) = ENNReal.ofReal (polygonLength T q) ∧
      ∃ t : Position n, IsClosedBilliard K T (fun j => q j - t) ∧
        polygonLength T (fun j => q j - t) = polygonLength T q := by
  obtain ⟨γ, hγ, hnc, hA, hc, -⟩ := Viterbo.CM.exists_char_cEHZ_eq hn (isConvexDomain_prod hK hT)
  obtain ⟨m, q, hm, hq, hmin, hmin'⟩ := exists_minimizer hn hK hT h0
  have hle : polygonLength T q ≤ action γ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m1, q1, hq1, hl1⟩ := exists_notTranslatable_le_action hK hT h0 hγ hnc hε
    obtain ⟨m2, q2, hm2, hq2, hl2⟩ := exists_small (T := T) hK hT q1 hq1
    linarith [hmin m2 q2 hm2 hq2]
  have hge := cEHZ_le_notTranslatable hn hK hT h0 q hq
  refine ⟨m, q, hm, hq, ?_, billiard_of_minimizer hK hT h0 hm q hq hmin hmin'⟩
  refine le_antisymm hge ?_
  rw [hc]
  exact ENNReal.ofReal_le_ofReal hle

lemma exists_min_char (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) :
    ∃ γ : ℝ → Phase n, IsGeneralizedClosedCharacteristic (K ×ˢ T) γ ∧ (∃ s t, γ s ≠ γ t) ∧
      cEHZ (K ×ˢ T) = ENNReal.ofReal |action γ| := by
  obtain ⟨γ, hγ, hnc, hpos, hc, -⟩ := Viterbo.CM.exists_char_cEHZ_eq hn (isConvexDomain_prod hK hT)
  exact ⟨γ, hγ, hnc, by rw [hc, abs_of_pos hpos]⟩

theorem exists_billiard_eq (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) :
    ∃ (m : ℕ) (q : Fin m → Position n), IsClosedBilliard K T q ∧
      cEHZ (K ×ˢ T) = ENNReal.ofReal (polygonLength T q) := by
  obtain ⟨m, q, -, -, hc, t, hb, hl⟩ := key hn hK hT h0
  exact ⟨m, _, hb, by rw [hl, hc]⟩

theorem exists_notTranslatable_eq (hn : 1 ≤ n) {K T : Set (Position n)} (hK : IsConvexDomain K)
    (hT : IsConvexDomain T) (h0 : (0 : Position n) ∈ interior T) :
    ∃ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 ∧ NotTranslatableIntoInterior K q ∧
      cEHZ (K ×ˢ T) = ENNReal.ofReal (polygonLength T q) := by
  obtain ⟨m, q, hm, hq, hc, -⟩ := key hn hK hT h0
  exact ⟨m, q, hm, hq, hc⟩

lemma polygonLength_nonneg {T : Set (Position n)} (hT : IsConvexDomain T)
    (h0 : (0 : Position n) ∈ interior T) {m : ℕ} (q : Fin m → Position n) :
    0 ≤ polygonLength T q :=
  PartB.polygonLength_nonneg' hT h0 q

theorem main (n : ℕ) (hn : 1 ≤ n)
    (K T : Set (OAI.SymmetricPolar.Position n)) (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (h0 : (0 : OAI.SymmetricPolar.Position n) ∈ interior T) :
    ∃ L : ℝ, cEHZ (K ×ˢ T) = ENNReal.ofReal L ∧
      (∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic (K ×ˢ T) γ ∧
        (∃ s t, γ s ≠ γ t) ∧ |action γ| = L) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q ∧
        polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q →
        L ≤ polygonLength T q) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 ∧
        NotTranslatableIntoInterior K q ∧ polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 →
        NotTranslatableIntoInterior K q → L ≤ polygonLength T q) := by
  obtain ⟨γ, hγ, hnc, hc⟩ := exists_min_char hn hK hT
  set L := |action γ|
  have hL : 0 ≤ L := abs_nonneg _
  have key : ∀ x : ℝ, 0 ≤ x → cEHZ (K ×ˢ T) = ENNReal.ofReal x → x = L := by
    intro x hx h
    rw [hc] at h
    exact (ENNReal.ofReal_eq_ofReal_iff hx hL).1 h.symm
  have le : ∀ x : ℝ, 0 ≤ x → cEHZ (K ×ˢ T) ≤ ENNReal.ofReal x → L ≤ x := by
    intro x hx h
    rw [hc] at h
    exact (ENNReal.ofReal_le_ofReal_iff hx).1 h
  refine ⟨L, hc, ⟨γ, hγ, hnc, rfl⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨m, q, hq, he⟩ := exists_billiard_eq hn hK hT h0
    exact ⟨m, q, hq, key _ (polygonLength_nonneg hT h0 q) he⟩
  · intro m q hq
    exact le _ (polygonLength_nonneg hT h0 q) (cEHZ_le_billiard hK hT h0 q hq)
  · obtain ⟨m, q, hm, hq, he⟩ := exists_notTranslatable_eq hn hK hT h0
    exact ⟨m, q, hm, hq, key _ (polygonLength_nonneg hT h0 q) he⟩
  · intro m q _ hq
    exact le _ (polygonLength_nonneg hT h0 q) (cEHZ_le_notTranslatable hn hK hT h0 q hq)

end Viterbo.Thm22
end

open Viterbo in
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (K T : Set (OAI.SymmetricPolar.Position n)) (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (h0 : (0 : OAI.SymmetricPolar.Position n) ∈ interior T) :
    ∃ L : ℝ, cEHZ (K ×ˢ T) = ENNReal.ofReal L ∧
      (∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic (K ×ˢ T) γ ∧
        (∃ s t, γ s ≠ γ t) ∧ |action γ| = L) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q ∧
        polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q →
        L ≤ polygonLength T q) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 ∧
        NotTranslatableIntoInterior K q ∧ polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 →
        NotTranslatableIntoInterior K q → L ≤ polygonLength T q) :=
  Viterbo.Thm22.main n hn K T hK hT h0
