-- Prove2me | solution 2 for Viterbo.systolicRatio_symplecticPProduct_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:42:15.949524+00:00
-- url     : https://prove2.me/submissions/64073792-de30-42cf-bdbf-014cb6e45ca0

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

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

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

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma J_add (x y : Phase n) : J (x + y) = J x + J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

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

lemma frontier_translate (S : Set (Phase n)) (w : Phase n) :
    frontier ((· + w) '' S) = (· + w) '' frontier S :=
  ((Homeomorph.addRight w).image_frontier S).symm

lemma normalCone_translate (S : Set (Phase n)) (w z : Phase n) :
    normalCone phaseInner ((· + w) '' S) (z + w) = normalCone phaseInner S z := by
  ext u
  simp only [normalCone, mem_ofPred_eq, forall_mem_image, add_sub_add_right_eq_sub]

lemma gcc_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    IsGeneralizedClosedCharacteristic ((· + w) '' S) (fun t => γ t + w) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := h
  refine ⟨fun t => by simp [hper t], fun t => ?_, v, hvint, fun a b => ?_, ?_⟩
  · rw [frontier_translate]; exact mem_image_of_mem _ (hfr t)
  · rw [← hftc a b]; exact add_sub_add_right_eq_sub _ _ _
  · filter_upwards [hae] with t ht
    rwa [normalCone_translate]

lemma action_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    action (fun t => γ t + w) = action γ := by
  obtain ⟨hper, -, v, hvint, hftc, -⟩ := h
  have hf' : ∀ a b, (fun t => γ t + w) b - (fun t => γ t + w) a = ∫ s in a..b, v s := by
    intro a b; rw [← hftc a b]; exact add_sub_add_right_eq_sub _ _ _
  have hγc := cont_of_ac hvint hftc
  rw [action_eq hvint hf', action_eq hvint hftc]
  have e : ∀ t, phaseInner (J (γ t + w)) (v t) =
      phaseInner (J (γ t)) (v t) + phaseInner (J w) (v t) := fun t => by
    rw [J_add, pI_add_left]
  simp only [e]
  rw [intervalIntegral.integral_add (ii_pI (w := fun t => J (γ t)) (continuous_J.comp hγc) hvint 0 1)
    (ii_pI (w := fun _ => J w) continuous_const hvint 0 1), integral_pI_const hvint, ← hftc 0 1,
    show γ 1 = γ 0 by simpa using hper 0, sub_self, pI_zero_right, add_zero]

lemma cEHZ_translate_le (S : Set (Phase n)) (w : Phase n) :
    cEHZ ((· + w) '' S) ≤ cEHZ S := by
  refine le_iInf₂ (fun γ hγ => ?_)
  have hnc : ∃ s t, (fun t => γ t + w) s ≠ (fun t => γ t + w) t := by
    obtain ⟨s, t, hst⟩ := hγ.2
    exact ⟨s, t, fun h => hst (add_right_cancel h)⟩
  refine (iInf₂_le (fun t => γ t + w) ⟨gcc_translate hγ.1 w, hnc⟩).trans ?_
  rw [action_translate hγ.1 w]

/-! ### Scaling -/

lemma normalCone_smul {S : Set (Phase n)} {α : ℝ} (hα : 0 < α) {x u : Phase n}
    (hu : u ∈ normalCone phaseInner S x) :
    α • u ∈ normalCone phaseInner (α • S) (α • x) := by
  rintro _ ⟨y, hy, rfl⟩
  have := hu y hy
  rw [← smul_sub, pI_smul_left, pI_smul_right]
  have h2 : 0 ≤ α * α := by positivity
  nlinarith

lemma frontier_smul' (S : Set (Phase n)) {α : ℝ} (hα : α ≠ 0) :
    frontier (α • S) = α • frontier S := by
  rw [← Set.image_smul, ← Set.image_smul]
  exact ((Homeomorph.smulOfNeZero α hα).image_frontier S).symm

lemma ftc_smul {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    ∀ a b, (fun t => α • γ t) b - (fun t => α • γ t) a = ∫ s in a..b, α • v s := by
  intro a b
  rw [intervalIntegral.integral_smul, ← hf a b, smul_sub]

lemma gcc_smul {S : Set (Phase n)} {γ : ℝ → Phase n} (h : IsGeneralizedClosedCharacteristic S γ)
    {α : ℝ} (hα : 0 < α) :
    IsGeneralizedClosedCharacteristic (α • S) (fun t => α • γ t) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := h
  refine ⟨fun t => by simp only [hper t], fun t => ?_, fun t => α • v t, hvint.smul α,
    ftc_smul hftc α, ?_⟩
  · rw [frontier_smul' S hα.ne']; exact smul_mem_smul_set (hfr t)
  · filter_upwards [hae] with t ⟨u, hu, hvu⟩
    exact ⟨α • u, normalCone_smul hα hu, by rw [J_smul, hvu]⟩

lemma action_smul {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    action (fun t => α • γ t) = α ^ 2 * action γ := by
  rw [action_eq (hv.smul α) (ftc_smul hf α), action_eq hv hf]
  have e : ∀ t, phaseInner (J (α • γ t)) (α • v t) = α ^ 2 * phaseInner (J (γ t)) (v t) := by
    intro t; rw [J_smul, pI_smul_left, pI_smul_right]; ring
  simp only [Pi.smul_apply, e, intervalIntegral.integral_const_mul]
  ring

lemma cEHZ_smul_le (S : Set (Phase n)) {α : ℝ} (hα : 0 < α) :
    cEHZ (α • S) ≤ ENNReal.ofReal (α ^ 2) * cEHZ S := by
  have h0 : ENNReal.ofReal (α ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  unfold cEHZ
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hγ => ?_
  have hnc : ∃ s t, (fun t => α • γ t) s ≠ (fun t => α • γ t) t := by
    obtain ⟨s, t, hst⟩ := hγ.2
    exact ⟨s, t, fun h => hst (smul_right_injective (Phase n) hα.ne' h)⟩
  refine (iInf₂_le (fun t => α • γ t) ⟨gcc_smul hγ.1 hα, hnc⟩).trans (le_of_eq ?_)
  obtain ⟨-, -, v, hv, hf, -⟩ := hγ.1
  rw [action_smul hv hf, abs_mul, abs_of_nonneg (sq_nonneg α),
    ENNReal.ofReal_mul (sq_nonneg α)]

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

lemma cEHZ_translate (S : Set (Phase n)) (d : Phase n) :
    cEHZ ((fun z => z + d) '' S) = cEHZ S := by
  refine le_antisymm (cEHZ_translate_le S d) ?_
  have h := cEHZ_translate_le ((· + d) '' S) (-d)
  rwa [image_image, show (fun x : Phase n => x + d + -d) = id from funext fun x => by simp,
    image_id] at h

lemma cEHZ_smul (S : Set (Phase n)) {α : ℝ} (hα : 0 < α) :
    cEHZ (α • S) = ENNReal.ofReal (α ^ 2) * cEHZ S := by
  refine le_antisymm (cEHZ_smul_le S hα) ?_
  have h2 := cEHZ_smul_le (α • S) (inv_pos.mpr hα)
  rw [inv_smul_smul₀ hα.ne'] at h2
  calc ENNReal.ofReal (α ^ 2) * cEHZ S
      ≤ ENNReal.ofReal (α ^ 2) * (ENNReal.ofReal (α⁻¹ ^ 2) * cEHZ (α • S)) := by gcongr
    _ = ENNReal.ofReal (α ^ 2 * α⁻¹ ^ 2) * cEHZ (α • S) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = cEHZ (α • S) := by
        rw [← mul_pow, mul_inv_cancel₀ hα.ne', one_pow, ENNReal.ofReal_one, one_mul]

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

lemma ell_mono {K L : Set (Phase n)} (hK : IsConvexDomain K) (hL : IsConvexDomain L) (hKL : K ⊆ L)
    {z : ℝ → Phase n} (hac : IsAC z) : ell K z ≤ ell L z := by
  obtain ⟨v, hv, hf⟩ := hac
  rw [ell_eq hv hf, ell_eq hv hf]
  refine intervalIntegral.integral_mono_on zero_le_one (ii_supp hK hv 0 1) (ii_supp hL hv 0 1)
    (fun t _ => ?_)
  exact csSup_le_csSup (bdd_supp hL.1 _) ((hK.2.2.mono interior_subset).image _) (image_mono hKL)

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

/-- Monotonicity of `cEHZ` under inclusion of convex domains. -/
theorem cEHZ_mono (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K) (hL : IsConvexDomain L)
    (hKL : K ⊆ L) : cEHZ K ≤ cEHZ L := by
  obtain ⟨γL, hγL, -, hAL, hcL, -⟩ := exists_char_cEHZ_eq hn hL
  obtain ⟨γK, -, -, hAK, hcK, hkeyK⟩ := exists_char_cEHZ_eq hn hK
  rw [hcK, hcL]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hkeyK γL hγL.1 (isAC_of_char hγL) hAL
  have h2 := ell_nonneg hK hγL.1 (isAC_of_char hγL)
  have h3 := ell_mono hK hL hKL (isAC_of_char hγL)
  have h4 := ell_char hL hγL
  have h5 : ell K γL ^ 2 ≤ ell L γL ^ 2 := pow_le_pow_left₀ h2 h3 2
  rw [h4] at h5
  nlinarith

end Viterbo.CM
end
section
namespace Viterbo.PP2.PartL

open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise

/-! ## Algebra of `phaseInner` and `J` -/

section Alg

variable {n : ℕ}

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_sub_right (w x y : Phase n) :
    phaseInner w (x - y) = phaseInner w x - phaseInner w y := by
  simp [phaseInner, inner_sub_right]; ring

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_zero_left (x : Phase n) : phaseInner 0 x = 0 := by simp [phaseInner]

lemma pI_self (z : Phase n) : phaseInner z z = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp [phaseInner]

lemma pI_self_nonneg (z : Phase n) : 0 ≤ phaseInner z z := by
  rw [pI_self]; positivity

lemma pI_self_eq_zero {z : Phase n} (h : phaseInner z z = 0) : z = 0 := by
  rw [pI_self] at h
  have h1 : ‖z.1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  have h2 : ‖z.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at h1 h2
  exact Prod.ext h1 h2

lemma pI_self_pos {z : Phase n} (h : z ≠ 0) : 0 < phaseInner z z :=
  lt_of_le_of_ne (pI_self_nonneg z) (fun h' => h (pI_self_eq_zero h'.symm))

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma J_zero : J (0 : Phase n) = 0 := by simp [J]

lemma J_eq_zero {z : Phase n} (h : J z = 0) : z = 0 := by
  simp only [J, Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

lemma pI_J_self (x : Phase n) : phaseInner x (J x) = 0 := by
  simp [phaseInner, J, inner_neg_right, real_inner_comm]

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

end Alg

/-! ## Coordinates of `ℝ^{m+k}` -/

section Coord

variable {m k : ℕ}

/-- First block of coordinates. -/
noncomputable def P1L : Position (m + k) →ₗ[ℝ] Position m where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.castAdd k i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Second block of coordinates. -/
noncomputable def P2L : Position (m + k) →ₗ[ℝ] Position k where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.natAdd m i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

noncomputable def P1 : Position (m + k) →L[ℝ] Position m := LinearMap.toContinuousLinearMap P1L
noncomputable def P2 : Position (m + k) →L[ℝ] Position k := LinearMap.toContinuousLinearMap P2L

lemma P1_apply (x : Position (m + k)) (i : Fin m) : (P1 x) i = x (Fin.castAdd k i) := rfl
lemma P2_apply (x : Position (m + k)) (i : Fin k) : (P2 x) i = x (Fin.natAdd m i) := rfl

lemma appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

lemma appendPos_natAdd (x : Position m) (y : Position k) (i : Fin k) :
    appendPos x y (Fin.natAdd m i) = y i := by
  simp [appendPos]

lemma P1_append (x : Position m) (y : Position k) : P1 (appendPos x y) = x := by
  ext i; rw [P1_apply, appendPos_castAdd]

lemma P2_append (x : Position m) (y : Position k) : P2 (appendPos x y) = y := by
  ext i; rw [P2_apply, appendPos_natAdd]

lemma append_P (x : Position (m + k)) : appendPos (P1 x) (P2 x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [appendPos_castAdd, P1_apply]
  · rw [appendPos_natAdd, P2_apply]

lemma inner_split (x y : Position (m + k)) :
    inner ℝ x y = inner ℝ (P1 x) (P1 y) + inner ℝ (P2 x) (P2 y) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add]
  rfl

/-- First phase block. -/
noncomputable def Q1 : Phase (m + k) →L[ℝ] Phase m :=
  (P1.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P1.comp (ContinuousLinearMap.snd ℝ _ _))

/-- Second phase block. -/
noncomputable def Q2 : Phase (m + k) →L[ℝ] Phase k :=
  (P2.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P2.comp (ContinuousLinearMap.snd ℝ _ _))

/-- The coordinate shuffle `Phase m × Phase k → Phase (m + k)`. -/
noncomputable def Ψ (z : Phase m) (w : Phase k) : Phase (m + k) :=
  (appendPos z.1 w.1, appendPos z.2 w.2)

lemma Q1_apply (p : Phase (m + k)) : Q1 p = (P1 p.1, P1 p.2) := rfl
lemma Q2_apply (p : Phase (m + k)) : Q2 p = (P2 p.1, P2 p.2) := rfl

lemma Q1_Ψ (z : Phase m) (w : Phase k) : Q1 (Ψ z w) = z := by
  simp [Q1_apply, Ψ, P1_append]

lemma Q2_Ψ (z : Phase m) (w : Phase k) : Q2 (Ψ z w) = w := by
  simp [Q2_apply, Ψ, P2_append]

lemma Ψ_Q (p : Phase (m + k)) : Ψ (Q1 p) (Q2 p) = p := by
  simp [Q1_apply, Q2_apply, Ψ, append_P]

lemma pI_split (p q : Phase (m + k)) :
    phaseInner p q = phaseInner (Q1 p) (Q1 q) + phaseInner (Q2 p) (Q2 q) := by
  simp only [phaseInner, Q1_apply, Q2_apply, inner_split p.1 q.1, inner_split p.2 q.2]
  ring

lemma Q1_J (p : Phase (m + k)) : Q1 (J p) = J (Q1 p) := by
  simp [Q1_apply, J]

lemma Q2_J (p : Phase (m + k)) : Q2 (J p) = J (Q2 p) := by
  simp [Q2_apply, J]

lemma Q_ext {p q : Phase (m + k)} (h1 : Q1 p = Q1 q) (h2 : Q2 p = Q2 q) : p = q := by
  rw [← Ψ_Q p, ← Ψ_Q q, h1, h2]

end Coord

/-! ## A subgradient inequality for positively homogeneous functions -/

section Subgrad

variable {n : ℕ}

/-- The data of a nonnegative, positively homogeneous function. -/
structure PosHom (g : Phase n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  smul : ∀ (c : ℝ) x, 0 ≤ c → g (c • x) = c * g x

lemma PosHom.zero {g : Phase n → ℝ} (hg : PosHom g) : g 0 = 0 := by
  have := hg.smul 0 0 le_rfl
  simpa using this

lemma PosHom.inner_nonneg {g : Phase n → ℝ} (hg : PosHom g) {a u : Phase n}
    (hN : ∀ a', g a' ≤ g a → phaseInner u (a' - a) ≤ 0) : 0 ≤ phaseInner u a := by
  have := hN 0 (by rw [hg.zero]; exact hg.nonneg a)
  rw [pI_sub_right, pI_comm u 0, pI_zero_left] at this
  linarith

lemma PosHom.inner_le {g : Phase n → ℝ} (hg : PosHom g) {a u : Phase n}
    (hN : ∀ a', g a' ≤ g a → phaseInner u (a' - a) ≤ 0) (hα : 0 < g a) (a' : Phase n) :
    phaseInner u a' ≤ g a' * (phaseInner u a / g a) := by
  have hua := hg.inner_nonneg hN
  rcases (hg.nonneg a').lt_or_eq with hpos | hzero
  · set s := g a / g a' with hs
    have hs0 : 0 < s := div_pos hα hpos
    have hgs : g (s • a') = g a := by
      rw [hg.smul s a' hs0.le, hs, div_mul_cancel₀ _ hpos.ne']
    have := hN (s • a') hgs.le
    rw [pI_sub_right, pI_smul_right] at this
    rw [hs] at this
    rw [mul_div_assoc', le_div_iff₀ hα]
    have h3 : g a / g a' * phaseInner u a' * g a' ≤ phaseInner u a * g a' :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hpos.ne'] at h3
    linarith
  · rw [← hzero, zero_mul]
    by_contra hc
    push Not at hc
    set l := (phaseInner u a + 1) / phaseInner u a' with hl
    have hl0 : 0 ≤ l := by positivity
    have := hN (l • a') (by rw [hg.smul l a' hl0, ← hzero, mul_zero]; exact hα.le)
    rw [pI_sub_right, pI_smul_right, hl, div_mul_cancel₀ _ hc.ne'] at this
    linarith

/-- The subgradient inequality `c ⟨u, a' - a⟩ ≤ g(a')² - g(a)²` at a point `a` where `u` is an outer
normal of the sublevel set `{g ≤ g a}`, provided `u ≠ 0`. -/
lemma PosHom.subgrad {g : Phase n → ℝ} (hg : PosHom g) {a u : Phase n} (hu : u ≠ 0)
    (hN : ∀ a', g a' ≤ g a → phaseInner u (a' - a) ≤ 0) :
    ∃ c : ℝ, ∀ a', c * phaseInner u (a' - a) ≤ g a' ^ 2 - g a ^ 2 := by
  rcases (hg.nonneg a).lt_or_eq with hα | hα
  · set H := phaseInner u a / g a with hH
    have hle := hg.inner_le hN hα
    have hH0 : 0 < H := by
      by_contra hc; push Not at hc
      have h1 := hle u
      have h2 : g u * H ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hg.nonneg u) hc
      have := pI_self_pos hu
      linarith
    refine ⟨2 * g a / H, fun a' => ?_⟩
    have h1 := hle a'
    have haH : phaseInner u a = g a * H := by rw [hH, mul_div_cancel₀ _ hα.ne']
    rw [pI_sub_right, haH]
    have h2 : 2 * g a / H * (phaseInner u a' - g a * H) ≤ 2 * g a / H * (g a' * H - g a * H) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 2 * g a / H * (g a' * H - g a * H) = 2 * g a * (g a' - g a) := by
      field_simp
    nlinarith [sq_nonneg (g a' - g a)]
  · refine ⟨0, fun a' => ?_⟩
    rw [← hα, zero_mul]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    positivity

end Subgrad

/-! ## The p-product and its gauge description -/

section Product

variable {m k : ℕ}

lemma gauge_posHom {n : ℕ} (X : Set (Phase n)) : PosHom (gauge X) :=
  ⟨fun x => gauge_nonneg x, fun c x hc => by rw [gauge_smul_of_nonneg hc, smul_eq_mul]⟩

/-- `g_X(z)² + g_Y(w)²` on `ℝ^{2(m+k)}`. -/
noncomputable def φ (X : Set (Phase m)) (Y : Set (Phase k)) (p : Phase (m + k)) : ℝ :=
  gauge X (Q1 p) ^ 2 + gauge Y (Q2 p) ^ 2

lemma toReal_half : (2 : ℝ≥0∞)⁻¹.toReal = 1 / 2 := by
  rw [ENNReal.toReal_inv]; norm_num

lemma rpow_half_sq {t : ℝ} (ht : 0 ≤ t) : (t ^ (2 : ℝ≥0∞)⁻¹.toReal) ^ 2 = t := by
  rw [toReal_half, ← Real.sqrt_eq_rpow, Real.sq_sqrt ht]

lemma rpow_half_nonneg (t : ℝ) : 0 ≤ t ^ (2 : ℝ≥0∞)⁻¹.toReal := by
  rw [toReal_half, ← Real.sqrt_eq_rpow]; exact Real.sqrt_nonneg _

lemma φ_Ψ (X : Set (Phase m)) (Y : Set (Phase k)) (z : Phase m) (w : Phase k) :
    φ X Y (Ψ z w) = gauge X z ^ 2 + gauge Y w ^ 2 := by
  rw [φ, Q1_Ψ, Q2_Ψ]

lemma φ_smul (X : Set (Phase m)) (Y : Set (Phase k)) {s : ℝ} (hs : 0 ≤ s) (p : Phase (m + k)) :
    φ X Y (s • p) = s ^ 2 * φ X Y p := by
  simp only [φ, map_smul, (gauge_posHom X).smul s _ hs, (gauge_posHom Y).smul s _ hs]
  ring

lemma continuous_φ {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hX0 : X ∈ 𝓝 0)
    (hY : Convex ℝ Y) (hY0 : Y ∈ 𝓝 0) : Continuous (φ X Y) := by
  have h1 := continuous_gauge hX hX0
  have h2 := continuous_gauge hY hY0
  unfold φ
  exact ((h1.comp Q1.continuous).pow 2).add ((h2.comp Q2.continuous).pow 2)

lemma φ_le_one_of_mem {X : Set (Phase m)} {Y : Set (Phase k)} {p : Phase (m + k)}
    (hp : p ∈ symplecticPProduct 2 X Y) : φ X Y p ≤ 1 := by
  simp only [symplecticPProduct, mem_iUnion] at hp
  obtain ⟨t, ht, zw, ⟨hz, hw⟩, rfl⟩ := hp
  obtain ⟨x, hx, hzx⟩ := Set.mem_smul_set.1 hz
  obtain ⟨y, hy, hwy⟩ := Set.mem_smul_set.1 hw
  show φ X Y (Ψ zw.1 zw.2) ≤ 1
  rw [φ_Ψ, ← hzx, ← hwy, (gauge_posHom X).smul _ _ (rpow_half_nonneg _),
    (gauge_posHom Y).smul _ _ (rpow_half_nonneg _), mul_pow, mul_pow,
    rpow_half_sq (by linarith [ht.2]), rpow_half_sq ht.1]
  have gx := gauge_le_one_of_mem hx
  have gy := gauge_le_one_of_mem hy
  have gx0 := gauge_nonneg (s := X) x
  have gy0 := gauge_nonneg (s := Y) y
  have h1 : gauge X x ^ 2 ≤ 1 := by nlinarith
  have h2 : gauge Y y ^ 2 ≤ 1 := by nlinarith
  nlinarith [ht.1, ht.2]

lemma mem_of_φ_lt_one {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hX0 : X ∈ 𝓝 0)
    (hY : Convex ℝ Y) (hY0 : Y ∈ 𝓝 0) {p : Phase (m + k)} (hp : φ X Y p < 1) :
    p ∈ symplecticPProduct 2 X Y := by
  set α := gauge X (Q1 p) with hα
  set β := gauge Y (Q2 p) with hβ
  have hα0 : 0 ≤ α := gauge_nonneg _
  have hβ0 : 0 ≤ β := gauge_nonneg _
  have hp' : α ^ 2 + β ^ 2 < 1 := hp
  set t := β ^ 2 + (1 - α ^ 2 - β ^ 2) / 2 with ht
  have ht0 : 0 ≤ t := by nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  set c1 := (1 - t) ^ (2 : ℝ≥0∞)⁻¹.toReal with hc1
  set c2 := t ^ (2 : ℝ≥0∞)⁻¹.toReal with hc2
  have hc1s : c1 ^ 2 = 1 - t := rpow_half_sq (by linarith)
  have hc2s : c2 ^ 2 = t := rpow_half_sq ht0
  have hc10 : 0 ≤ c1 := rpow_half_nonneg _
  have hc20 : 0 ≤ c2 := rpow_half_nonneg _
  have hαc : α < c1 := by
    by_contra h; push Not at h
    have : c1 ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ hc10 h 2
    nlinarith
  have hβc : β < c2 := by
    by_contra h; push Not at h
    have : c2 ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hc20 h 2
    nlinarith
  have hc1p : 0 < c1 := lt_of_le_of_lt hα0 hαc
  have hc2p : 0 < c2 := lt_of_le_of_lt hβ0 hβc
  have hxX : c1⁻¹ • Q1 p ∈ X := by
    apply setOfPred_gauge_lt_one_subset_self hX (mem_of_mem_nhds hX0) (absorbent_nhds_zero hX0)
    show gauge X (c1⁻¹ • Q1 p) < 1
    rw [(gauge_posHom X).smul _ _ (inv_nonneg.2 hc10), ← hα, inv_mul_lt_iff₀ hc1p, mul_one]
    exact hαc
  have hyY : c2⁻¹ • Q2 p ∈ Y := by
    apply setOfPred_gauge_lt_one_subset_self hY (mem_of_mem_nhds hY0) (absorbent_nhds_zero hY0)
    show gauge Y (c2⁻¹ • Q2 p) < 1
    rw [(gauge_posHom Y).smul _ _ (inv_nonneg.2 hc20), ← hβ, inv_mul_lt_iff₀ hc2p, mul_one]
    exact hβc
  simp only [symplecticPProduct, mem_iUnion]
  refine ⟨t, ⟨ht0, ht1⟩, (Q1 p, Q2 p), ⟨?_, ?_⟩, Ψ_Q p⟩
  · have := smul_mem_smul_set (a := c1) hxX
    rwa [smul_inv_smul₀ hc1p.ne'] at this
  · have := smul_mem_smul_set (a := c2) hyY
    rwa [smul_inv_smul₀ hc2p.ne'] at this

lemma mem_closure_of_φ_le_one {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X)
    (hX0 : X ∈ 𝓝 0) (hY : Convex ℝ Y) (hY0 : Y ∈ 𝓝 0) {p : Phase (m + k)} (hp : φ X Y p ≤ 1) :
    p ∈ closure (symplecticPProduct 2 X Y) := by
  have ht : Tendsto (fun s : ℝ => s • p) (𝓝[<] 1) (𝓝 p) := by
    have : Tendsto (fun s : ℝ => s • p) (𝓝 1) (𝓝 ((1 : ℝ) • p)) :=
      ((continuous_id.smul continuous_const).tendsto 1)
    rw [one_smul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  apply mem_closure_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  apply mem_of_φ_lt_one hX hX0 hY hY0
  rw [φ_smul X Y hs.1.le]
  have h0 : 0 ≤ φ X Y p := by unfold φ; positivity
  have : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
  nlinarith

lemma φ_eq_one_of_frontier {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X)
    (hX0 : X ∈ 𝓝 0) (hY : Convex ℝ Y) (hY0 : Y ∈ 𝓝 0) {p : Phase (m + k)}
    (hp : p ∈ frontier (symplecticPProduct 2 X Y)) : φ X Y p = 1 := by
  have hc := continuous_φ hX hX0 hY hY0
  have h1 : φ X Y p ≤ 1 := by
    have : closure (symplecticPProduct 2 X Y) ⊆ {q | φ X Y q ≤ 1} :=
      closure_minimal (fun q hq => φ_le_one_of_mem hq) (isClosed_le hc continuous_const)
    exact this hp.1
  have h2 : ¬ φ X Y p < 1 := by
    intro hlt
    have : {q | φ X Y q < 1} ⊆ interior (symplecticPProduct 2 X Y) :=
      interior_maximal (fun q hq => mem_of_φ_lt_one hX hX0 hY hY0 hq) (isOpen_lt hc continuous_const)
    exact hp.2 (this hlt)
  push Not at h2
  linarith

lemma normal_ext {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X)
    (hX0 : X ∈ 𝓝 0) (hY : Convex ℝ Y) (hY0 : Y ∈ 𝓝 0) {p u : Phase (m + k)}
    (hu : u ∈ normalCone phaseInner (symplecticPProduct 2 X Y) p) {p' : Phase (m + k)}
    (hp' : φ X Y p' ≤ 1) : phaseInner u (p' - p) ≤ 0 := by
  have hcl : IsClosed {q : Phase (m + k) | phaseInner u (q - p) ≤ 0} := by
    apply isClosed_le _ continuous_const
    have : Continuous (fun q : Phase (m + k) => (u, q - p)) := by fun_prop
    exact continuous_pI.comp this
  exact closure_minimal (fun q hq => hu q hq) hcl (mem_closure_of_φ_le_one hX hX0 hY hY0 hp')

end Product

/-! ## Local calculus lemmas -/

section Calc

lemma lip_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    {K : NNReal} (hh : LipschitzWith K h) {f : ℝ → E} {t : ℝ} (hf : HasDerivAt f 0 t) :
    HasDerivAt (fun s => h (f s)) 0 t := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound K ?_) hf
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [smul_zero, sub_zero, Real.norm_eq_abs]
  have := hh.dist_le_mul (f s) (f t)
  rw [Real.dist_eq, dist_eq_norm] at this
  exact this

lemma squeeze_hasDerivAt {F ℓ1 ℓ2 : ℝ → ℝ} {t : ℝ} (h1 : HasDerivAt ℓ1 0 t) (h2 : HasDerivAt ℓ2 0 t)
    (e1 : ℓ1 t = 0) (e2 : ℓ2 t = 0) (hl : ∀ s, ℓ1 s ≤ F s - F t) (hu : ∀ s, F s - F t ≤ -ℓ2 s) :
    HasDerivAt F 0 t := by
  rw [hasDerivAt_iff_isLittleO] at h1 h2 ⊢
  simp only [e1, e2, smul_zero, sub_zero] at h1 h2
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_)
    (h1.norm_left.add h2.norm_left)
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [smul_zero, sub_zero, Real.norm_eq_abs, one_mul]
  have a1 := hl s
  have a2 := hu s
  rw [abs_le]
  have b1 := abs_nonneg (ℓ1 s)
  have b2 := abs_nonneg (ℓ2 s)
  rw [abs_of_nonneg (by positivity : 0 ≤ |ℓ1 s| + |ℓ2 s|)]
  constructor
  · linarith [neg_abs_le (ℓ1 s)]
  · linarith [neg_abs_le (ℓ2 s)]

/-- The lower bound `ℓ(s) ≤ g(a s)² - g(a t)²` with `ℓ` differentiable at `t` with derivative `0`. -/
lemma lower_bound {n : ℕ} {g : Phase n → ℝ} (hg : PosHom g) {a : ℝ → Phase n} {t : ℝ} {u : Phase n}
    (hu : u ≠ 0) (hd : HasDerivAt a (J u) t)
    (hN : ∀ a', g a' ≤ g (a t) → phaseInner u (a' - a t) ≤ 0) :
    ∃ ℓ : ℝ → ℝ, HasDerivAt ℓ 0 t ∧ ℓ t = 0 ∧ ∀ s, ℓ s ≤ g (a s) ^ 2 - g (a t) ^ 2 := by
  obtain ⟨c, hc⟩ := hg.subgrad hu hN
  refine ⟨fun s => c * pIL u (a s - a t), ?_, by simp, fun s => ?_⟩
  · have h := ((pIL u).hasFDerivAt.comp_hasDerivAt t (hd.sub_const (a t))).const_mul c
    refine h.congr_deriv ?_
    simp only [pIL_apply]
    rw [pI_comm, pI_J_self, mul_zero]
  · simp only [pIL_apply]
    rw [pI_comm]; exact hc _

lemma hasDerivAt_sq_of_zero {n : ℕ} {X : Set (Phase n)} (hX : Convex ℝ X) (hX0 : X ∈ 𝓝 0)
    {a : ℝ → Phase n} {t : ℝ} (hd : HasDerivAt a 0 t) :
    HasDerivAt (fun s => gauge X (a s) ^ 2) 0 t := by
  obtain ⟨K, hK⟩ := hX.lipschitz_gauge hX0
  have h := lip_hasDerivAt_zero (h := gauge X) hK hd
  have := (hasDerivAt_pow 2 (gauge X (a t))).comp t h
  simpa [Function.comp_def] using this

/-- If `dist (f x) (f y) ≤ K dist (g x) (g y)` and `g` is absolutely continuous, so is `f`. -/
lemma ac_of_dist_le {f g : ℝ → ℝ} {K : ℝ} {a b : ℝ} (hK : 0 ≤ K)
    (h : ∀ x y, dist (f x) (f y) ≤ K * dist (g x) (g y))
    (hg : AbsolutelyContinuousOnInterval g a b) : AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h'⟩ := hg (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := h' E hE hsum
  calc ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, K * dist (g (E.2 i).1) (g (E.2 i).2) :=
        Finset.sum_le_sum (fun i _ => h _ _)
    _ = K * ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by
        gcongr; linarith
    _ = ε := by field_simp

/-- A periodic function constant on `[0, 1]` is constant. -/
lemma periodic_const {β : Type*} {F : ℝ → β} (hF : Function.Periodic F 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, F t = F 0) (s : ℝ) : F s = F 0 := by
  have h1 : F (s - (⌊s⌋ : ℝ) * 1) = F s := hF.sub_int_mul_eq ⌊s⌋
  rw [← h1]
  apply h
  rw [mul_one]
  exact ⟨sub_nonneg.2 (Int.floor_le s), (sub_lt_iff_lt_add'.2 (Int.lt_floor_add_one s)).le⟩

end Calc

/-! ## Reduced data: the two components of a characteristic of the p-product -/

section Red

variable {m k : ℕ}

/-- Normality at `(a, b)` of `(n1, n2)` with respect to `{g_X² + g_Y² ≤ 1}`. -/
def NC (X : Set (Phase m)) (Y : Set (Phase k)) (a : Phase m) (b : Phase k) (n1 : Phase m)
    (n2 : Phase k) : Prop :=
  ∀ a' b', gauge X a' ^ 2 + gauge Y b' ^ 2 ≤ 1 → phaseInner n1 (a' - a) + phaseInner n2 (b' - b) ≤ 0

lemma NC.swap {X : Set (Phase m)} {Y : Set (Phase k)} {a : Phase m} {b : Phase k} {n1 : Phase m}
    {n2 : Phase k} (h : NC X Y a b n1 n2) : NC Y X b a n2 n1 := by
  intro b' a' hs
  have := h a' b' (by linarith)
  linarith

lemma NC.fst {X : Set (Phase m)} {Y : Set (Phase k)} {a : Phase m} {b : Phase k} {n1 : Phase m}
    {n2 : Phase k} (h : NC X Y a b n1 n2) (hs : gauge X a ^ 2 + gauge Y b ^ 2 = 1) :
    ∀ a', gauge X a' ≤ gauge X a → phaseInner n1 (a' - a) ≤ 0 := by
  intro a' ha'
  have h0 := gauge_nonneg (s := X) a'
  have := h a' b (by nlinarith)
  rwa [sub_self, pI_comm n2 0, pI_zero_left, add_zero] at this

/-- The reduced data of a characteristic of `X ⊗₂ Y`. -/
structure Red (X : Set (Phase m)) (Y : Set (Phase k)) (a : ℝ → Phase m) (b : ℝ → Phase k)
    (va : ℝ → Phase m) (vb : ℝ → Phase k) : Prop where
  cX : Convex ℝ X
  nX : X ∈ 𝓝 0
  cY : Convex ℝ Y
  nY : Y ∈ 𝓝 0
  pa : Function.Periodic a 1
  pb : Function.Periodic b 1
  ia : LocallyIntegrable va volume
  ib : LocallyIntegrable vb volume
  fa : ∀ s t, a t - a s = ∫ x in s..t, va x
  fb : ∀ s t, b t - b s = ∫ x in s..t, vb x
  sph : ∀ t, gauge X (a t) ^ 2 + gauge Y (b t) ^ 2 = 1
  nc : ∀ᵐ t, ∃ n1 n2, va t = J n1 ∧ vb t = J n2 ∧ NC X Y (a t) (b t) n1 n2

variable {X : Set (Phase m)} {Y : Set (Phase k)} {a : ℝ → Phase m} {b : ℝ → Phase k}
  {va : ℝ → Phase m} {vb : ℝ → Phase k}

lemma Red.swap (H : Red X Y a b va vb) : Red Y X b a vb va where
  cX := H.cY
  nX := H.nY
  cY := H.cX
  nY := H.nX
  pa := H.pb
  pb := H.pa
  ia := H.ib
  ib := H.ia
  fa := H.fb
  fb := H.fa
  sph := fun t => by linarith [H.sph t]
  nc := by
    filter_upwards [H.nc] with t ⟨n1, n2, h1, h2, hN⟩
    exact ⟨n2, n1, h2, h1, hN.swap⟩

lemma Red.vI (H : Red X Y a b va vb) (s t : ℝ) : IntervalIntegrable va volume s t :=
  (H.ia.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

lemma Red.a_eq (H : Red X Y a b va vb) : a = fun x => a 0 + ∫ s in (0 : ℝ)..x, va s := by
  funext x; rw [← H.fa 0 x]; abel

lemma Red.cont (H : Red X Y a b va vb) : Continuous a := by
  rw [H.a_eq]
  exact continuous_const.add (intervalIntegral.continuous_primitive H.vI 0)

lemma Red.hderiv (H : Red X Y a b va vb) : ∀ᵐ x, HasDerivAt a (va x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral H.ia] with x hx
  rw [H.a_eq]
  simpa using (hx 0).const_add (a 0)

/-- The key local statement: `g_X(a)²` has derivative `0` at a.e. time. -/
lemma Red.hasDerivAt_F (H : Red X Y a b va vb) {t : ℝ} (hda : HasDerivAt a (va t) t)
    (hdb : HasDerivAt b (vb t) t) {n1 : Phase m} {n2 : Phase k} (h1 : va t = J n1)
    (h2 : vb t = J n2) (hN : NC X Y (a t) (b t) n1 n2) :
    HasDerivAt (fun s => gauge X (a s) ^ 2) 0 t := by
  have hFG : (fun s => gauge X (a s) ^ 2) = fun s => 1 - gauge Y (b s) ^ 2 := by
    funext s; linarith [H.sph s]
  by_cases hn1 : n1 = 0
  · rw [h1, hn1, J_zero] at hda
    exact hasDerivAt_sq_of_zero H.cX H.nX hda
  by_cases hn2 : n2 = 0
  · rw [h2, hn2, J_zero] at hdb
    rw [hFG]
    simpa using (hasDerivAt_sq_of_zero H.cY H.nY hdb).const_sub 1
  rw [h1] at hda
  rw [h2] at hdb
  obtain ⟨ℓ1, d1, e1, l1⟩ := lower_bound (gauge_posHom X) hn1 hda (hN.fst (H.sph t))
  obtain ⟨ℓ2, d2, e2, l2⟩ := lower_bound (gauge_posHom Y) hn2 hdb (hN.swap.fst (H.swap.sph t))
  refine squeeze_hasDerivAt d1 d2 e1 e2 l1 (fun s => ?_)
  have := l2 s
  have a1 := H.sph s
  have a2 := H.sph t
  linarith

lemma Red.ac_F (H : Red X Y a b va vb) :
    AbsolutelyContinuousOnInterval (fun s => gauge X (a s) ^ 2) 0 1 := by
  obtain ⟨L, hL⟩ := H.cX.lipschitz_gauge H.nX
  set N : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, ‖va s‖ with hN
  have hNac : AbsolutelyContinuousOnInterval N 0 1 :=
    (H.vI 0 1).norm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hf : AbsolutelyContinuousOnInterval (fun s => gauge X (a s)) 0 1 := by
    refine ac_of_dist_le (K := L) L.2 (fun x y => ?_) hNac
    calc dist (gauge X (a x)) (gauge X (a y)) ≤ L * dist (a x) (a y) := hL.dist_le_mul _ _
      _ ≤ L * dist (N x) (N y) := by
        gcongr
        rw [dist_eq_norm, H.fa y x, Real.dist_eq]
        show _ ≤ |(∫ s in (0 : ℝ)..x, ‖va s‖) - ∫ s in (0 : ℝ)..y, ‖va s‖|
        rw [
          intervalIntegral.integral_interval_sub_left (H.vI 0 x).norm (H.vI 0 y).norm]
        exact intervalIntegral.norm_integral_le_abs_integral_norm
  have := hf.mul hf
  convert this using 1
  funext s
  simp [pow_two]

lemma Red.F_const (H : Red X Y a b va vb) (t : ℝ) : gauge X (a t) = gauge X (a 0) := by
  have hder : ∀ᵐ x, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (fun s => gauge X (a s) ^ 2) 0 x := by
    filter_upwards [H.hderiv, H.swap.hderiv, H.nc] with x hda hdb ⟨n1, n2, h1, h2, hN⟩ _
    exact H.hasDerivAt_F hda hdb h1 h2 hN
  obtain ⟨C, hC⟩ := H.ac_F.const_of_ae_hasDerivAt_zero hder
  have hper : Function.Periodic (fun s => gauge X (a s) ^ 2) 1 := fun s => by
    simp only [H.pa s]
  have h01 : ∀ s ∈ Icc (0 : ℝ) 1, gauge X (a s) ^ 2 = gauge X (a 0) ^ 2 := by
    intro s hs
    rw [hC s (by simpa using hs), hC 0 (by simp)]
  have := periodic_const hper h01 t
  exact (pow_left_inj₀ (gauge_nonneg _) (gauge_nonneg _) two_ne_zero).1 this


/-- Half the integral of `⟨J a, v⟩` over a period. -/
noncomputable def Aint {n : ℕ} (a v : ℝ → Phase n) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..1, phaseInner (J (a t)) (v t)

lemma Red.A_nonneg (H : Red X Y a b va vb) : 0 ≤ Aint a va := by
  unfold Aint
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg_of_ae zero_le_one
  filter_upwards [H.nc] with t ⟨n1, n2, h1, h2, hN⟩
  rw [Pi.zero_apply, h1, pI_J_J, pI_comm]
  exact (gauge_posHom X).inner_nonneg (hN.fst (H.sph t))

lemma Red.intI (H : Red X Y a b va vb) :
    IntervalIntegrable (fun t => phaseInner (J (a t)) (va t)) volume 0 1 := by
  have hJc : Continuous (fun t => J (a t)) := by
    have := H.cont; unfold J; fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hJc.continuousOn
  refine ((H.vI 0 1).norm.const_mul (2 * C)).mono_fun' ?_ ?_
  · rw [uIoc_of_le zero_le_one]
    exact Continuous.comp_aestronglyMeasurable₂ (g := fun x y : Phase m => phaseInner x y)
      (by unfold phaseInner; fun_prop) hJc.aestronglyMeasurable (H.vI 0 1).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have h1 := abs_pI_le (J (a t)) (va t)
    have h2 := hC t (Ioc_subset_Icc_self ht)
    rw [Real.norm_eq_abs]
    have := norm_nonneg (va t)
    nlinarith

lemma Red.gcc (H : Red X Y a b va vb) (hα : 0 < gauge X (a 0)) :
    IsGeneralizedClosedCharacteristic X (fun t => (gauge X (a 0))⁻¹ • a t) := by
  set α := gauge X (a 0) with hαdef
  refine ⟨fun t => by simp only [H.pa t], fun t => ?_, fun t => α⁻¹ • va t, H.ia.smul α⁻¹,
    fun s t => ?_, ?_⟩
  · rw [← gauge_eq_one_iff_mem_frontier H.cX H.nX, (gauge_posHom X).smul _ _ (inv_nonneg.2 hα.le),
      H.F_const t, inv_mul_cancel₀ hα.ne']
  · rw [← smul_sub, H.fa s t, intervalIntegral.integral_smul]
  · filter_upwards [H.nc] with t ⟨n1, n2, h1, h2, hN⟩
    refine ⟨α⁻¹ • n1, fun y hy => ?_, by rw [h1, J_smul]⟩
    have hN1 := hN.fst (H.sph t) (α • y) (by
      rw [(gauge_posHom X).smul _ _ hα.le, H.F_const t]
      have := gauge_le_one_of_mem hy
      nlinarith)
    rw [show y - α⁻¹ • a t = α⁻¹ • (α • y - a t) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hα.ne', one_smul], pI_smul_left, pI_smul_right]
    have : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
    have := mul_nonpos_of_nonneg_of_nonpos this hN1
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hα.le) this

lemma Red.action_x (H : Red X Y a b va vb) (hα : 0 < gauge X (a 0)) :
    action (fun t => (gauge X (a 0))⁻¹ • a t) = (gauge X (a 0) ^ 2)⁻¹ * Aint a va := by
  set α := gauge X (a 0) with hαdef
  unfold action Aint
  have : ∫ t in (0 : ℝ)..1, phaseInner (J (α⁻¹ • a t)) (_root_.deriv (fun t => α⁻¹ • a t) t) =
      ∫ t in (0 : ℝ)..1, (α⁻¹ * α⁻¹) * phaseInner (J (a t)) (va t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [H.hderiv] with t hd _
    have hd' : HasDerivAt (fun t => α⁻¹ • a t) (α⁻¹ • va t) t := hd.const_smul α⁻¹
    rw [hd'.deriv, J_smul, pI_smul_left, pI_smul_right]
    ring
  rw [this, intervalIntegral.integral_const_mul]
  field_simp

lemma Red.const_b (H : Red X Y a b va vb) (hac : ∀ t, a t = a 0) (hα : 0 < gauge X (a 0)) :
    ∀ t, b t = b 0 := by
  have hvb : ∀ᵐ t, vb t = 0 := by
    filter_upwards [H.hderiv, H.nc] with t hda ⟨n1, n2, h1, h2, hN⟩
    have hconst : a = fun _ => a 0 := funext hac
    have hd0 : HasDerivAt a 0 t := by rw [hconst]; exact hasDerivAt_const t (a 0)
    have hn1 : n1 = 0 := J_eq_zero (h1 ▸ hda.unique hd0)
    rw [h2]
    suffices n2 = 0 by rw [this, J_zero]
    by_contra hn2
    set β := gauge Y (b t) with hβ
    have hβ0 : 0 ≤ β := gauge_nonneg _
    have hs := H.sph t
    rw [hac t] at hs
    have hβ1 : β < 1 := by nlinarith
    set G := gauge Y n2 with hG
    have hG0 : 0 ≤ G := gauge_nonneg _
    set ε := (1 - β) / (G + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have hεG : ε * (G + 1) = 1 - β := by rw [hε]; field_simp
    have hb' : gauge Y (b t + ε • n2) ≤ 1 := by
      have := gauge_add_le H.cY (absorbent_nhds_zero H.nY) (b t) (ε • n2)
      rw [(gauge_posHom Y).smul _ _ hε0.le] at this
      nlinarith
    have hb'0 : 0 ≤ gauge Y (b t + ε • n2) := gauge_nonneg _
    have := hN 0 (b t + ε • n2) (by rw [(gauge_posHom X).zero]; nlinarith)
    rw [hn1, pI_zero_left, zero_add, add_sub_cancel_left, pI_smul_right] at this
    have := mul_pos hε0 (pI_self_pos hn2)
    linarith
  intro t
  have := H.fb 0 t
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : Phase k))
    (hvb.mono fun x hx _ => hx), intervalIntegral.integral_zero] at this
  exact sub_eq_zero.1 this

lemma Red.nonconst_a (H : Red X Y a b va vb) (hnc : (∃ s t, a s ≠ a t) ∨ (∃ s t, b s ≠ b t))
    (hα : 0 < gauge X (a 0)) : ∃ s t, a s ≠ a t := by
  by_contra h
  push Not at h
  have hac : ∀ t, a t = a 0 := fun t => h t 0
  have hbc := H.const_b hac hα
  rcases hnc with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · exact hst (h s t)
  · exact hst ((hbc s).trans (hbc t).symm)

lemma Red.cEHZ_le (H : Red X Y a b va vb) (hnc : (∃ s t, a s ≠ a t) ∨ (∃ s t, b s ≠ b t))
    (hα : 0 < gauge X (a 0)) :
    cEHZ X ≤ ENNReal.ofReal ((gauge X (a 0) ^ 2)⁻¹ * Aint a va) := by
  obtain ⟨s, t, hst⟩ := H.nonconst_a hnc hα
  have hne : (fun t => (gauge X (a 0))⁻¹ • a t) s ≠ (fun t => (gauge X (a 0))⁻¹ • a t) t := by
    intro h
    apply hst
    have := congrArg (fun z => gauge X (a 0) • z) h
    simpa [smul_smul, mul_inv_cancel₀ hα.ne'] using this
  refine (iInf₂_le (fun t => (gauge X (a 0))⁻¹ • a t) ⟨H.gcc hα, s, t, hne⟩).trans ?_
  rw [H.action_x hα, abs_of_nonneg (mul_nonneg (by positivity) H.A_nonneg)]

lemma final_arith {cX cY : ℝ≥0∞} {α β A1 A2 : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hs : α ^ 2 + β ^ 2 = 1) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (c1 : 0 < α → cX ≤ ENNReal.ofReal ((α ^ 2)⁻¹ * A1))
    (c2 : 0 < β → cY ≤ ENNReal.ofReal ((β ^ 2)⁻¹ * A2)) :
    min cX cY ≤ ENNReal.ofReal (A1 + A2) := by
  set M := min cX cY with hM
  have hMt : M ≠ ⊤ := by
    rcases hα0.lt_or_eq with h | h
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_left cX cY).trans (c1 h))
    · have hβ : 0 < β := by
        rcases hβ0.lt_or_eq with h' | h'
        · exact h'
        · rw [← h, ← h'] at hs; norm_num at hs
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_right cX cY).trans (c2 hβ))
  set μ := M.toReal with hμ
  have hμ0 : 0 ≤ μ := ENNReal.toReal_nonneg
  have hMμ : M = ENNReal.ofReal μ := (ENNReal.ofReal_toReal hMt).symm
  have k1 : α ^ 2 * μ ≤ A1 := by
    rcases hα0.lt_or_eq with h | h
    · have : M ≤ _ := (min_le_left cX cY).trans (c1 h)
      rw [hMμ, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      have hα2 : 0 < α ^ 2 := by positivity
      rw [inv_mul_eq_div, le_div_iff₀ hα2] at this
      linarith
    · rw [← h]; simpa using hA1
  have k2 : β ^ 2 * μ ≤ A2 := by
    rcases hβ0.lt_or_eq with h | h
    · have : M ≤ _ := (min_le_right cX cY).trans (c2 h)
      rw [hMμ, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      have hβ2 : 0 < β ^ 2 := by positivity
      rw [inv_mul_eq_div, le_div_iff₀ hβ2] at this
      linarith
    · rw [← h]; simpa using hA2
  rw [hMμ]
  apply ENNReal.ofReal_le_ofReal
  have : μ = α ^ 2 * μ + β ^ 2 * μ := by rw [← add_mul, hs, one_mul]
  linarith

lemma Red.main (H : Red X Y a b va vb) (hnc : (∃ s t, a s ≠ a t) ∨ (∃ s t, b s ≠ b t)) :
    min (cEHZ X) (cEHZ Y) ≤ ENNReal.ofReal (Aint a va + Aint b vb) := by
  have hs := H.sph 0
  exact final_arith (gauge_nonneg _) (gauge_nonneg _) hs H.A_nonneg H.swap.A_nonneg
    (H.cEHZ_le hnc) (H.swap.cEHZ_le hnc.symm)

end Red

/-! ## The main theorem -/

lemma clm_locallyIntegrable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {v : ℝ → E}
    (hv : LocallyIntegrable v volume) : LocallyIntegrable (fun t => L (v t)) volume := by
  refine (hv.smul ‖L‖).mono (L.continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t => ?_))
  rw [Pi.smul_apply, norm_smul, norm_norm]
  exact L.le_opNorm (v t)

lemma red_of_gcc {m k : ℕ} {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X)
    (nX : X ∈ 𝓝 0) (hY : Convex ℝ Y) (nY : Y ∈ 𝓝 0) {γ v : ℝ → Phase (m + k)}
    (hper : Function.Periodic γ 1) (hfr : ∀ t, γ t ∈ frontier (symplecticPProduct 2 X Y))
    (hvint : LocallyIntegrable v volume) (hftc : ∀ a b, γ b - γ a = ∫ s in a..b, v s)
    (hae : ∀ᵐ t, v t ∈ J '' normalCone phaseInner (symplecticPProduct 2 X Y) (γ t)) :
    Red X Y (fun t => Q1 (γ t)) (fun t => Q2 (γ t)) (fun t => Q1 (v t)) (fun t => Q2 (v t)) := by
  have hvI : ∀ a b : ℝ, IntervalIntegrable v volume a b := fun a b =>
    (hvint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  refine ⟨hX, nX, hY, nY, fun t => by simp only [hper t], fun t => by simp only [hper t],
    clm_locallyIntegrable Q1 hvint, clm_locallyIntegrable Q2 hvint, fun s t => ?_, fun s t => ?_,
    fun t => φ_eq_one_of_frontier hX nX hY nY (hfr t), ?_⟩
  · rw [← map_sub, hftc s t, Q1.intervalIntegral_comp_comm (hvI s t)]
  · rw [← map_sub, hftc s t, Q2.intervalIntegral_comp_comm (hvI s t)]
  · filter_upwards [hae] with t ⟨u, hu, hut⟩
    refine ⟨Q1 u, Q2 u, by rw [← hut, Q1_J], by rw [← hut, Q2_J], fun a' b' h => ?_⟩
    have := normal_ext hX nX hY nY hu (p' := Ψ a' b') (by rw [φ_Ψ]; exact h)
    rwa [pI_split, map_sub, map_sub, Q1_Ψ, Q2_Ψ] at this

theorem min_le_cEHZ_pprod_of_interior {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y)
    (hX0 : 0 ∈ interior X) (hY0 : 0 ∈ interior Y) :
    min (cEHZ X) (cEHZ Y) ≤ cEHZ (symplecticPProduct 2 X Y) := by
  have nX : X ∈ 𝓝 0 := mem_interior_iff_mem_nhds.1 hX0
  have nY : Y ∈ 𝓝 0 := mem_interior_iff_mem_nhds.1 hY0
  refine le_iInf₂ (fun γ hγ => ?_)
  obtain ⟨⟨hper, hfr, v, hvint, hftc, hae⟩, hnc⟩ := hγ
  have H := red_of_gcc hX.2.1 nX hY.2.1 nY hper hfr hvint hftc hae
  have hderiv : ∀ᵐ x, HasDerivAt γ (v x) x := by
    have hγeq : γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
      funext x; rw [← hftc 0 x]; abel
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hvint] with x hx
    rw [hγeq]
    simpa using (hx 0).const_add (γ 0)
  have hact : action γ = Aint (fun t => Q1 (γ t)) (fun t => Q1 (v t)) +
      Aint (fun t => Q2 (γ t)) (fun t => Q2 (v t)) := by
    unfold action Aint
    rw [← mul_add, ← intervalIntegral.integral_add H.intI H.swap.intI]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx _
    rw [hx.deriv, pI_split, Q1_J, Q2_J]
  have hnc' : (∃ s t, Q1 (γ s) ≠ Q1 (γ t)) ∨ (∃ s t, Q2 (γ s) ≠ Q2 (γ t)) := by
    by_contra h
    push Not at h
    obtain ⟨s, t, hst⟩ := hnc
    exact hst (Q_ext (h.1 s t) (h.2 s t))
  rw [hact, abs_of_nonneg (add_nonneg H.A_nonneg H.swap.A_nonneg)]
  exact H.main hnc'

end Viterbo.PP2.PartL
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
/-!
# Part V: `(m+k)! Vol(X ⊗₂ Y) = m! Vol X · k! Vol Y`

Route: the symplectic 2-product is the image of `Zs X Y = ⋃ t, (√(1-t) X) × (√t Y)` under a
volume-preserving coordinate permutation `Ψ`. For a measurable star-shaped `K` in a space of real
dimension `2n`, `∫ ρ{s | x ∈ √s K} dx = n! Vol K` with `ρ = e^{-s} ds` on `(0, ∞)` (Tonelli), and
the integrand factorizes over `Zs X Y` (the "gauge squared" of a 2-product is the sum of the gauges
squared). This gives the identity for compact star-shaped sets; convex domains containing `0` are
sandwiched between compact star-shaped sets of almost the same volume.
-/
/-! ## The coordinate permutation `Ψ` is volume preserving -/
@[simp] theorem appendPos_castAdd' {m k : ℕ} (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

@[simp] theorem appendPos_natAdd' {m k : ℕ} (x : Position m) (y : Position k) (j : Fin k) :
    appendPos x y (Fin.natAdd m j) = y j := by
  simp [appendPos]

theorem append_mp (m k : ℕ) :
    MeasurePreserving (fun xy : Position m × Position k => appendPos xy.1 xy.2)
      (volume.prod volume) volume := by
  have h1 := (PiLp.volume_preserving_ofLp (Fin m)).prod (PiLp.volume_preserving_ofLp (Fin k))
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin k => ℝ)
  have h3 := volume_measurePreserving_piCongrLeft (fun _ : Fin (m + k) => ℝ) finSumFinEquiv
  have h4 := PiLp.volume_preserving_toLp (Fin (m + k))
  have := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun xy : Position m × Position k => appendPos xy.1 xy.2) =
      (WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm ∘ Prod.map WithLp.ofLp WithLp.ofLp) := by
    funext xy
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [appendPos_castAdd', Function.comp_apply]
      rw [← finSumFinEquiv_apply_left, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      rfl
    · simp only [appendPos_natAdd', Function.comp_apply]
      rw [← finSumFinEquiv_apply_right, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      rfl
  rw [heq]
  exact this

theorem shuffle_mp {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have e3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have e4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have e5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  have := e5.comp (e4.comp (e3.comp (e2.comp e1)))
  exact this

theorem appendPos_add' {m k : ℕ} (x x' : Position m) (y y' : Position k) :
    appendPos (x + x') (y + y') = appendPos x y + appendPos x' y' := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_smul' {m k : ℕ} (c : ℝ) (x : Position m) (y : Position k) :
    appendPos (c • x) (c • y) = c • appendPos x y := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_bij' {m k : ℕ} : Function.Bijective
    (fun xy : Position m × Position k => appendPos xy.1 xy.2) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only at h
    have h1 : x = x' := by
      ext i
      have := congrArg (fun z : Position (m + k) => z (Fin.castAdd k i)) h
      simpa using this
    have h2 : y = y' := by
      ext j
      have := congrArg (fun z : Position (m + k) => z (Fin.natAdd m j)) h
      simpa using this
    rw [h1, h2]
  · intro z
    refine ⟨((WithLp.equiv 2 _).symm (fun i => z (Fin.castAdd k i)),
      (WithLp.equiv 2 _).symm (fun j => z (Fin.natAdd m j))), ?_⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

noncomputable def appendLin (m k : ℕ) : (Position m × Position k) →ₗ[ℝ] Position (m + k) where
  toFun xy := appendPos xy.1 xy.2
  map_add' a b := appendPos_add' a.1 b.1 a.2 b.2
  map_smul' c a := appendPos_smul' c a.1 a.2

noncomputable def appendL (m k : ℕ) : (Position m × Position k) ≃L[ℝ] Position (m + k) :=
  (LinearEquiv.ofBijective (appendLin m k) appendPos_bij').toContinuousLinearEquiv

noncomputable def PsiL (m k : ℕ) : (Phase m × Phase k) ≃L[ℝ] Phase (m + k) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ (Position m) (Position m) (Position k)
    (Position k)).trans ((appendL m k).prodCongr (appendL m k))

noncomputable def PsiE (m k : ℕ) : (Phase m × Phase k) ≃ᵐ Phase (m + k) :=
  (PsiL m k).toHomeomorph.toMeasurableEquiv

theorem PsiE_coe (m k : ℕ) : (⇑(PsiE m k) : Phase m × Phase k → Phase (m + k)) =
    fun zw => (appendPos zw.1.1 zw.2.1, appendPos zw.1.2 zw.2.2) := rfl

theorem PsiE_mp (m k : ℕ) : MeasurePreserving (PsiE m k) (volume.prod volume) volume := by
  rw [PsiE_coe]
  have := ((append_mp m k).prod (append_mp m k)).comp
    (shuffle_mp (volume : Measure (Position m)) (volume : Measure (Position m))
      (volume : Measure (Position k)) (volume : Measure (Position k)))
  exact this

theorem volume_image_Psi (m k : ℕ) (Z : Set (Phase m × Phase k)) :
    volume ((fun zw : Phase m × Phase k => (appendPos zw.1.1 zw.2.1, appendPos zw.1.2 zw.2.2)) '' Z)
      = (volume.prod volume) Z := by
  rw [← PsiE_coe, MeasurableEquiv.image_eq_preimage_symm]
  exact ((PsiE_mp m k).symm _).measure_preimage_equiv Z

/-! ## The exponential-gauge computation -/
noncomputable def rho : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (Real.exp (-s)))

theorem rho_apply (T : Set ℝ) :
    rho T = ∫⁻ s in T ∩ Ioi 0, ENNReal.ofReal (Real.exp (-s)) := by
  rw [rho, withDensity_apply', Measure.restrict_restrict' measurableSet_Ioi]

theorem setLIntegral_exp_Ioi {γ : ℝ} :
    ∫⁻ s in Ioi γ, ENNReal.ofReal (Real.exp (-s)) = ENNReal.ofReal (Real.exp (-γ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi γ)
    (Eventually.of_forall (fun s => (Real.exp_pos _).le)), integral_exp_neg_Ioi]

theorem rho_eq {T : Set ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h1 : Ioi γ ⊆ T) (h2 : T ∩ Ioi 0 ⊆ Ici γ) :
    rho T = ENNReal.ofReal (Real.exp (-γ)) := by
  rw [rho_apply]
  apply le_antisymm
  · calc _ ≤ ∫⁻ s in Ici γ, ENNReal.ofReal (Real.exp (-s)) := lintegral_mono_set h2
      _ = ∫⁻ s in Ioi γ, ENNReal.ofReal (Real.exp (-s)) :=
          setLIntegral_congr Ioi_ae_eq_Ici.symm
      _ = _ := setLIntegral_exp_Ioi
  · rw [← setLIntegral_exp_Ioi]
    apply lintegral_mono_set
    intro s hs
    exact ⟨h1 hs, lt_of_le_of_lt hγ hs⟩

theorem rho_zero {T : Set ℝ} (h : T ∩ Ioi 0 = ∅) : rho T = 0 := by
  rw [rho_apply, h, Measure.restrict_empty, lintegral_zero_measure]

instance : SFinite rho := by unfold rho; infer_instance

theorem lintegral_pow_exp (n : ℕ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (s ^ n) =
      (n.factorial : ℝ≥0∞) := by
  have hG := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at hG
  have hconv := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hG hconv
  rw [← ENNReal.ofReal_natCast, hG, ofReal_integral_eq_lintegral_ofReal hconv]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_of_lt hs) _)

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem measurableSet_W {K : Set V} (hK : MeasurableSet K) :
    MeasurableSet {p : V × ℝ | (√p.2)⁻¹ • p.1 ∈ K} := by
  have : Measurable (fun p : V × ℝ => (√p.2)⁻¹ • p.1) := by
    apply Measurable.smul
    · exact (Real.continuous_sqrt.measurable.comp measurable_snd).inv
    · exact measurable_fst
  exact this hK

theorem tonelli (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ}
    (hd : Module.finrank ℝ V = 2 * n) {K : Set V} (hK : MeasurableSet K) :
    ∫⁻ x, rho {s | (√s)⁻¹ • x ∈ K} ∂μ = (n.factorial : ℝ≥0∞) * μ K := by
  have hW := measurableSet_W hK
  have h1 : ∫⁻ x, rho {s | (√s)⁻¹ • x ∈ K} ∂μ = (μ.prod rho) {p : V × ℝ | (√p.2)⁻¹ • p.1 ∈ K} :=
    (Measure.prod_apply hW).symm
  rw [h1, Measure.prod_apply_symm hW, rho,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_right hW)]
  have h2 : ∀ s ∈ Ioi (0 : ℝ), ((fun s => ENNReal.ofReal (Real.exp (-s))) *
      fun y => μ ((fun x => (x, y)) ⁻¹' {p : V × ℝ | (√p.2)⁻¹ • p.1 ∈ K})) s =
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (s ^ n) * μ K := by
    intro s hs
    have hs' : (0 : ℝ) < √s := Real.sqrt_pos.mpr hs
    have hset : ((fun x => (x, s)) ⁻¹' {p : V × ℝ | (√p.2)⁻¹ • p.1 ∈ K}) = √s • K := by
      ext x
      simp [mem_smul_set_iff_inv_smul_mem₀ hs'.ne']
    simp only [Pi.mul_apply]
    rw [hset, Measure.addHaar_smul, hd, abs_of_pos (pow_pos hs' _), pow_mul, Real.sq_sqrt (le_of_lt hs),
      mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_mul_const _ (by fun_prop),
    lintegral_pow_exp]

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
open scoped Classical
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Star-shaped about `0`, containing `0`. -/
def IsStar (X : Set V) : Prop := (0 : V) ∈ X ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ x ∈ X, c • x ∈ X

/-- The scales `u > 0` with `x ∈ √u • X`. -/
def Asc (X : Set V) (x : V) : Set ℝ := {u | 0 < u ∧ (√u)⁻¹ • x ∈ X}

theorem Asc_up {X : Set V} (hX : IsStar X) {x : V} {u u' : ℝ} (hu : u ∈ Asc X x) (h : u ≤ u') :
    u' ∈ Asc X x := by
  have hu0 := hu.1
  have hu'0 : 0 < u' := lt_of_lt_of_le hu0 h
  have hs : 0 < √u := Real.sqrt_pos.mpr hu0
  have hs' : 0 < √u' := Real.sqrt_pos.mpr hu'0
  refine ⟨hu'0, ?_⟩
  have hc1 : √u / √u' ≤ 1 := (div_le_one hs').mpr (Real.sqrt_le_sqrt h)
  have := hX.2 (√u / √u') (by positivity) hc1 _ hu.2
  rw [smul_smul] at this
  convert this using 2
  field_simp

theorem Asc_bdd (X : Set V) (x : V) : BddBelow (Asc X x) := ⟨0, fun _ hu => hu.1.le⟩

theorem Asc_sInf_nonneg (X : Set V) (x : V) : 0 ≤ sInf (Asc X x) :=
  Real.sInf_nonneg (fun _ hu => hu.1.le)

theorem Asc_Ioi {X : Set V} (hX : IsStar X) {x : V} (hne : (Asc X x).Nonempty) :
    Ioi (sInf (Asc X x)) ⊆ Asc X x := by
  intro s hs
  obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hne hs
  exact Asc_up hX hu hus.le

theorem Asc_ge {X : Set V} {x : V} {u : ℝ} (hu : u ∈ Asc X x) : sInf (Asc X x) ≤ u :=
  csInf_le (Asc_bdd X x) hu

theorem rho_T {X : Set V} (hX : IsStar X) (x : V) :
    rho {s | (√s)⁻¹ • x ∈ X} =
      if (Asc X x).Nonempty then ENNReal.ofReal (Real.exp (-sInf (Asc X x))) else 0 := by
  split_ifs with hne
  · apply rho_eq (Asc_sInf_nonneg X x)
    · intro s hs
      exact (Asc_Ioi hX hne hs).2
    · rintro s ⟨hs, hs0⟩
      exact Asc_ge ⟨hs0, hs⟩
  · apply rho_zero
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    intro hs hs0
    exact hne ⟨s, hs0, hs⟩

theorem Asc_zero {X : Set V} (hX : IsStar X) : Asc X 0 = Ioi 0 := by
  ext u
  simp [Asc, smul_zero, hX.1]

theorem key_le {X : Set V} (hX : IsStar X) {a : V} {s w : ℝ} (hs : 0 < s) (hw : 0 ≤ w)
    (h : (√s)⁻¹ • a ∈ √w • X) : (Asc X a).Nonempty ∧ sInf (Asc X a) ≤ s * w := by
  rcases hw.eq_or_lt with rfl | hw
  · rw [Real.sqrt_zero, zero_smul_set ⟨0, hX.1⟩, Set.mem_zero, smul_eq_zero] at h
    have ha : a = 0 := h.resolve_left (inv_ne_zero (Real.sqrt_pos.mpr hs).ne')
    subst ha
    rw [Asc_zero hX, csInf_Ioi, mul_zero]
    exact ⟨⟨1, mem_Ioi.mpr one_pos⟩, le_rfl⟩
  · have hmem : s * w ∈ Asc X a := by
      refine ⟨mul_pos hs hw, ?_⟩
      rw [mem_smul_set_iff_inv_smul_mem₀ (Real.sqrt_pos.mpr hw).ne', smul_smul] at h
      rw [Real.sqrt_mul hs.le, mul_inv, mul_comm]
      exact h
    exact ⟨⟨_, hmem⟩, Asc_ge hmem⟩

theorem key_mem {X : Set V} {a : V} {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (h : s * w ∈ Asc X a) : (√s)⁻¹ • a ∈ √w • X := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (Real.sqrt_pos.mpr hw).ne', smul_smul]
  have := h.2
  rw [Real.sqrt_mul hs.le, mul_inv, mul_comm] at this
  exact this

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
open scoped Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
/-- The `2`-product in sqrt form. -/
def Zs (X : Set E) (Y : Set F) : Set (E × F) :=
  ⋃ t ∈ Icc (0 : ℝ) 1, (√(1 - t) • X) ×ˢ (√t • Y)

theorem mem_Zs_smul {X : Set E} {Y : Set F} (s : ℝ) (a : E) (b : F) :
    (√s)⁻¹ • (a, b) ∈ Zs X Y ↔
      ∃ t ∈ Icc (0 : ℝ) 1, (√s)⁻¹ • a ∈ √(1 - t) • X ∧ (√s)⁻¹ • b ∈ √t • Y := by
  simp only [Zs, mem_iUnion, mem_prod, Prod.smul_mk, exists_prop]

theorem rho_Z {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (a : E) (b : F) :
    rho {s | (√s)⁻¹ • (a, b) ∈ Zs X Y} =
      if (Asc X a).Nonempty ∧ (Asc Y b).Nonempty then
        ENNReal.ofReal (Real.exp (-(sInf (Asc X a) + sInf (Asc Y b)))) else 0 := by
  split_ifs with hne
  · have hα := Asc_sInf_nonneg X a
    have hβ := Asc_sInf_nonneg Y b
    apply rho_eq (add_nonneg hα hβ)
    · intro s hs
      simp only [mem_Ioi] at hs
      have hs0 : 0 < s := lt_of_le_of_lt (add_nonneg hα hβ) hs
      set α := sInf (Asc X a)
      set β := sInf (Asc Y b)
      set d := (s - α - β) / 2
      have hd : 0 < d := by simp only [d]; linarith
      have hu : α + d ∈ Asc X a := Asc_Ioi hX hne.1 (by simp only [mem_Ioi]; linarith)
      have hv : β + d ∈ Asc Y b := Asc_Ioi hY hne.2 (by simp only [mem_Ioi]; linarith)
      rw [mem_ofPred_eq, mem_Zs_smul]
      have huv : (α + d) + (β + d) = s := by simp only [d]; ring
      refine ⟨(β + d) / s, ⟨by positivity, (div_le_one hs0).mpr (by linarith)⟩, ?_, ?_⟩
      · have h1 : 1 - (β + d) / s = (α + d) / s := by field_simp; linarith
        rw [h1]
        apply key_mem hs0 (by positivity)
        rwa [mul_div_cancel₀ _ hs0.ne']
      · apply key_mem hs0 (by positivity)
        rwa [mul_div_cancel₀ _ hs0.ne']
    · rintro s ⟨hs, hs0⟩
      rw [mem_ofPred_eq, mem_Zs_smul] at hs
      obtain ⟨t, ht, h1, h2⟩ := hs
      have k1 := (key_le hX hs0 (by linarith [ht.2]) h1).2
      have k2 := (key_le hY hs0 ht.1 h2).2
      simp only [mem_Ici]
      nlinarith
  · apply rho_zero
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    intro hs hs0
    rw [mem_Zs_smul] at hs
    obtain ⟨t, ht, h1, h2⟩ := hs
    exact hne ⟨(key_le hX hs0 (by linarith [ht.2]) h1).1, (key_le hY hs0 ht.1 h2).1⟩

theorem rho_Z_mul {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (p : E × F) :
    rho {s | (√s)⁻¹ • p ∈ Zs X Y} =
      rho {s | (√s)⁻¹ • p.1 ∈ X} * rho {s | (√s)⁻¹ • p.2 ∈ Y} := by
  obtain ⟨a, b⟩ := p
  rw [rho_Z hX hY, rho_T hX, rho_T hY]
  split_ifs with h h1 h2 <;> try simp_all
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
theorem main_measurable (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = 2 * m) (hF : Module.finrank ℝ F = 2 * k)
    {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (hXm : MeasurableSet X)
    (hYm : MeasurableSet Y) (hZ : MeasurableSet (Zs X Y)) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) := by
  have hd : Module.finrank ℝ (E × F) = 2 * (m + k) := by
    rw [Module.finrank_prod, hE, hF]; ring
  rw [← tonelli (μ.prod ν) hd hZ, ← tonelli μ hE hXm, ← tonelli ν hF hYm]
  simp_rw [rho_Z_mul hX hY]
  exact lintegral_prod_mul (measurable_measure_prodMk_left (measurableSet_W hXm)).aemeasurable
    (measurable_measure_prodMk_left (measurableSet_W hYm)).aemeasurable

theorem Zs_eq_image (X : Set E) (Y : Set F) :
    Zs X Y = (fun q : ℝ × E × F => (√(1 - q.1) • q.2.1, √q.1 • q.2.2)) ''
      (Icc 0 1 ×ˢ (X ×ˢ Y)) := by
  ext ⟨a, b⟩
  simp only [Zs, mem_iUnion, mem_prod, mem_image, exists_prop, Prod.mk.injEq, mem_smul_set,
    Prod.exists]
  constructor
  · rintro ⟨t, ht, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
    exact ⟨t, x, y, ⟨ht, hx, hy⟩, rfl, rfl⟩
  · rintro ⟨t, x, y, ⟨ht, hx, hy⟩, rfl, rfl⟩
    exact ⟨t, ht, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

theorem Zs_compact {X : Set E} {Y : Set F} (hX : IsCompact X) (hY : IsCompact Y) :
    IsCompact (Zs X Y) := by
  rw [Zs_eq_image]
  apply (isCompact_Icc.prod (hX.prod hY)).image
  fun_prop

theorem Zs_mono {X X' : Set E} {Y Y' : Set F} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    Zs X Y ⊆ Zs X' Y' := by
  apply iUnion₂_mono
  intro t _
  exact prod_mono (smul_set_mono hX) (smul_set_mono hY)

theorem main_compact (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = 2 * m) (hF : Module.finrank ℝ F = 2 * k)
    {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (hXc : IsCompact X)
    (hYc : IsCompact Y) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) :=
  main_measurable μ ν hE hF hX hY hXc.isClosed.measurableSet hYc.isClosed.measurableSet
    (Zs_compact hXc hYc).isClosed.measurableSet

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
theorem isStar_of_convex {X : Set E} (hX : Convex ℝ X) (h0 : (0 : E) ∈ X) : IsStar X :=
  ⟨h0, fun _ hc0 hc1 _ hx => hX.smul_mem_of_zero_mem h0 hx ⟨hc0, hc1⟩⟩

theorem measure_closure_convex (μ : Measure E) [μ.IsAddHaarMeasure] {X : Set E}
    (hX : Convex ℝ X) : μ (closure X) = μ X := by
  apply le_antisymm _ (measure_mono subset_closure)
  rw [closure_eq_self_union_frontier]
  calc μ (X ∪ frontier X) ≤ μ X + μ (frontier X) := measure_union_le _ _
    _ = μ X := by rw [hX.addHaar_frontier μ, add_zero]

/-- Inner compact star-shaped approximant. -/
def Kin (X : Set E) (c : E) (r : ℝ) : Set E :=
  (fun q : ℝ × E => q.1 • q.2) '' (Icc 0 1 ×ˢ (AffineMap.homothety c r '' closure X))

theorem Kin_compact {X : Set E} (hb : Bornology.IsBounded X) (c : E) (r : ℝ) :
    IsCompact (Kin X c r) := by
  have hcl : IsCompact (closure X) := hb.isCompact_closure
  apply (isCompact_Icc.prod (hcl.image (AffineMap.homothety_continuous c r))).image
  fun_prop

theorem Kin_star {X : Set E} {c : E} (hc : c ∈ X) (r : ℝ) : IsStar (Kin X c r) := by
  refine ⟨⟨(0, AffineMap.homothety c r c), ⟨⟨le_rfl, zero_le_one⟩,
    ⟨c, subset_closure hc, rfl⟩⟩, zero_smul _ _⟩, ?_⟩
  rintro t ht0 ht1 _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  refine ⟨(t * s, y), ⟨⟨mul_nonneg ht0 hs.1, ?_⟩, hy⟩, ?_⟩
  · calc t * s ≤ 1 * 1 := mul_le_mul ht1 hs.2 hs.1 zero_le_one
      _ = 1 := one_mul 1
  · simp [smul_smul]

theorem Kin_sub {X : Set E} (hX : Convex ℝ X) (h0 : (0 : E) ∈ X) {c : E} (hc : c ∈ interior X)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Kin X c r ⊆ X := by
  rintro _ ⟨⟨s, y⟩, ⟨hs, ⟨x, hx, rfl⟩⟩, rfl⟩
  have hy : AffineMap.homothety c r x ∈ X := by
    have : AffineMap.homothety c r x = (1 - r) • c + r • x := by
      rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
      abel
    rw [this]
    exact interior_subset (hX.combo_interior_closure_mem_interior hc hx (by linarith) hr0
      (by ring))
  exact hX.smul_mem_of_zero_mem h0 hy hs

theorem Kin_vol (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (hE : Module.finrank ℝ E = 2 * m) {X : Set E} (c : E) {r : ℝ} (hr0 : 0 ≤ r) :
    ENNReal.ofReal (r ^ (2 * m)) * μ X ≤ μ (Kin X c r) := by
  calc ENNReal.ofReal (r ^ (2 * m)) * μ X = μ (AffineMap.homothety c r '' X) := by
        rw [Measure.addHaar_image_homothety, hE, abs_of_nonneg (pow_nonneg hr0 _)]
    _ ≤ μ (Kin X c r) := by
        apply measure_mono
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨(1, AffineMap.homothety c r x), ⟨⟨zero_le_one, le_rfl⟩,
          ⟨x, subset_closure hx, rfl⟩⟩, one_smul _ _⟩

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
theorem exists_r {a : ℝ≥0∞} (ha : a < 1) (N : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ a < ENNReal.ofReal (r ^ N) := by
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ N)) (𝓝[<] 1) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ N)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ N))) :=
      (ENNReal.continuous_ofReal.comp (continuous_pow N)).tendsto 1
    rw [one_pow, ENNReal.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨r, h1, h2⟩ := ((ht.eventually (lt_mem_nhds ha)).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
  exact ⟨r, h2.1, h2.2, h1⟩

theorem main_convex (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = 2 * m) (hF : Module.finrank ℝ F = 2 * k)
    {X : Set E} {Y : Set F} (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    (hXc : Convex ℝ X) (hYc : Convex ℝ Y) (hXi : (interior X).Nonempty)
    (hYi : (interior Y).Nonempty) (hX0 : (0 : E) ∈ X) (hY0 : (0 : F) ∈ Y) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) := by
  apply le_antisymm
  · calc ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs X Y)
        ≤ ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs (closure X) (closure Y)) := by
          gcongr
          exact Zs_mono subset_closure subset_closure
      _ = ((m.factorial : ℝ≥0∞) * μ (closure X)) * ((k.factorial : ℝ≥0∞) * ν (closure Y)) :=
          main_compact μ ν hE hF (isStar_of_convex hXc.closure (subset_closure hX0))
            (isStar_of_convex hYc.closure (subset_closure hY0)) hXb.isCompact_closure
            hYb.isCompact_closure
      _ = _ := by rw [measure_closure_convex μ hXc, measure_closure_convex ν hYc]
  · apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    obtain ⟨r, hr0, hr1, har⟩ := exists_r ha (2 * m + 2 * k)
    obtain ⟨c, hc⟩ := hXi
    obtain ⟨d, hd⟩ := hYi
    have hpow : ENNReal.ofReal (r ^ (2 * m + 2 * k)) =
        ENNReal.ofReal (r ^ (2 * m)) * ENNReal.ofReal (r ^ (2 * k)) := by
      rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hr0.le _)]
    calc a * (((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y))
        ≤ ENNReal.ofReal (r ^ (2 * m + 2 * k)) *
          (((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y)) := by
          gcongr
      _ = ((m.factorial : ℝ≥0∞) * (ENNReal.ofReal (r ^ (2 * m)) * μ X)) *
          ((k.factorial : ℝ≥0∞) * (ENNReal.ofReal (r ^ (2 * k)) * ν Y)) := by
          rw [hpow]; ring
      _ ≤ ((m.factorial : ℝ≥0∞) * μ (Kin X c r)) * ((k.factorial : ℝ≥0∞) * ν (Kin Y d r)) := by
          gcongr
          · exact Kin_vol μ hE c hr0.le
          · exact Kin_vol ν hF d hr0.le
      _ = ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs (Kin X c r) (Kin Y d r)) :=
          (main_compact μ ν hE hF (Kin_star (interior_subset hc) r)
            (Kin_star (interior_subset hd) r) (Kin_compact hXb c r) (Kin_compact hYb d r)).symm
      _ ≤ ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Zs X Y) := by
          gcongr
          exact Zs_mono (Kin_sub hXc hX0 hc hr0.le hr1) (Kin_sub hYc hY0 hd hr0.le hr1)

end Viterbo.PP2.PartV
end

section
set_option linter.unusedSectionVars false
namespace Viterbo.PP2.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
/-! ## Assembly -/
theorem pprod_eq_image {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k)) :
    symplecticPProduct 2 X Y =
      (fun zw : Phase m × Phase k => (appendPos zw.1.1 zw.2.1, appendPos zw.1.2 zw.2.2)) ''
        Zs X Y := by
  have h2 : (2 : ℝ≥0∞)⁻¹.toReal = 1 / 2 := by
    rw [ENNReal.toReal_inv]; norm_num
  rw [Zs, image_iUnion₂, symplecticPProduct, h2]
  simp_rw [← Real.sqrt_eq_rpow]

theorem finrank_phase (n : ℕ) : Module.finrank ℝ (Phase n) = 2 * n := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin]; ring

instance (n : ℕ) : (volume : Measure (Phase n)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

theorem volume_pprod {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y) :
    ((m + k).factorial : ℝ≥0∞) * volume (symplecticPProduct 2 X Y) =
      ((m.factorial : ℝ≥0∞) * volume X) * ((k.factorial : ℝ≥0∞) * volume Y) := by
  rw [pprod_eq_image, volume_image_Psi]
  exact main_convex volume volume (finrank_phase m) (finrank_phase k) hX.1 hY.1 hX.2.1 hY.2.1
    hX.2.2 hY.2.2 hX0 hY0

end Viterbo.PP2.PartV
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
/-!
# Blueprint: Sys(X ⊗₂ Y) = Sys X · Sys Y when c_EHZ X = c_EHZ Y

Interfaces (each `sorry` is a Part), and the assembly of the target from them.

* `volume_pprod` (Part V): `(m+k)! Vol(X ⊗₂ Y) = m! k! Vol X Vol Y`.
* `cEHZ_pprod_le_left/right` (Part U): lift a characteristic of `X` (resp. `Y`) into `X ⊗₂ Y`.
* `min_le_cEHZ_pprod_of_interior` (Part L): lower bound when `0 ∈ int X`, `0 ∈ int Y`
  (conservation of `g_X(a)²` along a characteristic).
* `isConvexDomain_pprod`, `min_le_cEHZ_pprod` (Part G): convexity of the product; the general lower
  bound from Part L and three properties of `cEHZ` on convex domains (Part M, `Viterbo.CM`):
  translation invariance and scaling, proved directly, and monotonicity under inclusion, from
  `Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`.
-/
alias volume_pprod := Viterbo.PP2.PartV.volume_pprod

end Viterbo.PP2
end

section
namespace Viterbo.PP2.PartU
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Algebra of `phaseInner` -/

lemma pI_zero_left (x : Phase n) : phaseInner 0 x = 0 := by simp [phaseInner]

lemma J_zero : J (0 : Phase n) = 0 := by simp [J]

end Viterbo.PP2.PartU
end

section
namespace Viterbo.PP2.PartU
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
/-! ## Coordinates of `ℝ^{m+k}` -/
/-- First block of coordinates. -/
noncomputable def P1L : Position (m + k) →ₗ[ℝ] Position m where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.castAdd k i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Second block of coordinates. -/
noncomputable def P2L : Position (m + k) →ₗ[ℝ] Position k where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.natAdd m i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

noncomputable def P1 : Position (m + k) →L[ℝ] Position m := LinearMap.toContinuousLinearMap P1L

noncomputable def P2 : Position (m + k) →L[ℝ] Position k := LinearMap.toContinuousLinearMap P2L

lemma P1_apply (x : Position (m + k)) (i : Fin m) : (P1 x) i = x (Fin.castAdd k i) := rfl

lemma P2_apply (x : Position (m + k)) (i : Fin k) : (P2 x) i = x (Fin.natAdd m i) := rfl

lemma appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

lemma appendPos_natAdd (x : Position m) (y : Position k) (i : Fin k) :
    appendPos x y (Fin.natAdd m i) = y i := by
  simp [appendPos]

lemma P1_append (x : Position m) (y : Position k) : P1 (appendPos x y) = x := by
  ext i; rw [P1_apply, appendPos_castAdd]

lemma P2_append (x : Position m) (y : Position k) : P2 (appendPos x y) = y := by
  ext i; rw [P2_apply, appendPos_natAdd]

lemma append_P (x : Position (m + k)) : appendPos (P1 x) (P2 x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [appendPos_castAdd, P1_apply]
  · rw [appendPos_natAdd, P2_apply]

lemma inner_split (x y : Position (m + k)) :
    inner ℝ x y = inner ℝ (P1 x) (P1 y) + inner ℝ (P2 x) (P2 y) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add]
  rfl

/-- First phase block. -/
noncomputable def Q1 : Phase (m + k) →L[ℝ] Phase m :=
  (P1.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P1.comp (ContinuousLinearMap.snd ℝ _ _))

/-- Second phase block. -/
noncomputable def Q2 : Phase (m + k) →L[ℝ] Phase k :=
  (P2.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P2.comp (ContinuousLinearMap.snd ℝ _ _))

/-- The coordinate shuffle `Phase m × Phase k → Phase (m + k)`. -/
noncomputable def Ψ (z : Phase m) (w : Phase k) : Phase (m + k) :=
  (appendPos z.1 w.1, appendPos z.2 w.2)

lemma Q1_apply (p : Phase (m + k)) : Q1 p = (P1 p.1, P1 p.2) := rfl

lemma Q2_apply (p : Phase (m + k)) : Q2 p = (P2 p.1, P2 p.2) := rfl

lemma Q1_Ψ (z : Phase m) (w : Phase k) : Q1 (Ψ z w) = z := by
  simp [Q1_apply, Ψ, P1_append]

lemma Q2_Ψ (z : Phase m) (w : Phase k) : Q2 (Ψ z w) = w := by
  simp [Q2_apply, Ψ, P2_append]

lemma Ψ_Q (p : Phase (m + k)) : Ψ (Q1 p) (Q2 p) = p := by
  simp [Q1_apply, Q2_apply, Ψ, append_P]

lemma pI_split (p q : Phase (m + k)) :
    phaseInner p q = phaseInner (Q1 p) (Q1 q) + phaseInner (Q2 p) (Q2 q) := by
  simp only [phaseInner, Q1_apply, Q2_apply, inner_split p.1 q.1, inner_split p.2 q.2]
  ring

lemma Q1_J (p : Phase (m + k)) : Q1 (J p) = J (Q1 p) := by
  simp [Q1_apply, J]

lemma Q2_J (p : Phase (m + k)) : Q2 (J p) = J (Q2 p) := by
  simp [Q2_apply, J]

lemma Q_ext {p q : Phase (m + k)} (h1 : Q1 p = Q1 q) (h2 : Q2 p = Q2 q) : p = q := by
  rw [← Ψ_Q p, ← Ψ_Q q, h1, h2]

/-- The left embedding `z ↦ Ψ z 0`. -/
noncomputable def LlL : Phase m →ₗ[ℝ] Phase (m + k) where
  toFun z := Ψ z 0
  map_add' z w := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])
  map_smul' c z := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])

noncomputable def Ll : Phase m →L[ℝ] Phase (m + k) := LinearMap.toContinuousLinearMap (LlL (k := k))

lemma Ll_apply (z : Phase m) : (Ll (k := k)) z = Ψ z 0 := rfl

end Viterbo.PP2.PartU
end

section
namespace Viterbo.PP2.PartU
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n n' : ℕ}
/-! ## Lifting characteristics along an isometric section -/
/-- The data of a linear section `L` of a linear projection `Q` that commutes with `J` and is
adjoint to `Q` for `phaseInner`. -/
structure IsoSection (L : Phase n →L[ℝ] Phase n') (Q : Phase n' →L[ℝ] Phase n) : Prop where
  left_inv : ∀ z, Q (L z) = z
  J_comm : ∀ z, L (J z) = J (L z)
  adj : ∀ z p, phaseInner (L z) p = phaseInner z (Q p)

lemma IsoSection.deriv_comp {L : Phase n →L[ℝ] Phase n'} {Q : Phase n' →L[ℝ] Phase n}
    (hL : IsoSection L Q) (x : ℝ → Phase n) (t : ℝ) :
    deriv (fun s => L (x s)) t = L (deriv x t) := by
  by_cases hx : DifferentiableAt ℝ x t
  · exact (L.hasFDerivAt.comp_hasDerivAt t hx.hasDerivAt).deriv
  · have hLx : ¬ DifferentiableAt ℝ (fun s => L (x s)) t := by
      intro hd
      apply hx
      have : DifferentiableAt ℝ (fun s => Q (L (x s))) t := Q.differentiableAt.comp t hd
      simpa [hL.left_inv] using this
    rw [deriv_zero_of_not_differentiableAt hx, deriv_zero_of_not_differentiableAt hLx, map_zero]

lemma IsoSection.action_eq {L : Phase n →L[ℝ] Phase n'} {Q : Phase n' →L[ℝ] Phase n}
    (hL : IsoSection L Q) (x : ℝ → Phase n) :
    action (fun s => L (x s)) = action x := by
  unfold action
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [hL.deriv_comp x t, ← hL.J_comm, hL.adj, hL.left_inv]

lemma IsoSection.lift {L : Phase n →L[ℝ] Phase n'} {Q : Phase n' →L[ℝ] Phase n}
    (hL : IsoSection L Q) {X : Set (Phase n)} {Z : Set (Phase n')}
    (hXZ : ∀ z ∈ X, L z ∈ Z) (hZX : ∀ p ∈ Z, Q p ∈ X) {x : ℝ → Phase n}
    (hx : IsGeneralizedClosedCharacteristic X x) :
    IsGeneralizedClosedCharacteristic Z (fun s => L (x s)) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hvN⟩ := hx
  refine ⟨fun t => by simp only [hper t], fun t => ?_, fun s => L (v s), ?_, ?_, ?_⟩
  · have hxt := hfr t
    refine ⟨?_, ?_⟩
    · have h1 : L '' closure X ⊆ closure (L '' X) := image_closure_subset_closure_image L.continuous
      have h2 : closure (L '' X) ⊆ closure Z :=
        closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hXZ z hz)
      exact h2 (h1 ⟨x t, hxt.1, rfl⟩)
    · intro hint
      apply hxt.2
      rw [mem_interior]
      refine ⟨L ⁻¹' interior Z, fun z hz => ?_, isOpen_interior.preimage L.continuous, hint⟩
      have := hZX _ (interior_subset hz)
      rwa [hL.left_inv] at this
  · exact locallyIntegrable_iff.2 fun K hK => L.integrable_comp (hvint.integrableOn_isCompact hK)
  · intro a b
    have hvI : IntervalIntegrable v volume a b :=
      (hvint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    rw [L.intervalIntegral_comp_comm hvI, ← hftc, map_sub]
  · filter_upwards [hvN] with t ht
    obtain ⟨u, hu, hvu⟩ := ht
    refine ⟨L u, fun p hp => ?_, ?_⟩
    · rw [hL.adj, map_sub, hL.left_inv]
      exact hu _ (hZX p hp)
    · rw [← hL.J_comm, hvu]

theorem IsoSection.cEHZ_le {L : Phase n →L[ℝ] Phase n'} {Q : Phase n' →L[ℝ] Phase n}
    (hL : IsoSection L Q) {X : Set (Phase n)} {Z : Set (Phase n')}
    (hXZ : ∀ z ∈ X, L z ∈ Z) (hZX : ∀ p ∈ Z, Q p ∈ X) : cEHZ Z ≤ cEHZ X := by
  unfold cEHZ
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨hxc, s, t, hst⟩ := hx
  have hne : ∃ s t, (fun r => L (x r)) s ≠ (fun r => L (x r)) t := by
    refine ⟨s, t, fun h => hst ?_⟩
    have := congrArg Q h
    simpa [hL.left_inv] using this
  refine (iInf₂_le (fun r => L (x r)) ⟨hL.lift hXZ hZX hxc, hne⟩).trans_eq ?_
  rw [hL.action_eq]

end Viterbo.PP2.PartU
end

section
namespace Viterbo.PP2.PartU
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
lemma isoSection_left : IsoSection (Ll (m := m) (k := k)) Q1 where
  left_inv z := by rw [Ll_apply, Q1_Ψ]
  J_comm z := Q_ext (by rw [Q1_J, Ll_apply, Ll_apply, Q1_Ψ, Q1_Ψ])
    (by rw [Q2_J, Ll_apply, Ll_apply, Q2_Ψ, Q2_Ψ, J_zero])
  adj z p := by rw [pI_split, Ll_apply, Q1_Ψ, Q2_Ψ, pI_zero_left, add_zero]

lemma toReal_half : (2 : ℝ≥0∞)⁻¹.toReal = 1 / 2 := by
  rw [ENNReal.toReal_inv]; norm_num

lemma rpow_half_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ^ (2 : ℝ≥0∞)⁻¹.toReal ∈ Icc (0 : ℝ) 1 := by
  rw [toReal_half, ← Real.sqrt_eq_rpow]
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr ht.2⟩

lemma smul_subset_of_convex {n : ℕ} {X : Set (Phase n)} (hX : Convex ℝ X) (hX0 : 0 ∈ X)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s • X ⊆ X := by
  rintro _ ⟨x, hx, rfl⟩
  exact hX.smul_mem_of_zero_mem hX0 hx hs

lemma mem_pprod_fst {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hX0 : 0 ∈ X)
    {p : Phase (m + k)} (hp : p ∈ symplecticPProduct 2 X Y) : Q1 p ∈ X := by
  simp only [symplecticPProduct, mem_iUnion] at hp
  obtain ⟨t, ht, zw, ⟨hz, _⟩, rfl⟩ := hp
  have : Q1 (Ψ zw.1 zw.2) = zw.1 := Q1_Ψ _ _
  rw [show (fun zw : Phase m × Phase k => (appendPos zw.1.1 zw.2.1, appendPos zw.1.2 zw.2.2)) zw
    = Ψ zw.1 zw.2 from rfl, this]
  exact smul_subset_of_convex hX hX0 (rpow_half_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1]⟩) hz

lemma zero_rpow_half : (0 : ℝ) ^ (2 : ℝ≥0∞)⁻¹.toReal = 0 := by
  rw [toReal_half]; norm_num

lemma left_mem_pprod {X : Set (Phase m)} {Y : Set (Phase k)} (hY0 : 0 ∈ Y) {z : Phase m}
    (hz : z ∈ X) : Ll z ∈ symplecticPProduct 2 X Y := by
  simp only [symplecticPProduct, mem_iUnion]
  refine ⟨0, ⟨le_rfl, zero_le_one⟩, (z, 0), ⟨?_, ?_⟩, rfl⟩
  · rw [sub_zero, Real.one_rpow, one_smul]; exact hz
  · rw [zero_rpow_half]; exact ⟨0, hY0, zero_smul _ _⟩

theorem cEHZ_pprod_le_left {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : Convex ℝ X) (hY : Convex ℝ Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y) :
    cEHZ (symplecticPProduct 2 X Y) ≤ cEHZ X :=
  isoSection_left.cEHZ_le (fun _ hz => left_mem_pprod hY0 hz)
    (fun _ hp => mem_pprod_fst hX hX0 hp)

end Viterbo.PP2.PartU
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
alias cEHZ_pprod_le_left := Viterbo.PP2.PartU.cEHZ_pprod_le_left

end Viterbo.PP2
end

section
namespace Viterbo.PP2.PartU
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}

end Viterbo.PP2.PartU
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}

end Viterbo.PP2
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
theorem min_le_cEHZ_pprod_of_interior {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y)
    (hX0 : 0 ∈ interior X) (hY0 : 0 ∈ interior Y) :
    min (cEHZ X) (cEHZ Y) ≤ cEHZ (symplecticPProduct 2 X Y) :=
  Viterbo.PP2.PartL.min_le_cEHZ_pprod_of_interior X Y hX hY hX0 hY0

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}

end Viterbo.PP2
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
/-- First block of coordinates. -/
noncomputable def P1L : Position (m + k) →ₗ[ℝ] Position m where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.castAdd k i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Second block of coordinates. -/
noncomputable def P2L : Position (m + k) →ₗ[ℝ] Position k where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.natAdd m i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

noncomputable def P1 : Position (m + k) →L[ℝ] Position m := LinearMap.toContinuousLinearMap P1L

noncomputable def P2 : Position (m + k) →L[ℝ] Position k := LinearMap.toContinuousLinearMap P2L

lemma P1_apply (x : Position (m + k)) (i : Fin m) : (P1 x) i = x (Fin.castAdd k i) := rfl

lemma P2_apply (x : Position (m + k)) (i : Fin k) : (P2 x) i = x (Fin.natAdd m i) := rfl

lemma appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

lemma appendPos_natAdd (x : Position m) (y : Position k) (i : Fin k) :
    appendPos x y (Fin.natAdd m i) = y i := by
  simp [appendPos]

lemma P1_append (x : Position m) (y : Position k) : P1 (appendPos x y) = x := by
  ext i; rw [P1_apply, appendPos_castAdd]

lemma P2_append (x : Position m) (y : Position k) : P2 (appendPos x y) = y := by
  ext i; rw [P2_apply, appendPos_natAdd]

lemma append_P (x : Position (m + k)) : appendPos (P1 x) (P2 x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [appendPos_castAdd, P1_apply]
  · rw [appendPos_natAdd, P2_apply]

/-- First phase block. -/
noncomputable def Q1 : Phase (m + k) →L[ℝ] Phase m :=
  (P1.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P1.comp (ContinuousLinearMap.snd ℝ _ _))

/-- Second phase block. -/
noncomputable def Q2 : Phase (m + k) →L[ℝ] Phase k :=
  (P2.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P2.comp (ContinuousLinearMap.snd ℝ _ _))

/-- The coordinate shuffle `Phase m × Phase k → Phase (m + k)`. -/
noncomputable def Ψ (z : Phase m) (w : Phase k) : Phase (m + k) :=
  (appendPos z.1 w.1, appendPos z.2 w.2)

lemma Q1_apply (p : Phase (m + k)) : Q1 p = (P1 p.1, P1 p.2) := rfl

lemma Q2_apply (p : Phase (m + k)) : Q2 p = (P2 p.1, P2 p.2) := rfl

lemma Q1_Ψ (z : Phase m) (w : Phase k) : Q1 (Ψ z w) = z := by
  simp [Q1_apply, Ψ, P1_append]

lemma Q2_Ψ (z : Phase m) (w : Phase k) : Q2 (Ψ z w) = w := by
  simp [Q2_apply, Ψ, P2_append]

lemma Ψ_Q (p : Phase (m + k)) : Ψ (Q1 p) (Q2 p) = p := by
  simp [Q1_apply, Q2_apply, Ψ, append_P]

lemma Q_ext {p q : Phase (m + k)} (h1 : Q1 p = Q1 q) (h2 : Q2 p = Q2 q) : p = q := by
  rw [← Ψ_Q p, ← Ψ_Q q, h1, h2]

/-- `Ψ` as a linear equivalence. -/
noncomputable def ΨLe : (Phase m × Phase k) ≃ₗ[ℝ] Phase (m + k) where
  toFun zw := Ψ zw.1 zw.2
  invFun p := (Q1 p, Q2 p)
  map_add' a b := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])
  map_smul' c a := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])
  left_inv a := by simp [Q1_Ψ, Q2_Ψ]
  right_inv p := Ψ_Q p

noncomputable def ΨL : (Phase m × Phase k) ≃L[ℝ] Phase (m + k) :=
  (ΨLe (m := m) (k := k)).toContinuousLinearEquiv

lemma ΨL_apply (zw : Phase m × Phase k) : ΨL zw = Ψ zw.1 zw.2 := rfl

lemma toReal_half : (2 : ℝ≥0∞)⁻¹.toReal = 1 / 2 := by
  rw [ENNReal.toReal_inv]; norm_num

lemma pprod_eq (X : Set (Phase m)) (Y : Set (Phase k)) :
    symplecticPProduct 2 X Y = ⋃ t ∈ Icc (0 : ℝ) 1,
      ΨL '' ((Real.sqrt (1 - t) • X) ×ˢ (Real.sqrt t • Y)) := by
  simp only [symplecticPProduct, toReal_half, ← Real.sqrt_eq_rpow]
  rfl

lemma mem_pprod_iff {X : Set (Phase m)} {Y : Set (Phase k)} {p : Phase (m + k)} :
    p ∈ symplecticPProduct 2 X Y ↔
      ∃ s τ : ℝ, 0 ≤ s ∧ 0 ≤ τ ∧ s ^ 2 + τ ^ 2 = 1 ∧ Q1 p ∈ s • X ∧ Q2 p ∈ τ • Y := by
  rw [pprod_eq]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨t, ht, zw, ⟨hz, hw⟩, rfl⟩
    refine ⟨Real.sqrt (1 - t), Real.sqrt t, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_, ?_⟩
    · rw [Real.sq_sqrt (by linarith [ht.2]), Real.sq_sqrt ht.1]; ring
    · rw [ΨL_apply, Q1_Ψ]; exact hz
    · rw [ΨL_apply, Q2_Ψ]; exact hw
  · rintro ⟨s, τ, hs, hτ, h1, h2, h3⟩
    refine ⟨τ ^ 2, ⟨by positivity, by nlinarith⟩, (Q1 p, Q2 p), ⟨?_, ?_⟩, Ψ_Q p⟩
    · have : 1 - τ ^ 2 = s ^ 2 := by linarith
      rw [this, Real.sqrt_sq hs]; exact h2
    · rw [Real.sqrt_sq hτ]; exact h3

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
lemma smul_subset_smul {X : Set (Phase n)} (hX : Convex ℝ X) (hX0 : (0 : Phase n) ∈ X)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') : s • X ⊆ s' • X := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hs.eq_or_lt with h | h
  · subst h
    exact ⟨0, hX0, by simp⟩
  · have hs' : 0 < s' := lt_of_lt_of_le h hss
    refine ⟨(s / s') • x, hX.smul_mem_of_zero_mem hX0 hx ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_one hs']; exact hss
    · simp only [smul_smul]; congr 1; field_simp

lemma add_mem_smul {X : Set (Phase n)} (hX : Convex ℝ X) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {a b : Phase n} (ha : a ∈ s • X) (hb : b ∈ t • X) : a + b ∈ (s + t) • X := by
  rw [hX.add_smul hs ht]; exact add_mem_add ha hb

lemma smul_mem_smul {X : Set (Phase n)} {s c : ℝ} {a : Phase n} (ha : a ∈ s • X) :
    c • a ∈ (c * s) • X := by
  rw [mul_smul]; exact smul_mem_smul_set ha

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
lemma mem_pprod_of_le {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hX0 : (0 : Phase m) ∈ X)
    {p : Phase (m + k)} {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) (h : s ^ 2 + τ ^ 2 ≤ 1)
    (h1 : Q1 p ∈ s • X) (h2 : Q2 p ∈ τ • Y) : p ∈ symplecticPProduct 2 X Y := by
  rw [mem_pprod_iff]
  refine ⟨Real.sqrt (1 - τ ^ 2), τ, Real.sqrt_nonneg _, hτ, ?_, ?_, h2⟩
  · rw [Real.sq_sqrt (by linarith [sq_nonneg s])]; ring
  · refine smul_subset_smul hX hX0 hs ?_ h1
    exact Real.le_sqrt_of_sq_le (by linarith)

theorem isConvexDomain_pprod {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y) :
    IsConvexDomain (symplecticPProduct 2 X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsub : symplecticPProduct 2 X Y ⊆ ΨL '' (X ×ˢ Y) := by
      intro p hp
      obtain ⟨s, τ, hs, hτ, h, h1, h2⟩ := mem_pprod_iff.1 hp
      refine ⟨(Q1 p, Q2 p), ⟨?_, ?_⟩, Ψ_Q p⟩
      · have := smul_subset_smul hX.2.1 hX0 hs (s' := 1) (by nlinarith) h1
        rwa [one_smul] at this
      · have := smul_subset_smul hY.2.1 hY0 hτ (s' := 1) (by nlinarith) h2
        rwa [one_smul] at this
    exact (ΨL.toContinuousLinearMap.lipschitz.isBounded_image (hX.1.prod hY.1)).subset hsub
  · intro p hp q hq a b ha hb hab
    obtain ⟨s1, τ1, hs1, hτ1, h1, hp1, hp2⟩ := mem_pprod_iff.1 hp
    obtain ⟨s2, τ2, hs2, hτ2, h2, hq1, hq2⟩ := mem_pprod_iff.1 hq
    apply mem_pprod_of_le hX.2.1 hX0 (s := a * s1 + b * s2) (τ := a * τ1 + b * τ2)
      (by positivity) (by positivity)
    · have : s1 * s2 + τ1 * τ2 ≤ 1 := by nlinarith [sq_nonneg (s1 - s2), sq_nonneg (τ1 - τ2)]
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg ha hb]
    · rw [map_add, map_smul, map_smul]
      exact add_mem_smul hX.2.1 (by positivity) (by positivity)
        (smul_mem_smul hp1) (smul_mem_smul hq1)
    · rw [map_add, map_smul, map_smul]
      exact add_mem_smul hY.2.1 (by positivity) (by positivity)
        (smul_mem_smul hp2) (smul_mem_smul hq2)
  · obtain ⟨x, hx⟩ := hX.2.2
    obtain ⟨y, hy⟩ := hY.2.2
    set c := Real.sqrt (1 - 1 / 2) with hc
    have hc0 : c ≠ 0 := by rw [hc]; positivity
    have hO : IsOpen (ΨL '' ((c • interior X) ×ˢ (c • interior Y))) :=
      ΨL.toHomeomorph.isOpenMap _
        ((isOpen_interior.smul₀ hc0).prod (isOpen_interior.smul₀ hc0))
    have hsub : ΨL '' ((c • interior X) ×ˢ (c • interior Y)) ⊆ symplecticPProduct 2 X Y := by
      rw [pprod_eq]
      intro p hp
      simp only [mem_iUnion]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      have e : Real.sqrt (1 / 2) = c := by rw [hc]; norm_num
      rw [e]
      exact image_mono (Set.prod_mono (smul_set_mono interior_subset)
        (smul_set_mono interior_subset)) hp
    exact ⟨_, interior_maximal hsub hO ⟨(c • x, c • y),
      ⟨smul_mem_smul_set hx, smul_mem_smul_set hy⟩, rfl⟩⟩

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}

end Viterbo.PP2
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}

lemma isConvexDomain_translate {X : Set (Phase n)} (hX : IsConvexDomain X) (d : Phase n) :
    IsConvexDomain ((fun z => z + d) '' X) := by
  refine ⟨(IsometryEquiv.addRight d).isometry.lipschitz.isBounded_image hX.1, ?_, ?_⟩
  · have := hX.2.1.vadd d
    rwa [← image_vadd, show (fun x : Phase n => d +ᵥ x) = fun z => z + d by
      funext z; rw [vadd_eq_add, add_comm]] at this
  · have e : (fun z => z + d) '' interior X = interior ((fun z => z + d) '' X) :=
      (Homeomorph.addRight d).image_interior X
    rw [← e]
    exact hX.2.2.image _

lemma zero_mem_interior_translate {X : Set (Phase n)} (hX : Convex ℝ X) (hX0 : (0 : Phase n) ∈ X)
    {x0 : Phase n} (hx0 : x0 ∈ interior X) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (0 : Phase n) ∈ interior ((fun z => z + -(ε • x0)) '' X) := by
  have e : (fun z => z + -(ε • x0)) '' interior X = interior ((fun z => z + -(ε • x0)) '' X) :=
    (Homeomorph.addRight (-(ε • x0))).image_interior X
  rw [← e]
  refine ⟨ε • x0, ?_, by simp⟩
  have := hX.combo_self_interior_mem_interior hX0 hx0 (a := 1 - ε) (b := ε) (by linarith) hε
    (by ring)
  simpa using this

lemma isConvexDomain_smul' {X : Set (Phase n)} (hX : IsConvexDomain X) {c : ℝ} (hc : 0 < c) :
    IsConvexDomain (c • X) := by
  refine ⟨hX.1.smul₀ c, hX.2.1.smul c, ?_⟩
  rw [interior_smul₀ hc.ne']
  exact hX.2.2.smul_set

lemma cEHZ_translate (hn : 1 ≤ n) {X : Set (Phase n)} (hX : IsConvexDomain X) (d : Phase n) :
    cEHZ ((fun z => z + d) '' X) = cEHZ X := by
  exact Viterbo.CM.cEHZ_translate X d

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2.PartG
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
lemma scale_ineq {s τ ε : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) (h : s ^ 2 + τ ^ 2 = 1) (hε : 0 < ε) :
    (1 / (1 + 2 * ε) * (s + (1 - s) * ε)) ^ 2 + (1 / (1 + 2 * ε) * (τ + (1 - τ) * ε)) ^ 2 ≤ 1 := by
  have hs1 : s ≤ 1 := by nlinarith
  have hτ1 : τ ≤ 1 := by nlinarith
  have hS0 : 0 ≤ s + (1 - s) * ε := by nlinarith
  have hT0 : 0 ≤ τ + (1 - τ) * ε := by nlinarith
  have hS : s + (1 - s) * ε ≤ s + ε := by nlinarith
  have hT : τ + (1 - τ) * ε ≤ τ + ε := by nlinarith
  have h1 := pow_le_pow_left₀ hS0 hS 2
  have h2 := pow_le_pow_left₀ hT0 hT 2
  have h3 : ε * (s + τ) ≤ ε * 2 := mul_le_mul_of_nonneg_left (by linarith) hε.le
  have key : (s + (1 - s) * ε) ^ 2 + (τ + (1 - τ) * ε) ^ 2 ≤ (1 + 2 * ε) ^ 2 := by
    nlinarith [sq_nonneg ε]
  have hA : 0 < 1 + 2 * ε := by linarith
  rw [one_div_mul_eq_div, one_div_mul_eq_div, div_pow, div_pow, ← add_div, div_le_one (by positivity)]
  exact key

lemma shift_subset {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hX0 : (0 : Phase m) ∈ X) {x0 : Phase m} {y0 : Phase k} (hx0 : x0 ∈ X) (hy0 : y0 ∈ Y)
    {ε : ℝ} (hε : 0 < ε) :
    (fun z => z + ΨL ((1 / (1 + 2 * ε) * ε) • x0, (1 / (1 + 2 * ε) * ε) • y0)) ''
      ((1 / (1 + 2 * ε)) • symplecticPProduct 2 ((fun z => z + -(ε • x0)) '' X)
        ((fun z => z + -(ε • y0)) '' Y)) ⊆ symplecticPProduct 2 X Y := by
  set lam := 1 / (1 + 2 * ε) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨s, τ, hs, hτ, h, h1, h2⟩ := mem_pprod_iff.1 hp
  obtain ⟨_, ⟨x, hx, rfl⟩, hxe⟩ := Set.mem_smul_set.1 h1
  obtain ⟨_, ⟨y, hy, rfl⟩, hye⟩ := Set.mem_smul_set.1 h2
  have hs1 : s ≤ 1 := by nlinarith
  have hτ1 : τ ≤ 1 := by nlinarith
  apply mem_pprod_of_le hX hX0 (s := lam * (s + (1 - s) * ε)) (τ := lam * (τ + (1 - τ) * ε))
    (by positivity) (mul_nonneg hlam0 (by nlinarith)) (scale_ineq hs hτ h hε)
  · rw [map_add, map_smul, ΨL_apply, Q1_Ψ, ← hxe]
    have e : lam • (s • (x + -(ε • x0))) + (lam * ε) • x0 =
        lam • (s • x + ((1 - s) * ε) • x0) := by module
    rw [e]
    exact smul_mem_smul (add_mem_smul hX hs (by nlinarith) (smul_mem_smul_set hx)
      (smul_mem_smul_set hx0))
  · rw [map_add, map_smul, ΨL_apply, Q2_Ψ, ← hye]
    have e : lam • (τ • (y + -(ε • y0))) + (lam * ε) • y0 =
        lam • (τ • y + ((1 - τ) * ε) • y0) := by module
    rw [e]
    exact smul_mem_smul (add_mem_smul hY hτ (by nlinarith) (smul_mem_smul_set hy)
      (smul_mem_smul_set hy0))

theorem min_le_cEHZ_pprod {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y) :
    min (cEHZ X) (cEHZ Y) ≤ cEHZ (symplecticPProduct 2 X Y) := by
  obtain ⟨x0, hx0⟩ := hX.2.2
  obtain ⟨y0, hy0⟩ := hY.2.2
  have bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal ((1 / (1 + 2 * ε)) ^ 2) * min (cEHZ X) (cEHZ Y) ≤
        cEHZ (symplecticPProduct 2 X Y) := by
    intro ε hε hε1
    set Xε := (fun z => z + -(ε • x0)) '' X
    set Yε := (fun z => z + -(ε • y0)) '' Y
    have hXε := isConvexDomain_translate hX (-(ε • x0))
    have hYε := isConvexDomain_translate hY (-(ε • y0))
    have hXε0 := zero_mem_interior_translate hX.2.1 hX0 hx0 hε hε1
    have hYε0 := zero_mem_interior_translate hY.2.1 hY0 hy0 hε hε1
    have hL := min_le_cEHZ_pprod_of_interior Xε Yε hXε hYε hXε0 hYε0
    rw [cEHZ_translate hm hX, cEHZ_translate hk hY] at hL
    have hZε := isConvexDomain_pprod Xε Yε hXε hYε (interior_subset hXε0) (interior_subset hYε0)
    have hlam : 0 < 1 / (1 + 2 * ε) := by positivity
    calc ENNReal.ofReal ((1 / (1 + 2 * ε)) ^ 2) * min (cEHZ X) (cEHZ Y)
        ≤ ENNReal.ofReal ((1 / (1 + 2 * ε)) ^ 2) * cEHZ (symplecticPProduct 2 Xε Yε) := by
          gcongr
      _ = cEHZ ((1 / (1 + 2 * ε)) • symplecticPProduct 2 Xε Yε) :=
          (Viterbo.CM.cEHZ_smul _ hlam).symm
      _ = cEHZ ((fun z => z + ΨL ((1 / (1 + 2 * ε) * ε) • x0, (1 / (1 + 2 * ε) * ε) • y0)) ''
            ((1 / (1 + 2 * ε)) • symplecticPProduct 2 Xε Yε)) := (Viterbo.CM.cEHZ_translate _ _).symm
      _ ≤ cEHZ (symplecticPProduct 2 X Y) :=
          Viterbo.CM.cEHZ_mono (by omega)
            (isConvexDomain_translate (isConvexDomain_smul' hZε hlam) _)
            (isConvexDomain_pprod X Y hX hY hX0 hY0)
            (shift_subset hX.2.1 hY.2.1 hX0 (interior_subset hx0) (interior_subset hy0) hε)
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  have hat : a ≠ ⊤ := ne_top_of_lt ha
  set r := a.toReal with hr
  have hr1 : r < 1 := by
    rw [hr]; exact (ENNReal.toReal_lt_toReal hat ENNReal.one_ne_top).2 ha |>.trans_eq (by simp)
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  set ε := (1 - r) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  refine le_trans ?_ (bound ε hε0 hε1)
  gcongr
  rw [← ENNReal.ofReal_toReal hat]
  apply ENNReal.ofReal_le_ofReal
  rw [← hr, div_pow, one_pow, le_div_iff₀ (by positivity)]
  have : r = 1 - 4 * ε := by rw [hε]; ring
  rw [this]
  nlinarith [mul_pos hε0 hε0, mul_pos (mul_pos hε0 hε0) hε0]

end Viterbo.PP2.PartG
end

section
namespace Viterbo.PP2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {m k : ℕ}
alias min_le_cEHZ_pprod := Viterbo.PP2.PartG.min_le_cEHZ_pprod

/-! ## Assembly -/
lemma volume_pos_of_isConvexDomain {n : ℕ} {S : Set (Phase n)} (hS : IsConvexDomain S) :
    0 < volume S := by
  obtain ⟨x, hx⟩ := hS.2.2
  exact MeasureTheory.Measure.measure_pos_of_nonempty_interior _ ⟨x, hx⟩

lemma volume_lt_top_of_isConvexDomain {n : ℕ} {S : Set (Phase n)} (hS : IsConvexDomain S) :
    volume S < ⊤ :=
  hS.1.measure_lt_top

theorem main (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X : Set (OAI.SymmetricPolar.Phase m)) (Y : Set (OAI.SymmetricPolar.Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y)
    (hXY : cEHZ X = cEHZ Y) :
    systolicRatio (symplecticPProduct 2 X Y) = systolicRatio X * systolicRatio Y := by
  set c := cEHZ X with hc
  have hZ : cEHZ (symplecticPProduct 2 X Y) = c := by
    apply le_antisymm (cEHZ_pprod_le_left X Y hX.2.1 hY.2.1 hX0 hY0)
    have := min_le_cEHZ_pprod hm hk X Y hX hY hX0 hY0
    rwa [← hXY, min_self] at this
  have hV := volume_pprod hm hk X Y hX hY hX0 hY0
  have hvX0 := (volume_pos_of_isConvexDomain hX).ne'
  have hvY0 := (volume_pos_of_isConvexDomain hY).ne'
  have hvXt := (volume_lt_top_of_isConvexDomain hX).ne
  have hvYt := (volume_lt_top_of_isConvexDomain hY).ne
  have hfm : (m.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hfk : (k.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hA : (m.factorial : ℝ≥0∞) * volume X ≠ 0 := mul_ne_zero hfm hvX0
  have hB : (k.factorial : ℝ≥0∞) * volume Y ≠ 0 := mul_ne_zero hfk hvY0
  have hA' : (m.factorial : ℝ≥0∞) * volume X ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvXt
  have hB' : (k.factorial : ℝ≥0∞) * volume Y ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvYt
  unfold systolicRatio
  rw [hZ, hV, ← hXY, pow_add, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hA) (Or.inl hA')]
  ring

end Viterbo.PP2
end

section
open Viterbo.PP2 in
theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X : Set (OAI.SymmetricPolar.Phase m)) (Y : Set (OAI.SymmetricPolar.Phase k))
    (hX : Viterbo.IsConvexDomain X) (hY : Viterbo.IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y)
    (hXY : Viterbo.cEHZ X = Viterbo.cEHZ Y) :
    Viterbo.systolicRatio (Viterbo.symplecticPProduct 2 X Y) =
      Viterbo.systolicRatio X * Viterbo.systolicRatio Y :=
  main m k hm hk X Y hX hY hX0 hY0 hXY

end
