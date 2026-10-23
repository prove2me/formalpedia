-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P20.analytic_zeroSet_hausdorffDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:24:15.618276+00:00
-- url     : https://prove2.me/submissions/0a321157-f022-4fcb-be29-d75b2300ad0d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter
open scoped Topology ContDiff NNReal Nat

namespace X6P20

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- the auxiliary map straightening the level set -/
def phi (B : E → ℝ) (L : E →L[ℝ] ℝ) (v : E) (y : E) : E := y + (B y - L y) • v

/-- local nullity of the zero set near a regular zero -/
theorem local_null (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U)
    (x0 : E) (hx0 : x0 ∈ U) (hL : fderiv ℝ B x0 ≠ 0) :
    ∃ r > 0, μ (Metric.closedBall x0 r ∩ B ⁻¹' {0}) = 0 := by
  set L := fderiv ℝ B x0 with hLdef
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra h; push Not at h; exact hL (ContinuousLinearMap.ext h)
  set v : E := (L w)⁻¹ • w with hv
  have hLv : L v = 1 := by simp [hv, hw]
  have hBd : ∀ y ∈ U, HasFDerivAt B (fderiv ℝ B y) y := fun y hy =>
    ((hB.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hcont : ContinuousOn (fun y => fderiv ℝ B y) U :=
    hB.continuousOn_fderiv_of_isOpen hU le_rfl
  -- strict derivative of phi at x0 is the identity
  have hstrict : HasStrictFDerivAt (phi B L v)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x0 := by
    have h1 : HasStrictFDerivAt B L x0 :=
      (hB.contDiffAt (hU.mem_nhds hx0)).hasStrictFDerivAt (by norm_num)
    have h2 : HasStrictFDerivAt (fun y => B y - L y) (L - L) x0 := h1.sub L.hasStrictFDerivAt
    have h3 := HasStrictFDerivAt.add (h2.smul_const v) (hasStrictFDerivAt_id x0)
    convert h3 using 1
    · funext h; simp [phi, add_comm]
    · ext h; simp
  obtain ⟨t, ht, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := (1/2 : ℝ≥0)) (Or.inr (by norm_num))
  -- neighbourhood where B' v > 1/2
  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ 1/2 < fderiv ℝ B y v := by
    refine Filter.Eventually.and (hU.mem_nhds hx0) ?_
    have hc : ContinuousAt (fun y => fderiv ℝ B y v) x0 :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp
        (hcont.continuousAt (hU.mem_nhds hx0))
    have : (1/2 : ℝ) < fderiv ℝ B x0 v := by rw [← hLdef, hLv]; norm_num
    exact hc.eventually (lt_mem_nhds this)
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem ht hev)
  refine ⟨r, hr, ?_⟩
  set s := Metric.closedBall x0 r ∩ B ⁻¹' {0} with hs
  have hsU : ∀ y ∈ s, y ∈ t ∧ y ∈ U ∧ 1/2 < fderiv ℝ B y v := fun y hy =>
    ⟨(hrsub hy.1).1, (hrsub hy.1).2.1, (hrsub hy.1).2.2⟩
  have hsmeas : MeasurableSet s := by
    have : IsClosed s := ContinuousOn.preimage_isClosed_of_isClosed
      (fun y hy => (hBd y (hrsub hy).2.1).continuousAt.continuousWithinAt)
      Metric.isClosed_closedBall isClosed_singleton
    exact this.measurableSet
  -- derivative of phi
  set D : E → E →L[ℝ] E := fun y =>
    ContinuousLinearMap.id ℝ E + (fderiv ℝ B y - L).smulRight v with hD
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt (phi B L v) (D y) s y := by
    intro y hy
    have h2 : HasFDerivAt (fun y => B y - L y) (fderiv ℝ B y - L) y :=
      (hBd y (hsU y hy).2.1).sub L.hasFDerivAt
    have h3 := (h2.smul_const v).add (hasFDerivAt_id y)
    have : HasFDerivAt (phi B L v) (D y) y := by
      convert h3 using 1
      · ext z; simp [phi, add_comm]
      · ext h; simp [hD, add_comm]
    exact this.hasFDerivWithinAt
  have hinj : InjOn (phi B L v) s := by
    have := happrox.injOn (by
      by_cases hE : Subsingleton E
      · exact Or.inl hE
      · right
        rw [not_subsingleton_iff_nontrivial] at hE
        simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
          ContinuousLinearMap.nnnorm_id, inv_one]
        norm_num)
    exact this.mono fun y hy => (hsU y hy).1
  have himage : μ (phi B L v '' s) = 0 := by
    apply measure_mono_null _ (Measure.addHaar_submodule μ (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) ?_)
    · rintro _ ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, phi, map_add,
        map_smul, hLv, smul_eq_mul, mul_one]
      have : B y = 0 := hy.2
      linarith
    · intro htop
      apply hw
      have : w ∈ LinearMap.ker (L : E →ₗ[ℝ] ℝ) := htop ▸ Submodule.mem_top
      simpa using this
  have hint := lintegral_abs_det_fderiv_le_addHaar_image μ hsmeas hderiv hinj
  rw [himage, nonpos_iff_eq_zero] at hint
  have hmeasf : AEMeasurable (fun y => ENNReal.ofReal |(D y).det|) (μ.restrict s) := by
    apply ContinuousOn.aemeasurable _ hsmeas
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply continuous_abs.comp_continuousOn
    apply ContinuousLinearMap.continuous_det.comp_continuousOn
    apply continuousOn_const.add
    have : ContinuousOn (fun y => fderiv ℝ B y - L) s :=
      (hcont.mono fun y hy => (hsU y hy).2.1).sub continuousOn_const
    exact ((ContinuousLinearMap.smulRightL ℝ E E).flip v).continuous.comp_continuousOn this
  rw [setLIntegral_eq_zero_iff' hsmeas hmeasf] at hint
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hint] with y hy hys
  have hdet : (D y).det ≠ 0 := by
    intro h0
    have hk := LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0
    apply hk
    rw [LinearMap.ker_eq_bot']
    intro h hh
    have hh' : h + (fderiv ℝ B y h - L h) • v = 0 := by simpa [hD] using hh
    have e1 := congrArg L hh'
    have e2 := congrArg (fderiv ℝ B y) hh'
    simp only [map_add, map_smul, hLv, smul_eq_mul, mul_one, map_zero] at e1 e2
    have hc := (hsU y hys).2.2
    have ha : fderiv ℝ B y h = 0 := by linarith
    have hb : L h = 0 := by
      rw [ha] at e2
      have : L h * fderiv ℝ B y v = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · linarith
    rw [ha, hb] at hh'
    simpa using hh'
  have := hy hys
  simp only [ENNReal.ofReal_eq_zero] at this
  exact hdet (abs_nonpos_iff.1 this)

/-- the regular zero set of a C¹ function on an open set is null -/
theorem regular_null (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U) :
    μ {x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0} = 0 := by
  apply measure_null_of_locally_null
  rintro x0 ⟨hx0, -, hL⟩
  obtain ⟨r, hr, h0⟩ := local_null μ U hU B hB x0 hx0 hL
  refine ⟨Metric.closedBall x0 r ∩ B ⁻¹' {0}, ?_, h0⟩
  have : Metric.closedBall x0 r ∈ 𝓝[{x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0}] x0 :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x0 hr)
  filter_upwards [this, self_mem_nhdsWithin] with y hy hy'
  exact ⟨hy, hy'.2.1⟩

end X6P20


namespace X6P20B

open QAlgorithms.Papers.Independent.Dependency50.P20

/-- the coordinate list of a multi-index -/
def lst {d : ℕ} (t : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap (fun j => List.replicate (t j) j)

theorem mixed_eq {d : ℕ} (t : Fin d → ℕ) (f : Ambient d → ℝ) :
    mixedPartial t f = (lst t).foldr (fun j g => coordinatePartial j g) f := rfl

theorem lst_count {d : ℕ} (t : Fin d → ℕ) (j : Fin d) : (lst t).count j = t j := by
  unfold lst
  rw [List.count_flatMap]
  have : (List.map (List.count j ∘ fun i => List.replicate (t i) i) (List.finRange d))
      = List.map (fun i => if i = j then t j else 0) (List.finRange d) := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, List.count_replicate]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, ← List.sum_toFinset _ (List.nodup_finRange d)]
  simp

theorem lst_sorted {d : ℕ} (t : Fin d → ℕ) : (lst t).Pairwise (· ≤ ·) := by
  unfold lst
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => by simp, ?_⟩
  refine (List.pairwise_lt_finRange d).imp ?_
  intro a b hab x hx y hy
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  exact hab.le

theorem lst_of_sorted {d : ℕ} (l : List (Fin d)) (hl : l.Pairwise (· ≤ ·)) :
    lst (fun i => l.count i) = l := by
  apply List.Perm.eq_of_pairwise' (lst_sorted _) hl
  rw [List.perm_iff_count]
  intro a
  rw [lst_count]

theorem lst_zero {d : ℕ} : lst (fun _ : Fin d => 0) = [] := by
  simp [lst]

section smooth
variable {d : ℕ} {U : Set (Ambient d)}

theorem cp_smooth (hU : IsOpen U) (j : Fin d) (g : Ambient d → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (coordinatePartial j g) U := by
  have := hg.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact this.clm_apply contDiffOn_const

theorem foldr_smooth (hU : IsOpen U) (l : List (Fin d)) (g : Ambient d → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (l.foldr (fun j g => coordinatePartial j g) g) U := by
  induction l with
  | nil => simpa using hg
  | cons j l ih => exact cp_smooth hU j _ ih

theorem mixed_smooth (hU : IsOpen U) (t : Fin d → ℕ) (g : Ambient d → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) : ContDiffOn ℝ ∞ (mixedPartial t g) U :=
  foldr_smooth hU _ g hg

theorem foldr_congr {V : Set (Ambient d)} (hV : IsOpen V) (l : List (Fin d))
    (f g : Ambient d → ℝ) (hfg : EqOn f g V) :
    EqOn (l.foldr (fun j g => coordinatePartial j g) f)
      (l.foldr (fun j g => coordinatePartial j g) g) V := by
  induction l with
  | nil => simpa using hfg
  | cons j l ih =>
    intro y hy
    simp only [List.foldr_cons, coordinatePartial]
    have : (l.foldr (fun j g => coordinatePartial j g) f) =ᶠ[𝓝 y]
        (l.foldr (fun j g => coordinatePartial j g) g) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hy) ih
    rw [this.fderiv_eq]

theorem foldr_zero (l : List (Fin d)) :
    l.foldr (fun j g => coordinatePartial j g) (fun _ : Ambient d => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    funext x; simp [coordinatePartial]

end smooth

/-- the derivative cover, assuming a germ (quasianalyticity) property at zeros -/
theorem cover {d : ℕ} (U : Set (Ambient d)) (hU_open : IsOpen U)
    (hU_connected : IsConnected U) (A : Ambient d → ℝ) (hA : ContDiffOn ℝ ∞ A U)
    (hgerm : ∀ x ∈ U, (∀ t : Fin d → ℕ, mixedPartial t A x = 0) →
      ∃ V : Set (Ambient d), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ EqOn A (fun _ => 0) V)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    zeroSet U A ⊆ ⋃ t : Fin d → ℕ, regularZeroSet U (mixedPartial t A) := by
  rintro x ⟨hxU, hx0⟩
  -- step a: some derivative is nonzero at x
  have hex : ∃ t : Fin d → ℕ, mixedPartial t A x ≠ 0 := by
    by_contra hall
    push Not at hall
    set Z := {y | y ∈ U ∧ ∀ t : Fin d → ℕ, mixedPartial t A y = 0} with hZ
    set W := ⋃ t : Fin d → ℕ, U ∩ (mixedPartial t A) ⁻¹' {0}ᶜ with hW
    have hZo : IsOpen Z := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hyU, hy⟩
      obtain ⟨V, hVo, hyV, hVU, hAV⟩ := hgerm y hyU hy
      filter_upwards [hVo.mem_nhds hyV] with z hz
      refine ⟨hVU hz, fun t => ?_⟩
      have := foldr_congr hVo (lst t) A _ hAV hz
      rw [mixed_eq, this, foldr_zero]
    have hWo : IsOpen W := by
      apply isOpen_iUnion
      intro t
      exact (mixed_smooth hU_open t A hA).continuousOn.isOpen_inter_preimage hU_open
        isOpen_compl_singleton
    have hdisj : Disjoint Z W := by
      rw [Set.disjoint_left]
      rintro y ⟨_, hy⟩ hyW
      obtain ⟨t, -, ht⟩ := Set.mem_iUnion.1 hyW
      exact ht (hy t)
    have hcov : U ⊆ Z ∪ W := by
      intro y hy
      by_cases h : ∀ t : Fin d → ℕ, mixedPartial t A y = 0
      · exact Or.inl ⟨hy, h⟩
      · push Not at h
        obtain ⟨t, ht⟩ := h
        exact Or.inr (Set.mem_iUnion.2 ⟨t, hy, ht⟩)
    have hsub := hU_connected.isPreconnected.subset_left_of_subset_union hZo hWo hdisj hcov
      ⟨x, hxU, hxU, hall⟩
    obtain ⟨x', hx'U, hx'⟩ := hA_nonzero
    have := (hsub hx'U).2 (fun _ => 0)
    rw [mixed_eq, lst_zero] at this
    exact hx' this
  -- step b: minimal length
  classical
  have hP : ∃ n, ∃ t : Fin d → ℕ, (lst t).length = n ∧ mixedPartial t A x ≠ 0 := by
    obtain ⟨t, ht⟩ := hex; exact ⟨_, t, rfl, ht⟩
  obtain ⟨t, htn, ht⟩ := Nat.find_spec hP
  have hmin := fun m (hm : m < Nat.find hP) => Nat.find_min hP hm
  rcases hl : lst t with _ | ⟨j, rest⟩
  · rw [mixed_eq, hl] at ht; exact absurd hx0 ht
  · have hsorted : rest.Pairwise (· ≤ ·) := by
      have := lst_sorted t; rw [hl] at this; exact this.of_cons
    set t' : Fin d → ℕ := fun i => rest.count i
    have hl' : lst t' = rest := lst_of_sorted rest hsorted
    have hlt : (lst t').length < Nat.find hP := by
      rw [← htn, hl, hl']; simp
    have h0 : mixedPartial t' A x = 0 := by
      have := hmin _ hlt
      push Not at this
      exact this t' rfl
    have hd : mixedPartial t A = coordinatePartial j (mixedPartial t' A) := by
      rw [mixed_eq, hl, List.foldr_cons, mixed_eq, hl']
    refine Set.mem_iUnion.2 ⟨t', hxU, h0, ?_⟩
    rw [hd] at ht
    intro hg
    apply ht
    rw [norm_eq_zero] at hg
    have : fderiv ℝ (mixedPartial t' A) x = 0 := by
      have := congrArg (InnerProductSpace.toDual ℝ (Ambient d)) hg
      simpa [gradient] using this
    simp [coordinatePartial, this]

end X6P20B

namespace X6P20D

open QAlgorithms.Papers.Independent.Dependency50.P20 X6P20B

variable {d : ℕ}

noncomputable def e (j : Fin d) : Ambient d := EuclideanSpace.single j 1

/-- iterated derivative on basis vectors = iterated coordinate partials -/
theorem iter_eq (U : Set (Ambient d)) (hU : IsOpen U) (A : Ambient d → ℝ)
    (hA : AnalyticOnNhd ℝ A U) :
    ∀ (n : ℕ) (v : Fin n → Fin d), ∀ y ∈ U,
      iteratedFDeriv ℝ n A y (fun k => e (v k)) =
        (List.ofFn v).foldr (fun j g => coordinatePartial j g) A y := by
  intro n
  induction n with
  | zero => intro v y _; simp
  | succ n ih =>
    intro v y hy
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    set Φ : ContinuousMultilinearMap ℝ (fun _ : Fin n => Ambient d) ℝ →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Ambient d) ℝ (Fin.tail fun k => e (v k))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n A) y :=
      (hA.iteratedFDeriv n y hy).differentiableAt
    have h1 : fderiv ℝ (fun z => Φ (iteratedFDeriv ℝ n A z)) y =
        Φ.comp (fderiv ℝ (iteratedFDeriv ℝ n A) y) :=
      (Φ.hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
    have h2 : (fun z => Φ (iteratedFDeriv ℝ n A z)) =ᶠ[𝓝 y]
        (List.ofFn fun i => v i.succ).foldr (fun j g => coordinatePartial j g) A := by
      filter_upwards [hU.mem_nhds hy] with z hz
      rw [← ih (fun i => v i.succ) z hz]
      rfl
    have h3 := congrArg (fun T => T (e (v 0))) h1
    simp only at h3
    rw [h2.fderiv_eq] at h3
    rw [coordinatePartial]
    change _ = fderiv ℝ _ y (e (v 0))
    rw [h3]
    rfl

/-- germ property of analytic functions in terms of mixed partials -/
theorem germ (U : Set (Ambient d)) (hU : IsOpen U) (A : Ambient d → ℝ)
    (hA : AnalyticOnNhd ℝ A U) (x : Ambient d) (hx : x ∈ U)
    (hall : ∀ t : Fin d → ℕ, mixedPartial t A x = 0) :
    ∃ V : Set (Ambient d), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ EqOn A (fun _ => 0) V := by
  have hsym := (hA x hx).contDiffAt (n := ω)
  -- all iterated derivatives on basis vectors vanish
  have hbasis : ∀ (n : ℕ) (v : Fin n → Fin d), iteratedFDeriv ℝ n A x (fun k => e (v k)) = 0 := by
    intro n v
    have hperm := hsym.iteratedFDeriv_comp_perm (fun k => e (v k)) (Tuple.sort v)
    rw [← hperm, show ((fun k => e (v k)) ∘ ⇑(Tuple.sort v)) =
      fun k => e ((v ∘ Tuple.sort v) k) from rfl, iter_eq U hU A hA n (v ∘ Tuple.sort v) x hx]
    have hs : (List.ofFn (v ∘ Tuple.sort v)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_ofFn]
      intro i j hij
      exact Tuple.monotone_sort v hij.le
    have := lst_of_sorted _ hs
    rw [← hall (fun i => (List.ofFn (v ∘ Tuple.sort v)).count i), mixed_eq, this]
  have hdiag : ∀ (n : ℕ) (y : Ambient d), iteratedFDeriv ℝ n A x (fun _ => y) = 0 := by
    intro n y
    have hy : y = ∑ j, y j • e j := by
      ext i
      simp [e, Pi.single_apply]
    rw [hy, ContinuousMultilinearMap.map_sum]
    apply Finset.sum_eq_zero
    intro r _
    rw [ContinuousMultilinearMap.map_smul_univ, hbasis n r, smul_zero]
  obtain ⟨p, r, hp⟩ := hA x hx
  refine ⟨U ∩ Metric.eball x r, hU.inter Metric.isOpen_eball, ⟨hx, Metric.mem_eball_self hp.r_pos⟩,
    inter_subset_left, ?_⟩
  rintro z ⟨-, hz⟩
  have hmem : z - x ∈ Metric.eball (0 : Ambient d) r := by
    rw [Metric.mem_eball] at hz
    rw [Metric.mem_eball, edist_zero_right, ← edist_eq_enorm_sub]
    exact hz
  have hs := hp.hasSum_iteratedFDeriv hmem
  simp only [hdiag, smul_zero, add_sub_cancel] at hs
  exact hs.unique hasSum_zero

end X6P20D


open Module

namespace X6P20E

open X6P20

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- local Hausdorff dimension bound of the zero set near a regular zero -/
theorem local_dimH (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U)
    (x0 : E) (hx0 : x0 ∈ U) (hL : fderiv ℝ B x0 ≠ 0) :
    ∃ r > 0, dimH (Metric.closedBall x0 r ∩ B ⁻¹' {0}) ≤ (finrank ℝ E - 1 : ℕ) := by
  set L := fderiv ℝ B x0 with hLdef
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra h; push Not at h; exact hL (ContinuousLinearMap.ext h)
  set v : E := (L w)⁻¹ • w with hv
  have hLv : L v = 1 := by simp [hv, hw]
  have hstrict : HasStrictFDerivAt (phi B L v)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x0 := by
    have h1 : HasStrictFDerivAt B L x0 :=
      (hB.contDiffAt (hU.mem_nhds hx0)).hasStrictFDerivAt (by norm_num)
    have h2 : HasStrictFDerivAt (fun y => B y - L y) (L - L) x0 := h1.sub L.hasStrictFDerivAt
    have h3 := HasStrictFDerivAt.add (h2.smul_const v) (hasStrictFDerivAt_id x0)
    convert h3 using 1
    · funext h; simp [phi, add_comm]
    · ext h; simp
  obtain ⟨t, ht, happrox⟩ :=
    hstrict.approximates_deriv_on_nhds (c := (1/2 : ℝ≥0)) (Or.inr (by norm_num))
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
  refine ⟨r, hr, ?_⟩
  set s := Metric.closedBall x0 r ∩ B ⁻¹' {0} with hs
  have hc : Subsingleton E ∨ (1/2 : ℝ≥0) <
      ‖(((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases hE : Subsingleton E
    · exact Or.inl hE
    · right
      rw [not_subsingleton_iff_nontrivial] at hE
      simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one]
      norm_num
  have hanti := (happrox.mono_set (fun y hy => hrsub hy.1)).antilipschitz (s := s) hc
  have h1 : dimH s ≤ dimH (phi B L v '' s) := by
    have := hanti.le_dimH_image univ
    rw [← (isometry_subtype_coe (s := s)).dimH_image univ, Subtype.coe_image_univ] at this
    refine this.trans (dimH_mono ?_)
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩
  set K := LinearMap.ker (L : E →ₗ[ℝ] ℝ)
  have h2 : phi B L v '' s ⊆ (K : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [K, SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, phi, map_add,
      map_smul, hLv, smul_eq_mul, mul_one]
    have : B y = 0 := hy.2
    linarith
  have hK : K ≠ ⊤ := by
    intro htop
    apply hw
    have : w ∈ K := htop ▸ Submodule.mem_top
    simpa [K] using this
  have h3 : dimH (K : Set E) = finrank ℝ K := by
    rw [← Real.dimH_univ_eq_finrank K, ← (isometry_subtype_coe (s := (K : Set E))).dimH_image univ,
      Subtype.coe_image_univ]
  have h4 : finrank ℝ K ≤ finrank ℝ E - 1 := by
    have := Submodule.finrank_lt hK
    omega
  calc dimH s ≤ dimH (K : Set E) := h1.trans (dimH_mono h2)
    _ = finrank ℝ K := h3
    _ ≤ (finrank ℝ E - 1 : ℕ) := by exact_mod_cast h4

/-- the regular zero set of a C¹ function has Hausdorff dimension ≤ dim - 1 -/
theorem regular_dimH (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U) :
    dimH {x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0} ≤ (finrank ℝ E - 1 : ℕ) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x0, ⟨hx0, -, hL⟩, hx⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hlt
  obtain ⟨r, hr, h0⟩ := local_dimH U hU B hB x0 hx0 hL
  have : Metric.closedBall x0 r ∩ B ⁻¹' {0} ∈
      𝓝[{x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0}] x0 := by
    have hb : Metric.closedBall x0 r ∈ 𝓝[{x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0}] x0 :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x0 hr)
    filter_upwards [hb, self_mem_nhdsWithin] with y hy hy'
    exact ⟨hy, hy'.2.1⟩
  exact absurd (hx _ this) (not_lt.2 h0)

end X6P20E

open X6P20 X6P20B X6P20D X6P20E QAlgorithms.Papers.Independent.Dependency50.P20 in
theorem solution
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (A : Ambient d → ℝ) (hA : AnalyticOnNhd ℝ A U)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    dimH (zeroSet U A) ≤ (↑(d - 1) : ENNReal) := by
  have hcov := cover U hU_open hU_connected A (hA.contDiffOn hU_open.uniqueDiffOn)
    (fun x hx hall => germ U hU_open A hA x hx hall) hA_nonzero
  refine (dimH_mono hcov).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun t => ?_
  have hsm : ContDiffOn ℝ 1 (mixedPartial t A) U :=
    (mixed_smooth hU_open t A (hA.contDiffOn hU_open.uniqueDiffOn)).of_le (by simp)
  have := regular_dimH U hU_open _ hsm
  rw [finrank_euclideanSpace_fin] at this
  refine (dimH_mono ?_).trans this
  rintro x ⟨hx, h0, hg⟩
  refine ⟨hx, h0, fun hf => hg ?_⟩
  simp [gradient, hf]
