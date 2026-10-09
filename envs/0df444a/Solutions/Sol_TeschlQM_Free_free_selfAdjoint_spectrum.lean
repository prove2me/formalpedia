-- Prove2me | solution 1 for TeschlQM.Free.free_selfAdjoint_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:21:16.384555+00:00
-- url     : https://prove2.me/submissions/a7931cf2-502c-4776-bc45-46e32aeb363a

import Mathlib
import Definitions.Def_TeschlQM_Free_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace P2a4df184

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_unique (A : H →ₗ.[ℂ] H) (z : ℂ) (R R' : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R) (hR' : TeschlQM.Shared.IsResolventAt A z R') :
    R = R' := by
  ext φ
  obtain ⟨h, hφ⟩ := hR'.1 φ
  have := hR.2 ⟨R' φ, h⟩
  have e : ((⟨R' φ, h⟩ : A.domain) : H) = R' φ := rfl
  rw [e, hφ] at this
  exact this

theorem selfAdjoint_of_resolvent (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (-1) R)
    (hsym : ∀ φ ψ : H, ⟪R φ, ψ⟫_ℂ = ⟪φ, R ψ⟫_ℂ) [CompleteSpace H] : IsSelfAdjoint A := by
  have F1 : ∀ x : A.domain, (x : H) = R (A x + x) := by
    intro x
    have := hR.2 x
    rw [neg_smul, one_smul, sub_neg_eq_add] at this
    exact this.symm
  have F2 : ∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ + R φ = φ := by
    intro φ
    obtain ⟨h, e⟩ := hR.1 φ
    refine ⟨h, ?_⟩
    rw [neg_smul, one_smul, sub_neg_eq_add] at e
    exact e
  have hd : Dense (A.domain : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro v hv
    have h0 : ∀ φ : H, ⟪φ, R v⟫_ℂ = 0 := by
      intro φ
      rw [← hsym]
      obtain ⟨h, _⟩ := F2 φ
      exact (Submodule.mem_orthogonal _ _).1 hv _ h
    have hRv : R v = 0 := inner_self_eq_zero.1 (h0 (R v))
    obtain ⟨h, e⟩ := F2 v
    have : (⟨R v, h⟩ : A.domain) = 0 := Subtype.ext hRv
    rw [this, LinearPMap.map_zero, hRv, add_zero] at e
    exact e.symm
  have hfa : A.IsFormalAdjoint A := by
    intro x y
    calc ⟪A x, (y : H)⟫_ℂ = ⟪A x + x, (y : H)⟫_ℂ - ⟪(x : H), (y : H)⟫_ℂ := by
          rw [← inner_sub_left, add_sub_cancel_right]
      _ = ⟪A x + x, R (A y + y)⟫_ℂ - ⟪(x : H), (y : H)⟫_ℂ := by rw [← F1 y]
      _ = ⟪R (A x + x), A y + y⟫_ℂ - ⟪(x : H), (y : H)⟫_ℂ := by rw [hsym]
      _ = ⟪(x : H), A y + y⟫_ℂ - ⟪(x : H), (y : H)⟫_ℂ := by rw [← F1 x]
      _ = ⟪(x : H), A y⟫_ℂ := by rw [← inner_sub_right, add_sub_cancel_right]
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hfa.le_adjoint hd)
  have hadj := LinearPMap.adjoint_isFormalAdjoint hd
  have key : ∀ y : (LinearPMap.adjoint A).domain, ∃ h : (y : H) ∈ A.domain,
      A ⟨y, h⟩ = LinearPMap.adjoint A y := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, LinearPMap.adjoint A y = w := ⟨_, rfl⟩
    rw [hw]
    have hy : (y : H) = R (w + y) := by
      apply ext_inner_right ℂ
      intro φ
      obtain ⟨h, e⟩ := F2 φ
      have h1 : ⟪w, R φ⟫_ℂ = ⟪(y : H), φ - R φ⟫_ℂ := by
        have := hadj y ⟨R φ, h⟩
        rw [hw, eq_sub_of_add_eq e] at this
        exact this
      rw [hsym, inner_add_left, h1, inner_sub_right]
      ring
    obtain ⟨h, e⟩ := F2 (w + y)
    have h' : (y : H) ∈ A.domain := by rw [hy]; exact h
    refine ⟨h', ?_⟩
    have hsub : (⟨y, h'⟩ : A.domain) = ⟨R (w + y), h⟩ := Subtype.ext hy
    rw [hsub]
    calc A ⟨R (w + y), h⟩ = (w + y) - R (w + y) := eq_sub_of_add_eq e
      _ = w := by rw [← hy]; abel
  refine ⟨fun y hy => (key ⟨y, hy⟩).1, fun y x hxy => ?_⟩
  obtain ⟨h, e⟩ := key y
  rw [← e]
  congr 1
  exact Subtype.ext hxy

end Abstract

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable abbrev L2 (n : ℕ) := Lp ℂ 2 (volume : Measure (E n))

noncomputable abbrev U (n : ℕ) : L2 n ≃ₗᵢ[ℂ] L2 n := Lp.fourierTransformₗᵢ (E n) ℂ

noncomputable def sym (n : ℕ) (ξ : E n) : ℂ := ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem sym_cont (n : ℕ) : Continuous (sym n) := by unfold sym; fun_prop

def half : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ici 0

theorem sym_mem_half {n : ℕ} (ξ : E n) : sym n ξ ∈ half := ⟨_, Set.mem_Ici.2 (by positivity), rfl⟩

theorem half_closed : IsClosed half :=
  Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici

theorem mem_dom {n : ℕ} (ψ : L2 n) :
    ψ ∈ (TeschlQM.Free.freeHamiltonian n).domain ↔
      MemLp (fun ξ => sym n ξ * (U n ψ : E n → ℂ) ξ) 2 volume := Iff.rfl

theorem U_H0 {n : ℕ} (x : L2 n) (h : x ∈ (TeschlQM.Free.freeHamiltonian n).domain) :
    (U n (TeschlQM.Free.freeHamiltonian n ⟨x, h⟩) : E n → ℂ) =ᵐ[volume]
      fun ξ => sym n ξ * (U n x : E n → ℂ) ξ := by
  have : U n (TeschlQM.Free.freeHamiltonian n ⟨x, h⟩) =
      MemLp.toLp (fun ξ => sym n ξ * (U n x : E n → ℂ) ξ) ((mem_dom _).1 h) := by
    show U n ((U n).symm _) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [this]
  exact MemLp.coeFn_toLp _

theorem memLp_mul {n : ℕ} (g : E n → ℂ) (hg : Measurable g) (C : ℝ) (hC : ∀ ξ, ‖g ξ‖ ≤ C)
    (f : L2 n) : MemLp (fun ξ => g ξ * (f : E n → ℂ) ξ) 2 volume :=
  MemLp.of_le_mul (Lp.memLp f) (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun ξ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

noncomputable def mulCLM {n : ℕ} (g : E n → ℂ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ ξ, ‖g ξ‖ ≤ C) : L2 n →L[ℂ] L2 n :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul g hg C hC f).toLp _
      map_add' := by
        intro a b
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add a b] with x hx
        simp only [Pi.add_apply, hx, mul_add]
      map_smul' := by
        intro c a
        rw [← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c a] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul, RingHom.id_apply]
        ring }
    C (by
      intro f
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_mul g hg C hC f).coeFn_toLp] with ξ hξ
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hξ, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

theorem mulCLM_ae {n : ℕ} (g : E n → ℂ) (hg : Measurable g) (C : ℝ) (hC : ∀ ξ, ‖g ξ‖ ≤ C)
    (f : L2 n) : (mulCLM g hg C hC f : E n → ℂ) =ᵐ[volume] fun ξ => g ξ * (f : E n → ℂ) ξ :=
  (memLp_mul g hg C hC f).coeFn_toLp

/-! ## Q1: explicit resolvent off `[0, ∞)` -/

noncomputable def dz (z : ℂ) : ℝ := Metric.infDist z half

theorem dz_pos {z : ℂ} (hz : z ∉ half) : 0 < dz z :=
  (half_closed.notMem_iff_infDist_pos ⟨0, 0, Set.mem_Ici.2 le_rfl, by simp⟩).1 hz

theorem dz_le {n : ℕ} (z : ℂ) (ξ : E n) : dz z ≤ ‖sym n ξ - z‖ := by
  rw [norm_sub_rev, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem (sym_mem_half ξ)

theorem sym_sub_ne {n : ℕ} {z : ℂ} (hz : z ∉ half) (ξ : E n) : sym n ξ - z ≠ 0 := by
  intro h
  have := dz_le (n := n) z ξ
  rw [h, norm_zero] at this
  exact absurd this (not_le.2 (dz_pos hz))

noncomputable def mz (n : ℕ) (z : ℂ) (ξ : E n) : ℂ := (sym n ξ - z)⁻¹

theorem mz_meas (n : ℕ) (z : ℂ) : Measurable (mz n z) :=
  ((sym_cont n).measurable.sub_const z).inv

theorem mz_le {n : ℕ} {z : ℂ} (hz : z ∉ half) (ξ : E n) : ‖mz n z ξ‖ ≤ 1 / dz z := by
  rw [mz, norm_inv, one_div]
  exact inv_anti₀ (dz_pos hz) (dz_le z ξ)

theorem sym_mz_le {n : ℕ} {z : ℂ} (hz : z ∉ half) (ξ : E n) :
    ‖sym n ξ * mz n z ξ‖ ≤ 1 + ‖z‖ * (1 / dz z) := by
  have : sym n ξ * mz n z ξ = 1 + z * mz n z ξ := by
    rw [mz]
    field_simp [sym_sub_ne hz ξ]
    ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul]
  gcongr
  exact mz_le hz ξ

noncomputable def Rz (n : ℕ) {z : ℂ} (hz : z ∉ half) : L2 n →L[ℂ] L2 n :=
  ((U n).symm.toContinuousLinearEquiv : L2 n →L[ℂ] L2 n).comp
    ((mulCLM (mz n z) (mz_meas n z) _ (mz_le hz)).comp
      ((U n).toContinuousLinearEquiv : L2 n →L[ℂ] L2 n))

theorem U_Rz {n : ℕ} {z : ℂ} (hz : z ∉ half) (φ : L2 n) :
    U n (Rz n hz φ) = mulCLM (mz n z) (mz_meas n z) _ (mz_le hz) (U n φ) := by
  simp [Rz]

theorem U_Rz_ae {n : ℕ} {z : ℂ} (hz : z ∉ half) (φ : L2 n) :
    (U n (Rz n hz φ) : E n → ℂ) =ᵐ[volume] fun ξ => mz n z ξ * (U n φ : E n → ℂ) ξ := by
  rw [U_Rz]; exact mulCLM_ae _ _ _ _ _

theorem isResolvent_Rz {n : ℕ} {z : ℂ} (hz : z ∉ half) :
    TeschlQM.Shared.IsResolventAt (TeschlQM.Free.freeHamiltonian n) z (Rz n hz) := by
  constructor
  · intro φ
    have hmem : Rz n hz φ ∈ (TeschlQM.Free.freeHamiltonian n).domain := by
      rw [mem_dom]
      refine MemLp.of_le_mul (c := 1 + ‖z‖ * (1 / dz z)) (Lp.memLp (U n φ))
        (((sym_cont n).measurable.aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)) ?_
      filter_upwards [U_Rz_ae hz φ] with ξ hξ
      rw [hξ, ← mul_assoc, norm_mul]
      exact mul_le_mul_of_nonneg_right (sym_mz_le hz ξ) (norm_nonneg _)
    refine ⟨hmem, ?_⟩
    apply (U n).injective
    apply Lp.ext
    rw [map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (U n (TeschlQM.Free.freeHamiltonian n ⟨_, hmem⟩))
      (z • U n (Rz n hz φ)), Lp.coeFn_smul z (U n (Rz n hz φ)), U_H0 _ hmem,
      U_Rz_ae hz φ] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, h4, ← sub_mul, mz, ← mul_assoc,
      mul_inv_cancel₀ (sym_sub_ne hz ξ), one_mul]
  · rintro ⟨x, hx⟩
    apply (U n).injective
    apply Lp.ext
    filter_upwards [U_Rz_ae hz (TeschlQM.Free.freeHamiltonian n ⟨x, hx⟩ - z • x),
      Lp.coeFn_sub (U n (TeschlQM.Free.freeHamiltonian n ⟨x, hx⟩)) (z • U n x),
      Lp.coeFn_smul z (U n x), U_H0 x hx] with ξ h1 h2 h3 h4
    rw [h1, map_sub, map_smul, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul, ← sub_mul,
      mz, ← mul_assoc, inv_mul_cancel₀ (sym_sub_ne hz ξ), one_mul]

theorem inner_Rz {n : ℕ} {z : ℂ} (hz : z ∉ half) (ψ : L2 n) :
    ⟪ψ, Rz n hz ψ⟫_ℂ = ∫ ξ, mz n z ξ * ((‖(U n ψ : E n → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← (U n).inner_map_map, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [U_Rz_ae hz ψ] with ξ h
  rw [h, RCLike.inner_apply']
  have := RCLike.conj_mul ((U n ψ : E n → ℂ) ξ)
  push_cast
  rw [mul_left_comm, this]
  rfl

theorem Rz_symm {n : ℕ} {z : ℂ} (hz : z ∉ half) (hzr : z.im = 0) (φ ψ : L2 n) :
    ⟪Rz n hz φ, ψ⟫_ℂ = ⟪φ, Rz n hz ψ⟫_ℂ := by
  rw [← (U n).inner_map_map, ← (U n).inner_map_map φ, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [U_Rz_ae hz ψ, U_Rz_ae hz φ] with ξ h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  have : (starRingEnd ℂ) (mz n z ξ) = mz n z ξ := by
    have hw : (sym n ξ - z).im = 0 := by
      rw [Complex.sub_im, sym, Complex.ofReal_im, hzr, sub_zero]
    rw [Complex.conj_eq_iff_im, mz, Complex.inv_im, hw, neg_zero, zero_div]
  rw [this]
  ring

/-! ## Q3: `[0, ∞)` lies in the spectrum (Weyl sequence) -/

theorem not_resolvent {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) (R : L2 n →L[ℂ] L2 n)
    (hR : TeschlQM.Shared.IsResolventAt (TeschlQM.Free.freeHamiltonian n) (t : ℂ) R) : False := by
  set ε : ℝ := 1 / (‖R‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  set A : Set (E n) := {ξ | |4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 - t| < ε} with hA
  have hAo : IsOpen A := isOpen_lt (by fun_prop) continuous_const
  have hAne : A.Nonempty := by
    refine ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (Real.sqrt t / (2 * Real.pi)), ?_⟩
    show |4 * Real.pi ^ 2 * ‖EuclideanSpace.single (⟨0, hn⟩ : Fin n)
      (Real.sqrt t / (2 * Real.pi))‖ ^ 2 - t| < ε
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt ht]
    have : 4 * Real.pi ^ 2 * (t / (2 * Real.pi) ^ 2) - t = 0 := by
      field_simp; ring
    rw [this, abs_zero]; exact hε0
  have hAb : A ⊆ Metric.closedBall 0 (1 + t + ε) := by
    intro ξ hξ
    have h1 : |4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 - t| < ε := hξ
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 := (abs_lt.1 h1).2
    have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h3 : ‖ξ‖ ^ 2 ≤ t + ε := by nlinarith [sq_nonneg ‖ξ‖]
    nlinarith [norm_nonneg ξ]
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAfin : volume A ≠ ⊤ :=
    ((measure_mono hAb).trans_lt measure_closedBall_lt_top).ne
  have hApos : volume A ≠ 0 := hAo.measure_ne_zero volume hAne
  set f : L2 n := indicatorConstLp 2 hAm hAfin (1 : ℂ) with hf
  have hfae := (indicatorConstLp_coeFn : (f : E n → ℂ) =ᵐ[volume] A.indicator fun _ => (1 : ℂ))
  set ψ : L2 n := (U n).symm f with hψ
  have hUψ : U n ψ = f := (U n).apply_symm_apply f
  have hpt : ∀ ξ, ‖(sym n ξ - t) * A.indicator (fun _ => (1 : ℂ)) ξ‖ ≤
      ε * ‖A.indicator (fun _ => (1 : ℂ)) ξ‖ := by
    intro ξ
    by_cases hξ : ξ ∈ A
    · rw [Set.indicator_of_mem hξ, mul_one, norm_one, mul_one, sym, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hξ
    · rw [Set.indicator_of_notMem hξ]; simp
  have hdom : ψ ∈ (TeschlQM.Free.freeHamiltonian n).domain := by
    rw [mem_dom, hUψ]
    refine MemLp.of_le_mul (c := t + ε) (Lp.memLp f)
      (((sym_cont n).measurable.aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hfae] with ξ hξ
    rw [hξ]
    have h1 := hpt ξ
    have h2 : sym n ξ * A.indicator (fun _ => (1 : ℂ)) ξ =
        (sym n ξ - t) * A.indicator (fun _ => (1 : ℂ)) ξ + t * A.indicator (fun _ => (1 : ℂ)) ξ := by
      ring
    rw [h2]
    have h3 : ‖(t : ℂ) * A.indicator (fun _ => (1 : ℂ)) ξ‖ = t * ‖A.indicator (fun _ => (1 : ℂ)) ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    refine (norm_add_le _ _).trans ?_
    rw [h3]
    linarith
  set g : L2 n := TeschlQM.Free.freeHamiltonian n ⟨ψ, hdom⟩ - (t : ℂ) • ψ with hg
  have hgle : ‖g‖ ≤ ε * ‖ψ‖ := by
    rw [← (U n).norm_map g, ← (U n).norm_map ψ, hUψ]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    rw [hg, map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (U n (TeschlQM.Free.freeHamiltonian n ⟨ψ, hdom⟩))
      ((t : ℂ) • U n ψ), Lp.coeFn_smul (t : ℂ) (U n ψ), U_H0 ψ hdom, hfae] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, hUψ, h4, ← sub_mul]
    exact hpt ξ
  have hψg : R g = ψ := hR.2 ⟨ψ, hdom⟩
  have hψpos : 0 < ‖ψ‖ := by
    rw [← (U n).norm_map ψ, hUψ, hf, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top,
      norm_one, one_mul]
    apply Real.rpow_pos_of_pos
    exact ENNReal.toReal_pos hApos hAfin
  have h1 : ‖ψ‖ ≤ ‖R‖ * (ε * ‖ψ‖) := by
    calc ‖ψ‖ = ‖R g‖ := by rw [hψg]
      _ ≤ ‖R‖ * ‖g‖ := R.le_opNorm g
      _ ≤ ‖R‖ * (ε * ‖ψ‖) := by gcongr
  have h2 : ‖R‖ * ε < 1 := by
    rw [hε, mul_one_div, div_lt_one (by positivity)]; linarith
  nlinarith

/-! ## Q4: the spectral measure is absolutely continuous -/

theorem null_norm_preimage {n : ℕ} (hn : 0 < n) (T : Set ℝ) (hT : MeasurableSet T)
    (hT0 : volume T = 0) : volume {ξ : E n | ‖ξ‖ ∈ T} = 0 := by
  haveI : Nontrivial (E n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hk : ∀ k : ℕ, volume {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} = 0 := by
    intro k
    have hS : MeasurableSet (T ∩ Set.Iio (k : ℝ)) := hT.inter measurableSet_Iio
    have hm : MeasurableSet {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} := measurable_norm hS
    have hfin : volume {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} ≠ ⊤ := by
      refine ((measure_mono ?_).trans_lt (measure_ball_lt_top (x := (0 : E n)) (r := k))).ne
      intro ξ hξ
      rw [Metric.mem_ball, dist_zero_right]; exact hξ.2
    have hI := integral_fun_norm_addHaar (volume : Measure (E n))
      ((T ∩ Set.Iio (k : ℝ)).indicator (1 : ℝ → ℝ))
    have hR0 : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ (E n) - 1) •
        (T ∩ Set.Iio (k : ℝ)).indicator (1 : ℝ → ℝ) y = 0 := by
      apply integral_eq_zero_of_ae
      have : ∀ᵐ y ∂(volume : Measure ℝ), y ∉ T := measure_eq_zero_iff_ae_notMem.1 hT0
      filter_upwards [ae_restrict_of_ae this] with y hy
      simp [Set.indicator_of_notMem (fun h : y ∈ T ∩ Set.Iio (k : ℝ) => hy h.1)]
    rw [hR0, smul_zero, smul_zero] at hI
    have hL : (fun ξ : E n => (T ∩ Set.Iio (k : ℝ)).indicator (1 : ℝ → ℝ) ‖ξ‖) =
        {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)}.indicator 1 := by
      funext ξ
      by_cases h : ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show ξ ∈ {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} from h),
          Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show ξ ∉ {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} from h)]
    rw [hL, integral_indicator_one hm] at hI
    exact (measureReal_eq_zero_iff hfin).1 hI
  have hU : {ξ : E n | ‖ξ‖ ∈ T} ⊆ ⋃ k : ℕ, {ξ : E n | ‖ξ‖ ∈ T ∩ Set.Iio (k : ℝ)} := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := exists_nat_gt ‖ξ‖
    exact Set.mem_iUnion.2 ⟨k, hξ, hk⟩
  exact measure_mono_null hU (measure_iUnion_null hk)

theorem null_sym_preimage {n : ℕ} (hn : 0 < n) (s : Set ℝ) (hs0 : volume s = 0) :
    volume {ξ : E n | 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ∈ s} = 0 := by
  haveI : Nontrivial (E n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  set gfun : ℝ → ℝ := fun x => Real.sqrt x / (2 * Real.pi) with hgfun
  have hdiff : DifferentiableOn ℝ gfun (s ∩ Set.Ioi 0) := by
    intro x hx
    exact ((Real.hasDerivAt_sqrt (ne_of_gt hx.2)).differentiableAt.div_const _).differentiableWithinAt
  have hT0 : volume (gfun '' (s ∩ Set.Ioi 0)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null Set.inter_subset_left hs0)
  set T' := toMeasurable volume (gfun '' (s ∩ Set.Ioi 0))
  have hT'0 : volume T' = 0 := by rw [measure_toMeasurable]; exact hT0
  have hsub : {ξ : E n | 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ∈ s} ⊆ {0} ∪ {ξ : E n | ‖ξ‖ ∈ T'} := by
    intro ξ hξ
    by_cases h0 : ξ = 0
    · exact Or.inl h0
    · right
      apply subset_toMeasurable
      have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 h0
      refine ⟨4 * Real.pi ^ 2 * ‖ξ‖ ^ 2, ⟨hξ, Set.mem_Ioi.2 (by positivity)⟩, ?_⟩
      have : 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ 2 := by ring
      simp only [hgfun]
      rw [this, Real.sqrt_sq (by positivity)]
      field_simp
  refine measure_mono_null hsub (measure_union_null (measure_singleton 0) ?_)
  exact null_norm_preimage hn T' (measurableSet_toMeasurable _ _) hT'0

theorem spectral_ac {n : ℕ} (hn : 0 < n) (f : L2 n) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ ≪ volume ∧ ∀ z : ℂ,
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ =
        ∫ ξ, mz n z ξ * ((‖(f : E n → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
  set φ : E n → ℝ := fun ξ => 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with hφ
  have hφm : Measurable φ := by fun_prop
  set d : E n → NNReal := fun ξ => ‖(f : E n → ℂ) ξ‖₊ ^ 2 with hd
  have hdm : Measurable d := (Lp.stronglyMeasurable f).measurable.nnnorm.pow_const 2
  set ν : Measure (E n) := volume.withDensity (fun ξ => (d ξ : ENNReal)) with hν
  have hνfin : IsFiniteMeasure ν := by
    refine isFiniteMeasure_withDensity ?_
    have hi := (Lp.memLp f).integrable_norm_pow two_ne_zero
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hi.2)
    apply lintegral_congr
    intro ξ
    simp [hd, enorm, nnnorm_pow]
  refine ⟨Measure.map φ ν, inferInstance, ?_, ?_⟩
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
    rw [Measure.map_apply hφm hs]
    exact withDensity_absolutelyContinuous _ _ (null_sym_preimage hn s hs0)
  · intro z
    rw [integral_map hφm.aemeasurable (by fun_prop : Measurable fun t : ℝ => ((t : ℂ) - z)⁻¹).aestronglyMeasurable,
      hν, integral_withDensity_eq_integral_smul hdm]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [NNReal.smul_def, Complex.real_smul, mz, sym, mul_comm]
    simp [hd, hφ]

end P2a4df184

open TeschlQM.Free MeasureTheory InnerProductSpace in
theorem solution (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (freeHamiltonian n) ∧
      TeschlQM.Shared.spectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      ∀ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ ≪ volume ∧
          ∀ z : ℂ, z.im ≠ 0 →
            ∀ R : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
                Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
              TeschlQM.Shared.IsResolventAt (freeHamiltonian n) z R →
                ⟪ψ, R ψ⟫_ℂ = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ := by
  have hz1 : (-1 : ℂ) ∉ P2a4df184.half := by
    rintro ⟨t, ht, h⟩
    have := congrArg Complex.re h
    simp at this
    linarith [Set.mem_Ici.1 ht]
  refine ⟨?_, ?_, ?_⟩
  · exact P2a4df184.selfAdjoint_of_resolvent _ (P2a4df184.Rz n hz1)
      (P2a4df184.isResolvent_Rz hz1) (P2a4df184.Rz_symm hz1 (by simp))
  · ext z
    simp only [TeschlQM.Shared.spectrum, TeschlQM.Shared.resolventSet, Set.mem_compl_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hz
      exact h ⟨_, P2a4df184.isResolvent_Rz hz⟩
    · rintro ⟨t, ht, rfl⟩ ⟨R, hR⟩
      exact P2a4df184.not_resolvent hn t ht R hR
  · intro ψ
    obtain ⟨μ, hfin, hac, hint⟩ := P2a4df184.spectral_ac hn (P2a4df184.U n ψ)
    refine ⟨μ, hfin, hac, fun z hzim R hR => ?_⟩
    have hz : z ∉ P2a4df184.half := by
      rintro ⟨t, _, rfl⟩
      simp at hzim
    rw [P2a4df184.resolvent_unique _ _ _ _ hR (P2a4df184.isResolvent_Rz hz),
      P2a4df184.inner_Rz hz, hint z]
