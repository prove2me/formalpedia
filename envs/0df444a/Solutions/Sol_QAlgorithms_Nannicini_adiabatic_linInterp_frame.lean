-- Prove2me | solution 1 for QAlgorithms.Nannicini.adiabatic_linInterp_frame
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T15:01:26.326979+00:00
-- url     : https://prove2.me/submissions/d9bb7e18-94b8-47be-8d2b-c376a46873f6

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Theorems.Thm_QAlgorithms_Nannicini_linInterp_spectral_projector_regular
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique

set_option autoImplicit false

open QAlgorithms



open QAlgorithms.Nannicini

theorem solution.{u} : ∃ K : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (HI HF : Matrix ι ι ℂ), HI.IsHermitian → HF.IsHermitian →
    ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
    ∀ (φ0 : EuclideanSpace ℂ ι), IsState φ0 → act (linInterp HI HF 0) φ0 = (lam 0 : ℂ) • φ0 →
    ∀ (γ : ℝ), 0 < γ →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
    ∃ u u' v v' : ℝ → EuclideanSpace ℂ ι, u 0 = φ0 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt u (u' s) (Set.Icc 0 1) s ∧ HasDerivWithinAt v (v' s) (Set.Icc 0 1) s ∧
        IsState (u s) ∧ act (linInterp HI HF s) (u s) = (lam s : ℂ) • u s ∧
        act (linInterp HI HF s) (v s) - (lam s : ℂ) • v s = u' s ∧
        ‖v s‖ ≤ K * specNorm (HF - HI) / γ ^ 2 ∧
        ‖v' s‖ ≤ K * specNorm (HF - HI) ^ 2 / γ ^ 3 := by
  obtain ⟨K0, hK0⟩ := linInterp_spectral_projector_regular.{u}
  refine ⟨2 * max K0 0 + 1, ?_⟩
  intro ι _ _ HI HF hI hF lam hlam φ0 hφ0 hφ0e γ hγ hgap
  obtain ⟨P, P', R, R', hP'c, hS⟩ := hK0 HI HF hI hF lam hlam γ hγ hgap
  set N := specNorm (HF - HI) with hN
  set Dl : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) (HF - HI) with hDldef
  have hDl : ∀ x, act (HF - HI) x = Dl x := fun x => rfl
  have hDln : ‖Dl‖ = N := rfl
  have hN0 : 0 ≤ N := hDln ▸ norm_nonneg _
  set K' := max K0 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have key : ∀ (L : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (x : EuclideanSpace ℂ ι)
      (a b : ℝ), ‖L‖ ≤ a → ‖x‖ ≤ b → 0 ≤ a → ‖L x‖ ≤ a * b := fun L x a b hL hx ha =>
    (L.le_opNorm x).trans (mul_le_mul hL hx (norm_nonneg _) ha)
  have hri : ∀ z w : EuclideanSpace ℂ ι, inner ℝ z w = (inner ℂ z w).re := by
    intro z w
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, mul_comm]
  have hPc : ContinuousOn P (Set.Icc 0 1) := fun s hs => (hS s hs).1.continuousWithinAt
  have happ : ∀ {F : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)}
      {F0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {y : ℝ → EuclideanSpace ℂ ι}
      {y0 : EuclideanSpace ℂ ι} {s : ℝ}, HasDerivWithinAt F F0 (Set.Icc 0 1) s →
      HasDerivWithinAt y y0 (Set.Icc 0 1) s →
      HasDerivWithinAt (fun t => F t (y t)) (F0 (y s) + F s y0) (Set.Icc 0 1) s := by
    intro F F0 y y0 s hF hy
    have hF' : HasDerivWithinAt (fun t => (F t).restrictScalars ℝ) (F0.restrictScalars ℝ)
        (Set.Icc 0 1) s :=
      (ContinuousLinearMap.restrictScalarsL ℂ (EuclideanSpace ℂ ι) (EuclideanSpace ℂ ι) ℝ
        ℝ).hasFDerivAt.comp_hasDerivWithinAt s hF
    exact hF'.clm_apply hy
  -- `P P' P = 0`, from differentiating `P² = P`
  have hPPP : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, P s (P' s (P s x)) = 0 := by
    intro s hs x
    have hc0 : HasDerivWithinAt (fun _ : ℝ => P s x) 0 (Set.Icc 0 1) s :=
      hasDerivWithinAt_const _ _ _
    have h1 := happ (hS s hs).1 (happ (hS s hs).1 hc0)
    have h2 := happ (hS s hs).1 hc0
    have h2' : HasDerivWithinAt (fun t => P t (P t (P s x))) (P' s (P s x) + P s 0)
        (Set.Icc 0 1) s :=
      h2.congr_of_mem (fun t ht => (hS t ht).2.2.1 _) hs
    have h3 := (uniqueDiffOn_Icc zero_lt_one s hs).eq_deriv _ h1 h2'
    simp only [map_zero, add_zero, (hS s hs).2.2.1] at h3
    simpa using h3
  -- the bound `‖P'‖ ≤ 2N/γ`
  have hP'n : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖P' s x‖ ≤ 2 * N / γ * ‖x‖ := by
    intro s hs x
    obtain ⟨-, -, -, -, -, -, -, -, -, hP'f, hPn, hRn, -⟩ := hS s hs
    rw [hP'f, hDl, hDl]
    have hg : 0 ≤ 1 / γ := by positivity
    have a1 : ‖R s (Dl (P s x))‖ ≤ 1 / γ * (N * (1 * ‖x‖)) :=
      key _ _ _ _ hRn (key _ _ _ _ hDln.le (key _ _ _ _ hPn le_rfl zero_le_one) hN0) hg
    have a2 : ‖P s (Dl (R s x))‖ ≤ 1 * (N * (1 / γ * ‖x‖)) :=
      key _ _ _ _ hPn (key _ _ _ _ hDln.le (key _ _ _ _ hRn le_rfl hg) hN0) zero_le_one
    calc ‖-R s (Dl (P s x)) - P s (Dl (R s x))‖
        ≤ ‖R s (Dl (P s x))‖ + ‖P s (Dl (R s x))‖ := by
          rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]; exact norm_add_le _ _
      _ ≤ 1 / γ * (N * (1 * ‖x‖)) + 1 * (N * (1 / γ * ‖x‖)) := add_le_add a1 a2
      _ = 2 * N / γ * ‖x‖ := by ring
  -- the transport equation `u' = [P', P] u`, solved globally
  set c : ℝ → ℝ := fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hc
  have hcc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcmem : ∀ t, c t ∈ Set.Icc (0 : ℝ) 1 := fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
  have hceq : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t = t := fun t ht => by
    simp [hc, Set.projIcc_of_mem _ ht]
  set A : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    fun t => (P' t).comp (P t) - (P t).comp (P' t) with hA
  have hAc : ContinuousOn A (Set.Icc 0 1) := (hP'c.clm_comp hPc).sub (hPc.clm_comp hP'c)
  set B : ℝ → (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) :=
    fun t => (A (c t)).restrictScalars ℝ with hB
  have hBc : Continuous B :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (EuclideanSpace ℂ ι) (EuclideanSpace ℂ ι) ℝ
      ℝ).continuous.comp (hAc.comp_continuous hcc hcmem)
  obtain ⟨u, ⟨hu0, hud⟩, -⟩ := AsymptoticOperator.linearODE_existsUnique B hBc φ0
  have hudI : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt u (A s (u s)) (Set.Icc 0 1) s := by
    intro s hs
    have := (hud s).hasDerivWithinAt (s := Set.Icc 0 1)
    simpa [hB, hceq s hs] using this
  -- `u` stays in the range of `P`: `w = u - P u` solves `w' = -P' w`, `w(0) = 0`
  set w : ℝ → EuclideanSpace ℂ ι := fun t => u t - P t (u t) with hw
  have hwd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt w (-(P' s (w s))) (Set.Icc 0 1) s := by
    intro s hs
    have := (hudI s hs).sub (happ (hS s hs).1 (hudI s hs))
    refine this.congr_deriv ?_
    have hpp := (hS s hs).2.2.1
    have h3 := hPPP s hs (u s)
    simp only [hA, hw, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
      hpp, h3]
    abel
  have hw0 : w 0 = 0 := by
    simp only [hw, hu0, (hS 0 h0).2.2.2.2.1 φ0 hφ0e, sub_self]
  have hwz : ∀ s ∈ Set.Icc (0 : ℝ) 1, w s = 0 := by
    intro s hs
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := w) (δ := 0) (K := 2 * N / γ)
      (ε := 0) (a := 0) (b := 1) (fun t ht => (hwd t ht).continuousWithinAt)
      (fun t ht => (hwd t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
      (by rw [hw0, norm_zero])
      (fun t ht => by
        rw [norm_neg, add_zero]; exact hP'n t (Set.Ico_subset_Icc_self ht) _) s hs
    rw [gronwallBound_ε0_δ0] at this
    exact norm_le_zero_iff.mp this
  have huP : ∀ s ∈ Set.Icc (0 : ℝ) 1, P s (u s) = u s := fun s hs =>
    (sub_eq_zero.mp (hwz s hs)).symm
  have hRu : ∀ s ∈ Set.Icc (0 : ℝ) 1, R s (u s) = 0 := fun s hs => by
    rw [← huP s hs]; exact (hS s hs).2.2.2.2.2.2.2.1 _
  -- the velocity is `u' = -R D u`
  set u' : ℝ → EuclideanSpace ℂ ι := fun t => -R t (Dl (u t)) with hu'
  have hAu : ∀ s ∈ Set.Icc (0 : ℝ) 1, A s (u s) = u' s := by
    intro s hs
    obtain ⟨-, -, hpp, -, -, -, -, hrp, hpr, hP'f, -⟩ := hS s hs
    simp only [hA, hu', ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      huP s hs, hP'f, hDl, hRu s hs, map_zero, map_sub, map_neg, hpr, neg_zero, sub_zero]
  have hud' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt u (u' s) (Set.Icc 0 1) s :=
    fun s hs => (hudI s hs).congr_deriv (hAu s hs)
  have hinR : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, inner ℂ (u s) (R s y) = 0 := by
    intro s hs y
    rw [← huP s hs, (hS s hs).2.2.2.1, (hS s hs).2.2.2.2.2.2.2.2.1, inner_zero_right]
  -- `‖u‖ = 1`
  have hun : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖u s‖ = 1 := by
    have hc := constant_of_has_deriv_right_zero (f := fun t => ‖u t‖ ^ 2) (a := 0) (b := 1)
      (fun t ht => ((hud' t ht).norm_sq).continuousWithinAt)
      (fun t ht => by
        have := ((hud' t (Set.Ico_subset_Icc_self ht)).norm_sq).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht)
        refine this.congr_deriv ?_
        rw [hri, hu', inner_neg_right, hinR t (Set.Ico_subset_Icc_self ht)]
        simp)
    intro s hs
    have h := hc s hs
    simp only [hu0] at h
    rw [show ‖φ0‖ = 1 from hφ0, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  -- the vector `v = R u'`
  set v : ℝ → EuclideanSpace ℂ ι := fun t => R t (u' t) with hv
  set v' : ℝ → EuclideanSpace ℂ ι := fun t =>
    -(R' t (R t (Dl (u t))) + R t (R' t (Dl (u t)) + R t (Dl (u' t)))) with hv'
  refine ⟨u, u', v, v', hu0, fun s hs => ?_⟩
  obtain ⟨-, hRd, hpp, hsa, -, hHP, hHR, hrp, hpr, -, hPn, hRn, hR'n⟩ := hS s hs
  have hg : 0 ≤ 1 / γ := by positivity
  have hR'n' : ‖R' s‖ ≤ K' * N / γ ^ 2 :=
    hR'n.trans (by gcongr; exact le_max_left _ _)
  have hR'0 : 0 ≤ K' * N / γ ^ 2 := by positivity
  have hDu : ‖Dl (u s)‖ ≤ N * 1 := key _ _ _ _ hDln.le (hun s hs).le hN0
  have hu'n : ‖u' s‖ ≤ 1 / γ * (N * 1) := by
    rw [hu', norm_neg]; exact key _ _ _ _ hRn hDu hg
  have hK1 : (1 : ℝ) ≤ 2 * K' + 1 := by linarith
  refine ⟨hud' s hs, ?_, by simp [IsState, hun s hs], ?_, ?_, ?_, ?_⟩
  · -- derivative of `v = -R (R (D u))`
    have hDud : HasDerivWithinAt (fun t => Dl (u t)) (Dl (u' s)) (Set.Icc 0 1) s :=
      (Dl.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hud' s hs)
    have := (happ hRd (happ hRd hDud)).neg
    have heq : v = fun t => -(R t (R t (Dl (u t)))) := by
      funext t; simp [hv, hu']
    rw [heq]
    exact this
  · rw [← huP s hs]; exact hHP _
  · rw [hHR, hu']
    simp [hpr]
  · have : ‖v s‖ ≤ 1 / γ * (1 / γ * (N * 1)) := key _ _ _ _ hRn hu'n hg
    refine this.trans ?_
    calc 1 / γ * (1 / γ * (N * 1)) = 1 * N / γ ^ 2 := by field_simp
      _ ≤ (2 * K' + 1) * N / γ ^ 2 := by gcongr
  · have t1 : ‖R' s (R s (Dl (u s)))‖ ≤ K' * N / γ ^ 2 * (1 / γ * (N * 1)) :=
      key _ _ _ _ hR'n' (key _ _ _ _ hRn hDu hg) hR'0
    have t2 : ‖R' s (Dl (u s)) + R s (Dl (u' s))‖ ≤
        K' * N / γ ^ 2 * (N * 1) + 1 / γ * (N * (1 / γ * (N * 1))) :=
      (norm_add_le _ _).trans (add_le_add (key _ _ _ _ hR'n' hDu hR'0)
        (key _ _ _ _ hRn (key _ _ _ _ hDln.le hu'n hN0) hg))
    have t3 := key _ _ _ _ hRn t2 hg
    calc ‖v' s‖ ≤ ‖R' s (R s (Dl (u s)))‖ +
          ‖R s (R' s (Dl (u s)) + R s (Dl (u' s)))‖ := by
          rw [hv', norm_neg]; exact norm_add_le _ _
      _ ≤ K' * N / γ ^ 2 * (1 / γ * (N * 1)) +
          1 / γ * (K' * N / γ ^ 2 * (N * 1) + 1 / γ * (N * (1 / γ * (N * 1)))) :=
          add_le_add t1 t3
      _ = (2 * K' + 1) * N ^ 2 / γ ^ 3 := by field_simp; ring
