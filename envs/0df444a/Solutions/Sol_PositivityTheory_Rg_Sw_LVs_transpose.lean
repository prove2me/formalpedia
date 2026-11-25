-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:03.08304+00:00
-- url     : https://prove2.me/submissions/f1fe3847-54e3-407e-beda-ba8fa6bff697

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_first_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_second_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuousOn_inverse_first_block
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_first_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_second_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_eq_of_group
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_par_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem isOpen_dom_analytic_determinants : IsOpen (Dom n) := by
  have hdet : Continuous (fun x : M2 n => x.det) := continuous_id.matrix_det
  have hS0 : IsOpen {x : M2 n | x.det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hc1 : Continuous (fun x : M2 n => (u1 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
    fun_prop
  have hc2 : Continuous (fun x : M2 n => (u2 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have h4 : IsOpen ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) :=
    continuousOn_inverse_first_block.isOpen_inter_preimage hS0 (isOpen_ne_fun continuous_id.matrix_det continuous_const)
  have he : Dom n = {x : M2 n | (u1 x).det ≠ 0} ∩ {x : M2 n | (u2 x).det ≠ 0} ∩
      ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) := by
    ext x
    simp only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [he]
  exact ((isOpen_ne_fun hc1 continuous_const).inter (isOpen_ne_fun hc2 continuous_const)).inter h4
private theorem mem_dom_of_inG {x : M2 n} (hx : InG x) : x ∈ Dom n := by
  refine ⟨isUnit_det_of_inG' hx, det_first_cayley_block_ne_zero hx, det_second_cayley_block_ne_zero hx, ?_⟩
  rw [inverse_first_block_eq_of_group hx, det_conjTranspose]
  exact star_ne_zero.mpr (det_first_cayley_block_ne_zero hx)
private theorem mul_mem_dom_of_inP {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) : P * x ∈ Dom n := by
  obtain ⟨hG, h21⟩ := hP
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hPu := isUnit_det_of_inG' hG
  have hrel := congrArg Matrix.det (par_rel hG h21)
  rw [det_mul, det_one, det_conjTranspose] at hrel
  have h22 : (toBlocks₂₂ P).det ≠ 0 := right_ne_zero_of_mul_eq_one hrel
  have h11 : (toBlocks₁₁ P).det ≠ 0 := by
    have := left_ne_zero_of_mul_eq_one hrel
    exact fun h => this (by rw [h, star_zero])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_mul]
    exact hPu.mul hx0
  · rw [automorphy_first_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx1
  · rw [automorphy_second_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx2
  · rw [inverse_first_block_mul_parabolic h21 hPu, det_mul]
    refine mul_ne_zero hx3 ?_
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr h11)).ne_zero
private theorem contDiffOn_fderiv_apply_mul_right {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n) :
    ContDiffOn ℂ ∞ (fun x => fderiv ℂ G x (x * Z)) (Dom n) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have h1 := hcd.fderiv_right (m := ∞) (by simp)
  have h2 : ContDiffAt ℂ ∞ (fun x : M2 n => x * Z) x :=
    ((LinearMap.mulRight ℂ Z).toContinuousLinearMap).contDiff.contDiffAt
  exact (h1.clm_apply h2).contDiffWithinAt
private theorem eqOn_fderiv_apply_mul_of_eqOn {G1 G2 : M2 n → ℂ} (h : Set.EqOn G1 G2 (Dom n)) (Z : M2 n) :
    Set.EqOn (fun x => fderiv ℂ G1 x (x * Z)) (fun x => fderiv ℂ G2 x (x * Z)) (Dom n) := by
  intro x hx
  have : G1 =ᶠ[nhds x] G2 := Filter.eventuallyEq_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) h
  simp only [Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) this]
private theorem fderiv_apply_mul_equivariant_of_equivariant {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n} (hP : InP P) (c : ℂ)
    (h : ∀ x ∈ Dom n, G (P * x) = c * G x) (Z : M2 n) :
    ∀ x ∈ Dom n, fderiv ℂ G (P * x) (P * x * Z) = c * fderiv ℂ G x (x * Z) := by
  intro x hx
  let L : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ P).toContinuousLinearMap
  have hPx : P * x ∈ Dom n := mul_mem_dom_of_inP hP hx
  have hd1 : DifferentiableAt ℂ G (L x) :=
    (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hPx)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℂ G x := (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)).differentiableAt (by simp)
  have heq : (G ∘ L) =ᶠ[nhds x] (fun y => c * G y) :=
    Filter.eventually_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) (fun y hy => h y hy)
  have hA : HasFDerivAt (G ∘ L) ((fderiv ℂ G (L x)).comp L) x := hd1.hasFDerivAt.comp x L.hasFDerivAt
  have hA' : HasFDerivAt (fun y => c * G y) ((fderiv ℂ G (L x)).comp L) x := hA.congr_of_eventuallyEq heq.symm
  have hB : HasFDerivAt (fun y => c * G y) (c • fderiv ℂ G x) x := hd2.hasFDerivAt.const_mul c
  have e3 := hA'.unique hB
  have e4 : ((fderiv ℂ G (L x)).comp L) (x * Z) = (c • fderiv ℂ G x) (x * Z) := by rw [e3]
  rw [Matrix.mul_assoc]
  exact e4
private theorem fderiv_fderiv_mul_comm_of_mul_zero {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {a b : M2 n} (hab : a * b = 0)
    (hba : b * a = 0) :
    ∀ x ∈ Dom n, fderiv ℂ (fun y => fderiv ℂ G y (y * b)) x (x * a) =
      fderiv ℂ (fun y => fderiv ℂ G y (y * a)) x (x * b) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hsym : IsSymmSndFDerivAt ℂ G x := hcd.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hdd : DifferentiableAt ℂ (fderiv ℂ G) x :=
    (hcd.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have key : ∀ c d : M2 n, c * d = 0 →
      fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) = fderiv ℂ (fderiv ℂ G) x (x * c) (x * d) := by
    intro c d hcd0
    let R : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ d).toContinuousLinearMap
    have hfd := hdd.hasFDerivAt.clm_apply R.hasFDerivAt
    have h0 : R (x * c) = 0 := by
      show x * c * d = 0
      rw [Matrix.mul_assoc, hcd0, Matrix.mul_zero]
    have e1 : fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) =
        fderiv ℂ G x (R (x * c)) + fderiv ℂ (fderiv ℂ G) x (x * c) (R x) :=
      congrArg (fun T => T (x * c)) hfd.fderiv
    rw [e1, h0, map_zero, zero_add]
    rfl
  rw [key a b hab, key b a hba]
  exact hsym.eq _ _
private theorem iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) {m : ℕ} (W : Fin (m + 1) → M2 n)
    (hW : ∀ i : Fin m, W 0 * W i.succ = 0) {x : M2 n} (hx : x ∈ Dom n) :
    iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have hcd : ContDiffAt ℂ ∞ F x := hF.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hΦ : DifferentiableAt ℂ (iteratedFDeriv ℂ m F) x :=
    hcd.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))
  have hfd := hΦ.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (g := fun _ : Fin m => fun y => Lm y) (fun _ => Lm.hasFDerivAt)
  have hfd2 := hfd.continuousMultilinear_apply_const (fun i => W i.succ)
  have eL : iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) :=
    iteratedFDeriv_succ_apply_left _
  have e1 : fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) +
        (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
          (fun i => W i.succ) :=
    congrArg (fun T => T (x * W 0)) hfd2.fderiv
  have hS : (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
      (fun i => W i.succ) = 0 := by
    refine (ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply (iteratedFDeriv ℂ m F x)
      (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ)).trans ?_
    apply Finset.sum_eq_zero
    intro i _
    apply ContinuousMultilinearMap.map_coord_zero _ i
    refine (congrArg (fun f : M2 n →L[ℂ] M2 n => f (W i.succ))
      (Function.update_self i (Lm (x * W 0)) (fun _ : Fin m => Lm x))).trans ?_
    show x * W 0 * W i.succ = 0
    rw [Matrix.mul_assoc, hW i, Matrix.mul_zero]
  rw [eL, e1, hS, add_zero]
private theorem contDiffOn_foldr_fderiv_mul (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) :
    ContDiffOn ℂ ∞ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => exact hG
  | cons a l ih => exact contDiffOn_fderiv_apply_mul_right ih a
private theorem foldr_fderiv_mul_left_eq_of_equivariant (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n}
    (hP : InP P) (c : ℂ) (h : ∀ x ∈ Dom n, G (P * x) = c * G x) :
    ∀ x ∈ Dom n, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G (P * x) =
      c * l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G x := by
  induction l with
  | nil => exact h
  | cons a l ih => exact fderiv_apply_mul_equivariant_of_equivariant (contDiffOn_foldr_fderiv_mul l hG) hP c ih a
private theorem iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) :
    ∀ (m : ℕ) (W : Fin m → M2 n), (∀ i j, W i * W j = 0) → ∀ x ∈ Dom n,
      iteratedFDeriv ℂ m F x (fun i => x * W i) =
        (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F x := by
  intro m
  induction m with
  | zero =>
    intro W _ x _
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro W hW x hx
    rw [iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero hF W (fun i => hW 0 i.succ) hx, List.ofFn_succ, List.foldr_cons]
    exact eqOn_fderiv_apply_mul_of_eqOn (fun y hy => ih (fun i => W i.succ) (fun i j => hW _ _) y hy) (W 0) hx
private theorem foldr_fderiv_comm_fderiv_of_mul_zero (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n)
    (hZ : ∀ a ∈ l, Z * a = 0 ∧ a * Z = 0) :
    Set.EqOn (fun x => fderiv ℂ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) x (x * Z))
      (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) (fun x => fderiv ℂ G x (x * Z))) (Dom n) := by
  induction l with
  | nil => intro x _; rfl
  | cons a l ih =>
    intro x hx
    have ha : Z * a = 0 ∧ a * Z = 0 := hZ a (by simp)
    have h1 := fderiv_fderiv_mul_comm_of_mul_zero (contDiffOn_foldr_fderiv_mul l hG) ha.1 ha.2 x hx
    have h2 := eqOn_fderiv_apply_mul_of_eqOn (ih (fun b hb => hZ b (List.mem_cons_of_mem a hb))) a hx
    exact h1.trans h2
private theorem foldr_fderiv_reverse_eqOn_of_mul_zero (l : List (M2 n)) :
    ∀ {G : M2 n → ℂ}, ContDiffOn ℂ ∞ G (Dom n) → (∀ a ∈ l, ∀ b ∈ l, a * b = 0) →
      Set.EqOn (l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G)
        (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => intro G _ _ x _; rfl
  | cons a l ih =>
    intro G hG hl x hx
    have e1 := ih (contDiffOn_fderiv_apply_mul_right hG a)
      (fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)) hx
    have e2 := foldr_fderiv_comm_fderiv_of_mul_zero l hG a
      (fun b hb => ⟨hl a (by simp) b (by simp [hb]), hl b (by simp [hb]) a (by simp)⟩) hx
    rw [List.reverse_cons, List.foldr_append]
    exact e1.trans e2.symm
private theorem transpose_lemma_14 (hI : InfInv) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg]
    [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (χ1 χ2 : M2 n → ℂ)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (l : List (M2 n)) (hl : ∀ a ∈ l, ∀ b ∈ l, a * b = 0) (G1 : M2 n → ℂ) (hG1 : ContDiffOn ℂ ∞ G1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → G1 (P * x) = χ1 P * G1 x) :
    ∀ (G2 : M2 n → ℂ), ContDiffOn ℂ ∞ G2 (Dom n) → (∀ P x, InP P → x ∈ Dom n → G2 (P * x) = χ2 P * G2 x) →
      ∫ k, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 (ι k) * G2 (ι k) ∂μ =
        (-1) ^ l.length * ∫ k, G1 (ι k) * l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G2 (ι k) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hint : ∀ H K : M2 n → ℂ, ContDiffOn ℂ ∞ H (Dom n) → ContDiffOn ℂ ∞ K (Dom n) →
      Integrable (fun k => H (ι k) * K (ι k)) μ := by
    intro H K hH hK'
    have c1 : Continuous (fun k => H (ι k)) := hH.continuousOn.comp_continuous hι hin
    have c2 : Continuous (fun k => K (ι k)) := hK'.continuousOn.comp_continuous hι hin
    exact (c1.mul c2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  induction l with
  | nil =>
    intro G2 _ _
    simp
  | cons a l ih =>
    intro G2 hG2 h2
    have hl' : ∀ b ∈ l, ∀ c ∈ l, b * c = 0 :=
      fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)
    set H1 := l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 with hH1def
    have hH1 : ContDiffOn ℂ ∞ H1 (Dom n) := contDiffOn_foldr_fderiv_mul l hG1
    have hH1e : ∀ P x, InP P → x ∈ Dom n → H1 (P * x) = χ1 P * H1 x :=
      fun P x hP hx => foldr_fderiv_mul_left_eq_of_equivariant l hG1 hP (χ1 P) (fun y hy => h1 P y hP hy) x hx
    have hG2' : ContDiffOn ℂ ∞ (fun x => fderiv ℂ G2 x (x * a)) (Dom n) := contDiffOn_fderiv_apply_mul_right hG2 a
    have h2' : ∀ P x, InP P → x ∈ Dom n → fderiv ℂ G2 (P * x) (P * x * a) = χ2 P * fderiv ℂ G2 x (x * a) :=
      fun P x hP hx => fderiv_apply_mul_equivariant_of_equivariant hG2 hP (χ2 P) (fun y hy => h2 P y hP hy) a x hx
    have hinv := hI n H1 G2 (Dom n) isOpen_dom_analytic_determinants (fun x hx => mem_dom_of_inG hx) hH1 hG2
      (by
        intro p x hp hp21 hx
        have hP : InP p := ⟨hp, hp21⟩
        have hxD := mem_dom_of_inG hx
        rw [hH1e p x hP hxD, h2 p x hP hxD, ← h12 p hP]
        ring) Kg μ ι hι hK a
    rw [integral_add (hint _ _ (contDiffOn_fderiv_apply_mul_right hH1 a) hG2) (hint _ _ hH1 hG2')] at hinv
    have eA : ∫ k, (fun x => fderiv ℂ H1 x (x * a)) (ι k) * G2 (ι k) ∂μ =
        -∫ k, H1 (ι k) * (fun x => fderiv ℂ G2 x (x * a)) (ι k) ∂μ := eq_neg_of_add_eq_zero_left hinv
    have eB := ih hl' (fun x => fderiv ℂ G2 x (x * a)) hG2' h2'
    simp only [List.foldr_cons, List.reverse_cons, List.foldr_append, List.foldr_nil, List.length_cons]
    rw [eA, eB, pow_succ]
    ring
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (N : ℕ) (W : Fin N → M2 n) (hW : ∀ a b, W a * W b = 0) :
    ∫ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) * F2 (ι k) ∂μ =
      (-1) ^ N * ∫ k, F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hl : ∀ a ∈ List.ofFn W, ∀ b ∈ List.ofFn W, a * b = 0 := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hW i j
  have eA : ∀ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F1 (ι k) :=
    fun k => iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF1 N W hW (ι k) (hin k)
  have eB : ∀ k, iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F2 (ι k) :=
    fun k => (iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF2 N W hW (ι k) (hin k)).trans (foldr_fderiv_reverse_eqOn_of_mul_zero (List.ofFn W) hF2 hl (hin k)).symm
  simp_rw [eA, eB]
  have key := transpose_lemma_14 hI Kg μ ι hι hK χ1 χ2 h12 (List.ofFn W) hl F1 hF1 h1 F2 hF2 h2
  rw [List.length_ofFn] at key
  exact key
end PositivityTheory.Rg.Sw.LVs
