-- Prove2me | solution 1 for WheelerDeWittSuperspace.wdw_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T21:18:51.072931+00:00
-- url     : https://prove2.me/submissions/9004422d-ebcc-4b76-adb9-c0b8f5ea350d

import Definitions.Def_WheelerDeWittSuperspace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix

namespace WheelerDeWittSuperspace

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem cd_pD {m n : WithTop ℕ∞} {f : Config X → ℂ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n)
    (x : X) (a b : Fin 3) : ContDiff ℝ m (partialD f x a b) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

theorem fderiv_dir_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Config X → F} {h : Config X} (hf : DifferentiableAt ℝ (fderiv ℝ f) h) (u v : Config X) :
    fderiv ℝ (fun h' => fderiv ℝ f h' u) h v = fderiv ℝ (fderiv ℝ f) h v u := by
  rw [fderiv_clm_apply hf (differentiableAt_const u)]
  simp

theorem pD_swap {f : Config X → ℂ} (hf : ContDiff ℝ 2 f) (x y : X) (a b c d : Fin 3) :
    partialD (partialD f x a b) y c d = partialD (partialD f y c d) x a b := by
  funext h
  have hd : DifferentiableAt ℝ (fderiv ℝ f) h :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) h
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := h) (by simp)
  show fderiv ℝ (fun h' => fderiv ℝ f h' (coordDir x a b)) h (coordDir y c d) =
    fderiv ℝ (fun h' => fderiv ℝ f h' (coordDir y c d)) h (coordDir x a b)
  rw [fderiv_dir_apply hd, fderiv_dir_apply hd, hs]

theorem sum22_comm (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc _ = ∑ i : Fin 3 × Fin 3, ∑ j : Fin 3 × Fin 3, f i.1 i.2 j.1 j.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ j : Fin 3 × Fin 3, ∑ i : Fin 3 × Fin 3, f i.1 i.2 j.1 j.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem sum44_comm (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ a', ∑ b', ∑ c', ∑ d', f a b c d a' b' c' d' =
      ∑ a', ∑ b', ∑ c', ∑ d', ∑ a, ∑ b, ∑ c, ∑ d, f a b c d a' b' c' d' := by
  calc _ = ∑ i : Fin 3 × Fin 3 × Fin 3 × Fin 3, ∑ j : Fin 3 × Fin 3 × Fin 3 × Fin 3,
        f i.1 i.2.1 i.2.2.1 i.2.2.2 j.1 j.2.1 j.2.2.1 j.2.2.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ j : Fin 3 × Fin 3 × Fin 3 × Fin 3, ∑ i : Fin 3 × Fin 3 × Fin 3 × Fin 3,
        f i.1 i.2.1 i.2.2.1 i.2.2.2 j.1 j.2.1 j.2.2.1 j.2.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem cd_entry (z : X) (i j : Fin 3) : ContDiff ℝ ⊤ (fun h : Config X => h z i j) := by
  fun_prop

theorem cd_det (z : X) : ContDiff ℝ ⊤ (fun h : Config X => (metricAt h z).det) := by
  simp only [metricAt, Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

theorem cda_vol (z : X) {h : Config X} (hd : 0 < (metricAt h z).det) :
    ContDiffAt ℝ ⊤ (fun h' : Config X => volume (metricAt h' z)) h :=
  (cd_det z).contDiffAt.sqrt hd.ne'

theorem cda_deWitt (z : X) {h : Config X} (hd : 0 < (metricAt h z).det) (a b c d : Fin 3) :
    ContDiffAt ℝ ⊤ (fun h' : Config X => deWitt (metricAt h' z) a b c d) h := by
  have hp : ContDiff ℝ ⊤ (fun h' : Config X => metricAt h' z a c * metricAt h' z b d +
      metricAt h' z a d * metricAt h' z b c - metricAt h' z a b * metricAt h' z c d) := by
    simp only [metricAt, Matrix.of_apply]; fun_prop
  have hv : 0 < volume (metricAt h z) := Real.sqrt_pos.2 hd
  exact hp.contDiffAt.div (contDiffAt_const.mul (cda_vol z hd)) (by positivity)

theorem fderiv_apply_eq_zero_of_line_invariant {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (w v : E)
    (hf : ∀ t : ℝ, f (w + t • v) = f w) : fderiv ℝ f w v = 0 := by
  by_cases hd : DifferentiableAt ℝ f w
  · have h1 : HasDerivAt (fun t : ℝ => f (w + t • v)) (fderiv ℝ f w v) 0 := by
      have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      have hd' : HasFDerivAt f (fderiv ℝ f w) (w + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
      exact hd'.comp_hasDerivAt (0 : ℝ) hl
    have h2 : HasDerivAt (fun t : ℝ => f (w + t • v)) 0 0 := by
      simp_rw [hf]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

theorem coordDir_apply_of_ne {z x : X} (hzx : z ≠ x) (a b : Fin 3) : coordDir z a b x = 0 := by
  funext i j
  simp [coordDir, Ne.symm hzx]

theorem ofReal_hasFDerivAt {r : Config X → ℝ} {h : Config X} (hr : DifferentiableAt ℝ r h) :
    HasFDerivAt (fun h' => (r h' : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ r h)) h :=
  (Complex.ofRealCLM.hasFDerivAt (x := r h)).comp h hr.hasFDerivAt

theorem diff_ofReal {r : Config X → ℝ} {h : Config X} (hr : DifferentiableAt ℝ r h) :
    DifferentiableAt ℝ (fun h' => (r h' : ℂ)) h := (ofReal_hasFDerivAt hr).differentiableAt

theorem fderiv_ofReal_apply {r : Config X → ℝ} {h : Config X} (hr : DifferentiableAt ℝ r h)
    (u : Config X) : fderiv ℝ (fun h' => (r h' : ℂ)) h u = (fderiv ℝ r h u : ℂ) := by
  rw [(ofReal_hasFDerivAt hr).fderiv]; simp

theorem diff_G (y : X) {h : Config X} (hd : 0 < (metricAt h y).det) (a b c d : Fin 3) :
    DifferentiableAt ℝ (fun h' : Config X => (deWitt (metricAt h' y) a b c d : ℂ)) h :=
  diff_ofReal ((cda_deWitt y hd a b c d).differentiableAt (by simp))

theorem fderiv_G_eq_zero (y : X) (h u : Config X) (hu : u y = 0) (a b c d : Fin 3) :
    fderiv ℝ (fun h' : Config X => (deWitt (metricAt h' y) a b c d : ℂ)) h u = 0 :=
  fderiv_apply_eq_zero_of_line_invariant _ _ _ fun t => by simp [metricAt, hu]

theorem fderiv_Gsum (y : X) {h : Config X} (hd : 0 < (metricAt h y).det)
    (Φ : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Config X → ℂ)
    (hΦ : ∀ a b c d, DifferentiableAt ℝ (Φ a b c d) h) (u : Config X) (hu : u y = 0) :
    fderiv ℝ (fun h' => ∑ a, ∑ b, ∑ c, ∑ d,
        (deWitt (metricAt h' y) a b c d : ℂ) * Φ a b c d h') h u =
      ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h y) a b c d : ℂ) * fderiv ℝ (Φ a b c d) h u := by
  have hG := diff_G y hd
  simp (disch := fun_prop) only [fderiv_fun_sum, fderiv_fun_mul, _root_.sum_apply,
    _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_G_eq_zero y h u hu, mul_zero, add_zero]

theorem wdw_eq (kappa hbar Lam : ℝ) (R : Config X → X → ℝ) (Ψ : Config X → ℂ) (h : Config X)
    (z : X) : wdw kappa hbar Lam R Ψ h z = -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * kinetic Ψ h z +
      (potentialAt kappa Lam R h z : ℂ) * Ψ h := by
  simp only [wdw, potentialAt]; push_cast; ring

theorem cda_V (kappa Lam : ℝ) (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 2 (fun h => R h z))
    (y : X) {h : Config X} (hd : 0 < (metricAt h y).det) :
    ContDiffAt ℝ 2 (fun h' => potentialAt kappa Lam R h' y) h :=
  (contDiffAt_const.mul ((cda_vol y hd).of_le le_top)).mul
    ((hR y).contDiffAt.sub contDiffAt_const)

theorem deWitt_symm {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : ∀ i j, m i j = m j i) (a b c d : Fin 3) :
    deWitt m c d a b = deWitt m a b c d := by
  simp only [deWitt, hm c a, hm d b, hm c b, hm d a, hm c d]; ring

theorem sym_of_phys {h : Config X} (hh : IsPhysical h) (z : X) (i j : Fin 3) :
    metricAt h z i j = metricAt h z j i := by
  simpa using ((hh z).1.apply j i)

theorem D2_W (kappa hbar Lam : ℝ) (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 2 (fun h => R h z))
    (Ψ : Config X → ℂ) (hΨ : ContDiff ℝ 4 Ψ) (h : Config X) (x y : X) (hxy : x ≠ y)
    (hd : 0 < (metricAt h y).det) (a b c d : Fin 3) :
    partialD (partialD (fun h' => wdw kappa hbar Lam R Ψ h' y) x c d) x a b h =
      -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * ∑ a', ∑ b', ∑ c', ∑ d',
        (deWitt (metricAt h y) a' b' c' d' : ℂ) *
          partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h +
      ((partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) * Ψ h +
        (partialR (fun h' => potentialAt kappa Lam R h' y) x c d h : ℂ) * partialD Ψ x a b h +
        (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h +
        (potentialAt kappa Lam R h y : ℂ) * partialD (partialD Ψ x c d) x a b h) := by
  set V : Config X → ℝ := fun h' => potentialAt kappa Lam R h' y with hVdef
  set C : ℂ := -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2
  have hu : ∀ c d, coordDir x c d y = 0 := fun c d => coordDir_apply_of_ne hxy c d
  set U : Set (Config X) := {h' | 0 < (metricAt h' y).det}
  have hU : IsOpen U := isOpen_lt continuous_const (cd_det y).continuous
  have hVon : ContDiffOn ℝ 2 V U := fun h' hh' => (cda_V kappa Lam R hR y hh').contDiffWithinAt
  have hVd : ∀ h' ∈ U, DifferentiableAt ℝ V h' := fun h' hh' =>
    (cda_V kappa Lam R hR y hh').differentiableAt (by simp)
  have hV1 : ∀ c d, DifferentiableAt ℝ (partialR V x c d) h := fun c d =>
    ((((hVon.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hd)).differentiableAt (by simp))
  have hΨ3 : ∀ z c d, ContDiff ℝ 3 (partialD Ψ z c d) := fun z c d => cd_pD hΨ (by norm_num) z c d
  have hΨ2 : ∀ z c d z' a b, ContDiff ℝ 2 (partialD (partialD Ψ z c d) z' a b) :=
    fun z c d z' a b => cd_pD (hΨ3 z c d) (by norm_num) z' a b
  have hΨ1 : ∀ z c d z' a b z'' e f, ContDiff ℝ 1
      (partialD (partialD (partialD Ψ z c d) z' a b) z'' e f) :=
    fun z c d z' a b z'' e f => cd_pD (hΨ2 z c d z' a b) (by norm_num) z'' e f
  have dΨ : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have dΨ3 : ∀ z c d, Differentiable ℝ (partialD Ψ z c d) := fun z c d =>
    (hΨ3 z c d).differentiable (by simp)
  have dΨ2 : ∀ z c d z' a b, Differentiable ℝ (partialD (partialD Ψ z c d) z' a b) :=
    fun z c d z' a b => (hΨ2 z c d z' a b).differentiable (by simp)
  have dΨ1 : ∀ z c d z' a b z'' e f, Differentiable ℝ
      (partialD (partialD (partialD Ψ z c d) z' a b) z'' e f) :=
    fun z c d z' a b z'' e f => (hΨ1 z c d z' a b z'' e f).differentiable (by simp)
  have hW : (fun h' => wdw kappa hbar Lam R Ψ h' y) = fun h' => C * (∑ a', ∑ b', ∑ c', ∑ d',
      (deWitt (metricAt h' y) a' b' c' d' : ℂ) * partialD (partialD Ψ y c' d') y a' b' h') +
      (V h' : ℂ) * Ψ h' := by
    funext h'; rw [wdw_eq]; rfl
  -- first derivative, valid on all of `U`
  have step1 : ∀ h' ∈ U, partialD (fun h' => wdw kappa hbar Lam R Ψ h' y) x c d h' =
      C * (∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h' y) a' b' c' d' : ℂ) *
        partialD (partialD (partialD Ψ y c' d') y a' b') x c d h') +
      ((V h' : ℂ) * partialD Ψ x c d h' + Ψ h' * (partialR V x c d h' : ℂ)) := by
    intro h' hh'
    have hG := diff_G y hh'
    have hVc := diff_ofReal (hVd h' hh')
    simp only [partialD] at dΨ2 ⊢
    rw [hW, fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop),
      fderiv_fun_mul hVc (dΨ h')]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [fderiv_Gsum y hh' _ (fun a b c d => (dΨ2 y c d y a b) h') _ (hu c d),
      fderiv_ofReal_apply (hVd h' hh')]
    rfl
  have step2 := congrArg (fun L => L (coordDir x a b))
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (Filter.eventually_of_mem (hU.mem_nhds hd) step1))
  show fderiv ℝ (partialD (fun h' => wdw kappa hbar Lam R Ψ h' y) x c d) h (coordDir x a b) = _
  rw [step2]
  have hG := diff_G y hd
  have hVc := diff_ofReal (hVd h hd)
  have hV1c := diff_ofReal (hV1 c d)
  rw [fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop),
    fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_fun_mul hVc (dΨ3 x c d h),
    fderiv_fun_mul (dΨ h) hV1c]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_Gsum y hd _ (fun a' b' c' d' => (dΨ1 y c' d' y a' b' x c d) h) _ (hu a b),
    fderiv_ofReal_apply (hVd h hd), fderiv_ofReal_apply (hV1 c d)]
  simp only [partialD, partialR]
  ring

theorem P4_swap {Ψ : Config X → ℂ} (hΨ : ContDiff ℝ 4 Ψ) (x y : X) (a b c d a' b' c' d' : Fin 3) :
    partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b =
      partialD (partialD (partialD (partialD Ψ x c d) x a b) y c' d') y a' b' := by
  have h3 : ∀ z e f, ContDiff ℝ 2 (partialD Ψ z e f) := fun z e f =>
    (cd_pD hΨ (m := 3) (by norm_num) z e f).of_le (by norm_num)
  have h2 : ∀ z e f z' e' f', ContDiff ℝ 2 (partialD (partialD Ψ z e f) z' e' f') :=
    fun z e f z' e' f' => cd_pD (cd_pD hΨ (m := 3) (by norm_num) z e f) (by norm_num) z' e' f'
  rw [pD_swap (h3 y c' d') y x a' b' c d, pD_swap (hΨ.of_le (by norm_num)) y x c' d' c d,
    pD_swap (h2 x c d y c' d') y x a' b' a b, pD_swap (h3 x c d) y x c' d' a b]

theorem WW_expand (kappa hbar Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 2 (fun h => R h z))
    (Ψ : Config X → ℂ) (hΨ : ContDiff ℝ 4 Ψ) (h : Config X) (hh : IsPhysical h)
    (x y : X) (hxy : x ≠ y) :
    wdw kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' y) h x =
      -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * (-2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 *
        (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          ∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h y) a' b' c' d' : ℂ) *
            partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h)) +
      -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 *
        ((∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) *
              partialD Ψ x c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) *
              Ψ h)) + (potentialAt kappa Lam R h y : ℂ) * kinetic Ψ h x) +
      (potentialAt kappa Lam R h x : ℂ) * (-2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * kinetic Ψ h y +
        (potentialAt kappa Lam R h y : ℂ) * Ψ h) := by
  have hd : 0 < (metricAt h y).det := Matrix.PosDef.det_pos (hh y)
  rw [wdw_eq kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' y) h x]
  rw [wdw_eq kappa hbar Lam R Ψ h y]
  have e2 : (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
      ((partialR (fun h' => potentialAt kappa Lam R h' y) x c d h : ℂ) * partialD Ψ x a b h)) =
      ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
      ((partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h) := by
    rw [sum22_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [deWitt_symm (sym_of_phys hh x)]
  have key : kinetic (fun h' => wdw kappa hbar Lam R Ψ h' y) h x =
      -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          ∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h y) a' b' c' d' : ℂ) *
            partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h) +
        ((∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) * Ψ h)) + (potentialAt kappa Lam R h y : ℂ) * kinetic Ψ h x) := by
    simp only [kinetic, D2_W kappa hbar Lam R hR Ψ hΨ h x y hxy hd]
    have : ∀ a b c d : Fin 3, (deWitt (metricAt h x) a b c d : ℂ) *
        (-2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * ∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h y) a' b' c' d' : ℂ) *
            partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h +
          ((partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) * Ψ h +
            (partialR (fun h' => potentialAt kappa Lam R h' y) x c d h : ℂ) * partialD Ψ x a b h +
            (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h +
            (potentialAt kappa Lam R h y : ℂ) * partialD (partialD Ψ x c d) x a b h)) =
        -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 * ((deWitt (metricAt h x) a b c d : ℂ) * ∑ a', ∑ b', ∑ c', ∑ d',
            (deWitt (metricAt h y) a' b' c' d' : ℂ) *
            partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h) +
          (deWitt (metricAt h x) a b c d : ℂ) *
            (2 * (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h +
              (partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) * Ψ h) +
          (potentialAt kappa Lam R h y : ℂ) * ((deWitt (metricAt h x) a b c d : ℂ) * partialD (partialD Ψ x c d) x a b h) +
          ((deWitt (metricAt h x) a b c d : ℂ) * ((partialR (fun h' => potentialAt kappa Lam R h' y) x c d h : ℂ) * partialD Ψ x a b h) -
            (deWitt (metricAt h x) a b c d : ℂ) * ((partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) * partialD Ψ x c d h)) :=
      fun a b c d => by ring
    simp only [this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e2, sub_self, add_zero]
    simp only [← Finset.mul_sum]
    ring
  rw [key]
  ring


end

end WheelerDeWittSuperspace

open WheelerDeWittSuperspace

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ)
    (_hkappa : kappa ≠ 0) (_hhbar : hbar ≠ 0)
    (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 2 (fun h => R h z))
    (Ψ : Config X → ℂ) (hΨ : ContDiff ℝ 4 Ψ) (h : Config X) (hh : IsPhysical h)
    (x y : X) (hxy : x ≠ y) :
    wdw kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' y) h x -
      wdw kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' x) h y =
    -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 *
      ((∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) *
              partialD Ψ x c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) *
              Ψ h)) -
       (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h y) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' x) y a b h : ℂ) *
              partialD Ψ y c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' x) y c d) y a b h : ℂ) *
              Ψ h))) := by
  rw [WW_expand kappa hbar Lam R hR Ψ hΨ h hh x y hxy,
    WW_expand kappa hbar Lam R hR Ψ hΨ h hh y x (Ne.symm hxy)]
  have hA : (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          ∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h y) a' b' c' d' : ℂ) *
            partialD (partialD (partialD (partialD Ψ y c' d') y a' b') x c d) x a b h) =
      ∑ a', ∑ b', ∑ c', ∑ d', (deWitt (metricAt h y) a' b' c' d' : ℂ) *
          ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
            partialD (partialD (partialD (partialD Ψ x c d) x a b) y c' d') y a' b' h := by
    simp only [Finset.mul_sum]
    rw [sum44_comm]
    simp only [P4_swap hΨ x y, mul_left_comm]
  rw [hA]
  ring
