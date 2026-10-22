-- Prove2me | solution 1 for TsengCGD.Global.theorem1_b
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:48:26.813312+00:00
-- url     : https://prove2.me/submissions/232b6431-0f2e-468f-858c-1d7e6a81f9f5

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Global

namespace Cex1

noncomputable def v1 : Vec 1 := EuclideanSpace.single 0 1
def Dc : Set (Vec 1) := {x | 0 < x 0}
noncomputable def Pc : Vec 1 → ℝ := fun x => (x 0)⁻¹
noncomputable def fc : Vec 1 → ℝ := fun x => -4 / x 0 + (x 0) ^ 2 / 4
noncomputable def Hc : ℕ → Matrix (Fin 1) (Fin 1) ℝ := fun _ => 1
def Jc : ℕ → Finset (Fin 1) := fun _ => Finset.univ
noncomputable def xc : ℕ → Vec 1 := fun k => ((1 / 2 : ℝ) ^ k) • v1
noncomputable def dc : ℕ → Vec 1 := fun k => (-(1 / 2 : ℝ) ^ (k + 1)) • v1
def ac : ℕ → ℝ := fun _ => 1

lemma v1_zero : v1 0 = 1 := by simp [v1]

lemma xc0 (k : ℕ) : xc k 0 = (1 / 2 : ℝ) ^ k := by simp [xc, v1]
lemma dc0 (k : ℕ) : dc k 0 = -(1 / 2 : ℝ) ^ (k + 1) := by simp [dc, v1]

lemma inner_eq (u y : Vec 1) : ⟪u, y⟫ = u 0 * y 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_one]; ring

lemma qf_one (y : Vec 1) : qf 1 y = (y 0) ^ 2 := by
  simp [qf, dotProduct, Fin.sum_univ_one]; ring

lemma norm_sq' (y : Vec 1) : ‖y‖ ^ 2 = (y 0) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]; ring

lemma proj_eq : ((EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ) : Vec 1 → ℝ) = fun x => x 0 := by
  ext x; simp

lemma cont0 : Continuous (fun x : Vec 1 => x 0) := by
  rw [← proj_eq]; exact (EuclideanSpace.proj (0 : Fin 1)).continuous

lemma grad_inner (x y : Vec 1) (hx : 0 < x 0) :
    ⟪gradient fc x, y⟫ = (4 / (x 0) ^ 2 + x 0 / 2) * y 0 := by
  have hg : HasDerivAt (fun t : ℝ => -4 / t + t ^ 2 / 4) (4 / (x 0) ^ 2 + x 0 / 2) (x 0) := by
    have h1 := ((hasDerivAt_inv (ne_of_gt hx)).const_mul (-4))
    have h2 := (hasDerivAt_pow 2 (x 0)).div_const 4
    have h3 := h1.add h2
    have hfun : (fun t : ℝ => -4 / t + t ^ 2 / 4) = (fun t => -4 * t⁻¹ + t ^ 2 / 4) := by
      ext t; ring
    rw [hfun]
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hp : HasFDerivAt (fun z : Vec 1 => z 0) (EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ) x := by
    have := (EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ).hasFDerivAt (x := x)
    rwa [proj_eq] at this
  have hf' := hg.comp_hasFDerivAt x hp
  have hf : HasFDerivAt fc ((4 / (x 0) ^ 2 + x 0 / 2) • (EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ)) x :=
    hf'
  rw [gradient, InnerProductSpace.toDual_symm_apply, hf.fderiv]
  simp

open Classical in
lemma lsc : LowerSemicontinuous (fun x : Vec 1 => if x ∈ Dc then ((Pc x : ℝ) : EReal) else ⊤) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot =>
    convert isClosed_empty
    ext x; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    split_ifs <;> simp
  | coe r =>
    by_cases hr : 0 < r
    · convert isClosed_le continuous_const cont0 (f := fun _ => r⁻¹)
      ext x; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      by_cases hx : x ∈ Dc
      · simp only [hx, if_true, EReal.coe_le_coe_iff, Pc]
        have : 0 < x 0 := hx
        constructor
        · intro h; exact (inv_le_comm₀ this hr).mp h
        · intro h; exact (inv_le_comm₀ this hr).mpr h
      · simp only [hx, if_false, top_le_iff, EReal.coe_ne_top, false_iff, not_le]
        have : ¬ 0 < x 0 := hx
        have : 0 < r⁻¹ := inv_pos.mpr hr
        linarith
    · convert isClosed_empty
      ext x; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      by_cases hx : x ∈ Dc
      · simp only [hx, if_true, EReal.coe_le_coe_iff, Pc, not_le]
        have : 0 < x 0 := hx
        have := inv_pos.mpr this
        linarith
      · simp [hx]
  | top =>
    convert isClosed_univ
    ext x; simp

lemma isOpenD : IsOpen Dc := isOpen_lt continuous_const cont0

lemma convexP : ConvexOn ℝ Dc Pc := by
  have h := (convexOn_zpow (𝕜 := ℝ) (-1)).comp_linearMap
    ((EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ) : Vec 1 →ₗ[ℝ] ℝ)
  have hD : (((EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ) : Vec 1 →ₗ[ℝ] ℝ)) ⁻¹' Set.Ioi 0 = Dc := by
    ext x; simp [Dc]
  rw [hD] at h
  refine ⟨h.1, fun x hx y hy a b ha hb hab => ?_⟩
  have := h.2 hx hy ha hb hab
  simpa [Pc, _root_.zpow_neg_one] using this

lemma contdiff : ContDiffOn ℝ 1 fc Dc := by
  have hp : ContDiff ℝ 1 (fun x : Vec 1 => x 0) := by
    rw [← proj_eq]; exact (EuclideanSpace.proj (0 : Fin 1) : Vec 1 →L[ℝ] ℝ).contDiff
  exact (contDiffOn_const.div hp.contDiffOn (fun x hx => ne_of_gt hx)).add
    ((hp.pow 2).div_const 4).contDiffOn

lemma hs : Standing fc Dc Pc 1 where
  c_pos := one_pos
  properConvexLsc := ⟨⟨v1, by simp [Dc, v1_zero]⟩, convexP.1, convexP, lsc⟩
  smooth := ⟨Dc, isOpenD, subset_rfl, contdiff⟩

lemma add_apply0 (x y : Vec 1) (a : ℝ) : (x + a • y) 0 = x 0 + a * y 0 := by simp

lemma add_apply0' (x y : Vec 1) : (x + y) 0 = x 0 + y 0 := by simp

lemma dir (k : ℕ) : IsDir fc Dc Pc 1 (Hc k) (xc k) (Jc k) (dc k) := by
  have ht : 0 < xc k 0 := by rw [xc0]; positivity
  refine ⟨fun j hj => absurd (Finset.mem_univ j) hj, ?_, ?_⟩
  · show 0 < (xc k + dc k) 0
    rw [add_apply0', xc0, dc0, pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) k]
  · intro d' _ hd'
    have hu : 0 < xc k 0 + d' 0 := by have := hd'; simpa [Dc, add_apply0'] using this
    have hd : dc k 0 = -(xc k 0) / 2 := by rw [dc0, xc0, pow_succ]; ring
    simp only [subObj, Hc, grad_inner _ _ ht, qf_one, Pc, add_apply0', hd]
    set t := xc k 0
    set s := d' 0
    set u := t + s with hu_def
    have hs' : s = u - t := by rw [hu_def]; ring
    rw [hs']
    have hu0 : u ≠ 0 := hu.ne'
    have ht0 : t ≠ 0 := ht.ne'
    have key : ((4 / t ^ 2 + t / 2) * (u - t) + (u - t) ^ 2 / 2 + 1 * u⁻¹) -
        ((4 / t ^ 2 + t / 2) * (-t / 2) + (-t / 2) ^ 2 / 2 + 1 * (t + -t / 2)⁻¹) =
        (u - t / 2) ^ 2 / 2 + (2 * u - t) ^ 2 / (t ^ 2 * u) := by
      field_simp
      ring
    have : 0 ≤ (u - t / 2) ^ 2 / 2 + (2 * u - t) ^ 2 / (t ^ 2 * u) := by positivity
    linarith

lemma armtest (k : ℕ) : ArmijoTest fc Dc Pc 1 (1 / 2) 0 (Hc k) (xc k) (dc k) (ac k) := by
  have ht : 0 < xc k 0 := by rw [xc0]; positivity
  have hd : dc k 0 = -(xc k 0) / 2 := by rw [dc0, xc0, pow_succ]; ring
  refine ⟨?_, ?_⟩
  · show 0 < (xc k + ac k • dc k) 0
    rw [add_apply0, hd, ac]; linarith
  · show Fc fc Pc 1 (xc k + (1:ℝ) • dc k) ≤
      Fc fc Pc 1 (xc k) + (1:ℝ) * (1/2) * Delta fc Pc 1 0 (Hc k) (xc k) (dc k)
    rw [one_smul]
    simp only [Fc, Delta, fc, Pc, Hc, grad_inner _ _ ht, qf_one, add_apply0', hd, one_mul]
    set t := xc k 0
    have key : (-4 / t + t ^ 2 / 4 + t⁻¹ + 1 / 2 * ((4 / t ^ 2 + t / 2) * (-t / 2) + 0 * (-t / 2) ^ 2 +
        (t + -t / 2)⁻¹ - t⁻¹)) - (-4 / (t + -t / 2) + (t + -t / 2) ^ 2 / 4 + (t + -t / 2)⁻¹) =
        5 / (2 * t) + t ^ 2 / 16 := by
      field_simp
      ring
    have : 0 ≤ 5 / (2 * t) + t ^ 2 / 16 := by positivity
    linarith

lemma delta_le (k : ℕ) : Delta fc Pc 1 0 (Hc k) (xc k) (dc k) ≤ -1 := by
  have ht : 0 < xc k 0 := by rw [xc0]; positivity
  have ht1 : xc k 0 ≤ 1 := by rw [xc0]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd : dc k 0 = -(xc k 0) / 2 := by rw [dc0, xc0, pow_succ]; ring
  simp only [Delta, Pc, Hc, grad_inner _ _ ht, qf_one, add_apply0', hd]
  set t := xc k 0
  have key : (4 / t ^ 2 + t / 2) * (-t / 2) + 0 * (-t / 2) ^ 2 + 1 * (t + -t / 2)⁻¹ - 1 * t⁻¹ =
      -t⁻¹ - t ^ 2 / 4 := by
    field_simp
    ring
  rw [key]
  have : 1 ≤ t⁻¹ := by rw [le_inv_comm₀ one_pos ht]; simpa using ht1
  nlinarith

lemma hrun : IsCGDRun fc Dc Pc 1 Jc Hc xc dc ac where
  start := by show 0 < xc 0 0; rw [xc0]; norm_num
  iterate_mem := fun k => by show 0 < xc k 0; rw [xc0]; positivity
  J_nonempty := fun k => Finset.univ_nonempty
  H_posDef := fun k => Matrix.PosDef.one
  dir := dir
  step_pos := fun k => one_pos
  step := fun k => by
    simp only [xc, dc, ac, one_smul, ← add_smul]
    congr 1
    rw [pow_succ]; ring

lemma harm : IsArmijo fc Dc Pc 1 (1 / 2) (1 / 2) 0 (fun _ => 1) Hc xc dc ac := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, by norm_num⟩,
    fun _ => one_pos, fun k => ⟨0, by simp [ac], armtest k, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩⟩

lemma hA1 : Assumption1 Hc 1 1 := by
  refine ⟨one_pos, le_rfl, fun k z => ?_⟩
  simp only [Hc, qf_one, norm_sq' z, one_mul, le_refl, and_self]

lemma hGS : GaussSeidel Jc := ⟨1, le_rfl, fun k => by simp [Jc]⟩

lemma hsep (k : ℕ) : BlockSeparable Dc Pc (Jc k) := by
  refine ⟨Dc, Pc, Set.univ, fun _ => 0, hs.properConvexLsc, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Set.univ_nonempty, convex_univ, convexOn_const 0 convex_univ, ?_⟩
    simp only [Set.mem_univ, if_true]
    exact lowerSemicontinuous_const
  · intro x y hxy
    have : x = y := by
      ext i; fin_cases i; exact hxy 0 (Finset.mem_univ _)
    subst this; exact ⟨Iff.rfl, rfl⟩
  · intro x y _; exact ⟨by simp, rfl⟩
  · intro x; simp
  · intro x _; simp

lemma tend : Tendsto xc atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := h.smul_const v1
  rw [zero_smul] at this
  exact this

end Cex1

end TsengCGD.Global

open TsengCGD.Global

theorem solution : ¬ (∀ {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (xbar : Vec n)
    (hconv : Tendsto (x ∘ φ) atTop (𝓝 xbar)),

    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Tendsto (fun k => α k * Δ k) atTop (𝓝 0) ∧
    Tendsto (d ∘ φ) atTop (𝓝 0) ∧
    ∀ (Dk : ℕ → Matrix (Fin n) (Fin n) ℝ) (del delBar : ℝ),
      0 < del → del ≤ delBar →
      (∀ k, IsPosDiag (Dk k) ∧
        ∀ z : Vec n, del * ‖z‖ ^ 2 ≤ qf (Dk k) z ∧
          qf (Dk k) z ≤ delBar * ‖z‖ ^ 2) →
      Tendsto (fun i => dH f D P c (Dk (φ i)) (x (φ i)) (J (φ i)))
        atTop (𝓝 0)) := by
  intro h
  have h0 := h Cex1.fc Cex1.Dc Cex1.Pc 1 Cex1.hs Cex1.Jc Cex1.Hc Cex1.xc Cex1.dc Cex1.ac
    (fun _ => 1) (1 / 2) (1 / 2) 0 1 1 Cex1.hrun Cex1.harm Cex1.hA1 ⟨1, one_pos, fun _ => le_rfl⟩
    id strictMono_id 0 Cex1.tend
  obtain ⟨h1, -⟩ := h0
  have h2 : ∀ k, Cex1.ac k * Delta Cex1.fc Cex1.Pc 1 0 (Cex1.Hc k) (Cex1.xc k) (Cex1.dc k) ≤ -1 :=
    fun k => by simp only [Cex1.ac, one_mul]; exact Cex1.delta_le k
  have h3 := le_of_tendsto' h1 h2
  norm_num at h3
