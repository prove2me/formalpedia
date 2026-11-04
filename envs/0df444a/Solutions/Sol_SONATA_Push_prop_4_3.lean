-- Prove2me | solution 1 for SONATA.Push.prop_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:02:52.489848+00:00
-- url     : https://prove2.me/submissions/fd28902f-f200-4753-8007-091950c92ec0

import Mathlib
import Definitions.Def_SONATA_Push_Network
import Theorems.Thm_SONATA_Push_eq_74

open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem hess_symm {d : ℕ} (φ : E d → ℝ) (x : E d)
    (hd : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ y)
    (hg : DifferentiableAt ℝ (gradient φ) x) (u v : E d) :
    ⟪hess φ x u, v⟫ = ⟪hess φ x v, u⟫ := by
  have key : (fun y => fderiv ℝ φ y) =
      fun y => (innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ) (gradient φ y) := by
    funext y; ext w; simp [gradient, InnerProductSpace.toDual_symm_apply]
  have h1 : ∀ᶠ y in nhds x, HasFDerivAt φ (fderiv ℝ φ y) y :=
    hd.mono fun y hy => hy.hasFDerivAt
  have h2 : HasFDerivAt (fun y => fderiv ℝ φ y)
      ((innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ).comp (hess φ x)) x := by
    rw [key]; exact (innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ).hasFDerivAt.comp x hg.hasFDerivAt
  have := second_derivative_symmetric_of_eventually h1 h2 u v
  simpa [hess] using this

theorem norm_apply_le_of_quad {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (hsym : ∀ u v, ⟪A u, v⟫ = ⟪A v, u⟫) (D : ℝ)
    (h : ∀ w, |⟪A w, w⟫| ≤ D * ‖w‖ ^ 2) (u : V) : ‖A u‖ ≤ D * ‖u‖ := by
  have key : ∀ s : ℝ, 2 * s * ‖A u‖ ^ 2 ≤ D * (‖u‖ ^ 2 + s ^ 2 * ‖A u‖ ^ 2) := by
    intro s
    set v := s • A u with hv
    have hp := abs_le.mp (h (u + v))
    have hm := abs_le.mp (h (u - v))
    have e1 : ⟪A (u + v), u + v⟫ - ⟪A (u - v), u - v⟫ = 4 * ⟪A u, v⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hsym v u]; ring
    have e2 : ⟪A u, v⟫ = s * ‖A u‖ ^ 2 := by
      rw [hv, inner_smul_right, real_inner_self_eq_norm_sq]
    have e3 : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      have := parallelogram_law_with_norm ℝ u v
      nlinarith [this]
    have e4 : ‖v‖ ^ 2 = s ^ 2 * ‖A u‖ ^ 2 := by
      rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have e5 : D * ‖u + v‖ ^ 2 + D * ‖u - v‖ ^ 2 = 2 * D * (‖u‖ ^ 2 + s ^ 2 * ‖A u‖ ^ 2) := by
      rw [← mul_add, e3, e4]; ring
    linarith [hp.2, hm.1]
  rcases eq_or_lt_of_le (norm_nonneg (A u)) with h0 | hpos
  · rw [← h0]
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have := (abs_nonneg _).trans (h u)
      have hD : 0 ≤ D := by
        by_contra hc; push Not at hc
        have : D * ‖u‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
        linarith
      positivity
  · have hu : 0 < ‖u‖ := by
      rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
      · have : u = 0 := norm_eq_zero.mp hu.symm
        simp [this] at hpos
      · exact hu
    have k := key (‖u‖ / ‖A u‖)
    have e : (‖u‖ / ‖A u‖) ^ 2 * ‖A u‖ ^ 2 = ‖u‖ ^ 2 := by
      field_simp
    have e' : 2 * (‖u‖ / ‖A u‖) * ‖A u‖ ^ 2 = 2 * ‖u‖ * ‖A u‖ := by
      field_simp
    rw [e, e'] at k
    nlinarith

theorem gradient_Fsum {m d : ℕ} (f : Fin m → E d → ℝ) (z : E d)
    (h : ∀ j, DifferentiableAt ℝ (f j) z) :
    gradient (Fsum f) z = (1 / (m : ℝ)) • ∑ j, gradient (f j) z := by
  have hF : HasFDerivAt (Fsum f) ((1 / (m : ℝ)) • ∑ j, fderiv ℝ (f j) z) z := by
    have hs : HasFDerivAt (fun x => ∑ j, f j x) (∑ j, fderiv ℝ (f j) z) z :=
      HasFDerivAt.fun_sum (fun j _ => (h j).hasFDerivAt)
    have := hs.const_mul (1 / (m : ℝ))
    exact this
  rw [gradient, hF.fderiv]
  simp [gradient, map_sum]

/-- Network facts: nonnegativity of the weights. -/
theorem C_nonneg {m : ℕ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl : ℝ} (hN : NetworkHyp Edges B C cl) :
    ∀ ν i j, 0 ≤ C ν i j := by
  obtain ⟨_, hcl, hdiag, hoff, _⟩ := hN
  intro ν i j
  by_cases hij : i = j
  · subst hij; linarith [hdiag ν i]
  · by_cases he : Edges ν j i
    · linarith [((hoff ν i j hij).1 he)]
    · rw [(hoff ν i j hij).2 he]

theorem phi_pos {m d : ℕ} {K : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν i, 0 < φ ν i := by
  obtain ⟨_, _, hφ0, _, hφs, _, _⟩ := hrun
  have hC := C_nonneg hN
  have hdiag := hN.2.2.1
  have hcl := hN.2.1
  intro ν
  induction ν with
  | zero => intro i; rw [hφ0 i]; norm_num
  | succ n ih =>
    intro i
    rw [hφs n i]
    have hle : C n i i * φ n i ≤ ∑ j, C n i j * φ n j :=
      Finset.single_le_sum (f := fun j => C n i j * φ n j)
        (fun j _ => mul_nonneg (hC n i j) (ih j).le) (Finset.mem_univ i)
    have : 0 < C n i i * φ n i := mul_pos (lt_of_lt_of_le hcl (hdiag n i)) (ih i)
    linarith

theorem phi_sum {m d : ℕ} {K : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν, ∑ i, φ ν i = m := by
  obtain ⟨_, _, hφ0, _, hφs, _, _⟩ := hrun
  have hcol := hN.2.2.2.2
  intro ν
  induction ν with
  | zero => simp [hφ0]
  | succ n ih =>
    simp_rw [hφs n]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol n, one_mul]
    exact ih

theorem x_mem {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L)
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν i, x ν i ∈ K := by
  have hpos := phi_pos hN hrun
  have hC := C_nonneg hN
  obtain ⟨hx0, _, _, hxh, hφs, hxs, _⟩ := hrun
  have hKcv : Convex ℝ K := hA.2.2.1
  intro ν
  induction ν with
  | zero => exact hx0
  | succ n ih =>
    intro i
    have hhalf : ∀ j, xhalf α x xh n j ∈ K := by
      intro j
      exact hKcv.add_smul_sub_mem (ih j) (hxh n j).1 ⟨hα0.le, hα1⟩
    rw [hxs n i, Finset.smul_sum]
    simp_rw [smul_smul]
    apply hKcv.sum_mem
    · intro j _
      exact mul_nonneg (inv_nonneg.mpr (hpos (n + 1) i).le) (mul_nonneg (hC n i j) (hpos n j).le)
    · rw [← Finset.mul_sum, ← hφs n i]
      exact inv_mul_cancel₀ (hpos (n + 1) i).ne'
    · intro j _; exact hhalf j

theorem grad_lip {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {μi Li : Fin m → ℝ} (h1 : HessBounds K f μi Li)
    (j : Fin m) {a b : E d} (ha : a ∈ K) (hb : b ∈ K) :
    ‖gradient (f j) a - gradient (f j) b‖ ≤ Li j * ‖a - b‖ := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _⟩ := hA
  have hdiffAt : ∀ z ∈ O, DifferentiableAt ℝ (f j) z :=
    fun z hz => ((hfi j).1 z hz).differentiableAt (hO.mem_nhds hz)
  have hgAt : ∀ z ∈ O, DifferentiableAt ℝ (gradient (f j)) z :=
    fun z hz => ((hfi j).2.1 z hz).differentiableAt (hO.mem_nhds hz)
  have hder : ∀ z ∈ K, HasFDerivWithinAt (gradient (f j)) (hess (f j) z) K z :=
    fun z hz => (hgAt z (hKO hz)).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ z ∈ K, ‖hess (f j) z‖ ≤ Li j := by
    intro z hz
    obtain ⟨_, hLj, hq⟩ := h1 j
    apply ContinuousLinearMap.opNorm_le_bound _ hLj.le
    intro u
    apply norm_apply_le_of_quad
    · intro u v
      apply hess_symm
      · exact Filter.mem_of_superset (hO.mem_nhds (hKO hz)) fun y hy => hdiffAt y hy
      · exact hgAt z (hKO hz)
    · intro w
      obtain ⟨hlo, hhi⟩ := hq z hz w
      have : 0 ≤ μi j * ‖w‖ ^ 2 := mul_nonneg (h1 j).1 (sq_nonneg _)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖w‖]
  exact hKcv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hb ha

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem mono_aux (Ψ Ψ' : ℝ → ℝ) (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt Ψ (Ψ' t) t)
    (hnn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ Ψ' t) : MonotoneOn Ψ (Set.Icc 0 1) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hnn t (interior_subset ht))

theorem second_order_lower (ψ χ : ℝ → ℝ) (c α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (χ t) t)
    (hχ : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ χ', HasDerivAt χ χ' t ∧ c ≤ χ') :
    c / 2 * α ^ 2 ≤ ψ α - ψ 0 - α * χ 0 := by
  choose! χ' hχ' hc using hχ
  have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hΞ : MonotoneOn (fun t => χ t - c * t) (Set.Icc 0 1) := by
    apply mono_aux _ (fun t => χ' t - c)
    · intro t ht
      have h2 : HasDerivAt (fun t : ℝ => c * t) c t := by
        simpa using (hasDerivAt_id t).const_mul c
      exact (hχ' t ht).sub h2
    · intro t ht; linarith [hc t ht]
  have hΨ : MonotoneOn (fun t => ψ t - t * χ 0 - c / 2 * t ^ 2) (Set.Icc 0 1) := by
    apply mono_aux _ (fun t => χ t - χ 0 - c * t)
    · intro t ht
      have h1 := hψ t ht
      have h2 : HasDerivAt (fun t : ℝ => t * χ 0) (χ 0) t := by
        simpa using (hasDerivAt_id t).mul_const (χ 0)
      have h3 : HasDerivAt (fun t : ℝ => c / 2 * t ^ 2) (c * t) t := by
        have := (hasDerivAt_pow 2 t).const_mul (c / 2)
        exact this.congr_deriv (by norm_num; ring)
      exact (h1.sub h2).sub h3
    · intro t ht
      have := hΞ h01 ht ht.1
      simp only [mul_zero, sub_zero] at this
      linarith
  have := hΨ h01 ⟨hα0, hα1⟩ hα0
  simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero] at this
  linarith

theorem min_sc {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (a G : E d → ℝ) (c : E d) (μt : ℝ)
    (hμ : 0 ≤ μt) (ha : StrongConvexOn K μt a) (hG : ConvexOn ℝ K G) (x xh : E d)
    (hx : x ∈ K) (hxh : xh ∈ K)
    (hmin : IsMinOn (fun w => a w + ⟪c, w - x⟫ + G w) K xh) :
    a xh + ⟪c, xh - x⟫ + G xh + μt / 2 * ‖xh - x‖ ^ 2 ≤ a x + G x := by
  set N := ‖xh - x‖ ^ 2
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      a xh + ⟪c, xh - x⟫ + G xh + μt / 2 * N ≤ a x + G x + t * (μt / 2 * N) := by
    intro t ht0 ht1
    have hw : (1 - t) • xh + t • x ∈ K := hK hxh hx (by linarith) ht0.le (by ring)
    have h1 := isMinOn_iff.mp hmin _ hw
    have h2 := ha.2 hxh hx (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    have h3 := hG.2 hxh hx (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    have hlin : ⟪c, (1 - t) • xh + t • x - x⟫ = (1 - t) * ⟪c, xh - x⟫ := by
      have : (1 - t) • xh + t • x - x = (1 - t) • (xh - x) := by
        rw [smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
      rw [this, inner_smul_right]
    simp only [smul_eq_mul] at h1 h2 h3
    rw [hlin] at h1
    have : t * (a xh + ⟪c, xh - x⟫ + G xh) ≤ t * (a x + G x) - t * ((1 - t) * (μt / 2 * N)) := by
      nlinarith
    have h4 : a xh + ⟪c, xh - x⟫ + G xh ≤ a x + G x - (1 - t) * (μt / 2 * N) := by
      apply le_of_mul_le_mul_left _ ht0
      calc t * (a xh + ⟪c, xh - x⟫ + G xh) ≤ t * (a x + G x) - t * ((1 - t) * (μt / 2 * N)) := this
        _ = t * (a x + G x - (1 - t) * (μt / 2 * N)) := by ring
    nlinarith
  by_contra hcon
  push Not at hcon
  set R := μt / 2 * N
  have hR : 0 ≤ R := by positivity
  set ε := a xh + ⟪c, xh - x⟫ + G xh + R - (a x + G x)
  have hε : 0 < ε := by simp only [ε]; linarith
  set t := min 1 (ε / (2 * (R + 1)))
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R < ε := by
    have h1 : t ≤ ε / (2 * (R + 1)) := min_le_right _ _
    have h2 : t * R ≤ ε / (2 * (R + 1)) * R := mul_le_mul_of_nonneg_right h1 hR
    have h3 : ε / (2 * (R + 1)) * R < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have := key t ht0 ht1
  simp only [ε] at htR
  linarith

theorem fderiv_eq_inner_gradient {d : ℕ} (g : E d → ℝ) (z v : E d) :
    fderiv ℝ g z v = ⟪gradient g z, v⟫ := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem grad_diff_of_fderiv_diff {d : ℕ} (g : E d → ℝ) (z : E d)
    (h : DifferentiableAt ℝ (fderiv ℝ g) z) : DifferentiableAt ℝ (gradient g) z := by
  let J : StrongDual ℝ (E d) →L[ℝ] E d :=
    (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have : gradient g = fun w => J (fderiv ℝ g w) := rfl
  rw [this]
  exact J.differentiableAt.comp z h

theorem ft_smooth {d : ℕ} {O : Set (E d)} (hO : IsOpen O) (F2 : E d → E d → ℝ)
    (hs : ContDiffOn ℝ 2 (fun q : E d × E d => F2 q.1 q.2) (O ×ˢ O)) (x : E d) (hx : x ∈ O)
    (z : E d) (hz : z ∈ O) :
    DifferentiableAt ℝ (fun w => F2 w x) z ∧ DifferentiableAt ℝ (gradient (fun w => F2 w x)) z := by
  have hc : ContDiffOn ℝ 2 (fun w => F2 w x) O := by
    have := hs.comp (contDiffOn_id.prodMk contDiffOn_const) (fun w hw => ⟨hw, hx⟩)
    exact this
  have hca : ContDiffAt ℝ 2 (fun w => F2 w x) z := hc.contDiffAt (hO.mem_nhds hz)
  refine ⟨hca.differentiableAt (by norm_num), ?_⟩
  apply grad_diff_of_fderiv_diff
  exact (hca.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem Fsum_smooth {m d : ℕ} {O : Set (E d)} (hO : IsOpen O) (f : Fin m → E d → ℝ)
    (hf : ∀ j, DifferentiableOn ℝ (f j) O) (hg : ∀ j, DifferentiableOn ℝ (gradient (f j)) O)
    (z : E d) (hz : z ∈ O) :
    DifferentiableAt ℝ (Fsum f) z ∧ DifferentiableAt ℝ (gradient (Fsum f)) z := by
  have hfa : ∀ w ∈ O, ∀ j, DifferentiableAt ℝ (f j) w :=
    fun w hw j => (hf j w hw).differentiableAt (hO.mem_nhds hw)
  constructor
  · unfold Fsum
    exact (DifferentiableAt.fun_sum (fun j _ => hfa z hz j)).const_mul _
  · have heq : gradient (Fsum f) =ᶠ[nhds z] fun w => (1 / (m : ℝ)) • ∑ j, gradient (f j) w :=
      Filter.mem_of_superset (hO.mem_nhds hz) fun w hw => gradient_Fsum f w (hfa w hw)
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact (DifferentiableAt.fun_sum fun j _ => (hg j z hz).differentiableAt (hO.mem_nhds hz)).const_smul
      (1 / (m : ℝ))

theorem I1_core {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ) (μ L : ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ)
    (hA : AssumptionA K O f G μ L) (hC : AssumptionC K O f ft μt Lt) (hgap : HessGap K f ft Dl Du)
    (i : Fin m) (x xh y : E d) (hx : x ∈ K) (hxh : xh ∈ K)
    (hmin : IsMinOn (fun w => ft i w x + ⟪y - gradient (f i) x, w - x⟫ + G w) K xh)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    U f G (x + α • (xh - x)) ≤ U f G x - α * ((1 - α / 2) * μt i + α / 2 * Dl i) * ‖xh - x‖ ^ 2
      + α * ‖xh - x‖ * ‖gradient (Fsum f) x - y‖ := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _, _, _, hGc⟩ := hA
  obtain ⟨hsm, hmatch, _, hmut, hsc⟩ := hC i
  set dd := xh - x with hdd
  set a : E d → ℝ := fun w => ft i w x with ha_def
  have hxO : x ∈ O := hKO hx
  set z : ℝ → E d := fun t => x + t • dd with hz_def
  have hzK : ∀ t ∈ Set.Icc (0:ℝ) 1, z t ∈ K := fun t ht => hKcv.add_smul_sub_mem hx hxh ht
  have hline : ∀ t : ℝ, HasDerivAt z dd t := by
    intro t
    have h := ((hasDerivAt_id t).smul_const dd).const_add x
    rw [one_smul] at h; exact h
  -- derivative data
  have haS := fun w (hw : w ∈ O) => ft_smooth hO (ft i) hsm x hxO w hw
  have hFS := fun w (hw : w ∈ O) => Fsum_smooth hO f (fun j => (hfi j).1) (fun j => (hfi j).2.1) w hw
  set ψ : ℝ → ℝ := fun t => a (z t) - Fsum f (z t) with hψ_def
  set χ : ℝ → ℝ := fun t => ⟪gradient a (z t) - gradient (Fsum f) (z t), dd⟫ with hχ_def
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (χ t) t := by
    intro t ht
    have hO' : z t ∈ O := hKO (hzK t ht)
    have h1 := (haS _ hO').1.hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := (hFS _ hO').1.hasFDerivAt.comp_hasDerivAt t (hline t)
    have h := h1.sub h2
    have e : fderiv ℝ a (z t) dd - fderiv ℝ (Fsum f) (z t) dd = χ t := by
      simp only [χ, inner_sub_left, fderiv_eq_inner_gradient]
    rw [e] at h; exact h
  have hχ : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ χ', HasDerivAt χ χ' t ∧ Dl i * ‖dd‖ ^ 2 ≤ χ' := by
    intro t ht
    have hO' : z t ∈ O := hKO (hzK t ht)
    have h1 := (haS _ hO').2.hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := (hFS _ hO').2.hasFDerivAt.comp_hasDerivAt t (hline t)
    have h3 := (h1.sub h2).inner ℝ (hasDerivAt_const t dd)
    refine ⟨_, h3, ?_⟩
    simp only [inner_zero_right, zero_add]
    have hb := ((hgap i).2 (z t) (hzK t ht) x hx dd).1
    have e : (fderiv ℝ (gradient a) (z t)) dd - (fderiv ℝ (gradient (Fsum f)) (z t)) dd
        = (phess (ft i) (z t) x - hess (Fsum f) (z t)) dd := by
      simp [phess, hess, a]
    rw [e]; exact hb
  have h3 := second_order_lower ψ χ (Dl i * ‖dd‖ ^ 2) α hα0.le hα1 hψ hχ
  have hχ0 : χ 0 = ⟪gradient (f i) x - gradient (Fsum f) x, dd⟫ := by
    simp only [χ, z, zero_smul, add_zero]
    rw [← hmatch x hx]
    rfl
  have hz0 : z 0 = x := by simp [z]
  have hzα : z α = x + α • dd := rfl
  simp only [ψ, hz0, hχ0] at h3
  rw [← hzα]
  -- (1) minimizer inequality
  have h1 := min_sc hKcv a G (y - gradient (f i) x) (μt i) hmut.le (hsc x hx) hGc x xh hx hxh hmin
  -- (2) strong convexity along the segment
  have h2 := (hsc x hx).2 hx hxh (show (0:ℝ) ≤ 1 - α by linarith) hα0.le (by ring : (1 - α) + α = 1)
  have hzα' : (1 - α) • x + α • xh = z α := by
    simp only [z, dd]; rw [smul_sub, sub_smul, one_smul]; abel
  rw [hzα', norm_sub_rev] at h2
  simp only [smul_eq_mul] at h2
  -- (4) convexity of G
  have h4 := hGc.2 hx hxh (show (0:ℝ) ≤ 1 - α by linarith) hα0.le (by ring : (1 - α) + α = 1)
  rw [hzα'] at h4
  simp only [smul_eq_mul] at h4
  -- (5) Cauchy–Schwarz
  have h5 : ⟪gradient (Fsum f) x - y, dd⟫ ≤ ‖dd‖ * ‖gradient (Fsum f) x - y‖ := by
    rw [mul_comm]; exact real_inner_le_norm _ _
  have h5' := mul_le_mul_of_nonneg_left h5 hα0.le
  have h1' := mul_le_mul_of_nonneg_left h1 hα0.le
  simp only [inner_sub_left] at h1 h1' h3 h5 h5'
  simp only [U, a] at *
  nlinarith [sq_nonneg ‖dd‖]

end SPushAux



open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem sq_add_le' {d : ℕ} (a b : E d) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]

theorem convexOn_fsum {d : ℕ} {ι : Type*} {K : Set (E d)} (hK : Convex ℝ K) (g : ι → E d → ℝ)
    (s : Finset ι) (hg : ∀ i ∈ s, ConvexOn ℝ K (g i)) :
    ConvexOn ℝ K (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hK
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have e : (fun x => ∑ i ∈ insert a s, g i x) = g a + fun x => ∑ i ∈ s, g i x := by
      funext x; simp [Finset.sum_insert ha]
    rw [e]; exact h1.add h2

theorem convexOn_U {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) : ConvexOn ℝ K (U f G) := by
  obtain ⟨_, _, hKcv, _, _, hfi, _, _, _, hGc⟩ := hA
  have h1 : ConvexOn ℝ K (fun x => ∑ i, f i x) :=
    convexOn_fsum hKcv f Finset.univ (fun i _ => (hfi i).2.2.1)
  have h2 := (h1.smul (c := 1 / (m : ℝ)) (by positivity)).add hGc
  have e : U f G = (fun x => (1 / (m : ℝ)) • ∑ i, f i x) + G := by
    funext x; simp [U, Fsum, smul_eq_mul]
  rw [e]; exact h2

/-- Eq. (6) of the supporting material: `p_φ^{ν+1} ≤ Σ_i φ_i^ν (U(x_i^{ν+1/2}) − U⋆)`. -/
theorem pphi_next_le {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L)
    {ft : Fin m → E d → E d → ℝ} {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl α : ℝ} (hN : NetworkHyp Edges B C cl)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x y xh : ℕ → Fin m → E d} {φ : ℕ → Fin m → ℝ} (hrun : IsRun K f G ft C α x y xh φ)
    (xstar : E d) (ν : ℕ) :
    pphi f G xstar (φ (ν + 1)) (x (ν + 1)) ≤
      ∑ i, φ ν i * (U f G (xhalf α x xh ν i) - U f G xstar) := by
  have hpos := phi_pos hN hrun
  have hC := C_nonneg hN
  have hxK := x_mem hA hN hα0 hα1 hrun
  have hcol := hN.2.2.2.2
  have hUc := convexOn_U hA
  have hKcv : Convex ℝ K := hA.2.2.1
  obtain ⟨_, _, _, hxh, hφs, hxs, _⟩ := hrun
  have hhalf : ∀ j, xhalf α x xh ν j ∈ K := fun j =>
    hKcv.add_smul_sub_mem (hxK ν j) (hxh ν j).1 ⟨hα0.le, hα1⟩
  have hJ : ∀ i, φ (ν + 1) i * U f G (x (ν + 1) i) ≤
      ∑ j, C ν i j * φ ν j * U f G (xhalf α x xh ν j) := by
    intro i
    have hp := hpos (ν + 1) i
    have e : x (ν + 1) i = ∑ j, ((φ (ν + 1) i)⁻¹ * (C ν i j * φ ν j)) • xhalf α x xh ν j := by
      rw [hxs ν i, Finset.smul_sum]; simp_rw [smul_smul]
    have hw0 : ∀ j ∈ Finset.univ, 0 ≤ (φ (ν + 1) i)⁻¹ * (C ν i j * φ ν j) := fun j _ =>
      mul_nonneg (inv_nonneg.mpr hp.le) (mul_nonneg (hC ν i j) (hpos ν j).le)
    have hw1 : ∑ j, (φ (ν + 1) i)⁻¹ * (C ν i j * φ ν j) = 1 := by
      rw [← Finset.mul_sum, ← hφs ν i]; exact inv_mul_cancel₀ hp.ne'
    have hj := hUc.map_sum_le hw0 hw1 (fun j _ => hhalf j)
    rw [← e] at hj
    simp only [smul_eq_mul] at hj
    have := mul_le_mul_of_nonneg_left hj hp.le
    rw [Finset.mul_sum] at this
    calc φ (ν + 1) i * U f G (x (ν + 1) i)
        ≤ ∑ j, φ (ν + 1) i * ((φ (ν + 1) i)⁻¹ * (C ν i j * φ ν j) * U f G (xhalf α x xh ν j)) :=
          this
      _ = ∑ j, C ν i j * φ ν j * U f G (xhalf α x xh ν j) := by
          apply Finset.sum_congr rfl; intro j _; field_simp
  unfold pphi
  have e1 : ∑ i, φ (ν + 1) i * (U f G (x (ν + 1) i) - U f G xstar) =
      ∑ i, φ (ν + 1) i * U f G (x (ν + 1) i) - (∑ i, φ (ν + 1) i) * U f G xstar := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  have e2 : ∑ i, φ ν i * (U f G (xhalf α x xh ν i) - U f G xstar) =
      ∑ i, φ ν i * U f G (xhalf α x xh ν i) - (∑ i, φ ν i) * U f G xstar := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  have e3 : ∑ i, φ (ν + 1) i = ∑ i, φ ν i := by
    simp_rw [hφs ν]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hcol ν, one_mul]
  have e4 : ∑ i, ∑ j, C ν i j * φ ν j * U f G (xhalf α x xh ν j) =
      ∑ j, φ ν j * U f G (xhalf α x xh ν j) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    simp_rw [mul_assoc]; rw [← Finset.sum_mul, hcol ν j, one_mul]
  rw [e1, e2, e3]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hJ i)
  rw [e4] at this
  linarith

/-- First-order optimality of the local problem. -/
theorem fo_opt {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (a G : E d → ℝ) (c x xh w : E d)
    (hxh : xh ∈ K) (hw : w ∈ K) (hG : ConvexOn ℝ K G)
    (hmin : IsMinOn (fun w => a w + ⟪c, w - x⟫ + G w) K xh) (ha : DifferentiableAt ℝ a xh) :
    -⟪gradient a xh + c, w - xh⟫ ≤ G w - G xh := by
  set v := w - xh
  have hline : HasDerivAt (fun t : ℝ => xh + t • v) v 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add xh
    rw [one_smul] at h; exact h
  have ha' : HasFDerivAt a (fderiv ℝ a xh) (xh + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]; exact ha.hasFDerivAt
  have hd := ha'.comp_hasDerivAt (0:ℝ) hline
  have hlim := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      G xh - G w - ⟪c, v⟫ ≤ t⁻¹ • ((a ∘ fun t : ℝ => xh + t • v) (0 + t) - (a ∘ fun t : ℝ => xh + t • v) 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul]
    have hmem : xh + t • v ∈ K := hK.add_smul_sub_mem hxh hw ⟨ht0.le, ht1.le⟩
    have h1 := isMinOn_iff.mp hmin _ hmem
    have hconv : xh + t • v = (1 - t) • xh + t • w := by
      simp only [v, smul_sub, sub_smul, one_smul]; abel
    have h2 := hG.2 hxh hw (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    rw [← hconv] at h2
    simp only [smul_eq_mul] at h1 h2
    have hlin : ⟪c, xh + t • v - x⟫ = ⟪c, xh - x⟫ + t * ⟪c, v⟫ := by
      rw [show xh + t • v - x = (xh - x) + t • v by abel, inner_add_right, inner_smul_right]
    rw [hlin] at h1
    rw [le_inv_mul_iff₀ ht0]
    nlinarith
  have := ge_of_tendsto hlim hev
  rw [fderiv_eq_inner_gradient] at this
  rw [inner_add_left]
  linarith

theorem Dcoef_le_Dmx {m : ℕ} (Dl Du : Fin m → ℝ) (i : Fin m) :
    SONATA.Undir.Dcoef Dl Du i ≤ Dmx Dl Du :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- Strong convexity of `F` on `K` from the Hessian lower bound `μ`. -/
theorem sc_F {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {z w : E d} (hz : z ∈ K) (hw : w ∈ K) :
    Fsum f z + ⟪gradient (Fsum f) z, w - z⟫ + μ / 2 * ‖w - z‖ ^ 2 ≤ Fsum f w := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _, _, hH, _⟩ := hA
  set v := w - z
  set p : ℝ → E d := fun t => z + t • v
  have hpK : ∀ t ∈ Set.Icc (0:ℝ) 1, p t ∈ K := fun t ht => hKcv.add_smul_sub_mem hz hw ht
  have hline : ∀ t : ℝ, HasDerivAt p v t := by
    intro t
    have h := ((hasDerivAt_id t).smul_const v).const_add z
    rw [one_smul] at h; exact h
  have hFS := fun w (hw : w ∈ O) => Fsum_smooth hO f (fun j => (hfi j).1) (fun j => (hfi j).2.1) w hw
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => Fsum f (p t))
      ((fun t => ⟪gradient (Fsum f) (p t), v⟫) t) t := by
    intro t ht
    have h := (hFS _ (hKO (hpK t ht))).1.hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [fderiv_eq_inner_gradient] at h; exact h
  have hχ : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ χ', HasDerivAt (fun t => ⟪gradient (Fsum f) (p t), v⟫) χ' t
      ∧ μ * ‖v‖ ^ 2 ≤ χ' := by
    intro t ht
    have h1 := (hFS _ (hKO (hpK t ht))).2.hasFDerivAt.comp_hasDerivAt t (hline t)
    have h3 := h1.inner ℝ (hasDerivAt_const t v)
    refine ⟨_, h3, ?_⟩
    simp only [inner_zero_right, zero_add]
    exact (hH (p t) (hpK t ht) v).1
  have := second_order_lower _ _ (μ * ‖v‖ ^ 2) 1 zero_le_one le_rfl hψ hχ
  simp only [p, zero_smul, add_zero, one_smul, one_mul, one_pow] at this
  have e : z + v = w := by simp [v]
  rw [e] at this
  linarith

/-- Gradient-gap mean value bound: `‖(∇F − ∇f̃ᵢ(·;x))(w) − (∇F − ∇f̃ᵢ(·;x))(x)‖ ≤ Dᵢ ‖w − x‖`. -/
theorem gap_lip {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ}
    (hC : AssumptionC K O f ft μt Lt) (hgap : HessGap K f ft Dl Du) (i : Fin m) {x w : E d}
    (hx : x ∈ K) (hw : w ∈ K) :
    ‖(gradient (Fsum f) w - gradient (fun v => ft i v x) w) -
      (gradient (Fsum f) x - gradient (fun v => ft i v x) x)‖ ≤
      SONATA.Undir.Dcoef Dl Du i * ‖w - x‖ := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _⟩ := hA
  obtain ⟨hsm, _⟩ := hC i
  have haS := fun z (hz : z ∈ O) => ft_smooth hO (ft i) hsm x (hKO hx) z hz
  have hFS := fun z (hz : z ∈ O) => Fsum_smooth hO f (fun j => (hfi j).1) (fun j => (hfi j).2.1) z hz
  have hder : ∀ z ∈ K, HasFDerivWithinAt
      (fun z => gradient (Fsum f) z - gradient (fun v => ft i v x) z)
      (hess (Fsum f) z - phess (ft i) z x) K z := by
    intro z hz
    exact ((hFS z (hKO hz)).2.hasFDerivAt.sub (haS z (hKO hz)).2.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ K, ‖hess (Fsum f) z - phess (ft i) z x‖ ≤ SONATA.Undir.Dcoef Dl Du i := by
    intro z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (abs_nonneg _))
    intro u
    apply norm_apply_le_of_quad
    · intro u v
      have hs1 := hess_symm (Fsum f) z
        (Filter.mem_of_superset (hO.mem_nhds (hKO hz)) fun y hy => (hFS y hy).1)
        (hFS z (hKO hz)).2 u v
      have hs2 := hess_symm (fun v => ft i v x) z
        (Filter.mem_of_superset (hO.mem_nhds (hKO hz)) fun y hy => (haS y hy).1)
        (haS z (hKO hz)).2 u v
      simp only [ContinuousLinearMap.sub_apply, inner_sub_left]
      have e1 : phess (ft i) z x = hess (fun v => ft i v x) z := rfl
      rw [e1, hs1, hs2]
    · intro u
      obtain ⟨hlo, hhi⟩ := (hgap i).2 z hz x hx u
      have e : ⟪(hess (Fsum f) z - phess (ft i) z x) u, u⟫ =
          -⟪(phess (ft i) z x - hess (Fsum f) z) u, u⟫ := by
        simp only [ContinuousLinearMap.sub_apply, inner_sub_left]; ring
      rw [e, abs_neg, abs_le]
      have h1 : |Dl i| * ‖u‖ ^ 2 ≤ SONATA.Undir.Dcoef Dl Du i * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      have h2 : |Du i| * ‖u‖ ^ 2 ≤ SONATA.Undir.Dcoef Dl Du i * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      have h3 : -|Dl i| ≤ Dl i := neg_abs_le _
      have h4 : Du i ≤ |Du i| := le_abs_self _
      simp only [SONATA.Undir.Dcoef] at h1 h2 ⊢
      constructor <;> nlinarith [sq_nonneg ‖u‖]
  exact hKcv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hx hw

/-- (11) for one agent: `μ (U(x̂) − U⋆) ≤ Dᵢ² ‖d‖² + ‖δ‖²`. -/
theorem I2_agent {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ) (μ L : ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : E d)
    (hA : AssumptionA K O f G μ L) (hC : AssumptionC K O f ft μt Lt) (hgap : HessGap K f ft Dl Du)
    (hxs : xstar ∈ K)
    (i : Fin m) (x xh y : E d) (hx : x ∈ K) (hxh : xh ∈ K)
    (hmin : IsMinOn (fun w => ft i w x + ⟪y - gradient (f i) x, w - x⟫ + G w) K xh) :
    μ * (U f G xh - U f G xstar) ≤
      SONATA.Undir.Dcoef Dl Du i ^ 2 * ‖xh - x‖ ^ 2 + ‖gradient (Fsum f) x - y‖ ^ 2 := by
  have hμ : 0 < μ := hA.2.2.2.2.2.2.1
  have hKcv : Convex ℝ K := hA.2.2.1
  have hO := hA.2.2.2.1
  have hKO := hA.2.2.2.2.1
  have hGc : ConvexOn ℝ K G := hA.2.2.2.2.2.2.2.2.2
  obtain ⟨hsm, hmatch, _⟩ := hC i
  set a : E d → ℝ := fun v => ft i v x
  have haS := ft_smooth hO (ft i) hsm x (hKO hx) xh (hKO hxh)
  have h1 := fo_opt hKcv a G (y - gradient (f i) x) x xh xstar hxh hxs hGc hmin haS.1
  have h2 := sc_F hA hxh hxs
  -- e = ∇F(x̂) − ∇a(x̂) − (y − ∇fᵢ(x))
  set e : E d := gradient (Fsum f) xh - gradient a xh - (y - gradient (f i) x)
  have hU : U f G xh - U f G xstar ≤ -⟪e, xstar - xh⟫ - μ / 2 * ‖xstar - xh‖ ^ 2 := by
    simp only [U, e, inner_sub_left, inner_add_left] at h1 h2 ⊢
    linarith
  have hsq : -⟪e, xstar - xh⟫ - μ / 2 * ‖xstar - xh‖ ^ 2 ≤ ‖e‖ ^ 2 / (2 * μ) := by
    have h3 : -⟪e, xstar - xh⟫ ≤ ‖e‖ * ‖xstar - xh‖ := by
      have := real_inner_le_norm (-e) (xstar - xh)
      rw [inner_neg_left, norm_neg] at this; exact this
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖e‖ - μ * ‖xstar - xh‖), norm_nonneg e, norm_nonneg (xstar - xh)]
  have hgl := gap_lip hA hC hgap i hx hxh
  have hax : gradient a x = gradient (f i) x := hmatch x hx
  have he : e = ((gradient (Fsum f) xh - gradient a xh) - (gradient (Fsum f) x - gradient a x)) +
      (gradient (Fsum f) x - y) := by
    simp only [e, hax]; abel
  have hD0 : 0 ≤ SONATA.Undir.Dcoef Dl Du i := le_max_of_le_left (abs_nonneg _)
  have he2 : ‖e‖ ^ 2 ≤ 2 * (SONATA.Undir.Dcoef Dl Du i ^ 2 * ‖xh - x‖ ^ 2) +
      2 * ‖gradient (Fsum f) x - y‖ ^ 2 := by
    rw [he]
    have h4 := sq_add_le' ((gradient (Fsum f) xh - gradient a xh) - (gradient (Fsum f) x - gradient a x))
      (gradient (Fsum f) x - y)
    have h5 : ‖(gradient (Fsum f) xh - gradient a xh) - (gradient (Fsum f) x - gradient a x)‖ ^ 2 ≤
        (SONATA.Undir.Dcoef Dl Du i * ‖xh - x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hgl 2
    rw [mul_pow] at h5
    linarith
  have : μ * (U f G xh - U f G xstar) ≤ ‖e‖ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left (hU.trans hsq) hμ.le
    have e5 : μ * (‖e‖ ^ 2 / (2 * μ)) = ‖e‖ ^ 2 / 2 := by field_simp
    linarith
  linarith

end SPushAux


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem cross {α : Type*} (r : α → α → Prop) (S : α → Prop) {a c : α}
    (h : Relation.ReflTransGen r a c) (ha : S a) (hc : ¬ S c) :
    ∃ x y, S x ∧ ¬ S y ∧ r x y := by
  revert hc
  induction h with
  | refl => intro hc; exact absurd ha hc
  | @tail b c' _ hbc ih =>
    intro hc
    by_cases hb : S b
    · exact ⟨_, _, hb, hc, hbc⟩
    · exact ih hb

section core
variable {m : ℕ} (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ)
  (cl : ℝ) (φ : ℕ → Fin m → ℝ)

/-- reached set -/
noncomputable def Rset (s k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => cl ^ k ≤ φ (s + k) i)

theorem step_edge (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (ν : ℕ) (l i : Fin m) (h : l = i ∨ Edges ν l i) : cl * φ ν l ≤ φ (ν + 1) i := by
  rw [hφs ν i]
  have h1 : C ν i l * φ ν l ≤ ∑ j, C ν i j * φ ν j :=
    Finset.single_le_sum (f := fun j => C ν i j * φ ν j)
      (fun j _ => mul_nonneg (hC ν i j) (hpos ν j)) (Finset.mem_univ l)
  have h2 : cl ≤ C ν i l := by
    rcases h with h | h
    · subst h; exact hdiag ν l
    · by_cases hil : i = l
      · subst hil; exact hdiag ν i
      · exact hedge ν i l hil h
  have := mul_le_mul_of_nonneg_right h2 (hpos ν l)
  linarith

theorem Rset_mono (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (s : ℕ) {l i : Fin m} {k : ℕ} (hl : l ∈ Rset cl φ s k)
    (h : l = i ∨ Edges (s + k) l i) : i ∈ Rset cl φ s (k + 1) := by
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  have := step_edge Edges C cl φ hC hpos hφs hdiag hedge (s + k) l i h
  rw [pow_succ, ← add_assoc]
  have h3 := mul_le_mul_of_nonneg_left hl hcl.le
  linarith

theorem Rset_mono' (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (s : ℕ) {i : Fin m} {k k' : ℕ} (hk : k ≤ k') (hi : i ∈ Rset cl φ s k) :
    i ∈ Rset cl φ s k' := by
  induction k', hk using Nat.le_induction with
  | base => exact hi
  | succ n _ ih => exact Rset_mono Edges C cl φ hC hpos hφs hdiag hedge hcl s ih (Or.inl rfl)

theorem Rset_grow (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (hB : AssumptionB' Edges B) (w0 n : ℕ) {j : Fin m}
    (hj : j ∈ Rset cl φ (w0 * B) (n * B)) (hne : Rset cl φ (w0 * B) (n * B) ≠ Finset.univ) :
    Rset cl φ (w0 * B) (n * B) ⊂ Rset cl φ (w0 * B) ((n + 1) * B) := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ Rset cl φ (w0 * B) (n * B) := by
    by_contra hcon; push Not at hcon
    exact hne (Finset.eq_univ_of_forall hcon)
  have hpath := hB.2 (w0 + n) j i
  obtain ⟨a, b, ha, hb, t, ht1, ht2, hab⟩ :=
    cross _ (fun z => z ∈ Rset cl φ (w0 * B) (n * B)) hpath hj hi
  have e1 : (w0 + n) * B = w0 * B + n * B := by ring
  have e2 : (w0 + n + 1) * B = w0 * B + n * B + B := by ring
  have e3 : (n + 1) * B = n * B + B := by ring
  rw [e1] at ht1; rw [e2] at ht2
  obtain ⟨k, hk⟩ : ∃ k, t = w0 * B + k := ⟨t - w0 * B, by omega⟩
  have hk1 : n * B ≤ k := by omega
  have hk2 : k + 1 ≤ (n + 1) * B := by rw [e3]; omega
  have ha' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) hk1 ha
  rw [hk] at hab
  have hb' := Rset_mono Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) ha' (Or.inr hab)
  have hb'' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B) hk2 hb'
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨b, hb'', hb⟩
  · intro z hz
    exact Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
      (by rw [e3]; omega) hz

theorem Rset_count (hC : ∀ ν i j, 0 ≤ C ν i j) (hpos : ∀ ν i, 0 ≤ φ ν i)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j)
    (hdiag : ∀ ν i, cl ≤ C ν i i) (hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j)
    (hcl : 0 < cl) (hB : AssumptionB' Edges B) (w0 : ℕ) {j : Fin m}
    (hj : j ∈ Rset cl φ (w0 * B) 0) :
    ∀ n, Rset cl φ (w0 * B) (n * B) = Finset.univ ∨ n + 1 ≤ (Rset cl φ (w0 * B) (n * B)).card := by
  intro n
  induction n with
  | zero =>
    right; simp only [zero_mul, zero_add, Finset.one_le_card]; exact ⟨j, hj⟩
  | succ n ih =>
    by_cases hne : Rset cl φ (w0 * B) (n * B) = Finset.univ
    · left
      apply Finset.eq_univ_of_forall
      intro z
      have hz : z ∈ Rset cl φ (w0 * B) (n * B) := by rw [hne]; exact Finset.mem_univ z
      exact Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
        (Nat.mul_le_mul_right B (Nat.le_succ n)) hz
    · right
      rcases ih with h | h
      · exact absurd h hne
      · have hj' := Rset_mono' Edges C cl φ hC hpos hφs hdiag hedge hcl (w0 * B)
          (Nat.zero_le (n * B)) hj
        have := Finset.card_lt_card
          (Rset_grow Edges B C cl φ hC hpos hφs hdiag hedge hcl hB w0 n hj' hne)
        omega

end core

theorem phi_core {m : ℕ} (hm : 2 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl)
    (φ : ℕ → Fin m → ℝ) (hφ0 : ∀ i, φ 0 i = 1)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j) :
    ∀ ν i, phiLb m B cl ≤ φ ν i ∧ φ ν i ≤ phiUb m B cl := by
  have hC := C_nonneg hN
  obtain ⟨hB, hcl, hdiag, hoff, hcol⟩ := hN
  have hedge : ∀ ν i j, i ≠ j → Edges ν j i → cl ≤ C ν i j := fun ν i j h he => (hoff ν i j h).1 he
  have hm0 : 0 < m := by omega
  -- positivity and sum
  have hposs : ∀ ν i, 0 < φ ν i := by
    intro ν
    induction ν with
    | zero => intro i; rw [hφ0 i]; norm_num
    | succ n ih =>
      intro i
      rw [hφs n i]
      have hle : C n i i * φ n i ≤ ∑ j, C n i j * φ n j :=
        Finset.single_le_sum (f := fun j => C n i j * φ n j)
          (fun j _ => mul_nonneg (hC n i j) (ih j).le) (Finset.mem_univ i)
      have : 0 < C n i i * φ n i := mul_pos (lt_of_lt_of_le hcl (hdiag n i)) (ih i)
      linarith
  have hpos : ∀ ν i, 0 ≤ φ ν i := fun ν i => (hposs ν i).le
  have hsum : ∀ ν, ∑ i, φ ν i = m := by
    intro ν
    induction ν with
    | zero => simp [hφ0]
    | succ n ih =>
      simp_rw [hφs n]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol n, one_mul]
      exact ih
  have hcl1 : cl ≤ 1 := by
    have i0 : Fin m := ⟨0, hm0⟩
    have h1 : C 0 i0 i0 ≤ ∑ l, C 0 l i0 :=
      Finset.single_le_sum (f := fun l => C 0 l i0) (fun l _ => hC 0 l i0) (Finset.mem_univ i0)
    rw [hcol 0 i0] at h1
    linarith [hdiag 0 i0]
  have hdiagstep : ∀ t i, cl * φ t i ≤ φ (t + 1) i := fun t i =>
    step_edge Edges C cl φ hC hpos hφs hdiag hedge t i i (Or.inl rfl)
  have hiter : ∀ t k i, cl ^ k * φ t i ≤ φ (t + k) i := by
    intro t k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have := hdiagstep (t + k) i
      have h2 := mul_le_mul_of_nonneg_left (ih i) hcl.le
      rw [pow_succ, ← add_assoc]
      nlinarith
  set M := (m - 1) * B with hM
  have hlbeq : phiLb m B cl = cl ^ (2 * M) := by
    simp only [phiLb, hM]; ring_nf
  -- aligned windows: full reach
  have hfull : ∀ w0 i, cl ^ M ≤ φ (w0 * B + M) i := by
    intro w0 i
    obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, (1 : ℝ) ≤ φ (w0 * B) j := by
      have : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
      apply Finset.exists_le_of_sum_le Finset.univ_nonempty
      rw [hsum]; simp
    have hj0 : j ∈ Rset cl φ (w0 * B) 0 := by
      simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and, pow_zero, add_zero]
      exact hj
    have hc := Rset_count Edges B C cl φ hC hpos hφs hdiag hedge hcl hB w0 hj0 (m - 1)
    have huniv : Rset cl φ (w0 * B) ((m - 1) * B) = Finset.univ := by
      rcases hc with h | h
      · exact h
      · apply Finset.eq_univ_of_card
        have := Finset.card_le_univ (Rset cl φ (w0 * B) ((m - 1) * B))
        simp only [Fintype.card_fin] at this ⊢
        omega
    have hi : i ∈ Rset cl φ (w0 * B) ((m - 1) * B) := by rw [huniv]; exact Finset.mem_univ i
    simpa [Rset] using hi
  have hBM : B ≤ M := by
    rw [hM]; exact Nat.le_mul_of_pos_left B (by omega)
  have hlb : ∀ ν i, cl ^ (2 * M) ≤ φ ν i := by
    intro ν i
    by_cases hν : ν ≤ 2 * M
    · have h1 := hiter 0 ν i
      rw [hφ0 i, mul_one, zero_add] at h1
      exact (pow_le_pow_of_le_one hcl.le hcl1 hν).trans h1
    · push Not at hν
      have hBpos : 0 < B := hB.1
      obtain ⟨r, hr⟩ : ∃ r, r = ν - 2 * M := ⟨_, rfl⟩
      obtain ⟨w0, hw0⟩ : ∃ w0, w0 = (r + B - 1) / B := ⟨_, rfl⟩
      have hs1 : w0 * B ≤ r + B - 1 := by rw [hw0]; exact Nat.div_mul_le_self _ _
      have hs2 : r ≤ w0 * B := by
        have := Nat.lt_div_mul_add (a := r + B - 1) hBpos
        rw [← hw0] at this
        omega
      have hle : w0 * B + M ≤ ν := by omega
      obtain ⟨k, hk⟩ : ∃ k, ν = w0 * B + M + k := ⟨ν - (w0 * B + M), by omega⟩
      have h1 := hiter (w0 * B + M) k i
      rw [← hk] at h1
      have h2 := hfull w0 i
      have h3 : cl ^ k * cl ^ M ≤ cl ^ k * φ (w0 * B + M) i :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hcl.le k)
      have h4 : cl ^ (2 * M) ≤ cl ^ k * cl ^ M := by
        rw [← pow_add]
        exact pow_le_pow_of_le_one hcl.le hcl1 (by omega)
      linarith
  intro ν i
  refine ⟨hlbeq ▸ hlb ν i, ?_⟩
  -- upper bound
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin m, j0 ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  have hs := hsum ν
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
  have h1 : φ ν j0 ≤ ∑ j ∈ Finset.univ.erase i, φ ν j :=
    Finset.single_le_sum (f := fun j => φ ν j) (fun j _ => hpos ν j)
      (Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j0⟩)
  have h2 := hlb ν j0
  simp only [phiUb]
  have : (2 * (m - 1) * B) = 2 * M := by rw [hM]; ring
  rw [this]
  linarith

end SPushAux



open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

theorem Li_le_Lmx' {m : ℕ} (Li : Fin m → ℝ) (j : Fin m) : Li j ≤ Lmx Li :=
  le_ciSup (Set.finite_range Li).bddAbove j

/-- First-order characterization of strong convexity. -/
theorem sc_first_order {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (a : E d → ℝ) (μt : ℝ)
    (ha : StrongConvexOn K μt a) {z w : E d} (hz : z ∈ K) (hw : w ∈ K)
    (hd : DifferentiableAt ℝ a z) :
    a z + ⟪gradient a z, w - z⟫ + μt / 2 * ‖w - z‖ ^ 2 ≤ a w := by
  set v := w - z
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
    rw [one_smul] at h; exact h
  have ha' : HasFDerivAt a (fderiv ℝ a z) (z + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hlim := (ha'.comp_hasDerivAt (0:ℝ) hline).tendsto_slope_zero_right
  have hlim2 : Filter.Tendsto (fun t : ℝ => a w - a z - (1 - t) * (μt / 2 * ‖v‖ ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (a w - a z - (1 - 0) * (μt / 2 * ‖v‖ ^ 2))) := by
    have hc : Filter.Tendsto (fun t : ℝ => a w - a z - (1 - t) * (μt / 2 * ‖v‖ ^ 2)) (nhds 0)
        (nhds (a w - a z - (1 - 0) * (μt / 2 * ‖v‖ ^ 2))) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds.sub Filter.tendsto_id).mul tendsto_const_nhds)
    exact hc.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      t⁻¹ • ((a ∘ fun t : ℝ => z + t • v) (0 + t) - (a ∘ fun t : ℝ => z + t • v) 0) ≤
        a w - a z - (1 - t) * (μt / 2 * ‖v‖ ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul]
    have hconv : z + t • v = (1 - t) • z + t • w := by
      simp only [v, smul_sub, sub_smul, one_smul]; abel
    have h2 := ha.2 hz hw (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    rw [← hconv] at h2
    simp only [smul_eq_mul] at h2
    have hn : ‖z - w‖ = ‖v‖ := by rw [norm_sub_rev]
    rw [hn] at h2
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto_of_tendsto hlim hlim2 hev
  rw [fderiv_eq_inner_gradient] at this
  simp only [sub_zero, one_mul] at this
  linarith

theorem fo_opt_star {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {xstar w : E d} (hxs : xstar ∈ K) (hw : w ∈ K)
    (hmin : IsMinOn (U f G) K xstar) :
    -⟪gradient (Fsum f) xstar, w - xstar⟫ ≤ G w - G xstar := by
  obtain ⟨_, _, hKcv, hO, hKO, hfi, _, _, _, hGc⟩ := hA
  have hFS := Fsum_smooth hO f (fun j => (hfi j).1) (fun j => (hfi j).2.1) xstar (hKO hxs)
  have hmin' : IsMinOn (fun w => Fsum f w + ⟪(0 : E d), w - xstar⟫ + G w) K xstar := by
    have e : (fun w => Fsum f w + ⟪(0 : E d), w - xstar⟫ + G w) = U f G := by
      funext w; simp [U]
    rw [e]; exact hmin
  have := fo_opt hKcv (Fsum f) G 0 xstar xstar w hxs hw hGc hmin' hFS.1
  simpa using this

/-- Quadratic growth of `U` at the minimizer. -/
theorem U_growth {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    (hA : AssumptionA K O f G μ L) {xstar w : E d} (hxs : xstar ∈ K) (hw : w ∈ K)
    (hmin : IsMinOn (U f G) K xstar) :
    μ / 2 * ‖w - xstar‖ ^ 2 ≤ U f G w - U f G xstar := by
  have h1 := sc_F hA hxs hw
  have h2 := fo_opt_star hA hxs hw hmin
  simp only [U]; linarith

/-- (48): `μ̃ᵢ ‖x̂ − x⋆‖ ≤ Dᵢ ‖x⋆ − x‖ + ‖δ‖`. -/
theorem P43_agent {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ) (μ L : ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : E d)
    (hA : AssumptionA K O f G μ L) (hC : AssumptionC K O f ft μt Lt) (hgap : HessGap K f ft Dl Du)
    (hxs : xstar ∈ K) (hxsmin : IsMinOn (U f G) K xstar)
    (i : Fin m) (x xh y : E d) (hx : x ∈ K) (hxh : xh ∈ K)
    (hmin : IsMinOn (fun w => ft i w x + ⟪y - gradient (f i) x, w - x⟫ + G w) K xh) :
    μt i * ‖xh - xstar‖ ≤
      SONATA.Undir.Dcoef Dl Du i * ‖xstar - x‖ + ‖gradient (Fsum f) x - y‖ := by
  have hKcv : Convex ℝ K := hA.2.2.1
  have hO := hA.2.2.2.1
  have hKO := hA.2.2.2.2.1
  have hGc : ConvexOn ℝ K G := hA.2.2.2.2.2.2.2.2.2
  obtain ⟨hsm, hmatch, _, _, hsc⟩ := hC i
  set a : E d → ℝ := fun v => ft i v x
  have haS := fun z (hz : z ∈ O) => ft_smooth hO (ft i) hsm x (hKO hx) z hz
  have h1 := fo_opt hKcv a G (y - gradient (f i) x) x xh xstar hxh hxs hGc hmin (haS xh (hKO hxh)).1
  have h2 := fo_opt_star hA hxs hxh hxsmin
  have hs1 := sc_first_order hKcv a (μt i) (hsc x hx) hxh hxs (haS xh (hKO hxh)).1
  have hs2 := sc_first_order hKcv a (μt i) (hsc x hx) hxs hxh (haS xstar (hKO hxs)).1
  have hgl := gap_lip hA hC hgap i hx hxs
  have hax : gradient a x = gradient (f i) x := hmatch x hx
  set v := xh - xstar
  set E1 := (gradient (Fsum f) xstar - gradient a xstar) - (gradient (Fsum f) x - gradient a x)
  set δ := gradient (Fsum f) x - y
  have hv1 : xstar - xh = -v := by simp [v]
  rw [hv1] at h1 hs1
  rw [norm_neg] at hs1
  -- 0 ≤ ⟪E1, v⟫ - μ̃‖v‖² + ⟪δ, v⟫
  have key : μt i * ‖v‖ ^ 2 ≤ ⟪E1, v⟫ + ⟪δ, v⟫ := by
    have e1 : ⟪E1, v⟫ + ⟪δ, v⟫ = ⟪gradient (Fsum f) xstar, v⟫ - ⟪gradient a xstar, v⟫
        + ⟪gradient (f i) x, v⟫ - ⟪y, v⟫ := by
      simp only [E1, δ, inner_sub_left, ← hax]; ring
    rw [e1]
    simp only [inner_neg_right, inner_add_left, inner_sub_left] at h1 h2 hs1 hs2
    linarith
  have hE1 : ⟪E1, v⟫ ≤ SONATA.Undir.Dcoef Dl Du i * ‖xstar - x‖ * ‖v‖ := by
    refine (real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right hgl (norm_nonneg _)
  have hδ : ⟪δ, v⟫ ≤ ‖δ‖ * ‖v‖ := real_inner_le_norm _ _
  have hμt : 0 < μt i := (hC i).2.2.2.1
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · rw [← h0]
    have : 0 ≤ SONATA.Undir.Dcoef Dl Du i := le_max_of_le_left (abs_nonneg _)
    simp only [mul_zero]; positivity
  · have : μt i * ‖v‖ * ‖v‖ ≤ (SONATA.Undir.Dcoef Dl Du i * ‖xstar - x‖ + ‖δ‖) * ‖v‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

theorem mutmn_pos {m : ℕ} (hm : 0 < m) (μt : Fin m → ℝ) (h : ∀ i, 0 < μt i) : 0 < mutmn μt := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := μt)
  simp only [mutmn]; rw [← hi]; exact h i

theorem mutmn_le {m : ℕ} (μt : Fin m → ℝ) (i : Fin m) : mutmn μt ≤ μt i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem phi_lb_all {m : ℕ} (hm : 1 ≤ m) (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) (hN : NetworkHyp Edges B C cl)
    (φ : ℕ → Fin m → ℝ) (hφ0 : ∀ i, φ 0 i = 1)
    (hφs : ∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j) :
    ∀ ν i, phiLb m B cl ≤ φ ν i := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    have hcol := hN.2.2.2.2
    have hC1 : ∀ ν, C ν 0 0 = 1 := fun ν => by simpa using hcol ν 0
    have hφ1 : ∀ ν i, φ ν i = 1 := by
      intro ν; induction ν with
      | zero => exact hφ0
      | succ n ih => intro i; rw [hφs n i]; simp [Fin.fin_one_eq_zero i, hC1, ih]
    intro ν i; rw [hφ1]; simp [phiLb]
  · exact fun ν i => (phi_core h Edges B C cl hN φ hφ0 hφs ν i).1

theorem avg_grad_bound {m d : ℕ} (hm : 0 < m) (f : Fin m → E d → ℝ) (Lmax : ℝ) (hL : 0 ≤ Lmax)
    (X : Fin m → E d) (c : E d)
    (hlip : ∀ i j, ‖gradient (f j) (X i) - gradient (f j) (X j)‖ ≤ Lmax * ‖X i - X j‖) (i : Fin m) :
    ‖(1 / (m : ℝ)) • ∑ j, (gradient (f j) (X i) - gradient (f j) (X j))‖ ≤
      Lmax * (‖X i - c‖ + (1 / (m : ℝ)) * ∑ k, ‖X k - c‖) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖∑ j, (gradient (f j) (X i) - gradient (f j) (X j))‖ ≤
      ∑ j, Lmax * (‖X i - c‖ + ‖X j - c‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (hlip i j).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL
    have : X i - X j = (X i - c) - (X j - c) := by abel
    rw [this]; exact norm_sub_le _ _
  have h2 : ∑ j, Lmax * (‖X i - c‖ + ‖X j - c‖) = Lmax * (m * ‖X i - c‖ + ∑ k, ‖X k - c‖) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
  rw [h2] at h1
  calc 1 / (m : ℝ) * ‖∑ j, (gradient (f j) (X i) - gradient (f j) (X j))‖
      ≤ 1 / (m : ℝ) * (Lmax * (m * ‖X i - c‖ + ∑ k, ‖X k - c‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Lmax * (‖X i - c‖ + (1 / (m : ℝ)) * ∑ k, ‖X k - c‖) := by field_simp

/-- Proposition 4.3 in the run setting. -/
theorem P43_run {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ) (μ L : ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ)
    (ν : ℕ) :
    sqn (dir x xh ν) ≤
        6 / (μ * phiLb m B cl) *
            ((Dmx Dl Du / mutmn μt + 1) ^ 2 + 4 * Lmx Li ^ 2 / mutmn μt ^ 2) *
            pphi f G xstar (φ ν) (x ν)
          + 3 / mutmn μt ^ 2 * sqn (wperp (φ ν) (y ν)) := by
  have hm : 0 < m := hP.1
  have h74 := (SONATA.Push.eq_74 K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN α hα0 hα1
    x y xh φ hrun).2 ν
  obtain ⟨_, hA, hC, hgap, hxs, hxsmin⟩ := hP
  have hμ : 0 < μ := hA.2.2.2.2.2.2.1
  have hxK := x_mem hA hN hα0 hα1 hrun
  have hpos := phi_pos hN hrun
  have hlb := phi_lb_all hm Edges B C cl hN φ hrun.2.2.1 hrun.2.2.2.2.1
  have hlb0 : 0 < phiLb m B cl := by
    unfold phiLb; exact pow_pos hN.2.1 _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hμmn := mutmn_pos hm μt (fun i => (hC i).2.2.2.1)
  have hL0 : 0 ≤ Lmx Li := (h1 ⟨0, hm⟩).2.1.le.trans (Li_le_Lmx' Li ⟨0, hm⟩)
  have hD0 : 0 ≤ Dmx Dl Du :=
    (le_max_of_le_left (abs_nonneg _)).trans (Dcoef_le_Dmx Dl Du ⟨0, hm⟩)
  have hO := hA.2.2.2.1
  have hKO := hA.2.2.2.2.1
  have hfi := hA.2.2.2.2.2.1
  set X := x ν
  set b : Fin m → ℝ := fun k => ‖X k - xstar‖ with hb
  set S := ∑ k, b k ^ 2 with hS
  set P := Dmx Dl Du / mutmn μt + 1
  set Q := 1 / mutmn μt
  set R := Lmx Li / mutmn μt
  set bb := (1 / (m : ℝ)) * ∑ k, b k
  -- per-agent bound
  have hag : ∀ i, ‖dir x xh ν i‖ ≤ P * b i + Q * ‖wperp (φ ν) (y ν) i‖ + R * (b i + bb) := by
    intro i
    obtain ⟨hxhK, hmin⟩ := hrun.2.2.2.1 ν i
    have h48 := P43_agent K O f G μ L ft μt Lt Dl Du xstar hA hC hgap hxs hxsmin i (X i) (xh ν i)
      (y ν i) (hxK ν i) hxhK hmin
    -- δ bound
    have hdiff : ∀ j, DifferentiableAt ℝ (f j) (X i) := fun j =>
      ((hfi j).1 _ (hKO (hxK ν i))).differentiableAt (hO.mem_nhds (hKO (hxK ν i)))
    have hdel : gradient (Fsum f) (X i) - y ν i =
        (1 / (m : ℝ)) • ∑ j, (gradient (f j) (X i) - gradient (f j) (X j)) +
          -(wperp (φ ν) (y ν) i) := by
      simp only [wperp, gradient_Fsum f (X i) hdiff]
      rw [h74]
      simp only [gradAvg, Finset.sum_sub_distrib, smul_sub]
      abel
    have hA_i := avg_grad_bound hm f (Lmx Li) hL0 X xstar (fun i j =>
      (grad_lip hA h1 j (hxK ν i) (hxK ν j)).trans
        (mul_le_mul_of_nonneg_right (Li_le_Lmx' Li j) (norm_nonneg _))) i
    have hδ : ‖gradient (Fsum f) (X i) - y ν i‖ ≤ Lmx Li * (b i + bb) + ‖wperp (φ ν) (y ν) i‖ := by
      rw [hdel]; refine (norm_add_le _ _).trans ?_; rw [norm_neg]; linarith
    have hDi : SONATA.Undir.Dcoef Dl Du i ≤ Dmx Dl Du := Dcoef_le_Dmx Dl Du i
    have hDi0 : 0 ≤ SONATA.Undir.Dcoef Dl Du i := le_max_of_le_left (abs_nonneg _)
    have hmi : mutmn μt ≤ μt i := mutmn_le μt i
    -- ‖x̂ − x⋆‖ ≤ (Dmx/μ̃mn) bᵢ + ‖δ‖/μ̃mn
    have hv : ‖xh ν i - xstar‖ ≤ Dmx Dl Du / mutmn μt * b i +
        ‖gradient (Fsum f) (X i) - y ν i‖ / mutmn μt := by
      have hn : ‖xstar - X i‖ = b i := by simp only [b]; rw [norm_sub_rev]
      rw [hn] at h48
      have h3 : mutmn μt * ‖xh ν i - xstar‖ ≤ Dmx Dl Du * b i + ‖gradient (Fsum f) (X i) - y ν i‖ := by
        have := mul_le_mul_of_nonneg_right hmi (norm_nonneg (xh ν i - xstar))
        have := mul_le_mul_of_nonneg_right hDi (norm_nonneg (X i - xstar))
        simp only [b] at *
        linarith
      have e : Dmx Dl Du / mutmn μt * b i + ‖gradient (Fsum f) (X i) - y ν i‖ / mutmn μt =
          (Dmx Dl Du * b i + ‖gradient (Fsum f) (X i) - y ν i‖) / mutmn μt := by ring
      rw [e, le_div_iff₀ hμmn]
      linarith
    have hd : ‖dir x xh ν i‖ ≤ ‖xh ν i - xstar‖ + b i := by
      simp only [dir, b]
      have : xh ν i - x ν i = (xh ν i - xstar) + (xstar - x ν i) := by abel
      rw [this, ← norm_neg (X i - xstar)]
      refine (norm_add_le _ _).trans ?_
      simp [X]
    have hQ : ‖gradient (Fsum f) (X i) - y ν i‖ / mutmn μt ≤
        Q * ‖wperp (φ ν) (y ν) i‖ + R * (b i + bb) := by
      simp only [Q, R]
      rw [div_le_iff₀ hμmn]
      have : (1 / mutmn μt * ‖wperp (φ ν) (y ν) i‖ + Lmx Li / mutmn μt * (b i + bb)) * mutmn μt
          = ‖wperp (φ ν) (y ν) i‖ + Lmx Li * (b i + bb) := by field_simp
      rw [this]; linarith
    simp only [P]
    linarith
  have hb0 : ∀ i, 0 ≤ b i := fun i => norm_nonneg _
  have hbb0 : 0 ≤ bb := by
    have : 0 ≤ ∑ k, b k := Finset.sum_nonneg fun k _ => hb0 k
    simp only [bb]; positivity
  have hcs : (∑ k, b k) ^ 2 ≤ m * S := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
    simpa using this
  have hbb2 : bb ^ 2 ≤ (1 / (m : ℝ)) * S := by
    simp only [bb]; rw [mul_pow]
    have : (1 / (m : ℝ)) ^ 2 * (∑ k, b k) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 * (m * S) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have e : (1 / (m : ℝ)) ^ 2 * (m * S) = (1 / (m : ℝ)) * S := by field_simp
    linarith
  have hP0 : 0 ≤ P := by simp only [P]; positivity
  have hQ0 : 0 ≤ Q := by simp only [Q]; positivity
  have hR0 : 0 ≤ R := by simp only [R]; positivity
  have hsq : ∀ i, ‖dir x xh ν i‖ ^ 2 ≤ 3 * P ^ 2 * b i ^ 2 + 3 * Q ^ 2 * ‖wperp (φ ν) (y ν) i‖ ^ 2
      + 6 * R ^ 2 * (b i ^ 2 + (1 / (m : ℝ)) * S) := by
    intro i
    have h := hag i
    have hn := norm_nonneg (dir x xh ν i)
    have hw0 := norm_nonneg (wperp (φ ν) (y ν) i)
    have h2 : ‖dir x xh ν i‖ ^ 2 ≤ (P * b i + Q * ‖wperp (φ ν) (y ν) i‖ + R * (b i + bb)) ^ 2 :=
      pow_le_pow_left₀ hn h 2
    have h3 : (P * b i + Q * ‖wperp (φ ν) (y ν) i‖ + R * (b i + bb)) ^ 2 ≤
        3 * (P * b i) ^ 2 + 3 * (Q * ‖wperp (φ ν) (y ν) i‖) ^ 2 + 3 * (R * (b i + bb)) ^ 2 := by
      nlinarith [sq_nonneg (P * b i - Q * ‖wperp (φ ν) (y ν) i‖),
        sq_nonneg (P * b i - R * (b i + bb)), sq_nonneg (Q * ‖wperp (φ ν) (y ν) i‖ - R * (b i + bb))]
    have h4 : (b i + bb) ^ 2 ≤ 2 * (b i ^ 2 + (1 / (m : ℝ)) * S) := by
      nlinarith [sq_nonneg (b i - bb)]
    have h5 : 3 * (R * (b i + bb)) ^ 2 ≤ 6 * R ^ 2 * (b i ^ 2 + (1 / (m : ℝ)) * S) := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_left h4 (sq_nonneg R)
      nlinarith
    rw [mul_pow, mul_pow] at h3
    linarith
  have hsum : sqn (dir x xh ν) ≤ (3 * P ^ 2 + 12 * R ^ 2) * S + 3 * Q ^ 2 * sqn (wperp (φ ν) (y ν)) := by
    unfold sqn
    refine (Finset.sum_le_sum fun i _ => hsq i).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← hS]
    field_simp
    ring
  -- S ≤ 2 p / (μ φ_lb)
  have hS : S ≤ 2 / (μ * phiLb m B cl) * pphi f G xstar (φ ν) (x ν) := by
    have hg : ∀ k, μ / 2 * b k ^ 2 ≤ U f G (X k) - U f G xstar := fun k =>
      U_growth hA hxs (hxK ν k) hxsmin
    have hgap0 : ∀ k, 0 ≤ U f G (X k) - U f G xstar := fun k =>
      sub_nonneg.mpr (isMinOn_iff.mp hxsmin _ (hxK ν k))
    have hp : phiLb m B cl * ∑ k, (U f G (X k) - U f G xstar) ≤ pphi f G xstar (φ ν) (x ν) := by
      unfold pphi; rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hlb ν k) (hgap0 k)
    have hsS : μ / 2 * S ≤ ∑ k, (U f G (X k) - U f G xstar) := by
      rw [hS, Finset.mul_sum]; exact Finset.sum_le_sum fun k _ => hg k
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hRe : 12 * R ^ 2 = 12 * (Lmx Li ^ 2 / mutmn μt ^ 2) := by simp only [R]; rw [div_pow]
  have hQe : 3 * Q ^ 2 = 3 / mutmn μt ^ 2 := by simp only [Q]; rw [div_pow]; ring
  have hcoef : 0 ≤ 3 * P ^ 2 + 12 * R ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hS hcoef
  have e : (3 * P ^ 2 + 12 * R ^ 2) * (2 / (μ * phiLb m B cl) * pphi f G xstar (φ ν) (x ν)) =
      6 / (μ * phiLb m B cl) * (P ^ 2 + 4 * Lmx Li ^ 2 / mutmn μt ^ 2) *
        pphi f G xstar (φ ν) (x ν) := by
    simp only [R]; field_simp; ring
  rw [hQe] at hsum
  linarith

end SPushAux


open scoped RealInnerProductSpace

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ,
      sqn (dir x xh ν) ≤
        6 / (μ * phiLb m B cl) *
            ((SONATA.Undir.Dmx Dl Du / SONATA.Undir.mutmn μt + 1) ^ 2 + 4 * SONATA.Undir.Lmx Li ^ 2 / SONATA.Undir.mutmn μt ^ 2) *
            pphi f G xstar (φ ν) (x ν)
          + 3 / SONATA.Undir.mutmn μt ^ 2 * sqn (wperp (φ ν) (y ν)) :=
  fun ν => SPushAux.P43_run K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN μi Li h1 α hα0 hα1
    x y xh φ hrun ν
