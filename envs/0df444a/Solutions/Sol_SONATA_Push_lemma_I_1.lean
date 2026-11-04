-- Prove2me | solution 1 for SONATA.Push.lemma_I_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:48:27.987547+00:00
-- url     : https://prove2.me/submissions/bcc6ba26-719a-428f-986b-ff7978157bda

import Mathlib
import Definitions.Def_SONATA_Push_Network

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

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ, ∀ i : Fin m,
      U f G (xhalf α x xh ν i) ≤ U f G (x ν i)
        - α * ((1 - α / 2) * μt i + α / 2 * Dl i) * ‖dir x xh ν i‖ ^ 2
        + α * ‖dir x xh ν i‖ * ‖delta f (x ν) (y ν) i‖ := by
  intro ν i
  obtain ⟨_, hA, hC, hgap, _⟩ := hP
  have hxK := SPushAux.x_mem hA hN hα0 hα1 hrun
  obtain ⟨hxhK, hmin⟩ := hrun.2.2.2.1 ν i
  exact SPushAux.I1_core K O f G μ L ft μt Lt Dl Du hA hC hgap i (x ν i) (xh ν i) (y ν i)
    (hxK ν i) hxhK hmin α hα0 hα1
