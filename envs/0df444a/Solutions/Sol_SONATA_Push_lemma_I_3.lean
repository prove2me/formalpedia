-- Prove2me | solution 1 for SONATA.Push.lemma_I_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:43:33.530508+00:00
-- url     : https://prove2.me/submissions/570362ef-58f9-4369-b22d-3526f4787691

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

theorem Li_le_Lmx {m : ℕ} (Li : Fin m → ℝ) (j : Fin m) : Li j ≤ Lmx Li :=
  le_ciSup (Set.finite_range Li).bddAbove j

theorem sq_add_le {d : ℕ} (a b : E d) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]

theorem I3_core {m d : ℕ} (hm : 0 < m) (f : Fin m → E d → ℝ) (Lmax : ℝ) (hL : 0 ≤ Lmax)
    (X Y : Fin m → E d) (Φ : Fin m → ℝ)
    (hlip : ∀ i j, ‖gradient (f j) (X i) - gradient (f j) (X j)‖ ≤ Lmax * ‖X i - X j‖)
    (hdiff : ∀ i j, DifferentiableAt ℝ (f j) (X i))
    (hy : wavg Φ Y = gradAvg f X) :
    sqn (delta f X Y) ≤ 8 * Lmax ^ 2 * sqn (wperp Φ X) + 2 * sqn (wperp Φ Y) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set xb := wavg Φ X
  set a : Fin m → ℝ := fun k => ‖X k - xb‖ with ha
  set S := ∑ k, a k ^ 2 with hS
  have hSx : sqn (wperp Φ X) = S := rfl
  -- decomposition of delta
  set A : Fin m → E d := fun i => (1 / (m : ℝ)) • ∑ j, (gradient (f j) (X i) - gradient (f j) (X j))
  have hdel : ∀ i, delta f X Y i = A i + (-(wperp Φ Y i)) := by
    intro i
    simp only [delta, A, wperp, gradient_Fsum f (X i) (hdiff i)]
    rw [hy]
    simp only [gradAvg, Finset.sum_sub_distrib, smul_sub]
    abel
  have hA : ∀ i, ‖A i‖ ≤ Lmax * (a i + (1 / (m : ℝ)) * ∑ k, a k) := by
    intro i
    simp only [A]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖∑ j, (gradient (f j) (X i) - gradient (f j) (X j))‖ ≤
        ∑ j, Lmax * (a i + a j) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (hlip i j).trans ?_
      apply mul_le_mul_of_nonneg_left _ hL
      have : X i - X j = (X i - xb) - (X j - xb) := by abel
      rw [this]; exact norm_sub_le _ _
    have h2 : ∑ j, Lmax * (a i + a j) = Lmax * (m * a i + ∑ k, a k) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
    rw [h2] at h1
    calc 1 / (m : ℝ) * ‖∑ j, (gradient (f j) (X i) - gradient (f j) (X j))‖
        ≤ 1 / (m : ℝ) * (Lmax * (m * a i + ∑ k, a k)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Lmax * (a i + (1 / (m : ℝ)) * ∑ k, a k) := by field_simp
  have hcs : (∑ k, a k) ^ 2 ≤ m * S := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    simpa using this
  have hA2 : ∀ i, ‖A i‖ ^ 2 ≤ 2 * Lmax ^ 2 * (a i ^ 2 + (1 / (m : ℝ)) * S) := by
    intro i
    have h1 : ‖A i‖ ^ 2 ≤ Lmax ^ 2 * (a i + (1 / (m : ℝ)) * ∑ k, a k) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA i) 2
    have h2 : ((1 / (m : ℝ)) * ∑ k, a k) ^ 2 ≤ (1 / (m : ℝ)) * S := by
      rw [mul_pow]
      have : (1 / (m : ℝ)) ^ 2 * (∑ k, a k) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 * (m * S) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
      have e : (1 / (m : ℝ)) ^ 2 * (m * S) = (1 / (m : ℝ)) * S := by field_simp
      linarith
    have h3 : (a i + (1 / (m : ℝ)) * ∑ k, a k) ^ 2 ≤ 2 * (a i ^ 2 + (1 / (m : ℝ)) * S) := by
      nlinarith [sq_nonneg (a i - (1 / (m : ℝ)) * ∑ k, a k)]
    calc ‖A i‖ ^ 2 ≤ Lmax ^ 2 * (a i + (1 / (m : ℝ)) * ∑ k, a k) ^ 2 := h1
      _ ≤ Lmax ^ 2 * (2 * (a i ^ 2 + (1 / (m : ℝ)) * S)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * Lmax ^ 2 * (a i ^ 2 + (1 / (m : ℝ)) * S) := by ring
  have hsum : sqn (delta f X Y) ≤ ∑ i, (4 * Lmax ^ 2 * (a i ^ 2 + (1 / (m : ℝ)) * S)
      + 2 * ‖wperp Φ Y i‖ ^ 2) := by
    unfold sqn
    apply Finset.sum_le_sum
    intro i _
    rw [hdel i]
    refine (sq_add_le _ _).trans ?_
    rw [norm_neg]
    nlinarith [hA2 i]
  have hfin : ∑ i, (4 * Lmax ^ 2 * (a i ^ 2 + (1 / (m : ℝ)) * S) + 2 * ‖wperp Φ Y i‖ ^ 2)
      = 8 * Lmax ^ 2 * S + 2 * sqn (wperp Φ Y) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold sqn
    rw [← Finset.mul_sum, ← hS]
    field_simp
    ring
  rw [hSx]; linarith

end SPushAux

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
      sqn (delta f (x ν) (y ν)) ≤
        8 * SONATA.Undir.Lmx Li ^ 2 * sqn (wperp (φ ν) (x ν)) + 2 * sqn (wperp (φ ν) (y ν)) := by
  intro ν
  have hm : 0 < m := hP.1
  have hA := hP.2.1
  have hxK := SPushAux.x_mem hA hN hα0 hα1 hrun
  have h74 := (SONATA.Push.eq_74 K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN α hα0 hα1
    x y xh φ hrun).2 ν
  have hL0 : 0 ≤ SONATA.Undir.Lmx Li :=
    (h1 ⟨0, hm⟩).2.1.le.trans (SPushAux.Li_le_Lmx Li ⟨0, hm⟩)
  apply SPushAux.I3_core hm f _ hL0 (x ν) (y ν) (φ ν) _ _ h74
  · intro i j
    refine (SPushAux.grad_lip hA h1 j (hxK ν i) (hxK ν j)).trans ?_
    exact mul_le_mul_of_nonneg_right (SPushAux.Li_le_Lmx Li j) (norm_nonneg _)
  · intro i j
    obtain ⟨_, _, _, hO, hKO, hfi, _⟩ := hA
    exact ((hfi j).1 _ (hKO (hxK ν i))).differentiableAt (hO.mem_nhds (hKO (hxK ν i)))
