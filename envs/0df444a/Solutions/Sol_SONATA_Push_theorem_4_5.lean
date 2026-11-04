-- Prove2me | solution 1 for SONATA.Push.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:22:14.016116+00:00
-- url     : https://prove2.me/submissions/2ef3d4bc-2196-4787-b5b2-541dfef635f3

import Mathlib
import Definitions.Def_SONATA_Push_Network
import Theorems.Thm_SONATA_Push_prop_4_1
import Theorems.Thm_SONATA_Push_prop_4_3
import Theorems.Thm_SONATA_Push_phi_bounds
import Theorems.Thm_SONATA_Push_lemma_4_2

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


namespace SPushChain

theorem conv_geom (ρ z : ℝ) (hρ0 : 0 ≤ ρ) (hρz : ρ < z) (ν : ℕ) :
    ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * z ^ t ≤ z ^ ν / (z - ρ) := by
  have hz : 0 < z := lt_of_le_of_lt hρ0 hρz
  have hne : z - ρ ≠ 0 := by linarith
  induction ν with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
    have : 0 < z - ρ := by linarith
    positivity
  | succ n ih =>
    have e : ∑ t ∈ Finset.range (n + 1), ρ ^ (n + 1 - 1 - t) * z ^ t =
        ρ * ∑ t ∈ Finset.range n, ρ ^ (n - 1 - t) * z ^ t + z ^ n := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        have ht' : t < n := Finset.mem_range.mp ht
        have : n + 1 - 1 - t = (n - 1 - t) + 1 := by omega
        rw [this, pow_succ]; ring
      · simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left ih hρ0
    have h2 : ρ * (z ^ n / (z - ρ)) + z ^ n = z ^ (n + 1) / (z - ρ) := by
      field_simp; ring
    linarith

/-- Small-gain chaining of (80), (81a), (81b), (84) via the transformation (49). -/
theorem chain (p X Y D : ℕ → ℝ) (hp0 : ∀ ν, 0 ≤ p ν) (hX0 : ∀ ν, 0 ≤ X ν) (hY0 : ∀ ν, 0 ≤ Y ν)
    (hD0 : ∀ ν, 0 ≤ D ν)
    (σ η a1 a2 A0 A1 A2 C1 C2 ρ z α gP gR : ℝ)
    (hσ0 : 0 ≤ σ) (hσz : σ < z) (hρ0 : 0 ≤ ρ) (hρz : ρ < z) (hρ1 : ρ ≤ 1)
    (hη : 0 ≤ η) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hgP0 : 0 ≤ gP) (hgR0 : 0 ≤ gR)
    (h80 : ∀ ν, p (ν + 1) ≤ σ * p ν + η * (a1 * X ν + a2 * Y ν))
    (h81a : ∀ ν, X ν ≤ A0 * ρ ^ (2 * ν) * X 0 +
      A1 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * (α ^ 2 * D t))
    (h81b : ∀ ν, Y ν ≤ A0 * ρ ^ (2 * ν) * Y 0 +
      A2 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * (8 * X t + 2 * α ^ 2 * D t))
    (h84 : ∀ ν, D ν ≤ C1 * p ν + C2 * Y ν)
    (hgP : η ≤ gP * (z - σ)) (hgR : 1 ≤ gR * (z - ρ))
    (hgain : (C1 * gP * a1 * (A1 * gR) + (C1 * gP * a2 + C2) * (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR))
      * α ^ 2 ≤ 1 / 2) :
    ∃ R, ∀ ν, p ν ≤ R * z ^ ν := by
  have hz : 0 < z := lt_of_le_of_lt hρ0 hρz
  have hzρ : 0 < z - ρ := by linarith
  have hzσ : 0 < z - σ := by linarith
  have hinv : 1 / (z - ρ) ≤ gR := by rw [div_le_iff₀ hzρ]; linarith
  have hρ2 : ∀ t : ℕ, ρ ^ (2 * t) ≤ z ^ t := by
    intro t
    rw [pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg ρ)
    nlinarith
  set X0' := A0 * X 0
  set Y0' := A0 * Y 0
  set c := C1 * p 0 + C1 * gP * a1 * X0' + (C1 * gP * a2 + C2) * (Y0' + 8 * A2 * gR * X0')
  set Γ := C1 * gP * a1 * (A1 * gR) + (C1 * gP * a2 + C2) * (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR)
  have hX0' : 0 ≤ X0' := mul_nonneg hA0 (hX0 0)
  have hY0' : 0 ≤ Y0' := mul_nonneg hA0 (hY0 0)
  have hc0 : 0 ≤ c := by
    have := hp0 0
    simp only [c]; positivity
  set R := p 0 + gP * a1 * (X0' + A1 * gR * (α ^ 2 * (2 * c))) +
    gP * a2 * (Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * (α ^ 2 * (2 * c)))
  refine ⟨R, fun ν => ?_⟩
  -- the transformation (49) up to K = ν
  set K := ν
  have hne : (Finset.range (K + 1)).Nonempty := Finset.nonempty_range_add_one
  let M : (ℕ → ℝ) → ℝ := fun s => (Finset.range (K + 1)).sup' hne (fun t => s t / z ^ t)
  have hM_le : ∀ s : ℕ → ℝ, ∀ t ≤ K, s t ≤ M s * z ^ t := by
    intro s t ht
    have h := Finset.le_sup' (fun t => s t / z ^ t) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    have hzt : 0 < z ^ t := pow_pos hz t
    calc s t = s t / z ^ t * z ^ t := by field_simp
      _ ≤ M s * z ^ t := mul_le_mul_of_nonneg_right h hzt.le
  have hM_bound : ∀ s : ℕ → ℝ, ∀ Bd : ℝ, (∀ t ≤ K, s t ≤ Bd * z ^ t) → M s ≤ Bd := by
    intro s Bd h
    apply Finset.sup'_le
    intro t ht
    have hzt : 0 < z ^ t := pow_pos hz t
    rw [div_le_iff₀ hzt]
    exact h t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have hM0 : ∀ s : ℕ → ℝ, (∀ t, 0 ≤ s t) → 0 ≤ M s := by
    intro s hs
    have := hM_le s 0 (Nat.zero_le _)
    have h0 := hs 0
    simp at this
    linarith
  set MX := M X
  set MY := M Y
  set MD := M D
  set MP := M p
  have hMX0 := hM0 X hX0
  have hMY0 := hM0 Y hY0
  have hMD0 := hM0 D hD0
  have hMP0 := hM0 p hp0
  set u := α ^ 2 * MD
  have hu0 : 0 ≤ u := mul_nonneg (sq_nonneg α) hMD0
  -- convolution bound
  have hconv : ∀ (s : ℕ → ℝ) (Ms : ℝ), 0 ≤ Ms → (∀ t ≤ K, 0 ≤ s t ∧ s t ≤ Ms * z ^ t) →
      ∀ t ≤ K, ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * s j ≤ Ms * gR * z ^ t := by
    intro s Ms hMs hs t ht
    calc ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * s j
        ≤ ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * (Ms * z ^ j) := by
          apply Finset.sum_le_sum; intro j hj
          have hj' : j ≤ K := by have := Finset.mem_range.mp hj; omega
          exact mul_le_mul_of_nonneg_left (hs j hj').2 (pow_nonneg hρ0 _)
      _ = Ms * ∑ j ∈ Finset.range t, ρ ^ (t - 1 - j) * z ^ j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ Ms * (z ^ t / (z - ρ)) := mul_le_mul_of_nonneg_left (conv_geom ρ z hρ0 hρz t) hMs
      _ ≤ Ms * gR * z ^ t := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hMs
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right hinv (pow_nonneg hz.le t)
  -- (86)
  have hMX : MX ≤ X0' + A1 * gR * u := by
    apply hM_bound
    intro t ht
    have h1 := h81a t
    have h2 := hconv (fun j => α ^ 2 * D j) u hu0
      (fun j hj => ⟨mul_nonneg (sq_nonneg α) (hD0 j), by
        have := hM_le D j hj
        simp only [u, MD]; rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this (sq_nonneg α)⟩) t ht
    have h3 : A0 * ρ ^ (2 * t) * X 0 ≤ X0' * z ^ t := by
      simp only [X0']
      have := mul_le_mul_of_nonneg_left (hρ2 t) (mul_nonneg hA0 (hX0 0))
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h2 hA1
    beta_reduce at h4
    linarith
  -- (87)
  have hMY : MY ≤ Y0' + A2 * gR * (8 * MX + 2 * u) := by
    apply hM_bound
    intro t ht
    have h1 := h81b t
    have hW : 0 ≤ 8 * MX + 2 * u := by positivity
    have h2 := hconv (fun j => 8 * X j + 2 * α ^ 2 * D j) (8 * MX + 2 * u) hW
      (fun j hj => ⟨by have := hX0 j; have := hD0 j; positivity, by
        have hx := hM_le X j hj
        have hd := hM_le D j hj
        have hd' := mul_le_mul_of_nonneg_left hd (sq_nonneg α)
        simp only [u, MD, MX]
        nlinarith⟩) t ht
    have h3 : A0 * ρ ^ (2 * t) * Y 0 ≤ Y0' * z ^ t := by
      simp only [Y0']
      have := mul_le_mul_of_nonneg_left (hρ2 t) (mul_nonneg hA0 (hY0 0))
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h2 hA2
    beta_reduce at h4
    linarith
  -- (85)
  have hMP : MP ≤ p 0 + gP * (a1 * MX + a2 * MY) := by
    apply hM_bound
    have hQ : 0 ≤ a1 * MX + a2 * MY := by positivity
    have hW : 0 ≤ p 0 + gP * (a1 * MX + a2 * MY) := by have := hp0 0; positivity
    intro t ht
    induction t with
    | zero =>
      simp only [pow_zero, mul_one]
      have : 0 ≤ gP * (a1 * MX + a2 * MY) := by positivity
      linarith
    | succ n ih =>
      have ihn := ih (by omega)
      have hx := hM_le X n (by omega)
      have hy := hM_le Y n (by omega)
      have h1 := h80 n
      have hzn : 0 < z ^ n := pow_pos hz n
      have h2 : η * (a1 * X n + a2 * Y n) ≤ η * ((a1 * MX + a2 * MY) * z ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hη
        have := mul_le_mul_of_nonneg_left hx ha1
        have := mul_le_mul_of_nonneg_left hy ha2
        linarith
      have h3 : σ * p n ≤ σ * ((p 0 + gP * (a1 * MX + a2 * MY)) * z ^ n) :=
        mul_le_mul_of_nonneg_left ihn hσ0
      have h4 : η * (a1 * MX + a2 * MY) ≤ (z - σ) * (p 0 + gP * (a1 * MX + a2 * MY)) := by
        have := mul_le_mul_of_nonneg_right hgP hQ
        have := mul_nonneg hzσ.le (hp0 0)
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 hzn.le
      rw [pow_succ]
      linarith
  -- (88)
  have hMD : MD ≤ C1 * MP + C2 * MY := by
    apply hM_bound
    intro t ht
    have h1 := h84 t
    have := mul_le_mul_of_nonneg_left (hM_le p t ht) hC1
    have := mul_le_mul_of_nonneg_left (hM_le Y t ht) hC2
    linarith
  -- closing the loop
  have hY' : MY ≤ Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * u := by
    have := mul_le_mul_of_nonneg_left hMX (by positivity : (0:ℝ) ≤ 8 * A2 * gR)
    linarith
  have hloop : MD ≤ c + Γ * u := by
    have e1 := mul_le_mul_of_nonneg_left hMP hC1
    have e2 := mul_le_mul_of_nonneg_left hMX (by positivity : (0:ℝ) ≤ C1 * gP * a1)
    have e3 := mul_le_mul_of_nonneg_left hY' (by positivity : (0:ℝ) ≤ C1 * gP * a2 + C2)
    simp only [c, Γ]
    linarith
  have hΓu : Γ * u ≤ MD / 2 := by
    have : Γ * u = (Γ * α ^ 2) * MD := by simp only [u]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hgain hMD0
    linarith
  have hMDc : MD ≤ 2 * c := by linarith
  have hu2 : u ≤ α ^ 2 * (2 * c) := mul_le_mul_of_nonneg_left hMDc (sq_nonneg α)
  have hMX' : MX ≤ X0' + A1 * gR * (α ^ 2 * (2 * c)) := by
    have := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ A1 * gR)
    linarith
  have hY'' : MY ≤ Y0' + 8 * A2 * gR * X0' + (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) * (α ^ 2 * (2 * c)) := by
    have := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ 8 * A2 * gR * (A1 * gR) + 2 * A2 * gR)
    linarith
  have hMPR : MP ≤ R := by
    have e1 := mul_le_mul_of_nonneg_left hMX' (by positivity : (0:ℝ) ≤ gP * a1)
    have e2 := mul_le_mul_of_nonneg_left hY'' (by positivity : (0:ℝ) ≤ gP * a2)
    simp only [R]
    linarith
  have := hM_le p ν le_rfl
  have hzν : 0 < z ^ ν := pow_pos hz ν
  linarith [mul_le_mul_of_nonneg_right hMPR hzν.le]

end SPushChain


open scoped RealInnerProductSpace

namespace SPushAux
open SONATA.Push
open SONATA.Undir (E hess pgrad phess Lmx Dmx mutmn Dlmn)

/-- `∇²F = (1/m) Σ ∇²fⱼ` on `O`. -/
theorem hess_Fsum {m d : ℕ} {O : Set (E d)} (hO : IsOpen O) (f : Fin m → E d → ℝ)
    (hf : ∀ j, DifferentiableOn ℝ (f j) O) (hg : ∀ j, DifferentiableOn ℝ (gradient (f j)) O)
    (z : E d) (hz : z ∈ O) :
    hess (Fsum f) z = (1 / (m : ℝ)) • ∑ j, hess (f j) z := by
  have hfa : ∀ w ∈ O, ∀ j, DifferentiableAt ℝ (f j) w :=
    fun w hw j => (hf j w hw).differentiableAt (hO.mem_nhds hw)
  have heq : gradient (Fsum f) =ᶠ[nhds z] fun w => (1 / (m : ℝ)) • ∑ j, gradient (f j) w :=
    Filter.mem_of_superset (hO.mem_nhds hz) fun w hw => gradient_Fsum f w (hfa w hw)
  have hd : HasFDerivAt (fun w => (1 / (m : ℝ)) • ∑ j, gradient (f j) w)
      ((1 / (m : ℝ)) • ∑ j, hess (f j) z) z := by
    exact (HasFDerivAt.fun_sum fun j _ =>
      ((hg j z hz).differentiableAt (hO.mem_nhds hz)).hasFDerivAt).const_smul (1 / (m : ℝ))
  exact (hd.congr_of_eventuallyEq heq).fderiv

theorem hessBounds_exist {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ}
    {μ L : ℝ} (hm : 0 < m) (hA : AssumptionA K O f G μ L) :
    HessBounds K f (fun _ => 0) (fun _ => (m : ℝ) * L) := by
  obtain ⟨_, _, _, hO, hKO, hfi, _, hL, hH, _⟩ := hA
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  intro i
  refine ⟨le_rfl, by positivity, ?_⟩
  intro x hx u
  have hxO := hKO hx
  have hpsd : ∀ j, 0 ≤ ⟪hess (f j) x u, u⟫ := fun j => (hfi j).2.2.2 x hxO u
  refine ⟨by simpa using hpsd i, ?_⟩
  have hF := (hH x hx u).2
  rw [hess_Fsum hO f (fun j => (hfi j).1) (fun j => (hfi j).2.1) x hxO] at hF
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, inner_smul_left,
    sum_inner] at hF
  have h1 : ⟪hess (f i) x u, u⟫ ≤ ∑ j, ⟪hess (f j) x u, u⟫ :=
    Finset.single_le_sum (f := fun j => ⟪hess (f j) x u, u⟫) (fun j _ => hpsd j) (Finset.mem_univ i)
  have h2 : (starRingEnd ℝ) (1 / (m : ℝ)) = 1 / (m : ℝ) := by simp
  rw [h2] at hF
  have h3 : ∑ j, ⟪hess (f j) x u, u⟫ ≤ m * (L * ‖u‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hF hmR.le
    rw [← mul_assoc, mul_one_div_cancel hmR.ne', one_mul] at this
    exact this
  nlinarith

theorem cl_le_one {m : ℕ} (hm : 0 < m) {Edges : ℕ → Fin m → Fin m → Prop} {B : ℕ}
    {C : ℕ → Matrix (Fin m) (Fin m) ℝ} {cl : ℝ} (hN : NetworkHyp Edges B C cl) : cl ≤ 1 := by
  have hC := C_nonneg hN
  have i0 : Fin m := ⟨0, hm⟩
  have h1 : C 0 i0 i0 ≤ ∑ l, C 0 l i0 :=
    Finset.single_le_sum (f := fun l => C 0 l i0) (fun l _ => hC 0 l i0) (Finset.mem_univ i0)
  rw [hN.2.2.2.2 0 i0] at h1
  linarith [hN.2.2.1 0 i0]

end SPushAux

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (hcond : SONATA.Undir.Dlmn Dl ≤ SONATA.Undir.mutmn μt) :
    ∃ αbar : ℝ, 0 < αbar ∧ αbar ≤ 1 ∧ ∀ α : ℝ, 0 < α → α < αbar →
      ∀ x y xh : ℕ → Fin m → SONATA.Undir.E d, ∀ φ : ℕ → Fin m → ℝ, IsRun K f G ft C α x y xh φ →
        ∀ i : Fin m, ∃ Cc z : ℝ, 0 ≤ z ∧ z < 1 ∧
          ∀ ν : ℕ, |U f G (x ν i) - U f G xstar| ≤ Cc * z ^ ν := by
  have hm : 0 < m := hP.1
  have hA := hP.2.1
  have hxsmin := hP.2.2.2.2.2
  have hμ : 0 < μ := hA.2.2.2.2.2.2.1
  -- the bounds (1) with Lᵢ = m L
  have h1 : HessBounds K f (fun _ => (0:ℝ)) (fun _ => (m : ℝ) * L) := SPushAux.hessBounds_exist hm hA
  -- network constants of Lemma 4.2
  obtain ⟨c0, ρ, hc0, hρ0, hρ1, h42⟩ :=
    lemma_4_2 K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN _ _ h1
  -- problem constants
  obtain ⟨mn, hmn_def⟩ : ∃ v, v = SONATA.Undir.mutmn μt := ⟨_, rfl⟩
  obtain ⟨Dln, hDln_def⟩ : ∃ v, v = SONATA.Undir.Dlmn Dl := ⟨_, rfl⟩
  obtain ⟨Dm, hDm_def⟩ : ∃ v, v = SONATA.Undir.Dmx Dl Du := ⟨_, rfl⟩
  obtain ⟨Lm, hLm_def⟩ : ∃ v, v = SONATA.Undir.Lmx (fun _ : Fin m => (m : ℝ) * L) := ⟨_, rfl⟩
  obtain ⟨lb, hlb_def⟩ : ∃ v, v = phiLb m B cl := ⟨_, rfl⟩
  obtain ⟨ub, hub_def⟩ : ∃ v, v = phiUb m B cl := ⟨_, rfl⟩
  rw [← hmn_def, ← hDln_def] at hcond
  have hmn : 0 < mn := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := μt)
    rw [hmn_def, SONATA.Undir.mutmn, ← hi]; exact (hP.2.2.1 i).2.2.2.1
  have hcl := hN.2.1
  have hcl1 := SPushAux.cl_le_one hm hN
  have hlb : 0 < lb := by rw [hlb_def, phiLb]; exact pow_pos hcl _
  have hub : 0 ≤ ub := by
    rw [hub_def, phiUb]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : cl ^ (2 * (m - 1) * B) ≤ 1 := pow_le_one₀ hcl.le hcl1
    linarith
  have hLm : 0 ≤ Lm := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hL : 0 < L := hA.2.2.2.2.2.2.2.1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [hLm_def, SONATA.Undir.Lmx, ciSup_const]; positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  obtain ⟨b, hb_def⟩ : ∃ v, v = Dm ^ 2 / μ := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb_def]; positivity
  -- uniform constants
  obtain ⟨gP, hgP_def⟩ : ∃ v, v = mn⁻¹ * b * (4 / mn) + 2 / μ := ⟨_, rfl⟩
  obtain ⟨gR, hgR_def⟩ : ∃ v, v = 2 / (1 - ρ) := ⟨_, rfl⟩
  obtain ⟨a1, ha1_def⟩ : ∃ v, v = 8 * Lm ^ 2 := ⟨_, rfl⟩
  obtain ⟨A0, hA0_def⟩ : ∃ v, v = 2 * c0 ^ 2 := ⟨_, rfl⟩
  obtain ⟨A1, hA1_def⟩ : ∃ v, v = 2 * c0 ^ 2 * ρ ^ 2 / (1 - ρ) := ⟨_, rfl⟩
  obtain ⟨A2, hA2_def⟩ : ∃ v, v = 2 * c0 ^ 2 * ρ ^ 2 * m * Lm ^ 2 / (lb ^ 2 * (1 - ρ)) := ⟨_, rfl⟩
  obtain ⟨C1, hC1_def⟩ : ∃ v, v = 6 / (μ * lb) * ((Dm / mn + 1) ^ 2 + 4 * Lm ^ 2 / mn ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨C2, hC2_def⟩ : ∃ v, v = 3 / mn ^ 2 := ⟨_, rfl⟩
  have hgP0 : 0 ≤ gP := by rw [hgP_def]; positivity
  have hgR0 : 0 ≤ gR := by rw [hgR_def]; positivity
  have ha10 : 0 ≤ a1 := by rw [ha1_def]; positivity
  have hA00 : 0 ≤ A0 := by rw [hA0_def]; positivity
  have hA10 : 0 ≤ A1 := by rw [hA1_def]; positivity
  have hA20 : 0 ≤ A2 := by rw [hA2_def]; positivity
  have hC10 : 0 ≤ C1 := by rw [hC1_def]; positivity
  have hC20 : 0 ≤ C2 := by rw [hC2_def]; positivity
  obtain ⟨Γ, hΓ_def⟩ : ∃ v, v = C1 * (gP * ub) * a1 * (A1 * gR) +
      (C1 * (gP * ub) * 2 + C2) * (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR) := ⟨_, rfl⟩
  have hΓ0 : 0 ≤ Γ := by rw [hΓ_def]; positivity
  obtain ⟨α2, hα2_def⟩ : ∃ v, v = mn / (2 * (mn - Dln) + mn) := ⟨_, rfl⟩
  have hden : 0 < 2 * (mn - Dln) + mn := by linarith
  have hα2 : 0 < α2 := by rw [hα2_def]; exact div_pos hmn hden
  refine ⟨min (min 1 (1 - ρ)) (min α2 (1 / (2 * Γ + 1))),
    lt_min (lt_min one_pos h1ρ) (lt_min hα2 (by positivity)),
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro α hα0 hαb x y xh φ hrun i
  have hα1 : α < 1 := lt_of_lt_of_le hαb ((min_le_left _ _).trans (min_le_left _ _))
  have hαρ : α ≤ 1 - ρ := hαb.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hαα2 : α ≤ α2 := hαb.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hαΓ : α ≤ 1 / (2 * Γ + 1) := hαb.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the bracket a = aCoef
  obtain ⟨a, ha_def⟩ : ∃ v, v = aCoef mn Dln α mn := ⟨_, rfl⟩
  have ha_eq : a = mn / 2 - α / 2 * (mn - Dln) := by rw [ha_def, aCoef]; ring
  have hαmD : α * (mn - Dln) ≤ mn / 2 := by
    have h := mul_le_mul_of_nonneg_right hαα2 (by linarith : (0:ℝ) ≤ mn - Dln)
    have e : α2 * (mn - Dln) ≤ mn / 2 := by
      rw [hα2_def, div_mul_eq_mul_div, div_le_iff₀ hden]
      have e2 : mn / 2 * (2 * (mn - Dln) + mn) = mn * (mn - Dln) + mn ^ 2 / 2 := by ring
      rw [e2]; have := sq_nonneg mn; linarith
    linarith
  have ha_lo : mn / 4 ≤ a := by rw [ha_eq]; linarith
  have ha_pos : 0 < a := by linarith
  have hab : 0 < b + a := by linarith
  -- σ, η and z
  obtain ⟨σ, hσ_def⟩ : ∃ v, v = sigma μ mn Dln Dm α mn := ⟨_, rfl⟩
  obtain ⟨η, hη_def⟩ : ∃ v, v = eta μ mn Dln Dm α mn := ⟨_, rfl⟩
  have hσ : σ = (b + a * (1 - α)) / (b + a) := by
    rw [hσ_def, sigma, ← ha_def, ← hb_def]; field_simp; ring
  have hη : η = ((1 / 2) * mn⁻¹ * α * b + α / μ * a) / (b + a) := by
    rw [hη_def, eta, ← ha_def, ← hb_def]
  have hηpos : 0 ≤ η := by rw [hη]; positivity
  obtain ⟨z, hz_def⟩ : ∃ v, v = 1 - α * a / (2 * (b + a)) := ⟨_, rfl⟩
  have hq : α * a / (2 * (b + a)) ≤ α / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h' : a ≤ b + a := by linarith
    have := mul_le_mul_of_nonneg_left h' hα0.le
    have e : α / 2 * (2 * (b + a)) = α * (b + a) := by ring
    rw [e]; linarith
  have hqpos : 0 < α * a / (2 * (b + a)) := by positivity
  have hzσ : z - σ = α * a / (2 * (b + a)) := by
    rw [hσ, hz_def]; field_simp; ring
  have hσ0 : 0 ≤ σ := by
    have h' : 0 ≤ b + a * (1 - α) := by
      have := mul_nonneg ha_pos.le (by linarith : (0:ℝ) ≤ 1 - α); linarith
    rw [hσ]; exact div_nonneg h' hab.le
  have hσz : σ < z := by linarith
  have hz1 : z < 1 := by rw [hz_def]; linarith
  have hz0 : 0 ≤ z := by rw [hz_def]; linarith
  have hρz : ρ < z := by rw [hz_def]; linarith
  have hgR : 1 ≤ gR * (z - ρ) := by
    rw [hgR_def, div_mul_eq_mul_div, le_div_iff₀ h1ρ, hz_def]; linarith
  have hgP : η * ub ≤ gP * ub * (z - σ) := by
    have hη' : η ≤ gP * (z - σ) := by
      rw [hη, hzσ, div_le_iff₀ hab]
      have e : gP * (α * a / (2 * (b + a))) * (b + a) = gP * α * a / 2 := by field_simp
      rw [e, hgP_def]
      have hb' : (1 / 2) * mn⁻¹ * α * b ≤ mn⁻¹ * b * (4 / mn) * α * a / 2 := by
        have e3 : mn⁻¹ * b * (4 / mn) * α * a / 2 = (1 / 2) * mn⁻¹ * α * b * (4 * a / mn) := by
          field_simp
        rw [e3]
        have h4 : 1 ≤ 4 * a / mn := by rw [le_div_iff₀ hmn]; linarith
        have h5 : 0 ≤ (1 / 2) * mn⁻¹ * α * b := by positivity
        exact le_mul_of_one_le_right h5 h4
      have e2 : (mn⁻¹ * b * (4 / mn) + 2 / μ) * α * a / 2 = mn⁻¹ * b * (4 / mn) * α * a / 2
          + α / μ * a := by ring
      rw [e2]; linarith
    have := mul_le_mul_of_nonneg_right hη' hub
    linarith [show gP * (z - σ) * ub = gP * ub * (z - σ) by ring]
  have hgain : Γ * α ^ 2 ≤ 1 / 2 := by
    have h2 : α ^ 2 ≤ α := by
      calc α ^ 2 = α * α := sq α
        _ ≤ α * 1 := mul_le_mul_of_nonneg_left hα1.le hα0.le
        _ = α := mul_one α
    have h3 : Γ * α ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hαΓ hΓ0
      have e : Γ * (1 / (2 * Γ + 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
      linarith
    have := mul_le_mul_of_nonneg_left h2 hΓ0
    linarith
  -- the four sequences and their inequalities
  have hxK := SPushAux.x_mem hA hN hα0 hα1.le hrun
  have hpos := SPushAux.phi_pos hN hrun
  have hgap0 : ∀ ν j, 0 ≤ U f G (x ν j) - U f G xstar := fun ν j =>
    sub_nonneg.mpr (isMinOn_iff.mp hxsmin _ (hxK ν j))
  have hp0 : ∀ ν, 0 ≤ pphi f G xstar (φ ν) (x ν) := fun ν =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hpos ν j).le (hgap0 ν j)
  have hsqn : ∀ v : Fin m → SONATA.Undir.E d, 0 ≤ sqn v := fun v =>
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h41 := prop_4_1 K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN _ _ h1 α hα0 hα1.le
    x y xh φ hrun mn hmn (by rw [← hmn_def, ← hDln_def, ← ha_def]; exact ha_pos)
  have h43 := prop_4_3 K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN _ _ h1 α hα0 hα1.le
    x y xh φ hrun
  have h80 : ∀ ν, pphi f G xstar (φ (ν + 1)) (x (ν + 1)) ≤ σ * pphi f G xstar (φ ν) (x ν) +
      η * ub * (a1 * sqn (wperp (φ ν) (x ν)) + 2 * sqn (wperp (φ ν) (y ν))) := by
    intro ν
    have := h41.1 ν
    rw [← hmn_def, ← hDln_def, ← hDm_def, ← hσ_def, ← hη_def, ← hub_def, ← hLm_def] at this
    rw [ha1_def]; linarith
  have h81a : ∀ ν, sqn (wperp (φ ν) (x ν)) ≤ A0 * ρ ^ (2 * ν) * sqn (wperp (φ 0) (x 0)) +
      A1 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) := by
    intro ν; rw [hA0_def, hA1_def]; exact (h42 α hα0 hα1.le x y xh φ hrun ν).1
  have h81b : ∀ ν, sqn (wperp (φ ν) (y ν)) ≤ A0 * ρ ^ (2 * ν) * sqn (wperp (φ 0) (y 0)) +
      A2 * ∑ t ∈ Finset.range ν, ρ ^ (ν - 1 - t) *
        (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)) := by
    intro ν; rw [hA0_def, hA2_def, hLm_def, hlb_def]; exact (h42 α hα0 hα1.le x y xh φ hrun ν).2
  have h84 : ∀ ν, sqn (dir x xh ν) ≤ C1 * pphi f G xstar (φ ν) (x ν) +
      C2 * sqn (wperp (φ ν) (y ν)) := by
    intro ν; rw [hC1_def, hC2_def, hDm_def, hmn_def, hLm_def, hlb_def]; exact h43 ν
  have hgain' : (C1 * (gP * ub) * a1 * (A1 * gR) + (C1 * (gP * ub) * 2 + C2) *
      (8 * A2 * gR * (A1 * gR) + 2 * A2 * gR)) * α ^ 2 ≤ 1 / 2 := by rw [← hΓ_def]; exact hgain
  obtain ⟨R, hR⟩ := SPushChain.chain (fun ν => pphi f G xstar (φ ν) (x ν))
    (fun ν => sqn (wperp (φ ν) (x ν))) (fun ν => sqn (wperp (φ ν) (y ν)))
    (fun ν => sqn (dir x xh ν)) hp0 (fun ν => hsqn _) (fun ν => hsqn _)
    (fun ν => hsqn _) σ (η * ub) a1 2 A0 A1 A2 C1 C2 ρ z α (gP * ub) gR hσ0 hσz hρ0.le hρz hρ1.le
    (mul_nonneg hηpos hub) ha10 (by norm_num) hA00 hA10 hA20 hC10 hC20 (by positivity) hgR0
    h80 h81a h81b h84 hgP hgR hgain'
  -- the φ lower bound
  have hφlb : ∀ ν j, lb ≤ φ ν j := by
    rw [hlb_def]
    rcases Nat.lt_or_ge m 2 with h | h
    · have hm1 : m = 1 := by omega
      subst hm1
      have hcol := hN.2.2.2.2
      have hC1' : ∀ ν, C ν 0 0 = 1 := fun ν => by simpa using hcol ν 0
      have hφ1 : ∀ ν j, φ ν j = 1 := by
        intro ν; induction ν with
        | zero => exact hrun.2.2.1
        | succ n ih => intro j; rw [hrun.2.2.2.2.1 n j]; simp [Fin.fin_one_eq_zero j, hC1', ih]
      intro ν j; rw [hφ1]; simp [phiLb]
    · exact fun ν j => (phi_bounds K O f G μ L ft μt Lt Dl Du xstar Edges B C cl hP hN h α hα0
        hα1.le x y xh φ hrun ν j).1
  refine ⟨R / lb, z, hz0, hz1, fun ν => ?_⟩
  rw [abs_of_nonneg (hgap0 ν i)]
  have hsingle : φ ν i * (U f G (x ν i) - U f G xstar) ≤ pphi f G xstar (φ ν) (x ν) :=
    Finset.single_le_sum (f := fun j => φ ν j * (U f G (x ν j) - U f G xstar))
      (fun j _ => mul_nonneg (hpos ν j).le (hgap0 ν j)) (Finset.mem_univ i)
  have h2 : lb * (U f G (x ν i) - U f G xstar) ≤ R * z ^ ν := by
    have := mul_le_mul_of_nonneg_right (hφlb ν i) (hgap0 ν i)
    have := hR ν
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hlb]
  linarith
