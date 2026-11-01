-- Prove2me | solution 1 for StochCoordProx.display_23_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:21:09.077255+00:00
-- url     : https://prove2.me/submissions/c27d53ff-d107-4ead-8c02-0ffdf00c6af7

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_Hf
import Definitions.Def_StochCoordProx_model
import Definitions.Def_StochCoordProx_IsSCPGRun

open Set Filter Topology Matrix
open scoped InnerProductSpace

private lemma d31_real_remainder (g g' : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (g' t) t)
    (hbound : ∀ t, 0 ≤ t → |g' t - g' 0| ≤ L * t) :
    |g 1 - g 0 - g' 0| ≤ L / 2 := by
  let u : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 - L / 2 * t ^ 2
  let l : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 + L / 2 * t ^ 2
  have hu (t : ℝ) : HasDerivAt u (g' t - g' 0 - L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [u, id]) <;> ring
  have hl (t : ℝ) : HasDerivAt l (g' t - g' 0 + L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).add
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [l, id]) <;> ring
  have hanti : AntitoneOn u (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hu t).continuousAt.continuousWithinAt)
      (fun t _ => (hu t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hu t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).2
    linarith
  have hmono : MonotoneOn l (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hl t).continuousAt.continuousWithinAt)
      (fun t _ => (hl t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hl t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).1
    linarith
  have hu01 := hanti (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  have hl01 := hmono (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  dsimp [u, l] at hu01 hl01
  apply abs_le.mpr
  constructor <;> linarith

private lemma d31_transpose_inner {n p : ℕ} (U : Matrix (Fin n) (Fin p) ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin p)) :
    ⟪Matrix.toEuclideanLin Uᵀ a, b⟫_ℝ = ⟪a, Matrix.toEuclideanLin U b⟫_ℝ := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h]
  exact LinearMap.adjoint_inner_left _ _ _

private lemma d31_smooth_descent {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin p) ℝ) (LU : ℝ) (hf : Differentiable ℝ f)
    (hL : StochCoordProx.IsSmoothAlong f U LU)
    (x : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin p)) :
    |f (x + Matrix.toEuclideanLin U h) - f x - ⟪Matrix.toEuclideanLin Uᵀ (gradient f x), h⟫_ℝ| ≤
      LU / 2 * ‖h‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • Matrix.toEuclideanLin U h)
  let g' : ℝ → ℝ := fun t =>
    ⟪Matrix.toEuclideanLin Uᵀ (gradient f (x + t • Matrix.toEuclideanLin U h)), h⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • Matrix.toEuclideanLin U h)
        (Matrix.toEuclideanLin U h) t := by
      simpa using ((hasDerivAt_id t).smul_const (Matrix.toEuclideanLin U h)).const_add x
    have hc := (hf (x + t • Matrix.toEuclideanLin U h)).hasFDerivAt.comp_hasDerivAt t hp
    convert! hc using 1
    simp only [g', d31_transpose_inner, inner_gradient_left]
  have hb (t : ℝ) (ht : 0 ≤ t) : |g' t - g' 0| ≤ (LU * ‖h‖ ^ 2) * t := by
    have hproj := hL x (t • h)
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hproj
    dsimp [g']
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left, ← map_sub]
    calc
      _ ≤ ‖Matrix.toEuclideanLin Uᵀ
          (gradient f (x + t • Matrix.toEuclideanLin U h) - gradient f x)‖ * ‖h‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (LU * (t * ‖h‖)) * ‖h‖ := mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = (LU * ‖h‖ ^ 2) * t := by ring
  have hr := d31_real_remainder g g' (LU * ‖h‖ ^ 2) hd hb
  simpa [g, g', mul_div_assoc, div_mul_eq_mul_div] using hr

private lemma d31_convex_model_gap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (φ : V → ℝ) (a d : V) (H : ℝ) (hφ : ConvexOn ℝ univ φ)
    (hd : ∀ v, ⟪a, d⟫_ℝ + H / 2 * ‖d‖ ^ 2 + φ d ≤
      ⟪a, v⟫_ℝ + H / 2 * ‖v‖ ^ 2 + φ v) :
    ⟪a, d⟫_ℝ + H * ‖d‖ ^ 2 + φ d ≤ φ 0 := by
  have hseg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
      ⟪a, d⟫_ℝ + (1 + s) * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0 ≤ 0 := by
    have hc := hφ.2 (mem_univ d) (mem_univ (0 : V)) hs0
      (show 0 ≤ 1 - s by linarith) (show s + (1 - s) = 1 by ring)
    simp only [smul_zero, add_zero, smul_eq_mul] at hc
    have hm := hd (s • d)
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow] at hm
    have hmul : (1 - s) *
        (⟪a, d⟫_ℝ + (1 + s) * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0) ≤ 0 := by
      nlinarith
    by_contra hle
    have hp := mul_pos (show 0 < 1 - s by linarith) (lt_of_not_ge hle)
    linarith
  have htend : Tendsto (fun s : ℝ => ⟪a, d⟫_ℝ + (1 + s) * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0)
      (𝓝[<] 1) (𝓝 (⟪a, d⟫_ℝ + 2 * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0)) := by
    have hc : Continuous (fun s : ℝ =>
        ⟪a, d⟫_ℝ + (1 + s) * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0) := by fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  have hevent : ∀ᶠ s : ℝ in 𝓝[<] 1,
      ⟪a, d⟫_ℝ + (1 + s) * (H / 2 * ‖d‖ ^ 2) + φ d - φ 0 ≤ 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)), self_mem_nhdsWithin] with s hs0 hs1
    exact hseg s (le_of_lt hs0) hs1
  have hlimit := le_of_tendsto htend hevent
  linarith

private lemma d31_prox_descent {n p : ℕ} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (U : Matrix (Fin n) (Fin p) ℝ) (hU : U ∈ 𝒰)
    (LU η : ℝ) (hf : Differentiable ℝ f) (hL : StochCoordProx.IsSmoothAlong f U LU) (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin p))
    (hd : ∀ d' : EuclideanSpace ℝ (Fin p),
      StochCoordProx.model f ψ x U (StochCoordProx.Hf ψ 𝒰 LU η) d ≤
        StochCoordProx.model f ψ x U (StochCoordProx.Hf ψ 𝒰 LU η) d') :
    f (x + Matrix.toEuclideanLin U d) + ψ (x + Matrix.toEuclideanLin U d) ≤
      f x + ψ x - η / 2 * ‖d‖ ^ 2 := by
  have hs := (abs_le.mp (d31_smooth_descent f U LU hf hL x d)).2
  classical
  by_cases hc : StochCoordProx.ConvexAlongSubspaces ψ 𝒰
  · have hconv := hc x U hU
    have hm := d31_convex_model_gap (fun v => ψ (x + Matrix.toEuclideanLin U v))
      (Matrix.toEuclideanLin Uᵀ (gradient f x)) d (StochCoordProx.Hf ψ 𝒰 LU η) hconv
      (fun v => by have h := hd v; dsimp only [StochCoordProx.model] at h; linarith)
    simp only [map_zero, add_zero] at hm
    simp only [StochCoordProx.Hf, if_pos hc] at hm
    nlinarith
  · have hm := hd 0
    simp only [StochCoordProx.model, StochCoordProx.Hf, if_neg hc, map_zero, add_zero,
      inner_zero_right, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hm
    nlinarith

open StochCoordProx

theorem solution {n p : ℕ} {Ω : Type*} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (L : Matrix (Fin n) (Fin p) ℝ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hf : Differentiable ℝ f)
    (hL : ∀ V ∈ 𝒰, IsSmoothAlong f V (L V)) (xstar : EuclideanSpace ℝ (Fin n))
    (hxstar : ∀ y, f xstar + ψ xstar ≤ f y + ψ y)
    (U : ℕ → Ω → Matrix (Fin n) (Fin p) ℝ) (η : ℕ → Ω → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (d : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsSCPGRun f ψ 𝒰 L x₀ U η x d) (ηmin : Ω → ℝ) (hηmin : ∀ ω k, ηmin ω ≤ η k ω)
    (ω : Ω) (K : ℕ) :
    ηmin ω / 2 * ∑ i ∈ Finset.range (K + 1), ‖d i ω‖ ^ 2 ≤
        ∑ i ∈ Finset.range (K + 1), η i ω / 2 * ‖d i ω‖ ^ 2 ∧
      ∑ i ∈ Finset.range (K + 1), η i ω / 2 * ‖d i ω‖ ^ 2 ≤
        ∑ i ∈ Finset.range (K + 1),
          ((f (x i ω) + ψ (x i ω)) - (f (x (i + 1) ω) + ψ (x (i + 1) ω))) ∧
      ∑ i ∈ Finset.range (K + 1),
          ((f (x i ω) + ψ (x i ω)) - (f (x (i + 1) ω) + ψ (x (i + 1) ω))) =
        (f x₀ + ψ x₀) - (f (x (K + 1) ω) + ψ (x (K + 1) ω)) ∧
      (f x₀ + ψ x₀) - (f (x (K + 1) ω) + ψ (x (K + 1) ω)) ≤
        (f x₀ + ψ x₀) - (f xstar + ψ xstar) := by
  have hstep (i : ℕ) : η i ω / 2 * ‖d i ω‖ ^ 2 ≤
      (f (x i ω) + ψ (x i ω)) - (f (x (i + 1) ω) + ψ (x (i + 1) ω)) := by
    rcases (hrun ω).2 i with ⟨hUi, hηi, hmini, hxi⟩
    have hi := d31_prox_descent f ψ 𝒰 (U i ω) hUi (L (U i ω)) (η i ω)
      hf (hL _ hUi) hηi (x i ω) (d i ω) hmini
    rw [← hxi] at hi
    linarith
  have htel (m : ℕ) :
      (∑ i ∈ Finset.range m, ((f (x i ω) + ψ (x i ω)) -
        (f (x (i + 1) ω) + ψ (x (i + 1) ω)))) =
      (f (x 0 ω) + ψ (x 0 ω)) - (f (x m ω) + ψ (x m ω)) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (by linarith [hηmin ω i]) (sq_nonneg _)
  · exact Finset.sum_le_sum fun i _ => hstep i
  · simpa only [(hrun ω).1] using htel (K + 1)
  · linarith [hxstar (x (K + 1) ω)]

#print axioms solution
