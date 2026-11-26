-- Prove2me | solution 1 for PiBoundsF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:42.134072+00:00
-- url     : https://prove2.me/submissions/373d3e55-06da-4861-a5d1-6a87b00b0281

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PartitionChordSum
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PiBoundsF
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_PartitionChordSum
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ω' : Form1 E)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfB' : (ω'.fBound : ℝ) ≤ C)
    (hfL : (ω.fLip : ℝ) ≤ C) (hfL' : (ω'.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C)
    (hQ : ∀ q ∈ Q, |ω.f q - ω'.f q| ≤ ε) :
    |curveCurrent γ
        { f := fun x => ω.f x - ω'.f x,
          fBound := ω.fBound + ω'.fBound,
          f_bounded := fun x => (abs_sub _ _).trans
            (by push_cast; exact add_le_add (ω.f_bounded x) (ω'.f_bounded x)),
          fLip := ω.fLip + ω'.fLip,
          f_lipschitz := ω.f_lipschitz.sub ω'.f_lipschitz,
          pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz }|
      ≤ psiTilde m Q ε C γ := by
-- BODY
  have hL : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hCnn : (0:ℝ) ≤ C := hC.le
  have hLm : (0:ℝ) ≤ γ.len / m := by positivity
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  set W : Form1 E :=
    { f := fun x => ω.f x - ω'.f x,
      fBound := ω.fBound + ω'.fBound,
      f_bounded := fun x => (abs_sub _ _).trans
        (by push_cast; exact add_le_add (ω.f_bounded x) (ω'.f_bounded x)),
      fLip := ω.fLip + ω'.fLip,
      f_lipschitz := ω.f_lipschitz.sub ω'.f_lipschitz,
      pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz } with hW
  -- Step 1: the partition sum bound, at the RIGHT-endpoint sample points `u i = s (i+1)`.
  have hu : ∀ i : ℕ, i < m →
      (i:ℝ) * γ.len / m ≤ ((i:ℝ) + 1) * γ.len / m ∧
      ((i:ℝ) + 1) * γ.len / m ≤ ((i:ℝ) + 1) * γ.len / m := by
    intro i _
    refine ⟨?_, le_rfl⟩
    have hd : ((i:ℝ) + 1) * γ.len / m - (i:ℝ) * γ.len / m = γ.len / m := by
      field_simp; ring
    linarith
  have hpcs := PartitionChordSum γ W m hm (fun i => ((i:ℝ) + 1) * γ.len / m) hu
  -- Step 2: the two pointwise bounds on `f - f'`.
  have hQc : IsCompact (Q : Set E) := Q.finite_toSet.isCompact
  have hQn : (Q : Set E).Nonempty := Finset.coe_nonempty.mpr hQne
  have hfLz : ∀ z w : E, |ω.f z - ω.f w| ≤ C * dist z w := by
    intro z w
    have h := ω.f_lipschitz.dist_le_mul z w
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hfL dist_nonneg)
  have hfLz' : ∀ z w : E, |ω'.f z - ω'.f w| ≤ C * dist z w := by
    intro z w
    have h := ω'.f_lipschitz.dist_le_mul z w
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hfL' dist_nonneg)
  -- (a) the density-replacement bound
  have hgQ : ∀ z : E, |ω.f z - ω'.f z| ≤ ε + 2 * C * Metric.infDist z (Q : Set E) := by
    intro z
    obtain ⟨q, hqQ, hq⟩ := hQc.exists_infDist_eq_dist hQn z
    have h3 : |ω.f q - ω'.f q| ≤ ε := hQ q (Finset.mem_coe.mp hqQ)
    have h1 := hfLz z q
    have h2 := hfLz' z q
    rw [← hq] at h1 h2
    have heq : ω.f z - ω'.f z
        = ((ω.f z - ω.f q) - (ω'.f z - ω'.f q)) + (ω.f q - ω'.f q) := by ring
    rw [heq]
    have hA := abs_add_le ((ω.f z - ω.f q) - (ω'.f z - ω'.f q)) (ω.f q - ω'.f q)
    have hB := hsub (ω.f z - ω.f q) (ω'.f z - ω'.f q)
    linarith
  -- (b) the direct uniform bound, from `Form1.f_bounded`
  have hgB : ∀ z : E, |ω.f z - ω'.f z| ≤ 2 * C := by
    intro z
    have h1 : |ω.f z| ≤ C := (ω.f_bounded z).trans hfB
    have h2 : |ω'.f z| ≤ C := (ω'.f_bounded z).trans hfB'
    have hB := hsub (ω.f z) (ω'.f z)
    linarith
  -- Step 3: each chord term is bounded by the corresponding summand of `psiTilde`.
  have hterm : ∀ i : ℕ, i < m →
      |W.f (γ.toFun (((i:ℝ) + 1) * γ.len / m))
          * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m)))|
        ≤ C * γ.len / m * min (2 * C)
            (ε + 2 * C * Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)) := by
    intro i _
    set x : E := γ.toFun ((i:ℝ) * γ.len / m) with hx
    set y : E := γ.toFun (((i:ℝ) + 1) * γ.len / m) with hy
    have hchord : |W.pi y - W.pi x| ≤ C * γ.len / m := by
      have hWpi : W.pi y - W.pi x = ω.pi y - ω.pi x := rfl
      rw [hWpi]
      have h := ω.pi_lipschitz.dist_le_mul y x
      rw [Real.dist_eq] at h
      have h' : |ω.pi y - ω.pi x| ≤ C * dist y x :=
        h.trans (mul_le_mul_of_nonneg_right hpL dist_nonneg)
      have hdxy : dist y x ≤ γ.len / m := by
        have hc := (CurveLipschitz γ).dist_le_mul (((i:ℝ) + 1) * γ.len / m) ((i:ℝ) * γ.len / m)
        rw [hy, hx]
        refine hc.trans ?_
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        have hd : ((i:ℝ) + 1) * γ.len / m - (i:ℝ) * γ.len / m = γ.len / m := by
          field_simp; ring
        rw [hd, abs_of_nonneg hLm]
      have hmul := mul_le_mul_of_nonneg_left hdxy hCnn
      calc |ω.pi y - ω.pi x| ≤ C * dist y x := h'
        _ ≤ C * (γ.len / m) := hmul
        _ = C * γ.len / m := by ring
    have hminf : |W.f y| ≤ min (2 * C)
        (ε + 2 * C * Metric.infDist y (Q : Set E)) := by
      have hWf : W.f y = ω.f y - ω'.f y := rfl
      rw [hWf]
      exact le_min (hgB y) (hgQ y)
    have hminnn : (0:ℝ) ≤ min (2 * C) (ε + 2 * C * Metric.infDist y (Q : Set E)) :=
      le_min (by linarith) (by
        have hd := Metric.infDist_nonneg (x := y) (s := (Q : Set E))
        nlinarith)
    rw [abs_mul]
    calc |W.f y| * |W.pi y - W.pi x|
        ≤ min (2 * C) (ε + 2 * C * Metric.infDist y (Q : Set E)) * (C * γ.len / m) :=
          mul_le_mul hminf hchord (abs_nonneg _) hminnn
      _ = C * γ.len / m * min (2 * C) (ε + 2 * C * Metric.infDist y (Q : Set E)) := by ring
  -- Step 4: sum up and reindex onto `Finset.Icc 1 m`.
  have hSum : |∑ i ∈ Finset.range m,
        W.f (γ.toFun (((i:ℝ) + 1) * γ.len / m))
          * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m)))|
      ≤ ∑ i ∈ Finset.range m, C * γ.len / m * min (2 * C)
          (ε + 2 * C * Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi))
  have hshift : ∀ F : ℕ → ℝ, ∑ j ∈ Finset.Icc 1 m, F j = ∑ i ∈ Finset.range m, F (i + 1) := by
    intro F
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  have hpsi1 : C * γ.len / m * (∑ j ∈ Finset.Icc 1 m,
        min (2 * C)
          (ε + 2 * C * Metric.infDist (γ.toFun ((j:ℝ) * γ.len / m)) (Q : Set E)))
      = ∑ i ∈ Finset.range m, C * γ.len / m * min (2 * C)
          (ε + 2 * C * Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)) := by
    rw [Finset.mul_sum, hshift]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  -- Step 5: the error term.
  have herr : (W.fLip : ℝ) * (W.piLip : ℝ) * γ.len ^ 2 / m ≤ 2 * C ^ 2 * γ.len ^ 2 / m := by
    have hX : (0:ℝ) ≤ γ.len ^ 2 / m := by positivity
    have hWf : (W.fLip : ℝ) = (ω.fLip : ℝ) + (ω'.fLip : ℝ) := by
      show ((ω.fLip + ω'.fLip : NNReal) : ℝ) = _
      push_cast
      ring
    have hWp : (W.piLip : ℝ) = (ω.piLip : ℝ) := rfl
    have h1 : (W.fLip : ℝ) * (W.piLip : ℝ) ≤ 2 * C ^ 2 := by
      rw [hWf, hWp]
      nlinarith [ω.fLip.coe_nonneg, ω'.fLip.coe_nonneg, ω.piLip.coe_nonneg]
    calc (W.fLip : ℝ) * (W.piLip : ℝ) * γ.len ^ 2 / m
        = ((W.fLip : ℝ) * (W.piLip : ℝ)) * (γ.len ^ 2 / m) := by ring
      _ ≤ (2 * C ^ 2) * (γ.len ^ 2 / m) := mul_le_mul_of_nonneg_right h1 hX
      _ = 2 * C ^ 2 * γ.len ^ 2 / m := by ring
  -- Step 6: assemble.
  have hfin := abs_sub_abs_le_abs_sub (curveCurrent γ W)
    (∑ i ∈ Finset.range m,
      W.f (γ.toFun (((i:ℝ) + 1) * γ.len / m))
        * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m))))
  rw [psiTilde]
  rw [hpsi1]
  linarith
