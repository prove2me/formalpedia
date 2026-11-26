-- Prove2me | solution 1 for PiBoundsPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:11.552207+00:00
-- url     : https://prove2.me/submissions/c0dfe30f-8d0c-42b3-86ea-a45a0a67e4f0

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PartitionChordSum
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PiBoundsPi
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_PartitionChordSum
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ω' : Form1 E)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfL : (ω.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C) (hpL' : (ω'.piLip : ℝ) ≤ C)
    (hQ : ∀ q ∈ Q, |ω.pi q - ω'.pi q| ≤ ε) :
    |curveCurrent γ
        { f := ω.f, fBound := ω.fBound, f_bounded := ω.f_bounded,
          fLip := ω.fLip, f_lipschitz := ω.f_lipschitz,
          pi := fun x => ω.pi x - ω'.pi x,
          piLip := ω.piLip + ω'.piLip,
          pi_lipschitz := ω.pi_lipschitz.sub ω'.pi_lipschitz }|
      ≤ psi m Q ε C γ := by
-- BODY
  have hL : (0:ℝ) ≤ γ.len := γ.len_nonneg
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hCnn : (0:ℝ) ≤ C := hC.le
  have hLm : (0:ℝ) ≤ γ.len / m := by positivity
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  set W : Form1 E :=
    { f := ω.f, fBound := ω.fBound, f_bounded := ω.f_bounded,
      fLip := ω.fLip, f_lipschitz := ω.f_lipschitz,
      pi := fun x => ω.pi x - ω'.pi x,
      piLip := ω.piLip + ω'.piLip,
      pi_lipschitz := ω.pi_lipschitz.sub ω'.pi_lipschitz } with hW
  -- Step 1: the partition sum bound, at the left-endpoint sample points `u i = s i`.
  have hu : ∀ i : ℕ, i < m →
      (i:ℝ) * γ.len / m ≤ (i:ℝ) * γ.len / m ∧
      (i:ℝ) * γ.len / m ≤ ((i:ℝ) + 1) * γ.len / m := by
    intro i _
    refine ⟨le_rfl, ?_⟩
    have hd : ((i:ℝ) + 1) * γ.len / m - (i:ℝ) * γ.len / m = γ.len / m := by
      field_simp; ring
    linarith
  have hpcs := PartitionChordSum γ W m hm (fun i => (i:ℝ) * γ.len / m) hu
  -- Step 2: the two pointwise bounds on `π - π'`.
  have hQc : IsCompact (Q : Set E) := Q.finite_toSet.isCompact
  have hQn : (Q : Set E).Nonempty := Finset.coe_nonempty.mpr hQne
  have hpiL : ∀ z w : E, |ω.pi z - ω.pi w| ≤ C * dist z w := by
    intro z w
    have h := ω.pi_lipschitz.dist_le_mul z w
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hpL dist_nonneg)
  have hpiL' : ∀ z w : E, |ω'.pi z - ω'.pi w| ≤ C * dist z w := by
    intro z w
    have h := ω'.pi_lipschitz.dist_le_mul z w
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hpL' dist_nonneg)
  -- (a) the density-replacement bound
  have hgQ : ∀ z : E, |ω.pi z - ω'.pi z| ≤ ε + 2 * C * Metric.infDist z (Q : Set E) := by
    intro z
    obtain ⟨q, hqQ, hq⟩ := hQc.exists_infDist_eq_dist hQn z
    have h3 : |ω.pi q - ω'.pi q| ≤ ε := hQ q (Finset.mem_coe.mp hqQ)
    have h1 := hpiL z q
    have h2 := hpiL' z q
    rw [← hq] at h1 h2
    have heq : ω.pi z - ω'.pi z
        = ((ω.pi z - ω.pi q) - (ω'.pi z - ω'.pi q)) + (ω.pi q - ω'.pi q) := by ring
    rw [heq]
    have hA := abs_add_le ((ω.pi z - ω.pi q) - (ω'.pi z - ω'.pi q)) (ω.pi q - ω'.pi q)
    have hB := hsub (ω.pi z - ω.pi q) (ω'.pi z - ω'.pi q)
    linarith
  -- (b) the direct Lipschitz bound
  have hgd : ∀ z w : E,
      |(ω.pi z - ω'.pi z) - (ω.pi w - ω'.pi w)| ≤ 2 * C * dist z w := by
    intro z w
    have heq : (ω.pi z - ω'.pi z) - (ω.pi w - ω'.pi w)
        = (ω.pi z - ω.pi w) - (ω'.pi z - ω'.pi w) := by ring
    rw [heq]
    have h1 := hpiL z w
    have h2 := hpiL' z w
    have hB := hsub (ω.pi z - ω.pi w) (ω'.pi z - ω'.pi w)
    linarith
  -- Step 3: each chord term is bounded by the corresponding summand of `psi`.
  have hterm : ∀ i : ℕ, i < m →
      |W.f (γ.toFun ((i:ℝ) * γ.len / m))
          * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m)))|
        ≤ C * min (2 * C * γ.len / m)
            (2 * ε + 2 * C * (Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)
              + Metric.infDist (γ.toFun ((i:ℝ) * γ.len / m)) (Q : Set E))) := by
    intro i _
    set x : E := γ.toFun ((i:ℝ) * γ.len / m) with hx
    set y : E := γ.toFun (((i:ℝ) + 1) * γ.len / m) with hy
    have hfx : |W.f x| ≤ C := (ω.f_bounded x).trans hfB
    have hb1 : |(ω.pi y - ω'.pi y) - (ω.pi x - ω'.pi x)| ≤ 2 * C * γ.len / m := by
      refine (hgd y x).trans ?_
      have hdxy : dist y x ≤ γ.len / m := by
        have h := (CurveLipschitz γ).dist_le_mul (((i:ℝ) + 1) * γ.len / m) ((i:ℝ) * γ.len / m)
        rw [hy, hx]
        refine h.trans ?_
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        have hd : ((i:ℝ) + 1) * γ.len / m - (i:ℝ) * γ.len / m = γ.len / m := by
          field_simp; ring
        rw [hd, abs_of_nonneg hLm]
      have := mul_le_mul_of_nonneg_left hdxy (by linarith : (0:ℝ) ≤ 2 * C)
      calc 2 * C * dist y x = 2 * C * dist y x := rfl
        _ ≤ 2 * C * (γ.len / m) := this
        _ = 2 * C * γ.len / m := by ring
    have hb2 : |(ω.pi y - ω'.pi y) - (ω.pi x - ω'.pi x)|
        ≤ 2 * ε + 2 * C * (Metric.infDist y (Q : Set E) + Metric.infDist x (Q : Set E)) := by
      have h1 := hgQ y
      have h2 := hgQ x
      have hB := hsub (ω.pi y - ω'.pi y) (ω.pi x - ω'.pi x)
      linarith
    have hmin : |W.pi y - W.pi x|
        ≤ min (2 * C * γ.len / m)
            (2 * ε + 2 * C * (Metric.infDist y (Q : Set E) + Metric.infDist x (Q : Set E))) := by
      have hWpi : W.pi y - W.pi x = (ω.pi y - ω'.pi y) - (ω.pi x - ω'.pi x) := rfl
      rw [hWpi]
      exact le_min hb1 hb2
    rw [abs_mul]
    exact mul_le_mul hfx hmin (abs_nonneg _) hCnn
  -- Step 4: sum up and reindex onto `Finset.Icc 1 m`.
  have hSum : |∑ i ∈ Finset.range m,
        W.f (γ.toFun ((i:ℝ) * γ.len / m))
          * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m)))|
      ≤ ∑ i ∈ Finset.range m, C * min (2 * C * γ.len / m)
          (2 * ε + 2 * C * (Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)
            + Metric.infDist (γ.toFun ((i:ℝ) * γ.len / m)) (Q : Set E))) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi))
  have hshift : ∀ F : ℕ → ℝ, ∑ j ∈ Finset.Icc 1 m, F j = ∑ i ∈ Finset.range m, F (i + 1) := by
    intro F
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  have hpsi1 : C * (∑ j ∈ Finset.Icc 1 m,
        min (2 * C * γ.len / m)
          (2 * ε + 2 * C * (Metric.infDist (γ.toFun ((j:ℝ) * γ.len / m)) (Q : Set E)
            + Metric.infDist (γ.toFun (((j:ℝ) - 1) * γ.len / m)) (Q : Set E))))
      = ∑ i ∈ Finset.range m, C * min (2 * C * γ.len / m)
          (2 * ε + 2 * C * (Metric.infDist (γ.toFun (((i:ℝ) + 1) * γ.len / m)) (Q : Set E)
            + Metric.infDist (γ.toFun ((i:ℝ) * γ.len / m)) (Q : Set E))) := by
    rw [Finset.mul_sum, hshift]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  -- Step 5: the error term.
  have herr : (W.fLip : ℝ) * (W.piLip : ℝ) * γ.len ^ 2 / m ≤ 2 * C ^ 2 * γ.len ^ 2 / m := by
    have hX : (0:ℝ) ≤ γ.len ^ 2 / m := by positivity
    have hWf : (W.fLip : ℝ) = (ω.fLip : ℝ) := rfl
    have hWp : (W.piLip : ℝ) = (ω.piLip : ℝ) + (ω'.piLip : ℝ) := by
      show ((ω.piLip + ω'.piLip : NNReal) : ℝ) = _
      push_cast
      ring
    have h1 : (W.fLip : ℝ) * (W.piLip : ℝ) ≤ 2 * C ^ 2 := by
      rw [hWf, hWp]
      nlinarith [ω.fLip.coe_nonneg, ω.piLip.coe_nonneg, ω'.piLip.coe_nonneg]
    calc (W.fLip : ℝ) * (W.piLip : ℝ) * γ.len ^ 2 / m
        = ((W.fLip : ℝ) * (W.piLip : ℝ)) * (γ.len ^ 2 / m) := by ring
      _ ≤ (2 * C ^ 2) * (γ.len ^ 2 / m) := mul_le_mul_of_nonneg_right h1 hX
      _ = 2 * C ^ 2 * γ.len ^ 2 / m := by ring
  -- Step 6: assemble.
  have hfin := abs_sub_abs_le_abs_sub (curveCurrent γ W)
    (∑ i ∈ Finset.range m,
      W.f (γ.toFun ((i:ℝ) * γ.len / m))
        * (W.pi (γ.toFun (((i:ℝ) + 1) * γ.len / m)) - W.pi (γ.toFun ((i:ℝ) * γ.len / m))))
  rw [psi]
  rw [hpsi1]
  linarith
