-- Prove2me | solution 1 for OTDRO.WorstCase.ellRob_lambda_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:21:21.159989+00:00
-- url     : https://prove2.me/submissions/d31ee1e3-074f-404b-82c3-a09d331a46fb

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_ModelRiskOT_Duality_primalFeasible
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_OTDRO_WorstCase_Transport

open MeasureTheory Matrix

namespace OTDRO4

variable {d : ℕ}

lemma mulVec_inv_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) (b : Fin d → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM.isUnit), one_mulVec]

/-- `q = wᵀ A w` where `w = A⁻¹β`. -/
lemma quadInv_eq (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.quadInv A β x =
      dotProduct ((A x)⁻¹ *ᵥ β.ofLp) (A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp)) := by
  unfold OTDRO.Dual.quadInv
  rw [mulVec_inv_mulVec _ (hA x), dotProduct_comm]

lemma quadInv_nonneg (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ OTDRO.Dual.quadInv A β x := by
  rw [quadInv_eq A hA]
  have := (hA x).posSemidef.dotProduct_mulVec_nonneg ((A x)⁻¹ *ᵥ β.ofLp)
  simpa using this

lemma quadInv_le (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), ρ * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (A x *ᵥ v.ofLp)) :
    OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρ := by
  set W : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp) with hW
  have h1 : ρ * ‖W‖ ^ 2 ≤ OTDRO.Dual.quadInv A β x := by
    rw [quadInv_eq A hA]; exact hx W
  have h2 : OTDRO.Dual.quadInv A β x ≤ ‖β‖ * ‖W‖ := by
    have : OTDRO.Dual.quadInv A β x = inner ℝ W β := by
      unfold OTDRO.Dual.quadInv
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [hW]
    rw [this, mul_comm]
    exact real_inner_le_norm W β
  have hq0 := quadInv_nonneg A hA β x
  rw [le_div_iff₀ hρ]
  have hW0 : 0 ≤ ‖W‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖β‖ := norm_nonneg _
  -- ρ‖W‖ ≤ ‖β‖
  have h3 : ρ * ‖W‖ ≤ ‖β‖ := by
    rcases eq_or_lt_of_le hW0 with h | h
    · rw [← h]; simp [hb0]
    · nlinarith
  nlinarith

/-- measurability of the quadratic form `x ↦ vᵀ A(x) v` -/
lemma quadForm_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (v : Fin d → ℝ) :
    Measurable (fun x => dotProduct v (A x *ᵥ v)) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (x, x - WithLp.toLp 2 v)) := by
    fun_prop
  have := (hlsc.comp hc).measurable
  convert this using 2 with x
  simp [OTDRO.Dual.mahalCost, Function.comp]

lemma entry_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (i j : Fin d) :
    Measurable (fun x => A x i j) := by
  have h1 := quadForm_measurable A hlsc (Pi.single i 1 + Pi.single j 1)
  have h2 := quadForm_measurable A hlsc (Pi.single i 1 - Pi.single j 1)
  have key : ∀ x, A x i j = (dotProduct (Pi.single i 1 + Pi.single j 1)
      (A x *ᵥ (Pi.single i 1 + Pi.single j 1)) - dotProduct (Pi.single i 1 - Pi.single j 1)
      (A x *ᵥ (Pi.single i 1 - Pi.single j 1))) / 4 := by
    intro x
    have hs : A x j i = A x i j := by
      have := (hA x).isHermitian
      have h := congrFun (congrFun this i) j
      simpa using h
    simp only [mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
      sub_dotProduct, mulVec_single_one, single_one_dotProduct]
    simp [Matrix.col_apply, hs]
    ring
  simp_rw [key]
  exact (h1.sub h2).div_const _

lemma inv_entry_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (i j : Fin d) :
    Measurable (fun x => (A x)⁻¹ i j) := by
  have hAm : Measurable (fun x => (fun i j => A x i j : Fin d → Fin d → ℝ)) := by
    apply measurable_pi_lambda; intro i
    apply measurable_pi_lambda; intro j
    exact entry_measurable A hA hlsc i j
  have hdet : Measurable (fun M : Fin d → Fin d → ℝ => (Matrix.of M).det) := by
    have h : Continuous (fun M : Fin d → Fin d → ℝ => (Matrix.of M).det) :=
      (continuous_id.matrix_det (X := Matrix (Fin d) (Fin d) ℝ))
    exact h.measurable
  have hadj : Measurable (fun M : Fin d → Fin d → ℝ => (Matrix.of M).adjugate i j) := by
    have h : Continuous (fun M : Fin d → Fin d → ℝ => (Matrix.of M).adjugate i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (continuous_id.matrix_adjugate (X := Matrix (Fin d) (Fin d) ℝ)))
    exact h.measurable
  have : (fun x => (A x)⁻¹ i j) = fun x =>
      ((Matrix.of (fun i j => A x i j)).det)⁻¹ *
        (Matrix.of (fun i j => A x i j)).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply]
    rfl
  rw [this]
  exact ((hdet.comp hAm).inv).mul (hadj.comp hAm)

lemma quadInv_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (β : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun x => OTDRO.Dual.quadInv A β x) := by
  unfold OTDRO.Dual.quadInv
  simp only [dotProduct, mulVec]
  apply Finset.measurable_sum; intro i _
  apply Measurable.const_mul
  apply Finset.measurable_sum; intro j _
  exact (inv_entry_measurable A hA hlsc i j).mul_const _

/-- convex `ℓ` has an affine lower bound -/
lemma convex_lower (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ) (u : ℝ) :
    ℓ 0 - (|ℓ 0| + |ℓ 1| + |ℓ (-1)|) * |u| ≤ ℓ u := by
  rcases le_total 0 u with hu | hu
  · have hpos : 0 < 1 + u := by linarith
    have hab : u / (1 + u) + 1 / (1 + u) = 1 := by
      field_simp; ring
    have h : ℓ ((u / (1 + u)) • (-1 : ℝ) + (1 / (1 + u)) • u) ≤
        (u / (1 + u)) • ℓ (-1) + (1 / (1 + u)) • ℓ u :=
      hℓ.2 (Set.mem_univ (-1)) (Set.mem_univ u) (by positivity) (by positivity) hab
    have e : (u / (1 + u)) • (-1 : ℝ) + (1 / (1 + u)) • u = 0 := by
      simp only [smul_eq_mul]; ring
    rw [e] at h
    simp only [smul_eq_mul] at h
    have : (1 + u) * ℓ 0 ≤ u * ℓ (-1) + ℓ u := by
      have := mul_le_mul_of_nonneg_left h hpos.le
      have e2 : (1 + u) * (u / (1 + u) * ℓ (-1) + 1 / (1 + u) * ℓ u) = u * ℓ (-1) + ℓ u := by
        field_simp
      linarith
    rw [abs_of_nonneg hu]
    nlinarith [abs_nonneg (ℓ 0), abs_nonneg (ℓ 1), abs_nonneg (ℓ (-1)), le_abs_self (ℓ 0),
      neg_abs_le (ℓ 0), le_abs_self (ℓ (-1)), neg_abs_le (ℓ (-1))]
  · have hpos : 0 < 1 - u := by linarith
    have hab : -u / (1 - u) + 1 / (1 - u) = 1 := by
      field_simp; ring
    have h : ℓ ((-u / (1 - u)) • (1 : ℝ) + (1 / (1 - u)) • u) ≤
        (-u / (1 - u)) • ℓ 1 + (1 / (1 - u)) • ℓ u :=
      hℓ.2 (Set.mem_univ 1) (Set.mem_univ u) (div_nonneg (by linarith) hpos.le) (by positivity)
        hab
    have e : (-u / (1 - u)) • (1 : ℝ) + (1 / (1 - u)) • u = 0 := by
      simp only [smul_eq_mul]; ring
    rw [e] at h
    simp only [smul_eq_mul] at h
    have : (1 - u) * ℓ 0 ≤ -u * ℓ 1 + ℓ u := by
      have := mul_le_mul_of_nonneg_left h hpos.le
      have e2 : (1 - u) * (-u / (1 - u) * ℓ 1 + 1 / (1 - u) * ℓ u) = -u * ℓ 1 + ℓ u := by
        field_simp
      linarith
    rw [abs_of_nonpos hu]
    nlinarith [abs_nonneg (ℓ 0), abs_nonneg (ℓ 1), abs_nonneg (ℓ (-1)), le_abs_self (ℓ 0),
      neg_abs_le (ℓ 0), le_abs_self (ℓ 1), neg_abs_le (ℓ 1)]

lemma quad_bound (e b D t : ℝ) (he : 0 < e) (h : e * t ^ 2 ≤ b * t + D) :
    |t| ≤ 1 + (|b| + |D|) / e := by
  suffices hh : (|t| - 1) * e ≤ |b| + |D| by
    have := (le_div_iff₀ he).2 hh; linarith
  by_contra hc
  push Not at hc
  have hbt : b * t ≤ |b| * |t| := by
    rw [← abs_mul]; exact le_abs_self _
  have hD : D ≤ |D| := le_abs_self _
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1 : 1 < |t| := by
    by_contra h1; push Not at h1
    nlinarith [abs_nonneg b, abs_nonneg D, abs_nonneg t]
  nlinarith [abs_nonneg b, abs_nonneg D, abs_nonneg t]

lemma growth_set_bddBelow (ℓ : ℝ → ℝ) :
    BddBelow {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} :=
  ⟨0, fun _ hs => hs.1⟩

lemma kappa_nonneg (ℓ : ℝ → ℝ) (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)) :
    0 ≤ OTDRO.Dual.growthKappa ℓ :=
  le_csInf h (fun _ hs => hs.1)

/-- pick `s` in the growth set below any `c > κ`, with its bound `M` -/
lemma exists_growth_lt (ℓ : ℝ → ℝ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)) (c : ℝ)
    (hc : OTDRO.Dual.growthKappa ℓ < c) :
    ∃ s M : ℝ, 0 ≤ s ∧ s < c ∧ ∀ u, ℓ u ≤ M + s * u ^ 2 := by
  obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt h hc
  obtain ⟨M, hM⟩ := hsS.2
  exact ⟨s, M, hsS.1, hslt, fun u => by have := hM ⟨u, rfl⟩; simp only at this; linarith⟩

/-- `F` rewritten in the variable `t = γ√δ q`. -/
lemma Fobj_eq (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ γ : ℝ)
    (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) :
    OTDRO.Dual.Fobj ℓ A δ γ β lam x =
      ℓ (inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x) -
        lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x) *
          (γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x) ^ 2 + lam * Real.sqrt δ := by
  unfold OTDRO.Dual.Fobj
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  field_simp
  ring

/-- superlevel bound: if `F 0 ≤ F γ`, `q > 0` and the growth constant `s < λ/(√δ q)`, then
`|γ√δq|` is bounded. -/
lemma superlevel_bound (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) (s M : ℝ) (hM : ∀ u, ℓ u ≤ M + s * u ^ 2)
    (hs : s < lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x)) (γ : ℝ)
    (hγ : OTDRO.Dual.Fobj ℓ A δ 0 β lam x ≤ OTDRO.Dual.Fobj ℓ A δ γ β lam x) :
    |γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x| ≤
      1 + (|2 * s * inner ℝ β x| + |M + s * (inner ℝ β x) ^ 2 - ℓ (inner ℝ β x)|) /
        (lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x) - s) := by
  rw [Fobj_eq ℓ A δ _ hδ β lam x hq, Fobj_eq ℓ A δ _ hδ β lam x hq] at hγ
  set q := OTDRO.Dual.quadInv A β x
  set a : ℝ := inner ℝ β x
  set r := lam / (Real.sqrt δ * q)
  set t := γ * Real.sqrt δ * q
  apply quad_bound
  · linarith
  have hU := hM (a + t)
  simp at hγ
  nlinarith

/-- pointwise Lemma 1(a) -/
lemma lemma1a (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hq0 : 0 ≤ OTDRO.Dual.quadInv A β x)
    (hcase : OTDRO.Dual.quadInv A β x = 0 ∨ ∃ s M : ℝ, 0 ≤ s ∧ (∀ u, ℓ u ≤ M + s * u ^ 2) ∧
      s < lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x)) :
    (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧ OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊤ := by
  have hcont : Continuous ℓ := continuousOn_univ.1 (hℓ.continuousOn isOpen_univ)
  have hFc : Continuous (fun γ => OTDRO.Dual.Fobj ℓ A δ γ β lam x) := by
    unfold OTDRO.Dual.Fobj; fun_prop
  suffices h : (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty by
    refine ⟨h, ?_⟩
    obtain ⟨g, hg⟩ := h
    apply ne_top_of_le_ne_top (EReal.coe_ne_top (OTDRO.Dual.Fobj ℓ A δ g β lam x))
    unfold OTDRO.Dual.ellRob
    exact iSup_le fun c => EReal.coe_le_coe_iff.2 (hg c)
  rcases hcase with h0 | ⟨s, M, hs0, hM, hs⟩
  · refine ⟨0, fun c => ?_⟩
    unfold OTDRO.Dual.Fobj; rw [h0]; simp
  have hq : 0 < OTDRO.Dual.quadInv A β x := by
    rcases eq_or_lt_of_le hq0 with h | h
    · exfalso
      rw [← h] at hs; simp at hs; linarith
    · exact h
  set R := 1 + (|2 * s * inner ℝ β x| + |M + s * (inner ℝ β x) ^ 2 - ℓ (inner ℝ β x)|) /
        (lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x) - s)
  have hsdq : 0 < Real.sqrt δ * OTDRO.Dual.quadInv A β x := mul_pos (Real.sqrt_pos.2 hδ) hq
  set T := Metric.closedBall (0:ℝ) (R / (Real.sqrt δ * OTDRO.Dual.quadInv A β x))
  have hT : IsCompact T := isCompact_closedBall _ _
  have hR0 : 0 ≤ R := by
    have : 0 ≤ (|2 * s * inner ℝ β x| + |M + s * (inner ℝ β x) ^ 2 - ℓ (inner ℝ β x)|) /
        (lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x) - s) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have h0T : (0:ℝ) ∈ T := Metric.mem_closedBall_self (div_nonneg hR0 hsdq.le)
  obtain ⟨g, hgT, hg⟩ := hT.exists_isMaxOn ⟨0, h0T⟩ hFc.continuousOn
  refine ⟨g, fun c => ?_⟩
  by_cases hc : OTDRO.Dual.Fobj ℓ A δ 0 β lam x ≤ OTDRO.Dual.Fobj ℓ A δ c β lam x
  · have hb := superlevel_bound ℓ A δ hδ β lam x hq s M hM hs c hc
    have hcT : c ∈ T := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, le_div_iff₀ hsdq]
      calc |c| * (Real.sqrt δ * OTDRO.Dual.quadInv A β x)
          = |c| * |Real.sqrt δ * OTDRO.Dual.quadInv A β x| := by rw [abs_of_pos hsdq]
        _ = |c * Real.sqrt δ * OTDRO.Dual.quadInv A β x| := by rw [mul_assoc, abs_mul c]
        _ ≤ R := hb
    exact hg hcT
  · push Not at hc
    exact (hc.le.trans (hg h0T))

/-- pointwise Lemma 1(b): `F` is unbounded above -/
lemma lemma1b_unbdd (ℓ : ℝ → ℝ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : EuclideanSpace ℝ (Fin d))
    (hlt : lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x) (N : ℝ) :
    ∃ γ, N < OTDRO.Dual.Fobj ℓ A δ γ β lam x := by
  have hk := kappa_nonneg ℓ h
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set q := OTDRO.Dual.quadInv A β x with hqdef
  have hq : 0 < q := by
    by_contra hq; push Not at hq
    have : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hq
    linarith
  have hsdq : 0 < Real.sqrt δ * q := mul_pos hsd hq
  set r := lam / (Real.sqrt δ * q) with hr
  have hr0 : 0 ≤ r := div_nonneg hlam hsdq.le
  have hrk : r < OTDRO.Dual.growthKappa ℓ := by
    rw [hr, div_lt_iff₀ hsdq]; linarith
  set s' := (r + OTDRO.Dual.growthKappa ℓ) / 2
  have hs'1 : r < s' := by simp only [s']; linarith
  have hs'2 : s' < OTDRO.Dual.growthKappa ℓ := by simp only [s']; linarith
  have hnot : ¬ BddAbove (Set.range fun u : ℝ => ℓ u - s' * u ^ 2) := by
    intro hb
    have : OTDRO.Dual.growthKappa ℓ ≤ s' := csInf_le (growth_set_bddBelow ℓ) ⟨by linarith, hb⟩
    linarith
  set a : ℝ := inner ℝ β x
  set e := s' - r
  have he : 0 < e := by simp only [e]; linarith
  rw [not_bddAbove_iff] at hnot
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := hnot (N + (r * a) ^ 2 / e + r * a ^ 2)
  refine ⟨(u - a) / (Real.sqrt δ * q), ?_⟩
  rw [Fobj_eq ℓ A δ _ hδ β lam x hq]
  rw [← hqdef, ← hr]
  have ht : (u - a) / (Real.sqrt δ * q) * Real.sqrt δ * q = u - a := by
    field_simp
  rw [ht]
  have hlow : -((r * a) ^ 2 / e) ≤ e * u ^ 2 + 2 * r * a * u := by
    rw [neg_le, le_div_iff₀ he]
    nlinarith [sq_nonneg (e * u + r * a)]
  have : lam * Real.sqrt δ ≥ 0 := by positivity
  simp only at hu
  have hsplit : ℓ (a + (u - a)) - r * (u - a) ^ 2 =
      (ℓ u - s' * u ^ 2) + (e * u ^ 2 + 2 * r * a * u) - r * a ^ 2 := by
    simp only [e]; ring_nf
  rw [hsplit]
  linarith

lemma lemma1b (ℓ : ℝ → ℝ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : EuclideanSpace ℝ (Fin d))
    (hlt : lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x) :
    OTDRO.Dual.maximizers ℓ A δ β lam x = ∅ ∧ OTDRO.Dual.ellRob ℓ A δ β lam x = ⊤ := by
  constructor
  · ext g
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hg
    obtain ⟨γ, hγ⟩ := lemma1b_unbdd ℓ h A δ hδ β lam hlam x hlt (OTDRO.Dual.Fobj ℓ A δ g β lam x)
    exact absurd (hg γ) (not_le.2 hγ)
  · rw [EReal.eq_top_iff_forall_lt]
    intro y
    obtain ⟨γ, hγ⟩ := lemma1b_unbdd ℓ h A δ hδ β lam hlam x hlt y
    unfold OTDRO.Dual.ellRob
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hγ) (le_iSup (fun γ => ((OTDRO.Dual.Fobj ℓ A δ γ β lam x : ℝ) : EReal)) γ)

lemma ellRob_ge (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : EuclideanSpace ℝ (Fin d)) :
    ((ℓ (inner ℝ β x) : ℝ) : EReal) ≤ OTDRO.Dual.ellRob ℓ A δ β lam x := by
  unfold OTDRO.Dual.ellRob
  refine le_trans ?_ (le_iSup (fun γ => ((OTDRO.Dual.Fobj ℓ A δ γ β lam x : ℝ) : EReal)) 0)
  apply EReal.coe_le_coe_iff.2
  unfold OTDRO.Dual.Fobj
  have : 0 ≤ lam * Real.sqrt δ := by positivity
  simp; linarith

lemma ellRob_upper (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (Q s r0 M : ℝ)
    (hq0 : 0 ≤ OTDRO.Dual.quadInv A β x) (hqQ : OTDRO.Dual.quadInv A β x ≤ Q)
    (hs0 : 0 ≤ s) (hsr : s < r0) (hr0 : r0 * Real.sqrt δ * Q ≤ lam)
    (hM : ∀ u, ℓ u ≤ M + s * u ^ 2) :
    OTDRO.Dual.ellRob ℓ A δ β lam x ≤
      ((M + s * r0 / (r0 - s) * (inner ℝ β x) ^ 2 + lam * Real.sqrt δ : ℝ) : EReal) := by
  unfold OTDRO.Dual.ellRob
  refine iSup_le fun γ => EReal.coe_le_coe_iff.2 ?_
  unfold OTDRO.Dual.Fobj
  set q := OTDRO.Dual.quadInv A β x
  set a : ℝ := inner ℝ β x
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  set t := γ * Real.sqrt δ * q
  have h1 : r0 * t ^ 2 ≤ lam * Real.sqrt δ * (γ ^ 2 * q) := by
    have : lam * Real.sqrt δ * (γ ^ 2 * q) - r0 * t ^ 2 =
        γ ^ 2 * q * Real.sqrt δ * (lam - r0 * Real.sqrt δ * q) := by
      simp only [t]; ring_nf
    have h2 : 0 ≤ lam - r0 * Real.sqrt δ * q := by
      have : r0 * Real.sqrt δ * q ≤ r0 * Real.sqrt δ * Q :=
        mul_le_mul_of_nonneg_left hqQ (by have : 0 ≤ r0 := by linarith
                                          positivity)
      linarith
    have : 0 ≤ γ ^ 2 * q * Real.sqrt δ * (lam - r0 * Real.sqrt δ * q) := by positivity
    linarith
  have hU := hM (a + t)
  have he : 0 < r0 - s := by linarith
  have h3 : s * (a + t) ^ 2 - r0 * t ^ 2 ≤ s * r0 / (r0 - s) * a ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ he]
    nlinarith [sq_nonneg ((r0 - s) * t - s * a)]
  nlinarith

lemma extIntegral_lt_top_of {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → EReal)
    (h : ∫⁻ x, (φ x).toENNReal ∂ν < ⊤) : ModelRiskOT.Duality.extIntegral ν φ < ⊤ := by
  unfold ModelRiskOT.Duality.extIntegral
  set P := ∫⁻ x, (φ x).toENNReal ∂ν
  set N := ∫⁻ x, (-φ x).toENNReal ∂ν
  lift P to NNReal using h.ne with p
  induction N using ENNReal.recTopCoe with
  | top => simp
  | coe n =>
    rw [EReal.coe_nnreal_eq_coe_real, EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub]
    exact EReal.coe_lt_top _

lemma extIntegral_eq_top_of {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → EReal)
    (hP : ∫⁻ x, (φ x).toENNReal ∂ν = ⊤) (hN : ∫⁻ x, (-φ x).toENNReal ∂ν < ⊤) :
    ModelRiskOT.Duality.extIntegral ν φ = ⊤ := by
  unfold ModelRiskOT.Duality.extIntegral
  rw [hP]
  set N := ∫⁻ x, (-φ x).toENNReal ∂ν
  lift N to NNReal using hN.ne with n
  simp only [EReal.coe_ennreal_top]
  rw [show ((n : ENNReal) : EReal) = ((n : ℝ) : EReal) from rfl]
  exact EReal.top_sub_coe _

lemma integrable_norm_pow {P0 : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P0]
    (h4 : Integrable (fun x => ‖x‖ ^ 4) P0) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ k) P0 := by
  refine Integrable.mono' (h4.add (integrable_const 1)) (by fun_prop) (Filter.Eventually.of_forall ?_)
  intro x
  simp only [norm_pow, Real.norm_eq_abs, abs_norm, Pi.add_apply]
  rcases le_total ‖x‖ 1 with h | h
  · have : ‖x‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) h
    have : 0 ≤ ‖x‖ ^ 4 := by positivity
    linarith
  · have : ‖x‖ ^ k ≤ ‖x‖ ^ 4 := pow_le_pow_right₀ h hk
    linarith

end OTDRO4

open MeasureTheory Matrix

namespace OTDRO4

variable {d : ℕ}

lemma invDir_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (β : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun x => OTDRO.WorstCase.invDir A β x) := by
  have h : Measurable (fun x => ((A x)⁻¹ *ᵥ β.ofLp : Fin d → ℝ)) := by
    apply measurable_pi_lambda; intro i
    simp only [mulVec, dotProduct]
    apply Finset.measurable_sum; intro j _
    exact (inv_entry_measurable A hA hlsc i j).mul_const _
  unfold OTDRO.WorstCase.invDir
  exact (PiLp.continuous_toLp 2 _).measurable.comp h

lemma inner_invDir (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (β x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ β (OTDRO.WorstCase.invDir A β x) = OTDRO.Dual.quadInv A β x := by
  unfold OTDRO.WorstCase.invDir OTDRO.Dual.quadInv
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

lemma mahalCost_shift (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (δ : ℝ) (hδ : 0 ≤ δ) (β : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.mahalCost A x (OTDRO.WorstCase.shiftMap A δ β g x) =
      δ * g x ^ 2 * OTDRO.Dual.quadInv A β x := by
  unfold OTDRO.Dual.mahalCost OTDRO.WorstCase.shiftMap
  have e : (x - (x + (Real.sqrt δ * g x) • OTDRO.WorstCase.invDir A β x)).ofLp =
      (-(Real.sqrt δ * g x)) • ((A x)⁻¹ *ᵥ β.ofLp) := by
    unfold OTDRO.WorstCase.invDir
    ext i; simp
  rw [e, mulVec_smul, smul_dotProduct, dotProduct_smul, mulVec_inv_mulVec _ (hA x)]
  unfold OTDRO.Dual.quadInv
  simp only [smul_eq_mul]
  rw [dotProduct_comm]
  have : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
  linear_combination (g x ^ 2 * dotProduct β.ofLp ((A x)⁻¹ *ᵥ β.ofLp)) * this

lemma mahalCost_nonneg (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (x y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ OTDRO.Dual.mahalCost A x y := by
  unfold OTDRO.Dual.mahalCost
  have := (hA x).posSemidef.dotProduct_mulVec_nonneg (x - y).ofLp
  simpa using this

/-- Cauchy–Schwarz: `(βᵀ(y − x))² ≤ q(x) c(x, y)`. -/
lemma cs_cost (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x y : EuclideanSpace ℝ (Fin d)) :
    (inner ℝ β (y - x)) ^ 2 ≤ OTDRO.Dual.quadInv A β x * OTDRO.Dual.mahalCost A x y := by
  set M := A x
  set w := M⁻¹ *ᵥ β.ofLp
  set v := (x - y).ofLp
  have hMs : Mᵀ = M := by
    have := (hA x).isHermitian
    ext i j
    have h := congrFun (congrFun this i) j
    simpa using h
  -- bilinear form
  set Bf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun u u' => dotProduct u (M *ᵥ u')
  have hsym : ∀ u u', Bf u u' = Bf u' u := by
    intro u u'
    simp only [Bf]
    rw [dotProduct_mulVec, ← mulVec_transpose, hMs, dotProduct_comm]
  have hpos : ∀ u, 0 ≤ Bf u u := by
    intro u
    have := (hA x).posSemidef.dotProduct_mulVec_nonneg u
    simpa using this
  have hq : OTDRO.Dual.quadInv A β x = Bf w w := by
    simp only [Bf, w, M]; rw [mulVec_inv_mulVec _ (hA x), dotProduct_comm]; rfl
  have hc : OTDRO.Dual.mahalCost A x y = Bf v v := rfl
  have hin : inner ℝ β (y - x) = - Bf w v := by
    simp only [Bf, w, v, M]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have : Bf ((A x)⁻¹ *ᵥ β.ofLp) (x - y).ofLp = Bf (x - y).ofLp ((A x)⁻¹ *ᵥ β.ofLp) :=
      hsym _ _
    simp only [Bf] at this
    rw [this, mulVec_inv_mulVec _ (hA x)]
    have e : (y - x).ofLp = -(x - y).ofLp := by ext i; simp
    simp [e, dotProduct_comm]
  rw [hq, hc, hin, neg_sq]
  -- expand Bf (w - t v) (w - t v) ≥ 0
  have hexp : ∀ t : ℝ, Bf (w - t • v) (w - t • v) = Bf w w - 2 * t * Bf w v + t ^ 2 * Bf v v := by
    intro t
    have := hsym v w
    simp only [Bf] at this ⊢
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [this]; ring
  rcases eq_or_lt_of_le (hpos v) with h0 | h0
  · -- `Bf v v = 0` forces `Bf w v = 0`
    have : Bf w v = 0 := by
      by_contra hne
      have ht : 2 * ((Bf w w + 1) / (2 * Bf w v)) * Bf w v = Bf w w + 1 := by field_simp
      have h1 := hpos (w - ((Bf w w + 1) / (2 * Bf w v)) • v)
      rw [hexp, ← h0, ht] at h1
      linarith
    rw [this]; simpa using mul_nonneg (hpos w) (hpos v)
  · have h1 := hpos (w - (Bf w v / Bf v v) • v)
    rw [hexp] at h1
    field_simp at h1
    nlinarith

lemma Fobj_continuous (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun p : ℝ × ℝ => OTDRO.Dual.Fobj ℓ A δ p.1 β p.2 x) := by
  unfold OTDRO.Dual.Fobj; fun_prop

lemma mem_maximizers_iff_rat (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) (g : ℝ) :
    g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x ↔
      ∀ c : ℚ, OTDRO.Dual.Fobj ℓ A δ c β lam x ≤ OTDRO.Dual.Fobj ℓ A δ g β lam x := by
  constructor
  · intro h c; exact h c
  · intro h c
    have hc : Continuous (fun c : ℝ => OTDRO.Dual.Fobj ℓ A δ c β lam x) :=
      (Fobj_continuous ℓ hℓ A δ β x).comp (continuous_id.prodMk continuous_const)
    have hcl : IsClosed {c : ℝ | OTDRO.Dual.Fobj ℓ A δ c β lam x ≤ OTDRO.Dual.Fobj ℓ A δ g β lam x} :=
      isClosed_le hc continuous_const
    have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have : Set.range ((↑) : ℚ → ℝ) ⊆
        {c : ℝ | OTDRO.Dual.Fobj ℓ A δ c β lam x ≤ OTDRO.Dual.Fobj ℓ A δ g β lam x} := by
      rintro _ ⟨r, rfl⟩; exact h r
    have := hd.closure_eq ▸ closure_minimal this hcl
    exact this (Set.mem_univ c)

lemma maximizers_isClosed (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    IsClosed (OTDRO.Dual.maximizers ℓ A δ β lam x) := by
  have hc : Continuous (fun c : ℝ => OTDRO.Dual.Fobj ℓ A δ c β lam x) :=
    (Fobj_continuous ℓ hℓ A δ β x).comp (continuous_id.prodMk continuous_const)
  have : OTDRO.Dual.maximizers ℓ A δ β lam x =
      ⋂ c : ℝ, {g | OTDRO.Dual.Fobj ℓ A δ c β lam x ≤ OTDRO.Dual.Fobj ℓ A δ g β lam x} := by
    ext g; simp [OTDRO.Dual.maximizers]
  rw [this]
  exact isClosed_iInter fun c => isClosed_le continuous_const hc

lemma quadInv_pos (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < OTDRO.Dual.quadInv A β x := by
  unfold OTDRO.Dual.quadInv
  have h := (hA x).inv.dotProduct_mulVec_pos (x := β.ofLp) (by
    intro h0; apply hβ; ext i; simpa using congrFun h0 i)
  simpa using h

lemma Fobj_comp_measurable (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) :
    Measurable (fun x => OTDRO.Dual.Fobj ℓ A δ (h x) β lam x) := by
  have hq := quadInv_measurable A hA hlsc β
  have hin : Measurable (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ β x) :=
    (continuous_const.inner continuous_id).measurable
  unfold OTDRO.Dual.Fobj
  exact (hℓ.measurable.comp (hin.add ((hh.mul_const _).mul hq))).sub
    (measurable_const.mul (((hh.pow_const 2).mul hq).sub measurable_const))

/-- measurable selection of a prescribed square from the maximizer set -/
lemma select_sq (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : AEMeasurable V P0)
    (hmem : ∀ᵐ x ∂P0, ∃ g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x, g ^ 2 = V x) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, Measurable G ∧
      ∀ᵐ x ∂P0, G x ∈ OTDRO.Dual.maximizers ℓ A δ β lam x ∧ G x ^ 2 = V x := by
  set V' := hV.mk V
  have hV'm : Measurable V' := hV.measurable_mk
  have hVV' : V =ᵐ[P0] V' := hV.ae_eq_mk
  set C := ⋂ c : ℚ, {x | OTDRO.Dual.Fobj ℓ A δ c β lam x ≤
      OTDRO.Dual.Fobj ℓ A δ (Real.sqrt (V' x)) β lam x}
  have hC : MeasurableSet C := by
    apply MeasurableSet.iInter; intro c
    exact measurableSet_le (Fobj_comp_measurable ℓ hℓ A hA hlsc δ β lam _ measurable_const)
      (Fobj_comp_measurable ℓ hℓ A hA hlsc δ β lam _ hV'm.sqrt)
  classical
  refine ⟨fun x => if x ∈ C then Real.sqrt (V' x) else -Real.sqrt (V' x),
    Measurable.ite hC hV'm.sqrt hV'm.sqrt.neg, ?_⟩
  filter_upwards [hmem, hVV'] with x hx hxe
  obtain ⟨g, hg, hg2⟩ := hx
  have hV0 : 0 ≤ V' x := by rw [← hxe, ← hg2]; positivity
  have hsq : Real.sqrt (V' x) ^ 2 = V' x := Real.sq_sqrt hV0
  have hgpm : g = Real.sqrt (V' x) ∨ g = -Real.sqrt (V' x) := by
    have : g ^ 2 = Real.sqrt (V' x) ^ 2 := by rw [hsq, ← hxe, hg2]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  have hmemC : x ∈ C ↔ Real.sqrt (V' x) ∈ OTDRO.Dual.maximizers ℓ A δ β lam x := by
    rw [mem_maximizers_iff_rat ℓ hℓ]
    simp [C]
  by_cases hxC : x ∈ C
  · simp only [hxC, if_true]
    exact ⟨hmemC.1 hxC, by rw [hsq, hxe]⟩
  · simp only [hxC, if_false]
    refine ⟨?_, by rw [neg_sq, hsq, hxe]⟩
    rcases hgpm with h | h
    · exact absurd (hmemC.2 (h ▸ hg)) hxC
    · exact h ▸ hg

lemma maximizers_compact (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hb : BddAbove ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)) :
    IsCompact (OTDRO.Dual.maximizers ℓ A δ β lam x) := by
  obtain ⟨b, hb⟩ := hb
  apply Metric.isCompact_of_isClosed_isBounded (maximizers_isClosed ℓ hℓ A δ β lam x)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt b, fun g hg => ?_⟩
  have := hb ⟨g, hg, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact Real.abs_le_sqrt this

lemma shiftMap_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (δ : ℝ) (β : EuclideanSpace ℝ (Fin d))
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : Measurable G) :
    Measurable (fun x => (x, OTDRO.WorstCase.shiftMap A δ β G x)) := by
  unfold OTDRO.WorstCase.shiftMap
  exact measurable_id.prodMk (measurable_id.add
    ((measurable_const.mul hG).smul (invDir_measurable A hA hlsc β)))

lemma graph_map_fst (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : Measurable (fun x => (x, T x))) :
    (OTDRO.WorstCase.graphCoupling P0 T).map Prod.fst = P0 := by
  unfold OTDRO.WorstCase.graphCoupling
  rw [Measure.map_map measurable_fst hT]
  exact Measure.map_id

lemma mixture_eq (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (Gm Gp : EuclideanSpace ℝ (Fin d) → ℝ) (w : ℝ)
    (hw : OTDRO.WorstCase.bernoulliWeight (OTDRO.WorstCase.sqMoment P0 A β Gp)
      (OTDRO.WorstCase.sqMoment P0 A β Gm) = w) :
    OTDRO.WorstCase.mixtureCoupling P0 A δ β Gm Gp =
      ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 (OTDRO.WorstCase.shiftMap A δ β Gm) +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 (OTDRO.WorstCase.shiftMap A δ β Gp) := by
  unfold OTDRO.WorstCase.mixtureCoupling; rw [hw]

lemma cost_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2) := hlsc.measurable

lemma extIntegral_of_integrable {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ)
    (hφ : Integrable φ ν) :
    ModelRiskOT.Duality.extIntegral ν (fun p => (φ p : EReal)) = ((∫ p, φ p ∂ν : ℝ) : EReal) := by
  unfold ModelRiskOT.Duality.extIntegral
  have e1 : ∀ p, ((φ p : ℝ) : EReal).toENNReal = ENNReal.ofReal (φ p) := fun p => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have e2 : ∀ p, (-((φ p : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-φ p) := fun p => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  simp_rw [e1, e2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ]
  have h1 : ∫⁻ p, ENNReal.ofReal (φ p) ∂ν ≠ ⊤ := (hφ.lintegral_lt_top).ne
  have h2 : ∫⁻ p, ENNReal.ofReal (-φ p) ∂ν ≠ ⊤ := (hφ.neg.lintegral_lt_top).ne
  lift (∫⁻ p, ENNReal.ofReal (φ p) ∂ν) to NNReal using h1 with P
  lift (∫⁻ p, ENNReal.ofReal (-φ p) ∂ν) to NNReal using h2 with N
  simp only [ENNReal.coe_toReal]
  rw [EReal.coe_nnreal_eq_coe_real, EReal.coe_nnreal_eq_coe_real, EReal.coe_sub]

lemma extIntegral_congr_ae {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ ψ : X → EReal)
    (h : φ =ᵐ[ν] ψ) :
    ModelRiskOT.Duality.extIntegral ν φ = ModelRiskOT.Duality.extIntegral ν ψ := by
  unfold ModelRiskOT.Duality.extIntegral
  rw [lintegral_congr_ae (h.mono fun x hx => show (φ x).toENNReal = (ψ x).toENNReal by rw [hx]),
    lintegral_congr_ae (h.mono fun x hx => show (-φ x).toENNReal = (-ψ x).toENNReal by rw [hx])]

lemma extIntegral_parts_finite {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → EReal)
    (h1 : ModelRiskOT.Duality.extIntegral ν φ ≠ ⊤) (h2 : ModelRiskOT.Duality.extIntegral ν φ ≠ ⊥) :
    ∫⁻ x, (φ x).toENNReal ∂ν < ⊤ ∧ ∫⁻ x, (-φ x).toENNReal ∂ν < ⊤ := by
  unfold ModelRiskOT.Duality.extIntegral at h1 h2
  generalize ∫⁻ x, (φ x).toENNReal ∂ν = P at h1 h2 ⊢
  generalize ∫⁻ x, (-φ x).toENNReal ∂ν = N at h1 h2 ⊢
  induction N using ENNReal.recTopCoe with
  | top =>
    exfalso; apply h2
    rw [EReal.coe_ennreal_top]; exact EReal.sub_top _
  | coe n =>
    refine ⟨?_, ENNReal.coe_lt_top⟩
    induction P using ENNReal.recTopCoe with
    | top =>
      exfalso; apply h1
      rw [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real]
      exact EReal.top_sub_coe _
    | coe p => exact ENNReal.coe_lt_top

/-- integrability from finite positive and negative lower integrals -/
lemma integrable_of_parts {X : Type*} [MeasurableSpace X] (ν : Measure X) (R : X → ℝ)
    (hm : AEStronglyMeasurable R ν)
    (hP : ∫⁻ x, ENNReal.ofReal (R x) ∂ν < ⊤) (hN : ∫⁻ x, ENNReal.ofReal (-R x) ∂ν < ⊤) :
    Integrable R ν := by
  refine ⟨hm, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ x, ‖R x‖ₑ = ENNReal.ofReal (R x) + ENNReal.ofReal (-R x) := by
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs]
    rcases le_total 0 (R x) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (show -R x ≤ 0 by linarith), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  simp_rw [e]
  calc ∫⁻ x, ENNReal.ofReal (R x) + ENNReal.ofReal (-R x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (R x) ∂ν + ∫⁻ x, ENNReal.ofReal (-R x) ∂ν :=
        (lintegral_add_left' hm.aemeasurable.ennreal_ofReal _).le
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hP, hN⟩

lemma pointwise_dual (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hlam : 0 ≤ lam) (x : EuclideanSpace ℝ (Fin d)) (hq : 0 < OTDRO.Dual.quadInv A β x) (g : ℝ)
    (hg : g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x) (y : EuclideanSpace ℝ (Fin d)) :
    ℓ (inner ℝ β y) ≤ OTDRO.Dual.Fobj ℓ A δ g β lam x - lam * Real.sqrt δ +
      lam / Real.sqrt δ * OTDRO.Dual.mahalCost A x y := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  set q := OTDRO.Dual.quadInv A β x
  set b := inner ℝ β (y - x)
  have hcs : b ^ 2 ≤ q * OTDRO.Dual.mahalCost A x y := cs_cost A hA β x y
  set γ := b / (Real.sqrt δ * q)
  have h := hg γ
  unfold OTDRO.Dual.Fobj at h
  have e1 : inner ℝ β x + γ * Real.sqrt δ * q = inner ℝ β y := by
    have : γ * Real.sqrt δ * q = b := by simp only [γ]; field_simp
    rw [this]; simp only [b, inner_sub_right]; ring
  rw [e1] at h
  have e2 : lam * Real.sqrt δ * (γ ^ 2 * q - 1) = lam / Real.sqrt δ * (b ^ 2 / q) - lam * Real.sqrt δ := by
    simp only [γ]; field_simp
  rw [e2] at h
  have h3 : b ^ 2 / q ≤ OTDRO.Dual.mahalCost A x y := by
    rw [div_le_iff₀ hq]; linarith
  have h4 : lam / Real.sqrt δ * (b ^ 2 / q) ≤ lam / Real.sqrt δ * OTDRO.Dual.mahalCost A x y :=
    mul_le_mul_of_nonneg_left h3 (div_nonneg hlam hsd.le)
  unfold OTDRO.Dual.Fobj
  linarith

lemma weak_duality (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2))
    (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ) (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (hlam : 0 ≤ lam) (R : EuclideanSpace ℝ (Fin d) → ℝ) (hR : Integrable R P0)
    (hpt : ∀ᵐ x ∂P0, ∀ y, ℓ (inner ℝ β y) ≤ R x - lam * Real.sqrt δ +
      lam / Real.sqrt δ * OTDRO.Dual.mahalCost A x y)
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (hπ : π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ) :
    ModelRiskOT.Duality.primalObj (fun y => ℓ (inner ℝ β y)) π ≤ ((∫ x, R x ∂P0 : ℝ) : EReal) := by
  obtain ⟨hprob, hmarg, hcost⟩ := hπ
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set c := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    OTDRO.Dual.mahalCost A p.1 p.2
  have hcm : Measurable c := hlsc.measurable
  have hc0 : ∀ p, 0 ≤ c p := fun p => mahalCost_nonneg A hA p.1 p.2
  have hcint : Integrable c π := by
    refine ⟨hcm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ p, ‖c p‖ₑ = ENNReal.ofReal (c p) := fun p => by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hc0 p)]
    simp_rw [this]
    exact lt_of_le_of_lt hcost ENNReal.ofReal_lt_top
  have hcle : ∫ p, c p ∂π ≤ δ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hc0)
      hcm.aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcost
    rwa [ENNReal.toReal_ofReal hδ.le] at this
  have hRπ : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => R p.1) π := by
    rw [← hmarg] at hR
    exact (integrable_map_measure hR.aestronglyMeasurable measurable_fst.aemeasurable).1 hR
  set ψ := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    R p.1 - lam * Real.sqrt δ + lam / Real.sqrt δ * c p
  have hψ : Integrable ψ π := (hRπ.sub (integrable_const _)).add (hcint.const_mul _)
  have hpt' : ∀ᵐ p ∂π, ℓ (inner ℝ β p.2) ≤ ψ p := by
    rw [← hmarg] at hpt
    have := ae_of_ae_map measurable_fst.aemeasurable hpt
    filter_upwards [this] with p hp
    exact hp p.2
  set φ := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ℓ (inner ℝ β p.2)
  have hφm : Measurable φ :=
    hℓ.measurable.comp ((continuous_const.inner continuous_id).measurable.comp measurable_snd)
  have hψint : ∫ p, ψ p ∂π ≤ ∫ x, R x ∂P0 := by
    have e : ∫ p, ψ p ∂π = ∫ p, R p.1 ∂π - lam * Real.sqrt δ + lam / Real.sqrt δ * ∫ p, c p ∂π := by
      simp only [ψ]
      rw [integral_add (f := fun p => R p.1 - lam * Real.sqrt δ) (g := fun p => lam / Real.sqrt δ * c p)
        (hRπ.sub (integrable_const _)) (hcint.const_mul _),
        integral_const_mul]
      have i1 : ∫ p, (R p.1 - lam * Real.sqrt δ) ∂π = ∫ p, R p.1 ∂π - lam * Real.sqrt δ := by
        rw [integral_sub hRπ (integrable_const _)]; simp
      rw [i1]
    have e2 : ∫ p, R p.1 ∂π = ∫ x, R x ∂P0 := by
      have := integral_map (μ := π) measurable_fst.aemeasurable (f := R)
        (by rw [hmarg]; exact hR.aestronglyMeasurable)
      rw [hmarg] at this; exact this.symm
    have h5 : lam / Real.sqrt δ * ∫ p, c p ∂π ≤ lam / Real.sqrt δ * δ :=
      mul_le_mul_of_nonneg_left hcle (div_nonneg hlam hsd.le)
    have h6 : lam / Real.sqrt δ * δ = lam * Real.sqrt δ := by
      rw [div_mul_eq_mul_div, div_eq_iff hsd.ne', mul_assoc, Real.mul_self_sqrt hδ.le]
    rw [e, e2]; linarith
  unfold ModelRiskOT.Duality.primalObj ModelRiskOT.Duality.extIntegral
  have e1 : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ((φ p : ℝ) : EReal).toENNReal = ENNReal.ofReal (φ p) := fun p => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have e2 : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      (-((φ p : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-φ p) := fun p => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  change ((∫⁻ p, ((φ p : ℝ) : EReal).toENNReal ∂π : ENNReal) : EReal) -
      ((∫⁻ p, (-((φ p : ℝ) : EReal)).toENNReal ∂π : ENNReal) : EReal) ≤ _
  simp_rw [e1, e2]
  by_cases hN : ∫⁻ p, ENNReal.ofReal (-φ p) ∂π = ⊤
  · rw [hN, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
  · have hP : ∫⁻ p, ENNReal.ofReal (φ p) ∂π < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono_ae ?_) hψ.lintegral_lt_top
      filter_upwards [hpt'] with p hp
      exact ENNReal.ofReal_le_ofReal hp
    have hφi : Integrable φ π :=
      integrable_of_parts π φ hφm.aestronglyMeasurable hP (lt_top_iff_ne_top.2 hN)
    have := extIntegral_of_integrable π φ hφi
    unfold ModelRiskOT.Duality.extIntegral at this
    simp_rw [e1, e2] at this
    rw [this]
    exact EReal.coe_le_coe_iff.2 ((integral_mono_ae hφi hψ hpt').trans hψint)

section Mixture

variable (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
  (T1 T2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (h1 : Measurable (fun x => (x, T1 x))) (h2 : Measurable (fun x => (x, T2 x)))
  (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)

include h1 h2 hw0 hw1 in
lemma mix_prob :
    IsProbabilityMeasure (ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 T1 +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 T2) := by
  have p1 : IsProbabilityMeasure (OTDRO.WorstCase.graphCoupling P0 T1) :=
    Measure.isProbabilityMeasure_map h1.aemeasurable
  have p2 : IsProbabilityMeasure (OTDRO.WorstCase.graphCoupling P0 T2) :=
    Measure.isProbabilityMeasure_map h2.aemeasurable
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hw0 (by linarith)]
  simp

include h1 h2 hw0 hw1 in
lemma mix_marg :
    (ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 T1 +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 T2).map Prod.fst = P0 := by
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    graph_map_fst P0 T1 h1, graph_map_fst P0 T2 h2, ← add_smul,
    ← ENNReal.ofReal_add hw0 (by linarith)]
  simp

include h1 h2 in
lemma mix_lintegral (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ p, f p ∂(ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 T1 +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 T2) =
      ENNReal.ofReal w * ∫⁻ x, f (x, T1 x) ∂P0 + ENNReal.ofReal (1 - w) * ∫⁻ x, f (x, T2 x) ∂P0 := by
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  unfold OTDRO.WorstCase.graphCoupling
  rw [lintegral_map hf h1, lintegral_map hf h2]
  rfl

include h1 h2 hw0 hw1 in
lemma mix_integral (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Measurable f) (i1 : Integrable (fun x => f (x, T1 x)) P0)
    (i2 : Integrable (fun x => f (x, T2 x)) P0) :
    Integrable f (ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 T1 +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 T2) ∧
    ∫ p, f p ∂(ENNReal.ofReal w • OTDRO.WorstCase.graphCoupling P0 T1 +
      ENNReal.ofReal (1 - w) • OTDRO.WorstCase.graphCoupling P0 T2) =
      w * ∫ x, f (x, T1 x) ∂P0 + (1 - w) * ∫ x, f (x, T2 x) ∂P0 := by
  have j1 : Integrable f (OTDRO.WorstCase.graphCoupling P0 T1) :=
    (integrable_map_measure hf.aestronglyMeasurable h1.aemeasurable).2 i1
  have j2 : Integrable f (OTDRO.WorstCase.graphCoupling P0 T2) :=
    (integrable_map_measure hf.aestronglyMeasurable h2.aemeasurable).2 i2
  have k1 := j1.smul_measure (ENNReal.ofReal_ne_top (r := w))
  have k2 := j2.smul_measure (ENNReal.ofReal_ne_top (r := 1 - w))
  refine ⟨k1.add_measure k2, ?_⟩
  rw [integral_add_measure k1 k2, integral_smul_measure, integral_smul_measure]
  unfold OTDRO.WorstCase.graphCoupling
  rw [integral_map h1.aemeasurable hf.aestronglyMeasurable,
    integral_map h2.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hw0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

end Mixture

end OTDRO4

open Filter Topology

namespace OTDRO4.Danskin

/-- `Φ(γ, l) = Ψ(γ) − l (c₁γ² − c₀)` -/
def Phi (Ψ : ℝ → ℝ) (c1 c0 γ l : ℝ) : ℝ := Ψ γ - l * (c1 * γ ^ 2 - c0)

def IsMx (Ψ : ℝ → ℝ) (c1 c0 l γ : ℝ) : Prop := ∀ c, Phi Ψ c1 c0 c l ≤ Phi Ψ c1 c0 γ l

noncomputable def V (Ψ : ℝ → ℝ) (c1 c0 l : ℝ) : ℝ := ⨆ c, Phi Ψ c1 c0 c l

section
variable {Ψ : ℝ → ℝ} {c1 c0 : ℝ}

lemma Phi_shift (γ l l' : ℝ) :
    Phi Ψ c1 c0 γ l' = Phi Ψ c1 c0 γ l - (l' - l) * (c1 * γ ^ 2 - c0) := by
  unfold Phi; ring

lemma V_eq {l γ : ℝ} (h : IsMx Ψ c1 c0 l γ) : V Ψ c1 c0 l = Phi Ψ c1 c0 γ l :=
  le_antisymm (ciSup_le h) (le_ciSup ⟨_, by rintro _ ⟨c, rfl⟩; exact h c⟩ γ)

lemma V_ge {l γ : ℝ} {γ' : ℝ} (h : IsMx Ψ c1 c0 l γ') : Phi Ψ c1 c0 γ l ≤ V Ψ c1 c0 l := by
  rw [V_eq h]; exact h γ

variable (hΨ : Continuous Ψ) (hc1 : 0 < c1) {lam lam0 R : ℝ} (hl0 : lam0 < lam)
  (hex : ∀ l, lam0 ≤ l → ∃ γ, IsMx Ψ c1 c0 l γ)
  (hbd : ∀ l, lam0 ≤ l → ∀ γ, IsMx Ψ c1 c0 l γ → |γ| ≤ R)

include hΨ hl0 hex hbd in
lemma mx_compact : IsCompact {γ | IsMx Ψ c1 c0 lam γ} := by
  have hc : Continuous (fun γ => Phi Ψ c1 c0 γ lam) := by unfold Phi; fun_prop
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {γ | IsMx Ψ c1 c0 lam γ} = ⋂ c, {γ | Phi Ψ c1 c0 c lam ≤ Phi Ψ c1 c0 γ lam} := by
      ext γ; simp [IsMx]
    rw [this]; exact isClosed_iInter fun c => isClosed_le continuous_const hc
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨R, fun γ hγ => by
      simpa [Real.norm_eq_abs] using hbd lam hl0.le γ hγ⟩

include hΨ hl0 hex hbd in
lemma sq_attained :
    let S := (fun g : ℝ => g ^ 2) '' {γ | IsMx Ψ c1 c0 lam γ}
    sInf S ∈ S ∧ sSup S ∈ S ∧ BddAbove S ∧ BddBelow S := by
  intro S
  have hc : IsCompact S := (mx_compact hΨ hl0 hex hbd).image (continuous_pow 2)
  obtain ⟨γ, hγ⟩ := hex lam hl0.le
  have hne : S.Nonempty := ⟨γ ^ 2, γ, hγ, rfl⟩
  exact ⟨hc.sInf_mem hne, hc.sSup_mem hne, hc.bddAbove, hc.bddBelow⟩

include hΨ hc1 hl0 hex hbd in
/-- right derivative -/
lemma right_deriv :
    let m := sInf ((fun g : ℝ => g ^ 2) '' {γ | IsMx Ψ c1 c0 lam γ})
    Tendsto (fun l => (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam)) (𝓝[>] lam)
      (𝓝 (c0 - c1 * m)) := by
  intro m
  obtain ⟨hmS, -, -, hbb⟩ := sq_attained hΨ hl0 hex hbd
  obtain ⟨gm, hgm, hgm2⟩ := hmS
  simp only at hgm2
  have hVlam := V_eq hgm
  -- lower bound
  have hlow : ∀ l, lam < l → c0 - c1 * m ≤ (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam) := by
    intro l hl
    obtain ⟨γ, hγ⟩ := hex l (by linarith)
    have h1 := V_ge (γ := gm) hγ
    rw [Phi_shift gm lam l, ← hVlam, hgm2] at h1
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  -- upper bound via maximizers
  have hup : ∀ l, lam < l → ∀ γ, IsMx Ψ c1 c0 l γ →
      (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam) ≤ c0 - c1 * γ ^ 2 := by
    intro l hl γ hγ
    have h1 := V_eq hγ
    have h2 : Phi Ψ c1 c0 γ lam ≤ V Ψ c1 c0 lam := V_ge hgm
    rw [Phi_shift γ lam l] at h1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- maximizers near `lam` have square close to at least `m`
  have hnear : ∀ ε > 0, ∀ᶠ l in 𝓝[>] lam, ∀ γ, IsMx Ψ c1 c0 l γ → m - ε < γ ^ 2 := by
    intro ε hε
    set K := {γ : ℝ | |γ| ≤ R ∧ γ ^ 2 ≤ m - ε}
    have hKc : IsCompact K := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact (isClosed_le continuous_abs continuous_const).inter
          (isClosed_le (continuous_pow 2) continuous_const)
      · rw [Metric.isBounded_iff_subset_closedBall 0]
        exact ⟨R, fun γ hγ => by simpa [Real.norm_eq_abs] using hγ.1⟩
    rcases K.eq_empty_or_nonempty with hK | hK
    · filter_upwards [self_mem_nhdsWithin] with l hl γ hγ
      by_contra hc; push Not at hc
      have : γ ∈ K := ⟨hbd l (by simp at hl; linarith) γ hγ, hc⟩
      rw [hK] at this; exact this
    have hc : Continuous (fun γ => Phi Ψ c1 c0 γ lam) := by unfold Phi; fun_prop
    obtain ⟨γ0, hγ0K, hγ0⟩ := hKc.exists_isMaxOn hK hc.continuousOn
    have hγ0n : ¬ IsMx Ψ c1 c0 lam γ0 := by
      intro h
      have : m ≤ γ0 ^ 2 := csInf_le hbb ⟨γ0, h, rfl⟩
      linarith [hγ0K.2]
    have hη0 : Phi Ψ c1 c0 γ0 lam < V Ψ c1 c0 lam := by
      by_contra hc; push Not at hc
      apply hγ0n; intro c
      exact (V_ge (γ := c) hgm).trans hc
    set η0 := V Ψ c1 c0 lam - Phi Ψ c1 c0 γ0 lam
    have hη0p : 0 < η0 := by simp only [η0]; linarith
    have hm0 : 0 ≤ m := by have := sq_nonneg gm; rw [hgm2] at this; exact this
    have hmem : Set.Ioo lam (lam + η0 / (c1 * m + 1)) ∈ 𝓝[>] lam :=
      Ioo_mem_nhdsGT (by have : 0 < η0 / (c1 * m + 1) := by positivity
                         linarith)
    filter_upwards [hmem] with l hl γ hγ
    by_contra hcon; push Not at hcon
    have hγK : γ ∈ K := ⟨hbd l (by linarith [hl.1]) γ hγ, hcon⟩
    have h1 := V_eq hγ
    rw [Phi_shift γ lam l] at h1
    have h2 : Phi Ψ c1 c0 γ lam ≤ Phi Ψ c1 c0 γ0 lam := hγ0 hγK
    have h3 := V_ge (γ := gm) hγ
    rw [Phi_shift gm lam l, ← hVlam, hgm2] at h3
    have hlt : (l - lam) * (c1 * m + 1) < η0 := by
      have := hl.2
      rw [← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)] at this
      exact this
    have hsq : 0 ≤ c1 * γ ^ 2 := by positivity
    have hlpos : 0 < l - lam := by linarith [hl.1]
    nlinarith
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact lt_of_lt_of_le ha (hlow l hl)
  · intro b hb
    have hε : 0 < (b - (c0 - c1 * m)) / (2 * c1) := by
      apply div_pos (by linarith) (by linarith)
    filter_upwards [hnear _ hε, self_mem_nhdsWithin] with l hl hl'
    obtain ⟨γ, hγ⟩ := hex l (by simp at hl'; linarith)
    have h1 := hup l hl' γ hγ
    have h2 := hl γ hγ
    have : c1 * (m - (b - (c0 - c1 * m)) / (2 * c1)) < c1 * γ ^ 2 :=
      mul_lt_mul_of_pos_left h2 hc1
    have e : c1 * (m - (b - (c0 - c1 * m)) / (2 * c1)) = c1 * m - (b - (c0 - c1 * m)) / 2 := by
      field_simp
    linarith

include hΨ hc1 hl0 hex hbd in
/-- left derivative -/
lemma left_deriv :
    let M := sSup ((fun g : ℝ => g ^ 2) '' {γ | IsMx Ψ c1 c0 lam γ})
    Tendsto (fun l => (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam)) (𝓝[<] lam)
      (𝓝 (c0 - c1 * M)) := by
  intro M
  obtain ⟨-, hMS, hba, -⟩ := sq_attained hΨ hl0 hex hbd
  obtain ⟨gp, hgp, hgp2⟩ := hMS
  simp only at hgp2
  have hVlam := V_eq hgp
  have hup : ∀ l, lam0 ≤ l → l < lam →
      (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam) ≤ c0 - c1 * M := by
    intro l hl0' hl
    obtain ⟨γ, hγ⟩ := hex l hl0'
    have h1 := V_ge (γ := gp) hγ
    rw [Phi_shift gp lam l, ← hVlam, hgp2] at h1
    rw [div_le_iff_of_neg (by linarith)]
    nlinarith
  have hlow : ∀ l, l < lam → ∀ γ, IsMx Ψ c1 c0 l γ →
      c0 - c1 * γ ^ 2 ≤ (V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam) := by
    intro l hl γ hγ
    have h1 := V_eq hγ
    have h2 : Phi Ψ c1 c0 γ lam ≤ V Ψ c1 c0 lam := V_ge hgp
    rw [Phi_shift γ lam l] at h1
    rw [le_div_iff_of_neg (by linarith)]
    nlinarith
  have hnear : ∀ ε > 0, ∀ᶠ l in 𝓝[<] lam, ∀ γ, IsMx Ψ c1 c0 l γ → γ ^ 2 < M + ε := by
    intro ε hε
    set K := {γ : ℝ | |γ| ≤ R ∧ M + ε ≤ γ ^ 2}
    have hKc : IsCompact K := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact (isClosed_le continuous_abs continuous_const).inter
          (isClosed_le continuous_const (continuous_pow 2))
      · rw [Metric.isBounded_iff_subset_closedBall 0]
        exact ⟨R, fun γ hγ => by simpa [Real.norm_eq_abs] using hγ.1⟩
    have hmem0 : Set.Ioo lam0 lam ∈ 𝓝[<] lam := Ioo_mem_nhdsLT hl0
    rcases K.eq_empty_or_nonempty with hK | hK
    · filter_upwards [hmem0] with l hl γ hγ
      by_contra hc; push Not at hc
      have : γ ∈ K := ⟨hbd l hl.1.le γ hγ, hc⟩
      rw [hK] at this; exact this
    have hc : Continuous (fun γ => Phi Ψ c1 c0 γ lam) := by unfold Phi; fun_prop
    obtain ⟨γ0, hγ0K, hγ0⟩ := hKc.exists_isMaxOn hK hc.continuousOn
    have hγ0n : ¬ IsMx Ψ c1 c0 lam γ0 := by
      intro h
      have : γ0 ^ 2 ≤ M := le_csSup hba ⟨γ0, h, rfl⟩
      linarith [hγ0K.2]
    have hη0 : Phi Ψ c1 c0 γ0 lam < V Ψ c1 c0 lam := by
      by_contra hc; push Not at hc
      apply hγ0n; intro c
      exact (V_ge (γ := c) hgp).trans hc
    set η0 := V Ψ c1 c0 lam - Phi Ψ c1 c0 γ0 lam
    have hη0p : 0 < η0 := by simp only [η0]; linarith
    have hM0 : 0 ≤ M := by have := sq_nonneg gp; rw [hgp2] at this; exact this
    set C := c1 * R ^ 2 + 2 * |c0| + 1
    have hC : 0 < C := by positivity
    have hmem : Set.Ioo (lam - η0 / C) lam ∈ 𝓝[<] lam :=
      Ioo_mem_nhdsLT (by have : 0 < η0 / C := by positivity
                         linarith)
    filter_upwards [hmem, hmem0] with l hl hl' γ hγ
    by_contra hcon; push Not at hcon
    have hγR := hbd l hl'.1.le γ hγ
    have hγK : γ ∈ K := ⟨hγR, hcon⟩
    have h1 := V_eq hγ
    rw [Phi_shift γ lam l] at h1
    have h2 : Phi Ψ c1 c0 γ lam ≤ Phi Ψ c1 c0 γ0 lam := hγ0 hγK
    have h3 := V_ge (γ := gp) hγ
    rw [Phi_shift gp lam l, ← hVlam, hgp2] at h3
    have hlt : (lam - l) * C < η0 := by
      have := hl.1
      rw [sub_lt_comm, lt_div_iff₀ hC] at this
      linarith
    have hsq : γ ^ 2 ≤ R ^ 2 := by
      have := sq_abs γ ▸ pow_le_pow_left₀ (abs_nonneg γ) hγR 2
      linarith [sq_abs γ]
    have hlpos : 0 < lam - l := by linarith [hl.2]
    have hc0 := le_abs_self c0
    have hc0' := neg_abs_le c0
    have hM1 : 0 ≤ c1 * M := by positivity
    have hR1 : c1 * γ ^ 2 ≤ c1 * R ^ 2 := mul_le_mul_of_nonneg_left hsq hc1.le
    nlinarith
  rw [tendsto_order]
  constructor
  · intro a ha
    have hε : 0 < (c0 - c1 * M - a) / (2 * c1) := div_pos (by linarith) (by linarith)
    filter_upwards [hnear _ hε, self_mem_nhdsWithin, Ioo_mem_nhdsLT hl0] with l hl hl' hl''
    obtain ⟨γ, hγ⟩ := hex l hl''.1.le
    have h1 := hlow l hl' γ hγ
    have h2 := hl γ hγ
    have : c1 * γ ^ 2 < c1 * (M + (c0 - c1 * M - a) / (2 * c1)) := mul_lt_mul_of_pos_left h2 hc1
    have e : c1 * (M + (c0 - c1 * M - a) / (2 * c1)) = c1 * M + (c0 - c1 * M - a) / 2 := by
      field_simp
    linarith
  · intro b hb
    filter_upwards [Ioo_mem_nhdsLT hl0] with l hl
    exact lt_of_le_of_lt (hup l hl.1.le hl.2) hb

include hc1 hl0 hex hbd in
lemma slope_bound (l : ℝ) (hl : lam0 ≤ l) (hne : l ≠ lam) :
    |(V Ψ c1 c0 l - V Ψ c1 c0 lam) / (l - lam)| ≤ |c0| + c1 * R ^ 2 := by
  obtain ⟨γ, hγ⟩ := hex l hl
  obtain ⟨g, hg⟩ := hex lam hl0.le
  have hγR := hbd l hl γ hγ
  have hgR := hbd lam hl0.le g hg
  have hsq : ∀ x : ℝ, |x| ≤ R → c1 * x ^ 2 ≤ c1 * R ^ 2 := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ hc1.le
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
  have h1 := V_eq hγ
  have h2 := V_eq hg
  have h3 : Phi Ψ c1 c0 γ lam ≤ V Ψ c1 c0 lam := V_ge hg
  have h4 : Phi Ψ c1 c0 g l ≤ V Ψ c1 c0 l := V_ge hγ
  rw [Phi_shift γ lam l] at h1
  rw [Phi_shift g lam l, ← h2] at h4
  have hγ2 := hsq γ hγR
  have hg2 := hsq g hgR
  have hγ0 : 0 ≤ c1 * γ ^ 2 := by positivity
  have hg0 : 0 ≤ c1 * g ^ 2 := by positivity
  rw [abs_le]
  rcases lt_or_gt_of_ne hne with h | h
  · have hn : l - lam < 0 := by linarith
    constructor
    · rw [le_div_iff_of_neg hn]; nlinarith [le_abs_self c0, neg_abs_le c0]
    · rw [div_le_iff_of_neg hn]; nlinarith [le_abs_self c0, neg_abs_le c0]
  · have hp : 0 < l - lam := by linarith
    constructor
    · rw [le_div_iff₀ hp]; nlinarith [le_abs_self c0, neg_abs_le c0]
    · rw [div_le_iff₀ hp]; nlinarith [le_abs_self c0, neg_abs_le c0]

end

end OTDRO4.Danskin

open MeasureTheory Filter Topology Matrix

namespace OTDRO4

variable {d : ℕ}

lemma negpart_finite (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (δ : ℝ) :
    ∀ β : EuclideanSpace ℝ (Fin d), ∀ lam : ℝ, 0 ≤ lam →
      ∫⁻ x, (-OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal ∂P0 < ⊤ := by
  intro β lam hlam
  set L := |ℓ 0| + |ℓ 1| + |ℓ (-1)|
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => |ℓ 0| + L * ‖β‖ * ‖x‖) P0 :=
    (integrable_const _).add ((OTDRO4.integrable_norm_pow h2.moment4 1 (by norm_num)).const_mul
      (L * ‖β‖) |>.congr (Filter.Eventually.of_forall fun x => by simp))
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have h1 := OTDRO4.ellRob_ge ℓ A δ β lam hlam x
  have h3 := OTDRO4.convex_lower ℓ h2.convex (inner ℝ β x)
  have h4 : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := abs_real_inner_le_norm β x
  have hL : 0 ≤ L := by positivity
  have h5 : -ℓ (inner ℝ β x) ≤ |ℓ 0| + L * ‖β‖ * ‖x‖ := by
    have := mul_le_mul_of_nonneg_left h4 hL
    have := neg_abs_le (ℓ 0)
    nlinarith
  calc (-OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal
      ≤ (((-ℓ (inner ℝ β x) : ℝ)) : EReal).toENNReal := by
        apply EReal.toENNReal_le_toENNReal
        rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.2 h1
    _ ≤ ENNReal.ofReal (|ℓ 0| + L * ‖β‖ * ‖x‖) := by
        rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]; exact ENNReal.ofReal_le_ofReal h5

lemma fDelta_lt_top (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ)
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ β : EuclideanSpace ℝ (Fin d), ∀ (_ : β ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d)))),
      ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.lamThr P0 ℓ A δ β < lam →
      OTDRO.Dual.fDelta P0 ℓ A δ β lam < ⊤ := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hqbdd : ∀ β : EuclideanSpace ℝ (Fin d),
      ∀ᵐ x ∂P0, OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρmin := by
    intro β
    filter_upwards [hA.eig_bounds] with x hx
    exact OTDRO4.quadInv_le A hA.posDef β x ρmin hA.rhoMin_pos (fun v => (hx v).1)
  have hbu : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
    fun β => Filter.isBoundedUnder_of_eventually_le (hqbdd β)
  intro β _ lam hlam hthr
  apply OTDRO4.extIntegral_lt_top_of
  set Q := essSup (fun x => OTDRO.Dual.quadInv A β x) P0
  have hthr' : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * Q < lam := hthr
  obtain ⟨s, r0, M, hs0, hsr, hr0, hM⟩ : ∃ s r0 M : ℝ, 0 ≤ s ∧ s < r0 ∧
      r0 * Real.sqrt δ * Q ≤ lam ∧ ∀ u, ℓ u ≤ M + s * u ^ 2 := by
    rcases le_or_gt Q 0 with hQ | hQ
    · obtain ⟨s, M, hs0, _, hM⟩ := OTDRO4.exists_growth_lt ℓ h2.growth
        (OTDRO.Dual.growthKappa ℓ + 1) (by linarith)
      refine ⟨s, s + 1, M, hs0, by linarith, ?_, hM⟩
      have : (s + 1) * Real.sqrt δ * Q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ
      linarith
    · have hsdQ : 0 < Real.sqrt δ * Q := mul_pos hsd hQ
      obtain ⟨s, M, hs0, hslt, hM⟩ := OTDRO4.exists_growth_lt ℓ h2.growth
        (lam / (Real.sqrt δ * Q)) (by rw [lt_div_iff₀ hsdQ]; linarith)
      refine ⟨s, lam / (Real.sqrt δ * Q), M, hs0, hslt, ?_, hM⟩
      rw [mul_assoc, div_mul_cancel₀ _ hsdQ.ne']
  set c := s * r0 / (r0 - s)
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      |M| + c * ‖β‖ ^ 2 * ‖x‖ ^ 2 + lam * Real.sqrt δ) P0 :=
    ((integrable_const _).add ((OTDRO4.integrable_norm_pow h2.moment4 2 (by norm_num)).const_mul
      (c * ‖β‖ ^ 2) |>.congr (Filter.Eventually.of_forall fun x => by simp))).add
      (integrable_const _)
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [ae_le_essSup (hbu β)] with x hx
  have h1 := OTDRO4.ellRob_upper ℓ A δ hδ β lam x Q s r0 M
    (OTDRO4.quadInv_nonneg A hA.posDef β x) hx hs0 hsr hr0 hM
  have h4 : (inner ℝ β x) ^ 2 ≤ ‖β‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    have := abs_real_inner_le_norm β x
    have h0 : 0 ≤ |inner ℝ β x| := abs_nonneg _
    calc (inner ℝ β x) ^ 2 = |inner ℝ β x| ^ 2 := (sq_abs _).symm
      _ ≤ (‖β‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ h0 this 2
  have h5 : M + c * (inner ℝ β x) ^ 2 + lam * Real.sqrt δ ≤
      |M| + c * ‖β‖ ^ 2 * ‖x‖ ^ 2 + lam * Real.sqrt δ := by
    have := mul_le_mul_of_nonneg_left h4 hc
    have := le_abs_self M
    nlinarith
  calc (OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal
      ≤ (((M + c * (inner ℝ β x) ^ 2 + lam * Real.sqrt δ : ℝ)) : EReal).toENNReal :=
        EReal.toENNReal_le_toENNReal h1
    _ ≤ ENNReal.ofReal (|M| + c * ‖β‖ ^ 2 * ‖x‖ ^ 2 + lam * Real.sqrt δ) := by
        rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]; exact ENNReal.ofReal_le_ofReal h5

lemma superlevel_bound' (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) (s M r0 : ℝ) (hM : ∀ u, ℓ u ≤ M + s * u ^ 2)
    (hsr : s < r0) (hr : r0 * (Real.sqrt δ * OTDRO.Dual.quadInv A β x) ≤ lam) (γ : ℝ)
    (hγ : OTDRO.Dual.Fobj ℓ A δ 0 β lam x ≤ OTDRO.Dual.Fobj ℓ A δ γ β lam x) :
    |γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x| ≤
      1 + (|2 * s * inner ℝ β x| + |M + s * (inner ℝ β x) ^ 2 - ℓ (inner ℝ β x)|) / (r0 - s) := by
  rw [OTDRO4.Fobj_eq ℓ A δ _ hδ β lam x hq, OTDRO4.Fobj_eq ℓ A δ _ hδ β lam x hq] at hγ
  set q := OTDRO.Dual.quadInv A β x
  set a : ℝ := inner ℝ β x
  have hsdq : 0 < Real.sqrt δ * q := mul_pos (Real.sqrt_pos.2 hδ) hq
  set r := lam / (Real.sqrt δ * q)
  have hr0 : r0 ≤ r := by simp only [r]; rw [le_div_iff₀ hsdq]; exact hr
  set t := γ * Real.sqrt δ * q
  apply OTDRO4.quad_bound
  · linarith
  have hU := hM (a + t)
  simp at hγ
  have : r0 * t ^ 2 ≤ r * t ^ 2 := mul_le_mul_of_nonneg_right hr0 (sq_nonneg t)
  nlinarith

lemma ellRob_eq_iSup_rat (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.ellRob ℓ A δ β lam x = ⨆ c : ℚ, ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal) := by
  unfold OTDRO.Dual.ellRob
  apply le_antisymm
  · apply iSup_le; intro γ
    have hc : Continuous (fun c : ℝ => ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp
        ((OTDRO4.Fobj_continuous ℓ hℓ A δ β x).comp (continuous_id.prodMk continuous_const))
    set S := ⨆ c : ℚ, ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal)
    have hcl : IsClosed {c : ℝ | ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal) ≤ S} :=
      isClosed_le hc continuous_const
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆
        {c : ℝ | ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal) ≤ S} := by
      rintro _ ⟨r, rfl⟩
      exact le_iSup (fun c : ℚ => ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal)) r
    have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have := hd.closure_eq ▸ closure_minimal hsub hcl
    exact this (Set.mem_univ γ)
  · exact iSup_le fun c => le_iSup (fun γ : ℝ => ((OTDRO.Dual.Fobj ℓ A δ γ β lam x : ℝ) : EReal)) c

lemma ellRob_measurable (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Measurable (fun x => OTDRO.Dual.ellRob ℓ A δ β lam x) := by
  simp_rw [ellRob_eq_iSup_rat ℓ hℓ]
  apply Measurable.iSup; intro c
  exact (OTDRO4.Fobj_comp_measurable ℓ hℓ A hA hlsc δ β lam _ measurable_const).coe_real_ereal

lemma quadInv_ge (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), dotProduct v.ofLp (A x *ᵥ v.ofLp) ≤ ρ * ‖v‖ ^ 2) :
    ‖β‖ ^ 2 / ρ ≤ OTDRO.Dual.quadInv A β x := by
  have h := OTDRO4.cs_cost A hA β x (x + β)
  have e1 : x + β - x = β := by abel
  rw [e1, real_inner_self_eq_norm_sq] at h
  have e2 : OTDRO.Dual.mahalCost A x (x + β) = dotProduct β.ofLp (A x *ᵥ β.ofLp) := by
    unfold OTDRO.Dual.mahalCost
    have : (x - (x + β)).ofLp = -β.ofLp := by ext i; simp
    rw [this, Matrix.mulVec_neg]; simp
  rw [e2] at h
  have hb := hx β
  have hq0 := OTDRO4.quadInv_nonneg A hA β x
  have hβ2 : 0 < ‖β‖ ^ 2 := by positivity
  rw [div_le_iff₀ hρ]
  have : (‖β‖ ^ 2) ^ 2 ≤ OTDRO.Dual.quadInv A β x * (ρ * ‖β‖ ^ 2) :=
    h.trans (mul_le_mul_of_nonneg_left hb hq0)
  nlinarith

lemma extIntegral_ne_bot_of {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → EReal)
    (hN : ∫⁻ x, (-φ x).toENNReal ∂ν < ⊤) : ModelRiskOT.Duality.extIntegral ν φ ≠ ⊥ := by
  unfold ModelRiskOT.Duality.extIntegral
  generalize ∫⁻ x, (φ x).toENNReal ∂ν = P
  generalize hN' : ∫⁻ x, (-φ x).toENNReal ∂ν = N at hN
  lift N to NNReal using hN.ne with n
  induction P using ENNReal.recTopCoe with
  | top => rw [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real, EReal.top_sub_coe]; simp
  | coe p =>
    rw [EReal.coe_nnreal_eq_coe_real, EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _

lemma ofReal_toReal_le (e : EReal) : ENNReal.ofReal e.toReal ≤ e.toENNReal := by
  induction e using EReal.rec with
  | bot => simp
  | top => simp
  | coe r => rw [EReal.toReal_coe, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma ofReal_neg_toReal_le (e : EReal) : ENNReal.ofReal (-e.toReal) ≤ (-e).toENNReal := by
  have := ofReal_toReal_le (-e)
  rwa [EReal.toReal_neg_eq] at this

/-- the Danskin data at a point: maximizers coincide, values coincide -/
lemma Phi_eq_Fobj (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β x : EuclideanSpace ℝ (Fin d)) (γ l : ℝ) :
    OTDRO4.Danskin.Phi (fun γ => ℓ (inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x))
      (Real.sqrt δ * OTDRO.Dual.quadInv A β x) (Real.sqrt δ) γ l =
      OTDRO.Dual.Fobj ℓ A δ γ β l x := by
  unfold OTDRO4.Danskin.Phi OTDRO.Dual.Fobj; ring

lemma isMx_iff (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β x : EuclideanSpace ℝ (Fin d)) (γ l : ℝ) :
    OTDRO4.Danskin.IsMx (fun γ => ℓ (inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x))
      (Real.sqrt δ * OTDRO.Dual.quadInv A β x) (Real.sqrt δ) l γ ↔
      γ ∈ OTDRO.Dual.maximizers ℓ A δ β l x := by
  unfold OTDRO4.Danskin.IsMx OTDRO.Dual.maximizers
  simp only [Phi_eq_Fobj, Set.mem_ofPred_eq]

lemma V_eq_ellRob (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β x : EuclideanSpace ℝ (Fin d)) (l : ℝ)
    (hne : (OTDRO.Dual.maximizers ℓ A δ β l x).Nonempty) :
    OTDRO4.Danskin.V (fun γ => ℓ (inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x))
      (Real.sqrt δ * OTDRO.Dual.quadInv A β x) (Real.sqrt δ) l =
      (OTDRO.Dual.ellRob ℓ A δ β l x).toReal ∧
    OTDRO.Dual.ellRob ℓ A δ β l x = ((OTDRO.Dual.ellRob ℓ A δ β l x).toReal : EReal) := by
  obtain ⟨g, hg⟩ := hne
  have h1 := OTDRO4.Danskin.V_eq ((isMx_iff ℓ A δ β x g l).2 hg)
  rw [Phi_eq_Fobj] at h1
  have h2 : OTDRO.Dual.ellRob ℓ A δ β l x = ((OTDRO.Dual.Fobj ℓ A δ g β l x : ℝ) : EReal) := by
    unfold OTDRO.Dual.ellRob
    apply le_antisymm
    · exact iSup_le fun c => EReal.coe_le_coe_iff.2 (hg c)
    · exact le_iSup (fun c => ((OTDRO.Dual.Fobj ℓ A δ c β l x : ℝ) : EReal)) g
  rw [h2, EReal.toReal_coe]
  exact ⟨h1, rfl⟩

end OTDRO4

open MeasureTheory Filter Topology Matrix Set

namespace OTDRO4

variable {d : ℕ}

/-- uniform bound on maximizers for `l ≥ λ₀ > κ√δ q` -/
lemma unif_R (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) (lam0 : ℝ)
    (h0 : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam0) :
    ∃ R : ℝ, ∀ l, lam0 ≤ l → (OTDRO.Dual.maximizers ℓ A δ β l x).Nonempty ∧
      ∀ γ ∈ OTDRO.Dual.maximizers ℓ A δ β l x, |γ| ≤ R := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsdq : 0 < Real.sqrt δ * OTDRO.Dual.quadInv A β x := mul_pos hsd hq
  obtain ⟨s, M, hs0, hslt, hM⟩ := exists_growth_lt ℓ h (lam0 / (Real.sqrt δ * OTDRO.Dual.quadInv A β x))
    (by rw [lt_div_iff₀ hsdq]; linarith)
  set r0 := lam0 / (Real.sqrt δ * OTDRO.Dual.quadInv A β x)
  have hr0 : r0 * (Real.sqrt δ * OTDRO.Dual.quadInv A β x) = lam0 := div_mul_cancel₀ _ hsdq.ne'
  refine ⟨(1 + (|2 * s * inner ℝ β x| + |M + s * (inner ℝ β x) ^ 2 - ℓ (inner ℝ β x)|) / (r0 - s)) /
    (Real.sqrt δ * OTDRO.Dual.quadInv A β x), fun l hl => ⟨?_, fun γ hγ => ?_⟩⟩
  · apply (lemma1a ℓ hℓ A δ hδ β l x hq.le (Or.inr ⟨s, M, hs0, hM, ?_⟩)).1
    rw [lt_div_iff₀ hsdq]
    have := mul_lt_mul_of_pos_right hslt hsdq
    rw [hr0] at this; linarith
  · have hb := superlevel_bound' ℓ A δ hδ β l x hq s M r0 hM hslt (by rw [hr0]; exact hl) γ (hγ 0)
    rw [le_div_iff₀ hsdq]
    rw [mul_assoc, abs_mul, abs_of_pos hsdq] at hb
    exact hb

/-- The pointwise Proposition 2 for `q > 0`. -/
lemma erd_point_pos (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) (lam : ℝ)
    (hlam : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam) :
    (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧
      (∀ᶠ l in 𝓝 lam, OTDRO.Dual.ellRob ℓ A δ β l x ≠ ⊤) ∧
      (∃ m : ℝ, IsLeast ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) m ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) m (Set.Iic lam) lam) ∧
      (∃ M : ℝ, IsGreatest ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) M ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) M (Set.Ici lam) lam) ∧
      (DifferentiableAt ℝ (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) lam ↔
        ∃ s : ℝ, (fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x = {s}) := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hℓc : Continuous ℓ := continuousOn_univ.1 (hℓ.continuousOn isOpen_univ)
  set q := OTDRO.Dual.quadInv A β x with hqdef
  set lam0 := (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q + lam) / 2
  have hl0 : lam0 < lam := by simp only [lam0]; linarith
  have hl00 : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q < lam0 := by simp only [lam0]; linarith
  obtain ⟨R, hR⟩ := unif_R ℓ hℓ h A δ hδ β x hq lam0 hl00
  set Ψ := fun γ => ℓ (inner ℝ β x + γ * Real.sqrt δ * q)
  have hΨ : Continuous Ψ := by simp only [Ψ]; fun_prop
  have hc1 : 0 < Real.sqrt δ * q := mul_pos hsd hq
  have hex : ∀ l, lam0 ≤ l → ∃ γ, OTDRO4.Danskin.IsMx Ψ (Real.sqrt δ * q) (Real.sqrt δ) l γ := by
    intro l hl
    obtain ⟨γ, hγ⟩ := (hR l hl).1
    exact ⟨γ, (isMx_iff ℓ A δ β x γ l).2 hγ⟩
  have hbd : ∀ l, lam0 ≤ l → ∀ γ, OTDRO4.Danskin.IsMx Ψ (Real.sqrt δ * q) (Real.sqrt δ) l γ →
      |γ| ≤ R := fun l hl γ hγ => (hR l hl).2 γ ((isMx_iff ℓ A δ β x γ l).1 hγ)
  have hset : {γ | OTDRO4.Danskin.IsMx Ψ (Real.sqrt δ * q) (Real.sqrt δ) lam γ} =
      OTDRO.Dual.maximizers ℓ A δ β lam x := by
    ext γ; exact isMx_iff ℓ A δ β x γ lam
  have hRt := OTDRO4.Danskin.right_deriv hΨ hc1 hl0 hex hbd
  have hLt := OTDRO4.Danskin.left_deriv hΨ hc1 hl0 hex hbd
  obtain ⟨hmS, hMS, hba, hbb⟩ := OTDRO4.Danskin.sq_attained hΨ hl0 hex hbd
  simp only [hset] at hRt hLt hmS hMS hba hbb
  set m := sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)
  set M := sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)
  have hVeq : ∀ l, lam0 ≤ l → OTDRO4.Danskin.V Ψ (Real.sqrt δ * q) (Real.sqrt δ) l =
      (OTDRO.Dual.ellRob ℓ A δ β l x).toReal := fun l hl =>
    (V_eq_ellRob ℓ A δ β x l (hR l hl).1).1
  set f := fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal
  -- derivatives
  have hDR : HasDerivWithinAt f (Real.sqrt δ - Real.sqrt δ * q * m) (Set.Ici lam) lam := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hfil : Set.Ici lam \ {lam} = Set.Ioi lam := by
      ext l; simp [lt_iff_le_and_ne, eq_comm]
    rw [hfil]
    refine hRt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    rw [slope_def_field, hVeq l (by simp at hl; linarith), hVeq lam hl0.le]
  have hDL : HasDerivWithinAt f (Real.sqrt δ - Real.sqrt δ * q * M) (Set.Iic lam) lam := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hfil : Set.Iic lam \ {lam} = Set.Iio lam := by
      ext l; simp [lt_iff_le_and_ne]
    rw [hfil]
    refine hLt.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hl0] with l hl
    rw [slope_def_field, hVeq l hl.1.le, hVeq lam hl0.le]
  obtain ⟨gm, hgm, hgm2⟩ := hmS
  obtain ⟨gM, hgM, hgM2⟩ := hMS
  simp only at hgm2 hgM2
  set φ := fun γ : ℝ => -Real.sqrt δ * (γ ^ 2 * q - 1)
  have hφm : φ gm = Real.sqrt δ - Real.sqrt δ * q * m := by
    simp only [φ]; rw [hgm2]; ring
  have hφM : φ gM = Real.sqrt δ - Real.sqrt δ * q * M := by
    simp only [φ]; rw [hgM2]; ring
  have hφmono : ∀ γ γ' : ℝ, γ ^ 2 ≤ γ' ^ 2 → φ γ' ≤ φ γ := by
    intro γ γ' h
    simp only [φ]
    have : γ ^ 2 * q ≤ γ' ^ 2 * q := mul_le_mul_of_nonneg_right h hq.le
    nlinarith
  have hle_m : ∀ γ ∈ OTDRO.Dual.maximizers ℓ A δ β lam x, m ≤ γ ^ 2 :=
    fun γ hγ => csInf_le hbb ⟨γ, hγ, rfl⟩
  have hle_M : ∀ γ ∈ OTDRO.Dual.maximizers ℓ A δ β lam x, γ ^ 2 ≤ M :=
    fun γ hγ => le_csSup hba ⟨γ, hγ, rfl⟩
  have hLeast : IsLeast (φ '' OTDRO.Dual.maximizers ℓ A δ β lam x)
      (Real.sqrt δ - Real.sqrt δ * q * M) := by
    refine ⟨⟨gM, hgM, hφM⟩, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← hφM]; exact hφmono γ gM (by rw [hgM2]; exact hle_M γ hγ)
  have hGreatest : IsGreatest (φ '' OTDRO.Dual.maximizers ℓ A δ β lam x)
      (Real.sqrt δ - Real.sqrt δ * q * m) := by
    refine ⟨⟨gm, hgm, hφm⟩, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← hφm]; exact hφmono gm γ (by rw [hgm2]; exact hle_m γ hγ)
  refine ⟨(hR lam hl0.le).1, ?_, ⟨_, hLeast, hDL⟩, ⟨_, hGreatest, hDR⟩, ?_⟩
  · have : Set.Ioi (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q) ∈ 𝓝 lam := Ioi_mem_nhds hlam
    filter_upwards [this] with l hl
    exact (lemma1a ℓ hℓ A δ hδ β l x hq.le (Or.inr (by
      have hsdq : 0 < Real.sqrt δ * q := hc1
      obtain ⟨s, M', hs0, hslt, hM'⟩ := exists_growth_lt ℓ h (l / (Real.sqrt δ * q))
        (by rw [lt_div_iff₀ hsdq]; simp at hl; linarith)
      exact ⟨s, M', hs0, hM', hslt⟩))).2
  · constructor
    · rintro ⟨f', hf'⟩
      have h1 := hf'.hasDerivAt.hasDerivWithinAt (s := Set.Ici lam)
      have h2 := hf'.hasDerivAt.hasDerivWithinAt (s := Set.Iic lam)
      have e1 := (uniqueDiffWithinAt_Ici lam).eq_deriv _ h1 hDR
      have e2 := (uniqueDiffWithinAt_Iic lam).eq_deriv _ h2 hDL
      have hmM : m = M := by
        have : Real.sqrt δ * q * m = Real.sqrt δ * q * M := by linarith
        exact mul_left_cancel₀ hc1.ne' this
      refine ⟨Real.sqrt δ - Real.sqrt δ * q * m, ?_⟩
      ext v
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        have h1 := hle_m γ hγ
        have h2 := hle_M γ hγ
        have : γ ^ 2 = m := by rw [hmM] at h1 ⊢; linarith
        show φ γ = _
        simp only [φ]; rw [this]; ring
      · rintro rfl; exact ⟨gm, hgm, hφm⟩
    · rintro ⟨s0, hs0⟩
      have h1 : Real.sqrt δ - Real.sqrt δ * q * m = s0 := by
        have := hGreatest.1; rw [hs0] at this; exact this
      have h2 : Real.sqrt δ - Real.sqrt δ * q * M = s0 := by
        have := hLeast.1; rw [hs0] at this; exact this
      have hDL' : HasDerivWithinAt f (Real.sqrt δ - Real.sqrt δ * q * m) (Set.Iic lam) lam := by
        rw [h1, ← h2]; exact hDL
      have := hDL'.union hDR
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this.differentiableAt

lemma erd_ac_pos (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ)
    (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β x : EuclideanSpace ℝ (Fin d))
    (hq : 0 < OTDRO.Dual.quadInv A β x) (a b : ℝ)
    (ha : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < a)
    (hb : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < b) :
    AbsolutelyContinuousOnInterval (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) a b := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set q := OTDRO.Dual.quadInv A β x
  set lam0 := (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q + min a b) / 2
  have hmin : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q < min a b := lt_min ha hb
  have hl00 : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * q < lam0 := by simp only [lam0]; linarith
  have hl0m : lam0 < min a b := by simp only [lam0]; linarith
  obtain ⟨R, hR⟩ := unif_R ℓ hℓ h A δ hδ β x hq lam0 hl00
  set Ψ := fun γ => ℓ (inner ℝ β x + γ * Real.sqrt δ * q)
  have hc1 : 0 < Real.sqrt δ * q := mul_pos hsd hq
  have hex : ∀ l, lam0 ≤ l → ∃ γ, OTDRO4.Danskin.IsMx Ψ (Real.sqrt δ * q) (Real.sqrt δ) l γ := by
    intro l hl
    obtain ⟨γ, hγ⟩ := (hR l hl).1
    exact ⟨γ, (isMx_iff ℓ A δ β x γ l).2 hγ⟩
  have hbd : ∀ l, lam0 ≤ l → ∀ γ, OTDRO4.Danskin.IsMx Ψ (Real.sqrt δ * q) (Real.sqrt δ) l γ →
      |γ| ≤ R := fun l hl γ hγ => (hR l hl).2 γ ((isMx_iff ℓ A δ β x γ l).1 hγ)
  have hVeq : ∀ l, lam0 ≤ l → OTDRO4.Danskin.V Ψ (Real.sqrt δ * q) (Real.sqrt δ) l =
      (OTDRO.Dual.ellRob ℓ A δ β l x).toReal := fun l hl =>
    (V_eq_ellRob ℓ A δ β x l (hR l hl).1).1
  set C := |Real.sqrt δ| + Real.sqrt δ * q * R ^ 2
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal C)
  apply LipschitzOnWith.of_dist_le_mul
  intro l1 hl1 l2 hl2
  have hm1 : min a b ≤ l1 := (Set.mem_uIcc.1 hl1).elim (fun h => le_trans (min_le_left _ _) h.1)
    (fun h => le_trans (min_le_right _ _) h.1)
  have hm2 : min a b ≤ l2 := (Set.mem_uIcc.1 hl2).elim (fun h => le_trans (min_le_left _ _) h.1)
    (fun h => le_trans (min_le_right _ _) h.1)
  have hC0 : 0 ≤ C := by positivity
  rw [Real.coe_toNNReal _ hC0, Real.dist_eq, Real.dist_eq]
  rcases eq_or_ne l1 l2 with h12 | h12
  · rw [h12]; simp
  have hsl := OTDRO4.Danskin.slope_bound (Ψ := Ψ) (c0 := Real.sqrt δ) hc1
    (lt_of_lt_of_le hl0m hm2) hex hbd l1 (by linarith) h12
  rw [hVeq l1 (by linarith), hVeq l2 (by linarith), abs_div] at hsl
  have hpos : 0 < |l1 - l2| := abs_pos.2 (sub_ne_zero.2 h12)
  rw [div_le_iff₀ hpos] at hsl
  exact hsl

/-- `|q_β − q_β'| ≤ ‖β − β'‖ ‖β + β'‖ / ρ` -/
lemma quadInv_lip (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), ρ * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (A x *ᵥ v.ofLp))
    (β β' : EuclideanSpace ℝ (Fin d)) :
    |OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x| ≤ ‖β - β'‖ * ‖β + β'‖ / ρ := by
  set W := (A x)⁻¹
  have hWs : Wᵀ = W := by
    have hMs : (A x)ᵀ = A x := by
      have := (hA x).isHermitian
      ext i j
      have h := congrFun (congrFun this i) j
      simpa using h
    simp only [W]; rw [transpose_nonsing_inv, hMs]
  -- ‖W v‖ ≤ ‖v‖ / ρ
  have hWv : ∀ v : EuclideanSpace ℝ (Fin d),
      ‖(WithLp.toLp 2 (W *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin d))‖ ≤ ‖v‖ / ρ := by
    intro v
    set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (W *ᵥ v.ofLp)
    have h1 : ρ * ‖w‖ ^ 2 ≤ inner ℝ w v := by
      have := hx w
      have e : dotProduct w.ofLp (A x *ᵥ w.ofLp) = inner ℝ w v := by
        simp only [w, W]
        rw [mulVec_inv_mulVec _ (hA x), EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct_comm]
      linarith
    have h2 : inner ℝ w v ≤ ‖w‖ * ‖v‖ := real_inner_le_norm w v
    rw [le_div_iff₀ hρ]
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    rcases eq_or_lt_of_le hw0 with h | h
    · rw [← h]; simp
    · nlinarith
  have key : OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x =
      inner ℝ (β - β') (WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d)) := by
    unfold OTDRO.Dual.quadInv
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, mulVec_add, star_trivial]
    have hsym : dotProduct β'.ofLp (W *ᵥ β.ofLp) = dotProduct β.ofLp (W *ᵥ β'.ofLp) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hWs, dotProduct_comm]
    simp only [W] at hsym ⊢
    simp only [dotProduct_add, dotProduct_sub, sub_dotProduct, add_dotProduct]
    rw [dotProduct_comm ((A x)⁻¹ *ᵥ β.ofLp) β.ofLp, dotProduct_comm ((A x)⁻¹ *ᵥ β'.ofLp) β.ofLp,
      dotProduct_comm ((A x)⁻¹ *ᵥ β.ofLp) β'.ofLp, dotProduct_comm ((A x)⁻¹ *ᵥ β'.ofLp) β'.ofLp]
    rw [hsym]; ring
  rw [key]
  calc |inner ℝ (β - β') (WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d))|
      ≤ ‖β - β'‖ * ‖(WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖β - β'‖ * (‖β + β'‖ / ρ) := mul_le_mul_of_nonneg_left (hWv _) (norm_nonneg _)
    _ = ‖β - β'‖ * ‖β + β'‖ / ρ := by ring

lemma erd_point_zero (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β x : EuclideanSpace ℝ (Fin d)) (hq : OTDRO.Dual.quadInv A β x = 0) :
    (∀ l, OTDRO.Dual.ellRob ℓ A δ β l x = ((ℓ (inner ℝ β x) + l * Real.sqrt δ : ℝ) : EReal)) ∧
    (∀ l, OTDRO.Dual.maximizers ℓ A δ β l x = Set.univ) := by
  have hF : ∀ γ l, OTDRO.Dual.Fobj ℓ A δ γ β l x = ℓ (inner ℝ β x) + l * Real.sqrt δ := by
    intro γ l; unfold OTDRO.Dual.Fobj; rw [hq]; ring_nf
  refine ⟨fun l => ?_, fun l => ?_⟩
  · unfold OTDRO.Dual.ellRob; simp_rw [hF]; exact iSup_const
  · ext γ; simp [OTDRO.Dual.maximizers, hF]

lemma ae_quadInv_le_essSup_all (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) :
    ∀ᵐ x ∂P0, ∀ β : EuclideanSpace ℝ (Fin d),
      OTDRO.Dual.quadInv A β x ≤ essSup (fun y => OTDRO.Dual.quadInv A β y) P0 := by
  have hρ := hA.rhoMin_pos
  have hbu : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) := by
    intro β
    apply Filter.isBoundedUnder_of_eventually_le (a := ‖β‖ ^ 2 / ρmin)
    filter_upwards [hA.eig_bounds] with x hx
    exact quadInv_le A hA.posDef β x ρmin hρ (fun v => (hx v).1)
  have hcob : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsCoboundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
    fun β => Filter.isCoboundedUnder_le_of_le (ae P0) (fun x => quadInv_nonneg A hA.posDef β x)
  -- Q is "Lipschitz"
  have hQlip : ∀ β β' : EuclideanSpace ℝ (Fin d),
      essSup (fun y => OTDRO.Dual.quadInv A β' y) P0 ≤
        essSup (fun y => OTDRO.Dual.quadInv A β y) P0 + ‖β - β'‖ * ‖β + β'‖ / ρmin := by
    intro β β'
    apply essSup_le_of_ae_le _ _ (hcob β')
    filter_upwards [ae_le_essSup (hbu β), hA.eig_bounds] with y hy1 hy2
    have := quadInv_lip A hA.posDef y ρmin hρ (fun v => (hy2 v).1) β β'
    have h' := neg_abs_le (OTDRO.Dual.quadInv A β y - OTDRO.Dual.quadInv A β' y)
    show OTDRO.Dual.quadInv A β' y ≤ _
    linarith
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin d))
  have h1 : ∀ᵐ x ∂P0, ∀ β ∈ D, OTDRO.Dual.quadInv A β x ≤
      essSup (fun y => OTDRO.Dual.quadInv A β y) P0 :=
    (ae_ball_iff hDc).2 (fun β _ => ae_le_essSup (hbu β))
  filter_upwards [h1, hA.eig_bounds] with x hx hx2
  intro β
  apply le_of_forall_pos_le_add
  intro ε hε
  set η := min 1 (ε * ρmin / (2 * (2 * ‖β‖ + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨β', hβ', hβ'D⟩ := Metric.dense_iff.1 hDd β η hη
  rw [Metric.mem_ball, dist_eq_norm] at hβ'
  have hβ'' : ‖β - β'‖ < η := by rw [norm_sub_rev]; exact hβ'
  have hsum : ‖β + β'‖ ≤ 2 * ‖β‖ + 1 := by
    have : ‖β'‖ ≤ ‖β‖ + η := by
      have := norm_le_norm_add_norm_sub' β' β
      rw [norm_sub_rev] at this; linarith
    have := norm_add_le β β'
    have : η ≤ 1 := min_le_left _ _
    linarith
  set c := ‖β - β'‖ * ‖β + β'‖ / ρmin
  have hc : 2 * c ≤ ε := by
    simp only [c]
    have h3 : ‖β - β'‖ * ‖β + β'‖ ≤ η * (2 * ‖β‖ + 1) :=
      mul_le_mul hβ''.le hsum (norm_nonneg _) hη.le
    have h4 : η ≤ ε * ρmin / (2 * (2 * ‖β‖ + 1)) := min_le_right _ _
    have h5 : η * (2 * ‖β‖ + 1) ≤ ε * ρmin / 2 := by
      have hp : 0 < 2 * ‖β‖ + 1 := by positivity
      calc η * (2 * ‖β‖ + 1) ≤ ε * ρmin / (2 * (2 * ‖β‖ + 1)) * (2 * ‖β‖ + 1) :=
            mul_le_mul_of_nonneg_right h4 hp.le
        _ = ε * ρmin / 2 := by field_simp
    rw [mul_div_assoc', div_le_iff₀ hρ]
    linarith
  have hl1 := quadInv_lip A hA.posDef x ρmin hρ (fun v => (hx2 v).1) β β'
  have hl2 := hQlip β β'
  have hl3 : essSup (fun y => OTDRO.Dual.quadInv A β' y) P0 ≤
      essSup (fun y => OTDRO.Dual.quadInv A β y) P0 + c := hl2
  have hx' := hx β' hβ'D
  have := le_abs_self (OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x)
  linarith

end OTDRO4

open MeasureTheory Filter Topology

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (K : ℕ) (hK : 0 < K) (ℓi : Fin K → ℝ → ℝ) (hℓi : ∀ i, ContDiff ℝ 1 (ℓi i))
    (hmax : ∀ u, IsGreatest (Set.range fun i => ℓi i u) (ℓ u)) :
    ∀ᵐ x ∂P0, ∀ β ∈ B, ∀ lam : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < lam →
      (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧
      (∀ᶠ l in 𝓝 lam, OTDRO.Dual.ellRob ℓ A δ β l x ≠ ⊤) ∧
      (∀ a b : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < a → OTDRO.Dual.lamThr P0 ℓ A δ β < b →
        AbsolutelyContinuousOnInterval (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) a b) ∧
      (∃ m : ℝ, IsLeast ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) m ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) m (Set.Iic lam) lam) ∧
      (∃ M : ℝ, IsGreatest ((fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x) M ∧
        HasDerivWithinAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) M (Set.Ici lam) lam) ∧
      (DifferentiableAt ℝ (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) lam ↔
        ∃ s : ℝ, (fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
          OTDRO.Dual.maximizers ℓ A δ β lam x = {s}) := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hk := OTDRO4.kappa_nonneg ℓ h2.growth
  filter_upwards [OTDRO4.ae_quadInv_le_essSup_all P0 A ρmin ρmax hA] with x hx
  intro β _ lam hlam
  have hq0 := OTDRO4.quadInv_nonneg A hA.posDef β x
  have hκ : ∀ t, OTDRO.Dual.lamThr P0 ℓ A δ β < t →
      OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < t := by
    intro t ht
    have : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x ≤
        OTDRO.Dual.lamThr P0 ℓ A δ β :=
      mul_le_mul_of_nonneg_left (hx β) (by positivity)
    linarith
  rcases eq_or_lt_of_le hq0 with hq | hq
  · -- `q = 0`: everything is affine in `l`
    obtain ⟨hell, hmx⟩ := OTDRO4.erd_point_zero ℓ A δ β x hq.symm
    have hf : (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) =
        fun l => ℓ (inner ℝ β x) + l * Real.sqrt δ := by
      funext l; rw [hell l, EReal.toReal_coe]
    have himg : (fun γ => -Real.sqrt δ * (γ ^ 2 * OTDRO.Dual.quadInv A β x - 1)) ''
        OTDRO.Dual.maximizers ℓ A δ β lam x = {Real.sqrt δ} := by
      rw [hmx lam, ← hq]
      ext v; simp [eq_comm]
    have hder : HasDerivAt (fun l => (OTDRO.Dual.ellRob ℓ A δ β l x).toReal) (Real.sqrt δ) lam := by
      rw [hf]
      simpa using ((hasDerivAt_id lam).mul_const (Real.sqrt δ)).const_add (ℓ (inner ℝ β x))
    rw [himg]
    refine ⟨by rw [hmx lam]; exact Set.univ_nonempty, Filter.Eventually.of_forall
      fun l => by rw [hell l]; exact EReal.coe_ne_top _, fun a b _ _ => ?_,
      ⟨_, isLeast_singleton, hder.hasDerivWithinAt⟩,
      ⟨_, isGreatest_singleton, hder.hasDerivWithinAt⟩, ⟨fun _ => ⟨_, rfl⟩,
        fun _ => hder.differentiableAt⟩⟩
    rw [hf]
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal (Real.sqrt δ))
    apply LipschitzOnWith.of_dist_le_mul
    intro l1 _ l2 _
    rw [Real.coe_toNNReal _ hsd.le, Real.dist_eq, Real.dist_eq]
    have : ℓ (inner ℝ β x) + l1 * Real.sqrt δ - (ℓ (inner ℝ β x) + l2 * Real.sqrt δ) =
        Real.sqrt δ * (l1 - l2) := by ring
    rw [this, abs_mul, abs_of_pos hsd]
  · obtain ⟨h1, h2', h4, h5, h6⟩ :=
      OTDRO4.erd_point_pos ℓ h2.convex h2.growth A δ hδ β x hq lam (hκ lam hlam)
    exact ⟨h1, h2', fun a b ha hb => OTDRO4.erd_ac_pos ℓ h2.convex h2.growth A δ hδ β x hq a b
      (hκ a ha) (hκ b hb), h4, h5, h6⟩
