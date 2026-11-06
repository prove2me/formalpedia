-- Prove2me | solution 1 for OTDRO.WorstCase.effective_domain
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:44:17.422922+00:00
-- url     : https://prove2.me/submissions/8109b182-0e45-41ca-abf2-9d72411febc0

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

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

lemma quadInv_measurable (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (β : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun x => OTDRO.Dual.quadInv A β x) := by
  have hAm : Measurable (fun x => (fun i j => A x i j : Fin d → Fin d → ℝ)) := by
    apply measurable_pi_lambda; intro i
    apply measurable_pi_lambda; intro j
    exact entry_measurable A hA hlsc i j
  have hdet : Measurable (fun M : Fin d → Fin d → ℝ => (Matrix.of M).det) := by
    have h : Continuous (fun M : Fin d → Fin d → ℝ => (Matrix.of M).det) :=
      (continuous_id.matrix_det (X := Matrix (Fin d) (Fin d) ℝ))
    exact h.measurable
  have hadj : ∀ i j : Fin d,
      Measurable (fun M : Fin d → Fin d → ℝ => (Matrix.of M).adjugate i j) := by
    intro i j
    have h : Continuous (fun M : Fin d → Fin d → ℝ => (Matrix.of M).adjugate i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (continuous_id.matrix_adjugate (X := Matrix (Fin d) (Fin d) ℝ)))
    exact h.measurable
  have hinv : ∀ i j : Fin d, Measurable (fun x => (A x)⁻¹ i j) := by
    intro i j
    have : (fun x => (A x)⁻¹ i j) = fun x =>
        ((Matrix.of (fun i j => A x i j)).det)⁻¹ *
          (Matrix.of (fun i j => A x i j)).adjugate i j := by
      funext x
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
      simp [Matrix.smul_apply]
      rfl
    rw [this]
    exact ((hdet.comp hAm).inv).mul ((hadj i j).comp hAm)
  unfold OTDRO.Dual.quadInv
  simp only [dotProduct, mulVec]
  apply Finset.measurable_sum; intro i _
  apply Measurable.const_mul
  apply Finset.measurable_sum; intro j _
  exact (hinv i j).mul_const _

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

open MeasureTheory

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → ∀ x : EuclideanSpace ℝ (Fin d),
      (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam →
        (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧ OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊤) ∧
      (lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x →
        OTDRO.Dual.maximizers ℓ A δ β lam x = ∅ ∧ OTDRO.Dual.ellRob ℓ A δ β lam x = ⊤)) ∧
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.lamThr P0 ℓ A δ β < lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam < ⊤) ∧
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam < ⊤ → OTDRO.Dual.lamThr P0 ℓ A δ β ≤ lam) := by
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hk := OTDRO4.kappa_nonneg ℓ h2.growth
  -- pointwise part
  have hpw : ∀ β : EuclideanSpace ℝ (Fin d), ∀ lam : ℝ, 0 ≤ lam → ∀ x : EuclideanSpace ℝ (Fin d),
      (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam →
        (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧ OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊤) ∧
      (lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x →
        OTDRO.Dual.maximizers ℓ A δ β lam x = ∅ ∧ OTDRO.Dual.ellRob ℓ A δ β lam x = ⊤) := by
    intro β lam hlam x
    refine ⟨fun hlt => ?_, fun hlt => OTDRO4.lemma1b ℓ h2.growth A δ hδ β lam hlam x hlt⟩
    have hq0 := OTDRO4.quadInv_nonneg A hA.posDef β x
    apply OTDRO4.lemma1a ℓ h2.convex A δ hδ β lam x hq0
    rcases eq_or_lt_of_le hq0 with h | h
    · exact Or.inl h.symm
    · right
      have hsdq : 0 < Real.sqrt δ * OTDRO.Dual.quadInv A β x := mul_pos hsd h
      obtain ⟨s, M, hs0, hslt, hM⟩ := OTDRO4.exists_growth_lt ℓ h2.growth
        (lam / (Real.sqrt δ * OTDRO.Dual.quadInv A β x)) (by
          rw [lt_div_iff₀ hsdq]; linarith)
      exact ⟨s, M, hs0, hM, hslt⟩
  -- a.e. bound on q
  have hqbdd : ∀ β : EuclideanSpace ℝ (Fin d),
      ∀ᵐ x ∂P0, OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρmin := by
    intro β
    filter_upwards [hA.eig_bounds] with x hx
    exact OTDRO4.quadInv_le A hA.posDef β x ρmin hA.rhoMin_pos (fun v => (hx v).1)
  have hbu : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
    fun β => Filter.isBoundedUnder_of_eventually_le (hqbdd β)
  -- linear lower bound for the negative part
  have hneg : ∀ β : EuclideanSpace ℝ (Fin d), ∀ lam : ℝ, 0 ≤ lam →
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
  refine ⟨fun β _ => hpw β, ?_, ?_⟩
  · -- f < ⊤ above the threshold
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
  · -- f < ⊤ forces λ ≥ λ_thr
    intro β _ lam hlam hf
    by_contra hcon
    push Not at hcon
    set Q := essSup (fun x => OTDRO.Dual.quadInv A β x) P0
    have hcon' : lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * Q := hcon
    have hkpos : 0 < OTDRO.Dual.growthKappa ℓ := by
      rcases eq_or_lt_of_le hk with h | h
      · rw [← h] at hcon'; simp at hcon'; linarith
      · exact h
    have hksd : 0 < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ := mul_pos hkpos hsd
    have hcQ : lam / (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ) < Q := by
      rw [div_lt_iff₀ hksd]; linarith
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
      Filter.isCoboundedUnder_le_of_le (ae P0) (fun x => OTDRO4.quadInv_nonneg A hA.posDef β x)
    have hfreq := Filter.frequently_lt_of_lt_limsup hcob hcQ
    rw [frequently_ae_iff] at hfreq
    set E := {x | lam / (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ) < OTDRO.Dual.quadInv A β x}
    have hEm : MeasurableSet E :=
      measurableSet_lt measurable_const (OTDRO4.quadInv_measurable A hA.posDef hA.lsc β)
    have hP : ∫⁻ x, (OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal ∂P0 = ⊤ := by
      apply top_unique
      calc (⊤ : ENNReal) = ∫⁻ x, E.indicator (fun _ => (⊤ : ENNReal)) x ∂P0 := by
            rw [lintegral_indicator_const hEm, ENNReal.top_mul hfreq]
        _ ≤ ∫⁻ x, (OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal ∂P0 := by
            apply lintegral_mono
            intro x
            by_cases hx : x ∈ E
            · rw [Set.indicator_of_mem hx]
              have : lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x := by
                have := (div_lt_iff₀ hksd).1 hx; linarith
              show ⊤ ≤ (OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal
              rw [((hpw β lam hlam x).2 this).2]; simp
            · rw [Set.indicator_of_notMem hx]; exact zero_le
    have := OTDRO4.extIntegral_eq_top_of P0 _ hP (hneg β lam hlam)
    unfold OTDRO.Dual.fDelta at hf
    rw [this] at hf
    exact lt_irrefl _ hf
