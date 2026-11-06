-- Prove2me | solution 1 for OTDRO.WorstCase.worst_case_randomized_monge
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:58:51.988729+00:00
-- url     : https://prove2.me/submissions/195a715a-9444-4f93-b149-e1191d92309c

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_ModelRiskOT_Duality_primalFeasible
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_OTDRO_WorstCase_Transport
import Theorems.Thm_OTDRO_WorstCase_dual_lambda_derivatives

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

open MeasureTheory

open OTDRO.WorstCase
theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lamStar : ℝ) (hlam0 : 0 ≤ lamStar)
    (hmin : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lamStar)
    (hthr : OTDRO.Dual.lamThr P0 ℓ A δ β < lamStar) :
    ∃ Gminus Gplus : EuclideanSpace ℝ (Fin d) → ℝ,
      AEMeasurable Gminus P0 ∧ AEMeasurable Gplus P0 ∧
      (∀ᵐ x ∂P0, Gminus x ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x ∧
        Gplus x ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x ∧
        ∀ g ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x, Gminus x ^ 2 ≤ g ^ 2 ∧ g ^ 2 ≤ Gplus x ^ 2) ∧
      Integrable (fun x => Gminus x ^ 2 * OTDRO.Dual.quadInv A β x) P0 ∧
      Integrable (fun x => Gplus x ^ 2 * OTDRO.Dual.quadInv A β x) P0 ∧
      0 ≤ bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus) ∧
      bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus) ≤ 1 ∧
      mixtureCoupling P0 A δ β Gminus Gplus ∈
        ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
      ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
          (mixtureCoupling P0 A δ β Gminus Gplus) =
        ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ ∧
      ∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2) ∂(mixtureCoupling P0 A δ β Gminus Gplus) =
        ENNReal.ofReal δ := by
  set lam := lamStar with hlamdef
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hℓc : Continuous ℓ := continuousOn_univ.1 (h2.convex.continuousOn isOpen_univ)
  have hqm := OTDRO4.quadInv_measurable A hA.posDef hA.lsc β
  have hqpos := OTDRO4.quadInv_pos A hA.posDef β hβ
  obtain ⟨hfin, hder⟩ := OTDRO.WorstCase.dual_lambda_derivatives P0 A ρmin ρmax hA ℓ h2 δ hδ B hB
    β hβB hβ
  obtain ⟨hae, hIm, hIM, hDr, hDl⟩ := hder lam hthr
  set m : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x) with hm
  set M : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x) with hM
  set S : EuclideanSpace ℝ (Fin d) → Set ℝ :=
    fun x => (fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x with hS
  replace hIm : Integrable (fun x => OTDRO.Dual.quadInv A β x * m x) P0 := hIm
  replace hIM : Integrable (fun x => OTDRO.Dual.quadInv A β x * M x) P0 := hIM
  set clow := ∫ x, OTDRO.Dual.quadInv A β x * m x ∂P0 with hclow
  set cbar := ∫ x, OTDRO.Dual.quadInv A β x * M x ∂P0 with hcbar
  replace hDr : HasDerivWithinAt (fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal)
      (Real.sqrt δ * (1 - clow)) (Set.Ici lam) lam := hDr
  replace hDl : HasDerivWithinAt (fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal)
      (Real.sqrt δ * (1 - cbar)) (Set.Iic lam) lam := hDl
  -- measurability of `m`, `M`
  have hmm : AEMeasurable m P0 := by
    have := hIm.aemeasurable.div hqm.aemeasurable
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.div_apply]
    exact mul_div_cancel_left₀ _ (hqpos x).ne'
  have hMm : AEMeasurable M P0 := by
    have := hIM.aemeasurable.div hqm.aemeasurable
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.div_apply]
    exact mul_div_cancel_left₀ _ (hqpos x).ne'
  -- attainment
  have hatt : ∀ᵐ x ∂P0, m x ∈ S x ∧ M x ∈ S x ∧ BddAbove (S x) := by
    filter_upwards [hae] with x hx
    have hc := OTDRO4.maximizers_compact ℓ hℓc A δ β lam x hx.2
    have hSc : IsCompact (S x) := hc.image (continuous_pow 2)
    show sInf (S x) ∈ S x ∧ sSup (S x) ∈ S x ∧ BddAbove (S x)
    have hSn : (S x).Nonempty := hx.1.image _
    exact ⟨hSc.sInf_mem hSn, hSc.sSup_mem hSn, hx.2⟩
  obtain ⟨Gm, hGmm, hGm⟩ := OTDRO4.select_sq P0 ℓ hℓc A hA.posDef hA.lsc δ β lam m hmm
    (hatt.mono fun x hx => by obtain ⟨g, hg, hg2⟩ := hx.1; exact ⟨g, hg, hg2⟩)
  obtain ⟨Gp, hGpm, hGp⟩ := OTDRO4.select_sq P0 ℓ hℓc A hA.posDef hA.lsc δ β lam M hMm
    (hatt.mono fun x hx => by obtain ⟨g, hg, hg2⟩ := hx.2.1; exact ⟨g, hg, hg2⟩)
  -- integrability of the weighted squares
  have hintm : Integrable (fun x => Gm x ^ 2 * OTDRO.Dual.quadInv A β x) P0 :=
    hIm.congr (hGm.mono fun x hx => by simp only; rw [hx.2]; ring)
  have hintp : Integrable (fun x => Gp x ^ 2 * OTDRO.Dual.quadInv A β x) P0 :=
    hIM.congr (hGp.mono fun x hx => by simp only; rw [hx.2]; ring)
  have hsm : sqMoment P0 A β Gm = clow := by
    unfold sqMoment
    exact integral_congr_ae (hGm.mono fun x hx => by simp only; rw [hx.2]; ring)
  have hsp : sqMoment P0 A β Gp = cbar := by
    unfold sqMoment
    exact integral_congr_ae (hGp.mono fun x hx => by simp only; rw [hx.2]; ring)
  -- λ_thr ≥ 0, hence λ* > 0
  have hthr0 : 0 ≤ OTDRO.Dual.lamThr P0 ℓ A δ β := by
    unfold OTDRO.Dual.lamThr
    have hk := OTDRO4.kappa_nonneg ℓ h2.growth
    have hes : 0 ≤ essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by
      by_contra hneg
      push Not at hneg
      have hbu : Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) := by
        apply Filter.isBoundedUnder_of_eventually_le (a := ‖β‖ ^ 2 / ρmin)
        filter_upwards [hA.eig_bounds] with x hx
        exact OTDRO4.quadInv_le A hA.posDef β x ρmin hA.rhoMin_pos (fun v => (hx v).1)
      have h1 := ae_le_essSup hbu
      obtain ⟨x, hx⟩ := h1.exists
      linarith [hqpos x]
    positivity
  have hlampos : 0 < lam := lt_of_le_of_lt hthr0 hthr
  -- the dual objective is finite and monotone comparisons hold near λ*
  set φ := fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal with hφ
  have hcmp : ∀ l, OTDRO.Dual.lamThr P0 ℓ A δ β < l → 0 ≤ l → φ lam ≤ φ l := by
    intro l hl hl0
    have h := hmin (Set.mem_Ici.2 hl0)
    simp only [Set.mem_setOf_eq] at h
    exact EReal.toReal_le_toReal h (hfin lam hthr).2 (hfin l hl).1
  -- minimality ⇒ c̲ ≤ 1 ≤ c̄
  have hlow : clow ≤ 1 := by
    have hD := hDr
    rw [hasDerivWithinAt_iff_tendsto_slope] at hD
    have hfil : Set.Ici lam \ {lam} = Set.Ioi lam := by
      ext l; simp [lt_iff_le_and_ne, eq_comm]
    rw [hfil] at hD
    have hev : ∀ᶠ l in nhdsWithin lam (Set.Ioi lam), 0 ≤ slope φ lam l := by
      filter_upwards [self_mem_nhdsWithin] with l hl
      rw [slope_def_field]
      apply div_nonneg _ (by simp at hl; linarith)
      have := hcmp l (by simp at hl; linarith) (by simp at hl; linarith)
      linarith
    have := ge_of_tendsto hD hev
    have : 0 ≤ 1 - clow := by
      by_contra hc; push Not at hc
      have : Real.sqrt δ * (1 - clow) < 0 := mul_neg_of_pos_of_neg hsd hc
      linarith
    linarith
  have hhigh : 1 ≤ cbar := by
    have hD := hDl
    rw [hasDerivWithinAt_iff_tendsto_slope] at hD
    have hfil : Set.Iic lam \ {lam} = Set.Iio lam := by
      ext l; simp [lt_iff_le_and_ne]
    rw [hfil] at hD
    set l0 := max (OTDRO.Dual.lamThr P0 ℓ A δ β) 0
    have hl0 : l0 < lam := max_lt hthr hlampos
    have hev : ∀ᶠ l in nhdsWithin lam (Set.Iio lam), slope φ lam l ≤ 0 := by
      have hmem : Set.Ioo l0 lam ∈ nhdsWithin lam (Set.Iio lam) := Ioo_mem_nhdsLT hl0
      filter_upwards [hmem] with l hl
      rw [slope_def_field]
      apply div_nonpos_of_nonneg_of_nonpos _ (by linarith [hl.2])
      have := hcmp l (lt_of_le_of_lt (le_max_left _ _) hl.1)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hl.1))
      linarith
    have := le_of_tendsto hD hev
    have : 1 - cbar ≤ 0 := by
      by_contra hc; push Not at hc
      have : 0 < Real.sqrt δ * (1 - cbar) := mul_pos hsd hc
      linarith
    linarith
  -- the Bernoulli weight
  set w := bernoulliWeight cbar clow with hw
  have hw01 : 0 ≤ w ∧ w ≤ 1 ∧ w * clow + (1 - w) * cbar = 1 := by
    simp only [hw, bernoulliWeight]
    rcases eq_or_lt_of_le (show clow ≤ cbar by linarith) with h | h
    · rw [h, sub_self, div_zero]; refine ⟨le_refl _, zero_le_one, ?_⟩
      have : cbar = 1 := le_antisymm (h ▸ hlow) hhigh
      rw [this]; ring
    · have hpos : 0 < cbar - clow := by linarith
      refine ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith), ?_⟩
      field_simp; ring
  obtain ⟨hw0, hw1, hwsum⟩ := hw01
  -- the value function `R`
  set R := fun x => OTDRO.Dual.Fobj ℓ A δ (Gp x) β lam x with hR
  have hRm : Measurable R :=
    OTDRO4.Fobj_comp_measurable ℓ hℓc A hA.posDef hA.lsc δ β lam Gp hGpm
  have hRell : ∀ᵐ x ∂P0, OTDRO.Dual.ellRob ℓ A δ β lam x = ((R x : ℝ) : EReal) := by
    filter_upwards [hGp] with x hx
    unfold OTDRO.Dual.ellRob
    apply le_antisymm
    · exact iSup_le fun c => EReal.coe_le_coe_iff.2 (hx.1 c)
    · exact le_iSup (fun c => ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal)) (Gp x)
  have hRint : Integrable R P0 := by
    have hf := hfin lam hthr
    unfold OTDRO.Dual.fDelta at hf
    rw [OTDRO4.extIntegral_congr_ae P0 _ _ hRell] at hf
    obtain ⟨hP, hN⟩ := OTDRO4.extIntegral_parts_finite P0 _ hf.1 hf.2
    have e1 : ∀ x, ((R x : ℝ) : EReal).toENNReal = ENNReal.ofReal (R x) := fun x => by
      rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    have e2 : ∀ x, (-((R x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-R x) := fun x => by
      rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    simp_rw [e1] at hP; simp_rw [e2] at hN
    exact OTDRO4.integrable_of_parts P0 R hRm.aestronglyMeasurable hP hN
  -- weak duality
  have hpt : ∀ᵐ x ∂P0, ∀ y, ℓ (inner ℝ β y) ≤ R x - lam * Real.sqrt δ +
      lam / Real.sqrt δ * OTDRO.Dual.mahalCost A x y := by
    filter_upwards [hGp] with x hx y
    exact OTDRO4.pointwise_dual ℓ A hA.posDef δ hδ β lam hlam0 x (hqpos x) (Gp x) hx.1 y
  have hweak := OTDRO4.weak_duality P0 A hA.posDef hA.lsc ℓ hℓc δ hδ β lam hlam0 R hRint hpt
  -- the mixture
  have hT1 := OTDRO4.shiftMap_measurable A hA.posDef hA.lsc δ β Gm hGmm
  have hT2 := OTDRO4.shiftMap_measurable A hA.posDef hA.lsc δ β Gp hGpm
  have hmix : mixtureCoupling P0 A δ β Gm Gp =
      ENNReal.ofReal w • graphCoupling P0 (shiftMap A δ β Gm) +
      ENNReal.ofReal (1 - w) • graphCoupling P0 (shiftMap A δ β Gp) :=
    OTDRO4.mixture_eq P0 A δ β Gm Gp w (by rw [hsm, hsp])
  -- cost of the mixture
  have hcostG : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ,
      Integrable (fun x => G x ^ 2 * OTDRO.Dual.quadInv A β x) P0 →
      ∫⁻ x, ENNReal.ofReal (OTDRO.Dual.mahalCost A x (shiftMap A δ β G x)) ∂P0 =
        ENNReal.ofReal (δ * sqMoment P0 A β G) := by
    intro G hG
    simp_rw [OTDRO4.mahalCost_shift A hA.posDef δ hδ.le β G]
    unfold sqMoment
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · congr 1; funext x; ring_nf
    · exact hG.const_mul δ
    · exact Filter.Eventually.of_forall fun x => by
        have := (hqpos x).le
        positivity
  have hcost : ∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2)
      ∂(mixtureCoupling P0 A δ β Gm Gp) = ENNReal.ofReal δ := by
    rw [hmix, OTDRO4.mix_lintegral P0 _ _ hT1 hT2 w
      (fun p => ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2))
      (ENNReal.measurable_ofReal.comp (OTDRO4.cost_measurable A hA.lsc))]
    have hclow0 : 0 ≤ clow := integral_nonneg fun x => mul_nonneg (hqpos x).le
      (Real.sInf_nonneg (fun y hy => by obtain ⟨g, _, rfl⟩ := hy; positivity))
    rw [hcostG Gm hintm, hcostG Gp hintp, hsm, hsp, ← ENNReal.ofReal_mul hw0,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
        (mul_nonneg hw0 (mul_nonneg hδ.le hclow0))
        (mul_nonneg (by linarith) (mul_nonneg hδ.le (by linarith)))]
    congr 1
    linear_combination δ * hwsum
  have hfeas : mixtureCoupling P0 A δ β Gm Gp ∈
      ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ := by
    refine ⟨?_, ?_, hcost.le⟩
    · rw [hmix]; exact OTDRO4.mix_prob P0 _ _ hT1 hT2 w hw0 hw1
    · rw [hmix]; exact OTDRO4.mix_marg P0 _ _ hT1 hT2 w hw0 hw1
  -- objective of the mixture
  have hobjG : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ᵐ x ∂P0, G x ∈ OTDRO.Dual.maximizers ℓ A δ β lam x) →
      Integrable (fun x => G x ^ 2 * OTDRO.Dual.quadInv A β x) P0 →
      (fun x => ℓ (inner ℝ β (shiftMap A δ β G x))) =ᵐ[P0]
        (fun x => R x + lam * Real.sqrt δ * (G x ^ 2 * OTDRO.Dual.quadInv A β x - 1)) := by
    intro G hG _
    filter_upwards [hG, hGp] with x hx hxp
    have hinner : inner ℝ β (shiftMap A δ β G x) =
        inner ℝ β x + G x * Real.sqrt δ * OTDRO.Dual.quadInv A β x := by
      unfold shiftMap
      rw [inner_add_right, inner_smul_right, OTDRO4.inner_invDir]; ring
    have hRx : R x = OTDRO.Dual.Fobj ℓ A δ (G x) β lam x :=
      le_antisymm (hx (Gp x)) (hxp.1 (G x))
    rw [hinner, hRx]
    unfold OTDRO.Dual.Fobj; ring
  have hφm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ℓ (inner ℝ β p.2)) :=
    hℓc.measurable.comp ((continuous_const.inner continuous_id).measurable.comp measurable_snd)
  have hi1 : Integrable (fun x => ℓ (inner ℝ β (shiftMap A δ β Gm x))) P0 :=
    (hRint.add ((hintm.sub (integrable_const 1)).const_mul (lam * Real.sqrt δ))).congr
      (hobjG Gm (hGm.mono fun x hx => hx.1) hintm).symm
  have hi2 : Integrable (fun x => ℓ (inner ℝ β (shiftMap A δ β Gp x))) P0 :=
    (hRint.add ((hintp.sub (integrable_const 1)).const_mul (lam * Real.sqrt δ))).congr
      (hobjG Gp (hGp.mono fun x hx => hx.1) hintp).symm
  obtain ⟨hφint, hφeq⟩ := OTDRO4.mix_integral P0 _ _ hT1 hT2 w hw0 hw1
    (fun p => ℓ (inner ℝ β p.2)) hφm hi1 hi2
  have hval : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ᵐ x ∂P0, G x ∈ OTDRO.Dual.maximizers ℓ A δ β lam x) →
      Integrable (fun x => G x ^ 2 * OTDRO.Dual.quadInv A β x) P0 →
      ∫ x, ℓ (inner ℝ β (shiftMap A δ β G x)) ∂P0 =
        ∫ x, R x ∂P0 + lam * Real.sqrt δ * (sqMoment P0 A β G - 1) := by
    intro G hG hGi
    rw [integral_congr_ae (hobjG G hG hGi),
      integral_add (f := R) (g := fun x => lam * Real.sqrt δ *
        (G x ^ 2 * OTDRO.Dual.quadInv A β x - 1)) hRint
        ((hGi.sub (integrable_const 1)).const_mul _), integral_const_mul,
      integral_sub (f := fun x => G x ^ 2 * OTDRO.Dual.quadInv A β x) (g := fun _ => (1:ℝ))
        hGi (integrable_const 1)]
    simp [sqMoment]
  have hobj : ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
      (mixtureCoupling P0 A δ β Gm Gp) = ((∫ x, R x ∂P0 : ℝ) : EReal) := by
    have hie : ∫ p, ℓ (inner ℝ β p.2) ∂(ENNReal.ofReal w • graphCoupling P0 (shiftMap A δ β Gm) +
        ENNReal.ofReal (1 - w) • graphCoupling P0 (shiftMap A δ β Gp)) = ∫ x, R x ∂P0 := by
      rw [hφeq, hval Gm (hGm.mono fun x hx => hx.1) hintm,
        hval Gp (hGp.mono fun x hx => hx.1) hintp, hsm, hsp]
      linear_combination (lam * Real.sqrt δ) * hwsum
    calc ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) (mixtureCoupling P0 A δ β Gm Gp)
        = ModelRiskOT.Duality.extIntegral (ENNReal.ofReal w • graphCoupling P0 (shiftMap A δ β Gm) +
            ENNReal.ofReal (1 - w) • graphCoupling P0 (shiftMap A δ β Gp))
            (fun p => ((ℓ (inner ℝ β p.2) : ℝ) : EReal)) := by
          rw [← hmix]; rfl
      _ = ((∫ p, ℓ (inner ℝ β p.2) ∂(ENNReal.ofReal w • graphCoupling P0 (shiftMap A δ β Gm) +
            ENNReal.ofReal (1 - w) • graphCoupling P0 (shiftMap A δ β Gp)) : ℝ) : EReal) :=
          by
            have h := OTDRO4.extIntegral_of_integrable _ _ hφint
            exact h
      _ = ((∫ x, R x ∂P0 : ℝ) : EReal) := by rw [hie]
  -- conclusion
  refine ⟨Gm, Gp, hGmm.aemeasurable, hGpm.aemeasurable, ?_, hintm, hintp, ?_, ?_, hfeas, ?_, hcost⟩
  · filter_upwards [hGm, hGp, hatt] with x hxm hxp hxa
    refine ⟨hxm.1, hxp.1, fun g hg => ⟨?_, ?_⟩⟩
    · rw [hxm.2]; exact csInf_le ⟨0, fun y hy => by obtain ⟨g, _, rfl⟩ := hy; positivity⟩ ⟨g, hg, rfl⟩
    · rw [hxp.2]; exact le_csSup hxa.2.2 ⟨g, hg, rfl⟩
  · rw [hsm, hsp]; exact hw0
  · rw [hsm, hsp]; exact hw1
  · apply le_antisymm
    · unfold ModelRiskOT.Duality.primalValue
      exact le_iSup₂ (f := fun π _ => ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π)
        _ hfeas
    · unfold ModelRiskOT.Duality.primalValue
      rw [hobj]
      exact iSup₂_le fun π hπ => hweak π hπ
