-- Prove2me | solution 1 for OTDRO.StrongCvx.dual_optimizer_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:48:35.008335+00:00
-- url     : https://prove2.me/submissions/de4e2d3b-fafa-4730-b402-364cc67bf1b9

import Mathlib
import Theorems.Thm_OTDRO_WorstCase_effective_domain
import Theorems.Thm_OTDRO_WorstCase_dual_lambda_derivatives
import Theorems.Thm_OTDRO_StrongCvx_maximizer_first_order
import Definitions.Def_OTDRO_StrongCvx_Assumptions

open MeasureTheory Matrix Filter Topology

namespace OTDROL7

variable {d : ℕ}

lemma mulVec_inv_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) (b : Fin d → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM.isUnit), one_mulVec]

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

lemma kappa_nonneg (ℓ : ℝ → ℝ) (h : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)) :
    0 ≤ OTDRO.Dual.growthKappa ℓ :=
  le_csInf h (fun _ hs => hs.1)

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

lemma quadInv_pos (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < OTDRO.Dual.quadInv A β x := by
  unfold OTDRO.Dual.quadInv
  have h := (hA x).inv.dotProduct_mulVec_pos (x := β.ofLp) (by
    intro h0; apply hβ; ext i; simpa using congrFun h0 i)
  simpa using h

lemma Fobj_continuous (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun p : ℝ × ℝ => OTDRO.Dual.Fobj ℓ A δ p.1 β p.2 x) := by
  unfold OTDRO.Dual.Fobj; fun_prop

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

lemma ellRob_eq_iSup_rat (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.ellRob ℓ A δ β lam x = ⨆ c : ℚ, ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal) := by
  unfold OTDRO.Dual.ellRob
  apply le_antisymm
  · apply iSup_le; intro γ
    have hc : Continuous (fun c : ℝ => ((OTDRO.Dual.Fobj ℓ A δ c β lam x : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp
        ((OTDROL7.Fobj_continuous ℓ hℓ A δ β x).comp (continuous_id.prodMk continuous_const))
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
  exact (OTDROL7.Fobj_comp_measurable ℓ hℓ A hA hlsc δ β lam _ measurable_const).coe_real_ereal

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

lemma quadInv_ge (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), dotProduct v.ofLp (A x *ᵥ v.ofLp) ≤ ρ * ‖v‖ ^ 2) :
    ‖β‖ ^ 2 / ρ ≤ OTDRO.Dual.quadInv A β x := by
  have h := OTDROL7.cs_cost A hA β x (x + β)
  have e1 : x + β - x = β := by abel
  rw [e1, real_inner_self_eq_norm_sq] at h
  have e2 : OTDRO.Dual.mahalCost A x (x + β) = dotProduct β.ofLp (A x *ᵥ β.ofLp) := by
    unfold OTDRO.Dual.mahalCost
    have : (x - (x + β)).ofLp = -β.ofLp := by ext i; simp
    rw [this, Matrix.mulVec_neg]; simp
  rw [e2] at h
  have hb := hx β
  have hq0 := OTDROL7.quadInv_nonneg A hA β x
  have hβ2 : 0 < ‖β‖ ^ 2 := by positivity
  rw [div_le_iff₀ hρ]
  have : (‖β‖ ^ 2) ^ 2 ≤ OTDRO.Dual.quadInv A β x * (ρ * ‖β‖ ^ 2) :=
    h.trans (mul_le_mul_of_nonneg_left hb hq0)
  nlinarith

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

lemma negpart_finite (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (δ : ℝ) :
    ∀ β : EuclideanSpace ℝ (Fin d), ∀ lam : ℝ, 0 ≤ lam →
      ∫⁻ x, (-OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal ∂P0 < ⊤ := by
  intro β lam hlam
  set L := |ℓ 0| + |ℓ 1| + |ℓ (-1)|
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => |ℓ 0| + L * ‖β‖ * ‖x‖) P0 :=
    (integrable_const _).add ((OTDROL7.integrable_norm_pow h2.moment4 1 (by norm_num)).const_mul
      (L * ‖β‖) |>.congr (Filter.Eventually.of_forall fun x => by simp))
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have h1 := OTDROL7.ellRob_ge ℓ A δ β lam hlam x
  have h3 := OTDROL7.convex_lower ℓ h2.convex (inner ℝ β x)
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

/-- slope of `ℓ'` lies in `[0, M]` -/
lemma slope_mem (ℓ : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ ℓ) (hd : Differentiable ℝ ℓ)
    (hdd : Differentiable ℝ (deriv ℓ)) (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (s u : ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ M ∧ deriv ℓ (s + u) = deriv ℓ s + κ * u := by
  have hmono : Monotone (deriv ℓ) := by
    have := hc.monotoneOn_deriv (fun x _ => hd x)
    intro a b hab; exact this (Set.mem_univ a) (Set.mem_univ b) hab
  have hnn : ∀ x, 0 ≤ deriv (deriv ℓ) x := fun x => hmono.deriv_nonneg
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (deriv ℓ) x‖ ≤ M := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hM x
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdd x) hb convex_univ
    (Set.mem_univ s) (Set.mem_univ (s + u))
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at hlip
  rcases eq_or_ne u 0 with hu | hu
  · refine ⟨0, le_rfl, (hnn 0).trans (hM 0), ?_⟩
    simp [hu]
  · set κ := (deriv ℓ (s + u) - deriv ℓ s) / u
    have hκ : κ * u = deriv ℓ (s + u) - deriv ℓ s := by
      simp only [κ]; field_simp
    have hsign : 0 ≤ (deriv ℓ (s + u) - deriv ℓ s) * u := by
      rcases le_total 0 u with h | h
      · exact mul_nonneg (sub_nonneg.2 (hmono (by linarith))) h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hmono (by linarith))) h
    have hu2 : 0 < u ^ 2 := by positivity
    have hκ0 : 0 ≤ κ := by
      have : κ * u ^ 2 = (deriv ℓ (s + u) - deriv ℓ s) * u := by rw [← hκ]; ring
      by_contra hneg
      push_neg at hneg
      have : κ * u ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hu2
      linarith
    have hκM : κ ≤ M := by
      have h1 : |κ| * |u| ≤ M * |u| := by
        rw [← abs_mul, hκ]; exact hlip
      have := le_of_mul_le_mul_right h1 (abs_pos.2 hu)
      exact (le_abs_self κ).trans this
    exact ⟨κ, hκ0, hκM, by linarith⟩

/-- Taylor upper bound from `ℓ'' ≤ M`. -/
lemma taylor_upper (ℓ : ℝ → ℝ) (hd : Differentiable ℝ ℓ) (hdd : Differentiable ℝ (deriv ℓ))
    (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (u : ℝ) :
    ℓ u ≤ ℓ 0 + deriv ℓ 0 * u + M / 2 * u ^ 2 := by
  set g : ℝ → ℝ := fun u => ℓ 0 + deriv ℓ 0 * u + M / 2 * u ^ 2 - ℓ u with hg
  set g' : ℝ → ℝ := fun u => deriv ℓ 0 + M * u - deriv ℓ u with hg'
  have hgd : ∀ u, HasDerivAt g (g' u) u := by
    intro u
    have h1 := ((hasDerivAt_id' u).const_mul (deriv ℓ 0)).const_add (ℓ 0)
    have h2 := (hasDerivAt_pow 2 u).const_mul (M / 2)
    have h3 := (hd u).hasDerivAt
    have := (h1.add h2).sub h3
    exact this.congr_deriv (by simp only [g']; push_cast; ring)
  have hg'd : ∀ u, HasDerivAt g' (M - deriv (deriv ℓ) u) u := by
    intro u
    have h1 := ((hasDerivAt_id' u).const_mul M).const_add (deriv ℓ 0)
    have h3 := (hdd u).hasDerivAt
    have := h1.sub h3
    exact this.congr_deriv (by ring)
  have hg'mono : Monotone g' := by
    apply monotone_of_deriv_nonneg (fun u => (hg'd u).differentiableAt)
    intro u; rw [(hg'd u).deriv]; linarith [hM u]
  have hg'0 : g' 0 = 0 := by simp [g']
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun u => (hgd u).continuousAt
  have hg0 : g 0 = 0 := by simp [g]
  have key : 0 ≤ g u := by
    rcases le_total 0 u with h | h
    · have hm : MonotoneOn g (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hgc.continuousOn
          (fun v _ => (hgd v).differentiableAt.differentiableWithinAt)
        intro v hv; rw [interior_Ici] at hv
        rw [(hgd v).deriv, ← hg'0]; exact hg'mono (le_of_lt hv)
      have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
      linarith
    · have hm : AntitoneOn g (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hgc.continuousOn
          (fun v _ => (hgd v).differentiableAt.differentiableWithinAt)
        intro v hv; rw [interior_Iic] at hv
        rw [(hgd v).deriv, ← hg'0]; exact hg'mono (le_of_lt hv)
      have := hm (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
      linarith
  simp only [g] at key; linarith

lemma kappa_le (ℓ : ℝ → ℝ) (hd : Differentiable ℝ ℓ) (hdd : Differentiable ℝ (deriv ℓ))
    (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (hM0 : 0 < M) :
    OTDRO.Dual.growthKappa ℓ ≤ M / 2 := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hmem : M / 2 + ε / 2 ∈ {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} := by
    refine ⟨by positivity, ?_⟩
    refine ⟨ℓ 0 + (deriv ℓ 0) ^ 2 / (2 * ε), ?_⟩
    rintro _ ⟨u, rfl⟩
    have h := taylor_upper ℓ hd hdd M hM u
    have : deriv ℓ 0 * u - ε / 2 * u ^ 2 ≤ (deriv ℓ 0) ^ 2 / (2 * ε) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (deriv ℓ 0 - ε * u)]
    show ℓ u - (M / 2 + ε / 2) * u ^ 2 ≤ _
    nlinarith
  have := csInf_le ⟨0, fun s hs => hs.1⟩ hmem
  unfold OTDRO.Dual.growthKappa
  linarith

lemma sq_deriv_integrable {P0 : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P0]
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (hd : Differentiable ℝ ℓ)
    (hdd : Differentiable ℝ (deriv ℓ)) (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (hM0 : 0 < M)
    (β : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => (deriv ℓ (inner ℝ β x)) ^ 2) P0 := by
  have hlip : ∀ u, |deriv ℓ u| ≤ |deriv ℓ 0| + M * |u| := by
    intro u
    obtain ⟨κ, hκ0, hκM, hκ⟩ := slope_mem ℓ h2.convex hd hdd M hM 0 u
    rw [zero_add] at hκ
    rw [hκ]
    calc |deriv ℓ 0 + κ * u| ≤ |deriv ℓ 0| + |κ * u| := abs_add_le _ _
      _ ≤ |deriv ℓ 0| + M * |u| := by
        rw [abs_mul, abs_of_nonneg hκ0]
        have := mul_le_mul_of_nonneg_right hκM (abs_nonneg u); linarith
  set c0 := |deriv ℓ 0|
  have h2int := integrable_norm_pow h2.moment4 2 (by norm_num)
  refine Integrable.mono' ((integrable_const (2 * c0 ^ 2)).add
    (h2int.const_mul (2 * (M * ‖β‖) ^ 2))) (Continuous.aestronglyMeasurable (by
      have := hdd.continuous; fun_prop)) (Filter.Eventually.of_forall fun x => ?_)
  have h1 := hlip (inner ℝ β x)
  have h4 : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := abs_real_inner_le_norm β x
  have h5 : M * |inner ℝ β x| ≤ M * ‖β‖ * ‖x‖ := by
    have := mul_le_mul_of_nonneg_left h4 hM0.le; linarith
  have h6 : |deriv ℓ (inner ℝ β x)| ≤ c0 + M * ‖β‖ * ‖x‖ := by linarith
  have h7 : 0 ≤ |deriv ℓ (inner ℝ β x)| := abs_nonneg _
  simp only [Real.norm_eq_abs, abs_pow, Pi.add_apply]
  have : |deriv ℓ (inner ℝ β x)| ^ 2 ≤ (c0 + M * ‖β‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ h7 h6 2
  nlinarith [sq_nonneg (c0 - M * ‖β‖ * ‖x‖)]

lemma right_deriv_nonneg {g : ℝ → ℝ} {D a : ℝ} (h : HasDerivWithinAt g D (Set.Ici a) a)
    (hmin : ∀ b, a < b → g a ≤ g b) : 0 ≤ D := by
  have h' := h.Ioi_of_Ici
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi a) (by simp)] at h'
  apply ge_of_tendsto h'
  filter_upwards [self_mem_nhdsWithin] with b hb
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.2 (hmin b hb)) (sub_nonneg.2 (le_of_lt hb))

lemma left_deriv_nonpos {g : ℝ → ℝ} {D a T : ℝ} (hT : T < a)
    (h : HasDerivWithinAt g D (Set.Iic a) a)
    (hmin : ∀ b, T < b → b < a → g a ≤ g b) : D ≤ 0 := by
  have h' := h.Iio_of_Iic
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Iio a) (by simp)] at h'
  apply le_of_tendsto h'
  have hev : ∀ᶠ b in 𝓝[<] a, T < b := nhdsWithin_le_nhds (Ioi_mem_nhds hT)
  filter_upwards [self_mem_nhdsWithin, hev] with b hb hTb
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hmin b hTb hb)) (sub_nonpos.2 (le_of_lt hb))

/-- real representative of a finite `f_δ` -/
lemma real_rep (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (hℓc : Continuous ℓ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam)
    (htop : OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊤) :
    Integrable (fun x => (OTDRO.Dual.ellRob ℓ A δ β lam x).toReal) P0 ∧
    OTDRO.Dual.fDelta P0 ℓ A δ β lam =
      ((∫ x, (OTDRO.Dual.ellRob ℓ A δ β lam x).toReal ∂P0 : ℝ) : EReal) ∧
    ∀ᵐ x ∂P0, OTDRO.Dual.ellRob ℓ A δ β lam x =
      (((OTDRO.Dual.ellRob ℓ A δ β lam x).toReal : ℝ) : EReal) := by
  have hN := negpart_finite P0 A ℓ h2 δ β lam hlam
  have hbot := extIntegral_ne_bot_of P0 _ hN
  obtain ⟨hP, -⟩ := extIntegral_parts_finite P0 _ htop hbot
  have hmeas := ellRob_measurable ℓ hℓc A hA.posDef hA.lsc δ β lam
  have hlt : ∀ᵐ x ∂P0, (OTDRO.Dual.ellRob ℓ A δ β lam x).toENNReal < ⊤ :=
    ae_lt_top' hmeas.ereal_toENNReal.aemeasurable hP.ne
  have hae : ∀ᵐ x ∂P0, OTDRO.Dual.ellRob ℓ A δ β lam x =
      (((OTDRO.Dual.ellRob ℓ A δ β lam x).toReal : ℝ) : EReal) := by
    filter_upwards [hlt] with x hx
    have h1 : OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊤ := by
      intro h; rw [h] at hx; simp at hx
    have h2' : OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊥ := by
      intro h; have := ellRob_ge ℓ A δ β lam hlam x; rw [h] at this
      exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
    exact (EReal.coe_toReal h1 h2').symm
  have hint : Integrable (fun x => (OTDRO.Dual.ellRob ℓ A δ β lam x).toReal) P0 := by
    apply integrable_of_parts P0 _ hmeas.ereal_toReal.aestronglyMeasurable
    · exact lt_of_le_of_lt (lintegral_mono fun x => ofReal_toReal_le _) hP
    · exact lt_of_le_of_lt (lintegral_mono fun x => ofReal_neg_toReal_le _) hN
  refine ⟨hint, ?_, hae⟩
  unfold OTDRO.Dual.fDelta
  rw [extIntegral_congr_ae P0 _ _ hae]
  exact extIntegral_of_integrable P0 _ hint

end OTDROL7

open OTDROL7 in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar) :
    (1 / 2) / Real.sqrt ρmax * ‖β‖ *
      Real.sqrt (∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0) ≤ lamStar ∧
    lamStar ≤ (1 / Real.sqrt ρmin) * ‖β‖ *
      Real.sqrt (∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0) +
      (1 / 2) * Real.sqrt δ * M / ρmin * ‖β‖ ^ 2 := by
  have hc : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hρ := hA.rhoMin_pos
  have hρM := hA.rhoMax_pos
  have hM := h3.M_pos
  have hℓc : Continuous ℓ := h3.differentiable.continuous
  set E := ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 with hEdef
  have hEint := sq_deriv_integrable ℓ h2 h3.differentiable h3.deriv_differentiable M
    h3.second_deriv_le hM β
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hmin' : ∀ l, 0 ≤ l → OTDRO.Dual.fDelta P0 ℓ A δ β lamStar ≤
      OTDRO.Dual.fDelta P0 ℓ A δ β l := fun l hl => hmin (Set.mem_Ici.2 hl)
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · -- β = 0
    subst hβ0
    have hF : ∀ l x, OTDRO.Dual.ellRob ℓ A δ 0 l x = ((ℓ 0 + l * Real.sqrt δ : ℝ) : EReal) := by
      intro l x
      have hq : OTDRO.Dual.quadInv A 0 x = 0 := by simp [OTDRO.Dual.quadInv]
      unfold OTDRO.Dual.ellRob OTDRO.Dual.Fobj
      simp only [hq, inner_zero_left]
      have : ∀ γ : ℝ, ℓ (0 + γ * Real.sqrt δ * 0) - l * Real.sqrt δ * (γ ^ 2 * 0 - 1) =
          ℓ 0 + l * Real.sqrt δ := fun γ => by ring_nf
      simp_rw [this]; exact iSup_const
    have hf : ∀ l, OTDRO.Dual.fDelta P0 ℓ A δ 0 l = ((ℓ 0 + l * Real.sqrt δ : ℝ) : EReal) := by
      intro l
      unfold OTDRO.Dual.fDelta
      simp_rw [hF]
      rw [extIntegral_of_integrable P0 _ (integrable_const _)]
      simp
    have := hmin' 0 le_rfl
    rw [hf, hf, EReal.coe_le_coe_iff] at this
    have hl0 : lamStar ≤ 0 := by nlinarith
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  -- β ≠ 0
  have hq : ∀ x, 0 < OTDRO.Dual.quadInv A β x := fun x => quadInv_pos A hA.posDef β hβ0 x
  obtain ⟨hDfin, hDder⟩ := OTDRO.WorstCase.dual_lambda_derivatives P0 A ρmin ρmax hA ℓ h2 δ hδ
    B hB β hβB hβ0
  obtain ⟨-, hED2, hED3⟩ := OTDRO.WorstCase.effective_domain P0 A ρmin ρmax hA ℓ h2 δ hδ B hB
  set T := OTDRO.Dual.lamThr P0 ℓ A δ β with hTdef
  set Q := essSup (fun y => OTDRO.Dual.quadInv A β y) P0 with hQdef
  have hbu : Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := ‖β‖ ^ 2 / ρmin)
    filter_upwards [hA.eig_bounds] with x hx
    exact quadInv_le A hA.posDef β x ρmin hρ (fun v => (hx v).1)
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae P0) (fun y => OTDRO.Dual.quadInv A β y) :=
    Filter.isCoboundedUnder_le_of_le (ae P0) (fun y => quadInv_nonneg A hA.posDef β y)
  have hQle : Q ≤ ‖β‖ ^ 2 / ρmin := by
    apply essSup_le_of_ae_le _ _ hcob
    filter_upwards [hA.eig_bounds] with y hy
    exact quadInv_le A hA.posDef β y ρmin hρ (fun v => (hy v).1)
  have hQ0 : 0 ≤ Q := by
    have hae := ae_le_essSup hbu
    obtain ⟨x, hx⟩ := hae.exists
    exact (hq x).le.trans hx
  have hk0 := kappa_nonneg ℓ h2.growth
  have hkM := kappa_le ℓ h3.differentiable h3.deriv_differentiable M h3.second_deriv_le hM
  have hT0 : 0 ≤ T := by
    show 0 ≤ OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * Q; positivity
  set U0 := 1 / 2 * Real.sqrt δ * M / ρmin * ‖β‖ ^ 2 with hU0
  have hTU : T ≤ U0 := by
    show OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * Q ≤ U0
    have h1 : OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * Q ≤ M / 2 * Real.sqrt δ * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkM hc.le) hQ0
    have h2' : M / 2 * Real.sqrt δ * Q ≤ M / 2 * Real.sqrt δ * (‖β‖ ^ 2 / ρmin) :=
      mul_le_mul_of_nonneg_left hQle (by positivity)
    have e : U0 = M / 2 * Real.sqrt δ * (‖β‖ ^ 2 / ρmin) := by simp only [U0]; ring
    linarith
  -- finiteness at lamStar
  have hNbot : ∀ l, 0 ≤ l → OTDRO.Dual.fDelta P0 ℓ A δ β l ≠ ⊥ := fun l hl =>
    extIntegral_ne_bot_of P0 _ (negpart_finite P0 A ℓ h2 δ β l hl)
  have hstar_top : OTDRO.Dual.fDelta P0 ℓ A δ β lamStar ≠ ⊤ := by
    have h1 := (hDfin (T + 1) (by linarith)).1
    exact ne_top_of_le_ne_top h1 (hmin' (T + 1) (by linarith))
  have hTstar : T ≤ lamStar := hED3 β hβB lamStar hlam (lt_top_iff_ne_top.2 hstar_top)
  have hfr_le : ∀ a b, 0 ≤ a → T < b → OTDRO.Dual.fDelta P0 ℓ A δ β a ≤
      OTDRO.Dual.fDelta P0 ℓ A δ β b →
      (OTDRO.Dual.fDelta P0 ℓ A δ β a).toReal ≤ (OTDRO.Dual.fDelta P0 ℓ A δ β b).toReal := by
    intro a b ha hb hab
    exact EReal.toReal_le_toReal hab (hNbot a ha) (hDfin b hb).1
  -- key lower-bound claim
  have hK : ∀ a, T < a → (∀ b, a < b → OTDRO.Dual.fDelta P0 ℓ A δ β a ≤
      OTDRO.Dual.fDelta P0 ℓ A δ β b) →
      (1 / 2) / Real.sqrt ρmax * ‖β‖ * Real.sqrt E ≤ a := by
    intro a hTa hmono
    have ha0 : 0 < a := lt_of_le_of_lt hT0 hTa
    obtain ⟨hae, hiInf, -, hR, -⟩ := hDder a hTa
    have hRnn := right_deriv_nonneg hR (fun b hab =>
      hfr_le a b ha0.le (hTa.trans hab) (hmono b hab))
    have hI1 : ∫ x, OTDRO.Dual.quadInv A β x *
        sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β a x) ∂P0 ≤ 1 := by
      have := (mul_nonneg_iff_of_pos_left hc).1 hRnn; linarith
    have hpt : ∀ᵐ x ∂P0, ‖β‖ ^ 2 / ρmax * (1 / (4 * a ^ 2)) * (deriv ℓ (inner ℝ β x)) ^ 2 ≤
        OTDRO.Dual.quadInv A β x *
          sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β a x) := by
      filter_upwards [hae, hA.eig_bounds] with x hx hxe
      have hqge := quadInv_ge A hA.posDef β x hβ0 ρmax hρM (fun v => (hxe v).2)
      have hfo := OTDRO.StrongCvx.maximizer_first_order P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB
        hβ0 x a ha0 h3.differentiable hx.1
      have hinf : (deriv ℓ (inner ℝ β x)) ^ 2 / (4 * a ^ 2) ≤
          sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β a x) := by
        apply le_csInf (hx.1.image _)
        rintro _ ⟨γ, hγ, rfl⟩
        have h1 := (hfo γ hγ).2
        have h0 : 0 ≤ |deriv ℓ (inner ℝ β x)| / (2 * a) := by positivity
        have := pow_le_pow_left₀ h0 h1 2
        rw [div_pow, sq_abs, sq_abs] at this
        calc (deriv ℓ (inner ℝ β x)) ^ 2 / (4 * a ^ 2)
            = (deriv ℓ (inner ℝ β x)) ^ 2 / (2 * a) ^ 2 := by ring
          _ ≤ γ ^ 2 := this
      have e : ‖β‖ ^ 2 / ρmax * (1 / (4 * a ^ 2)) * (deriv ℓ (inner ℝ β x)) ^ 2 =
          ‖β‖ ^ 2 / ρmax * ((deriv ℓ (inner ℝ β x)) ^ 2 / (4 * a ^ 2)) := by ring
      rw [e]
      exact mul_le_mul hqge hinf (by positivity) (hq x).le
    have hint2 := hEint.const_mul (‖β‖ ^ 2 / ρmax * (1 / (4 * a ^ 2)))
    have hmono2 := integral_mono_ae hint2 hiInf hpt
    rw [integral_const_mul] at hmono2
    have hb : ‖β‖ ^ 2 / ρmax * (1 / (4 * a ^ 2)) * E ≤ 1 := hmono2.trans hI1
    -- conclude
    have hb2 : ‖β‖ ^ 2 * E ≤ 4 * a ^ 2 * ρmax := by
      have e : ‖β‖ ^ 2 / ρmax * (1 / (4 * a ^ 2)) * E = ‖β‖ ^ 2 * E / (4 * a ^ 2 * ρmax) := by
        field_simp
      rw [e, div_le_one (by positivity)] at hb
      exact hb
    have hs := Real.sqrt_le_sqrt hb2
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq ha0.le, show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hs
    have hsr : 0 < Real.sqrt ρmax := Real.sqrt_pos.2 hρM
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hsr]
    linarith
  refine ⟨?_, ?_⟩
  · -- lower bound
    rcases eq_or_lt_of_le hTstar with hTeq | hTlt
    · -- lamStar = T: convexity argument
      apply le_of_forall_gt_imp_ge_of_dense
      intro a hTa
      rw [← hTeq] at hTa
      apply hK a hTa
      intro b hab
      have hTb : T < b := hTa.trans hab
      obtain ⟨hint0, hf0, hae0⟩ := real_rep P0 A ρmin ρmax hA ℓ h2 hℓc δ β lamStar hlam
        hstar_top
      obtain ⟨hinta, hfa, haea⟩ := real_rep P0 A ρmin ρmax hA ℓ h2 hℓc δ β a
        (hT0.trans hTa.le) (hDfin a hTa).1
      obtain ⟨hintb, hfb, haeb⟩ := real_rep P0 A ρmin ρmax hA ℓ h2 hℓc δ β b
        (hT0.trans hTb.le) (hDfin b hTb).1
      have hlb : lamStar < a := by rw [← hTeq]; exact hTa
      set t := (b - a) / (b - lamStar) with ht
      have hbl : 0 < b - lamStar := by linarith
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hbl.le
      have ht1 : t ≤ 1 := by rw [div_le_one hbl]; linarith
      have hat : a = t * lamStar + (1 - t) * b := by
        simp only [t]; field_simp; ring
      have hpt : ∀ᵐ x ∂P0, (OTDRO.Dual.ellRob ℓ A δ β a x).toReal ≤
          t * (OTDRO.Dual.ellRob ℓ A δ β lamStar x).toReal +
            (1 - t) * (OTDRO.Dual.ellRob ℓ A δ β b x).toReal := by
        filter_upwards [hae0, haea, haeb] with x h0 ha hb
        have key : OTDRO.Dual.ellRob ℓ A δ β a x ≤
            ((t * (OTDRO.Dual.ellRob ℓ A δ β lamStar x).toReal +
              (1 - t) * (OTDRO.Dual.ellRob ℓ A δ β b x).toReal : ℝ) : EReal) := by
          refine (iSup_le fun γ => ?_ : (⨆ γ : ℝ, ((OTDRO.Dual.Fobj ℓ A δ γ β a x : ℝ) : EReal)) ≤ _)
          rw [EReal.coe_le_coe_iff]
          have e1 : ((OTDRO.Dual.Fobj ℓ A δ γ β lamStar x : ℝ) : EReal) ≤
              OTDRO.Dual.ellRob ℓ A δ β lamStar x :=
            le_iSup (fun c => ((OTDRO.Dual.Fobj ℓ A δ c β lamStar x : ℝ) : EReal)) γ
          have e2 : ((OTDRO.Dual.Fobj ℓ A δ γ β b x : ℝ) : EReal) ≤
              OTDRO.Dual.ellRob ℓ A δ β b x :=
            le_iSup (fun c => ((OTDRO.Dual.Fobj ℓ A δ c β b x : ℝ) : EReal)) γ
          rw [h0, EReal.coe_le_coe_iff] at e1
          rw [hb, EReal.coe_le_coe_iff] at e2
          have hlin : OTDRO.Dual.Fobj ℓ A δ γ β a x =
              t * OTDRO.Dual.Fobj ℓ A δ γ β lamStar x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ β b x := by
            unfold OTDRO.Dual.Fobj; rw [hat]; ring
          rw [hlin]
          have := mul_le_mul_of_nonneg_left e1 ht0
          have := mul_le_mul_of_nonneg_left e2 (by linarith : 0 ≤ 1 - t)
          linarith
        rw [ha, EReal.coe_le_coe_iff] at key
        exact key
      have hI : ∫ x, (OTDRO.Dual.ellRob ℓ A δ β a x).toReal ∂P0 ≤
          ∫ x, (t * (OTDRO.Dual.ellRob ℓ A δ β lamStar x).toReal +
            (1 - t) * (OTDRO.Dual.ellRob ℓ A δ β b x).toReal) ∂P0 :=
        integral_mono_ae hinta ((hint0.const_mul t).add (hintb.const_mul (1 - t))) hpt
      rw [integral_add (hint0.const_mul t) (hintb.const_mul (1 - t)), integral_const_mul,
        integral_const_mul] at hI
      have h0b := hmin' b (hT0.trans hTb.le)
      rw [hf0, hfb, EReal.coe_le_coe_iff] at h0b
      rw [hfa, hfb, EReal.coe_le_coe_iff]
      have := mul_le_mul_of_nonneg_left h0b ht0
      nlinarith
    · exact hK lamStar hTlt (fun b hb => hmin' b (hlam.trans hb.le))
  · -- upper bound
    have hfirst : 0 ≤ (1 / Real.sqrt ρmin) * ‖β‖ * Real.sqrt E := by positivity
    by_cases hU : lamStar ≤ U0
    · linarith
    push_neg at hU
    have hTlt : T < lamStar := lt_of_le_of_lt hTU hU
    have hl0 : 0 < lamStar := lt_of_le_of_lt hT0 hTlt
    obtain ⟨hae, -, hiSup, -, hL⟩ := hDder lamStar hTlt
    have hLnp := left_deriv_nonpos hTlt hL (fun b hTb hb =>
      hfr_le lamStar b hlam hTb (hmin' b (hT0.trans hTb.le)))
    have hI1 : 1 ≤ ∫ x, OTDRO.Dual.quadInv A β x *
        sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lamStar x) ∂P0 := by
      have : Real.sqrt δ * (1 - ∫ x, OTDRO.Dual.quadInv A β x *
          sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lamStar x) ∂P0) ≤
          Real.sqrt δ * 0 := by linarith
      have := le_of_mul_le_mul_left this hc
      linarith
    set D0 := 2 * lamStar - Real.sqrt δ * M * (‖β‖ ^ 2 / ρmin) with hD0
    have hD0eq : D0 = 2 * (lamStar - U0) := by simp only [D0, U0]; ring
    have hD0pos : 0 < D0 := by rw [hD0eq]; linarith
    have hpt : ∀ᵐ x ∂P0, OTDRO.Dual.quadInv A β x *
        sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lamStar x) ≤
        ‖β‖ ^ 2 / ρmin * (1 / D0 ^ 2) * (deriv ℓ (inner ℝ β x)) ^ 2 := by
      filter_upwards [hae, hA.eig_bounds] with x hx hxe
      have hqle := quadInv_le A hA.posDef β x ρmin hρ (fun v => (hxe v).1)
      have hfo := OTDRO.StrongCvx.maximizer_first_order P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB
        hβ0 x lamStar hl0 h3.differentiable hx.1
      have hsup : sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lamStar x) ≤
          (deriv ℓ (inner ℝ β x)) ^ 2 / D0 ^ 2 := by
        apply csSup_le (hx.1.image _)
        rintro _ ⟨γ, hγ, rfl⟩
        have h1 := (hfo γ hγ).1
        set q := OTDRO.Dual.quadInv A β x
        set s := inner ℝ β x
        obtain ⟨κ, hκ0, hκM, hκ⟩ := slope_mem ℓ h2.convex h3.differentiable
          h3.deriv_differentiable M h3.second_deriv_le s (Real.sqrt δ * γ * q)
        have hfoc : deriv ℓ (s + Real.sqrt δ * γ * q) = 2 * lamStar * γ := by
          have h2l : 0 < 2 * lamStar := by linarith
          rw [eq_div_iff h2l.ne'] at h1; linarith
        set D := 2 * lamStar - κ * (Real.sqrt δ * q)
        have hDeq : γ * D = deriv ℓ s := by simp only [D]; linear_combination hκ - hfoc
        have hDge : D0 ≤ D := by
          simp only [D, D0]
          have h1' : κ * (Real.sqrt δ * q) ≤ M * (Real.sqrt δ * q) :=
            mul_le_mul_of_nonneg_right hκM (mul_nonneg hc.le (hq x).le)
          have h2' : M * (Real.sqrt δ * q) ≤ Real.sqrt δ * M * (‖β‖ ^ 2 / ρmin) := by
            rw [show M * (Real.sqrt δ * q) = Real.sqrt δ * M * q by ring]
            exact mul_le_mul_of_nonneg_left hqle (by positivity)
          linarith
        have hDpos : 0 < D := lt_of_lt_of_le hD0pos hDge
        have habs : |γ| ≤ |deriv ℓ s| / D0 := by
          rw [le_div_iff₀ hD0pos, ← hDeq, abs_mul, abs_of_pos hDpos]
          exact mul_le_mul_of_nonneg_left hDge (abs_nonneg _)
        have := pow_le_pow_left₀ (abs_nonneg γ) habs 2
        rw [div_pow, sq_abs, sq_abs] at this
        exact this
      calc OTDRO.Dual.quadInv A β x *
            sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lamStar x)
          ≤ ‖β‖ ^ 2 / ρmin * ((deriv ℓ (inner ℝ β x)) ^ 2 / D0 ^ 2) := by
            apply mul_le_mul hqle hsup _ (by positivity)
            apply Real.sSup_nonneg
            rintro _ ⟨γ, -, rfl⟩; exact sq_nonneg γ
        _ = ‖β‖ ^ 2 / ρmin * (1 / D0 ^ 2) * (deriv ℓ (inner ℝ β x)) ^ 2 := by ring
    have hint2 := hEint.const_mul (‖β‖ ^ 2 / ρmin * (1 / D0 ^ 2))
    have hmono2 := integral_mono_ae hiSup hint2 hpt
    rw [integral_const_mul] at hmono2
    have hb : 1 ≤ ‖β‖ ^ 2 / ρmin * (1 / D0 ^ 2) * E := hI1.trans hmono2
    have hb2 : D0 ^ 2 ≤ ‖β‖ ^ 2 * E / ρmin := by
      have e : ‖β‖ ^ 2 / ρmin * (1 / D0 ^ 2) * E = (‖β‖ ^ 2 * E / ρmin) / D0 ^ 2 := by ring
      rw [e, one_le_div (by positivity)] at hb
      exact hb
    have hs := Real.sqrt_le_sqrt hb2
    rw [Real.sqrt_sq hD0pos.le, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (norm_nonneg _)] at hs
    have hsr : 0 < Real.sqrt ρmin := Real.sqrt_pos.2 hρ
    have e1 : 1 / Real.sqrt ρmin * ‖β‖ * Real.sqrt E = ‖β‖ * Real.sqrt E / Real.sqrt ρmin := by
      ring
    have hpos : 0 ≤ ‖β‖ * Real.sqrt E / Real.sqrt ρmin := by positivity
    rw [e1]
    rw [hD0eq] at hs
    show lamStar ≤ ‖β‖ * Real.sqrt E / Real.sqrt ρmin + U0
    linarith
