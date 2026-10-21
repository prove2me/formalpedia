-- Prove2me | solution 1 for SaddleSplit.Async.proposition_2_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:41:43.016337+00:00
-- url     : https://prove2.me/submissions/a9ef0c8f-2a04-4e0f-9c6c-799167f4c1f5

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting
import Theorems.Thm_DouglasRachfordPPA_GenDR_minty_theorem
import Theorems.Thm_DouglasRachfordPPA_GenDR_resolvent_single_valued_full_domain

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Gen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ss_resolvent_nonexp (A : E → Set E) (hA : IsMonotoneOp A) (γ : ℝ) (hγ : 0 < γ)
    (J : E → E) (hJ : IsResolvent γ A J) (u v : E) : ‖J u - J v‖ ≤ ‖u - v‖ := by
  have h := hA _ _ _ _ (hJ u) (hJ v)
  have e : γ⁻¹ • (u - J u) - γ⁻¹ • (v - J v) = γ⁻¹ • ((u - v) - (J u - J v)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have hγi : 0 < γ⁻¹ := inv_pos.2 hγ
  have h2 : ‖J u - J v‖ ^ 2 ≤ ⟪J u - J v, u - v⟫_ℝ := by nlinarith
  have h3 := real_inner_le_norm (J u - J v) (u - v)
  by_cases h0 : ‖J u - J v‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖J u - J v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem ss_addSV_monotone (A : E → Set E) (hA : IsMonotoneOp A) (F : E → E)
    (hF : ∀ x y, 0 ≤ ⟪x - y, F x - F y⟫_ℝ) : IsMonotoneOp (addSV A F) := by
  rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have e : a + F x - (b + F y) = (a - b) + (F x - F y) := by abel
  rw [e, inner_add_right]
  linarith [hA x y a b ha hb, hF x y]

theorem ss_max_add_lip [CompleteSpace E] (A : E → Set E) (hA : IsMaximalMonotone A) (F : E → E)
    (hFm : ∀ x y, 0 ≤ ⟪x - y, F x - F y⟫_ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hFL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) : IsMaximalMonotone (addSV A F) := by
  have hmon := ss_addSV_monotone A hA.1 F hFm
  rw [minty_theorem _ hmon]
  rw [Set.eq_univ_iff_forall]
  intro y
  set Lg : ℝ := 1 + L with hLg
  have hLg1 : 1 ≤ Lg := by linarith
  set lam : ℝ := 1 / Lg ^ 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]; nlinarith
  have hlamL : lam ^ 2 * Lg ^ 2 = lam := by
    rw [hlam]; field_simp
  obtain ⟨J, hJ, -⟩ := ((resolvent_single_valued_full_domain lam hlam0 A).2.2 hA)
  have hJn := ss_resolvent_nonexp A hA.1 lam hlam0 J hJ
  let Φ : E → E := fun x => J (x - lam • (x + F x - y))
  have hcontr : ∀ x x', ‖Φ x - Φ x'‖ ≤ Real.sqrt (1 - lam) * ‖x - x'‖ := by
    intro x x'
    refine (hJn _ _).trans ?_
    set d := x - x' with hd
    set g := d + (F x - F x') with hg
    have e : (x - lam • (x + F x - y)) - (x' - lam • (x' + F x' - y)) = d - lam • g := by
      rw [hd, hg]; module
    rw [e]
    have hdg : ‖d‖ ^ 2 ≤ ⟪d, g⟫_ℝ := by
      rw [hg, inner_add_right, real_inner_self_eq_norm_sq]; linarith [hFm x x']
    have hgn : ‖g‖ ≤ Lg * ‖d‖ := by
      rw [hg, hLg]
      calc ‖d + (F x - F x')‖ ≤ ‖d‖ + ‖F x - F x'‖ := norm_add_le _ _
        _ ≤ ‖d‖ + L * ‖d‖ := by linarith [hFL x x']
        _ = (1 + L) * ‖d‖ := by ring
    have hsq : ‖d - lam • g‖ ^ 2 ≤ (1 - lam) * ‖d‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hlam0, mul_pow]
      have h1 : ‖g‖ ^ 2 ≤ Lg ^ 2 * ‖d‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg g) hgn 2
        rw [mul_pow] at this; exact this
      have h2 : lam ^ 2 * ‖g‖ ^ 2 ≤ lam ^ 2 * (Lg ^ 2 * ‖d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : lam ^ 2 * (Lg ^ 2 * ‖d‖ ^ 2) = lam * ‖d‖ ^ 2 := by
        rw [← mul_assoc, hlamL]
      nlinarith
    have h0 : 0 ≤ 1 - lam := by linarith
    calc ‖d - lam • g‖ = Real.sqrt (‖d - lam • g‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 - lam) * ‖d‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (1 - lam) * ‖d‖ := by
        rw [Real.sqrt_mul h0, Real.sqrt_sq (norm_nonneg _)]
  have hK : Real.sqrt (1 - lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  have hC : ContractingWith (Real.sqrt (1 - lam)).toNNReal Φ := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]; simpa using hK
    · refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
      exact hcontr x x'
  haveI : Nonempty E := ⟨0⟩
  set x := ContractingWith.fixedPoint Φ hC
  have hfix : Φ x = x := ContractingWith.fixedPoint_isFixedPt hC
  set u := x - lam • (x + F x - y) with hu
  have hJu : J u = x := hfix
  have hr := hJ u
  rw [hJu] at hr
  have e : lam⁻¹ • (u - x) = y - x - F x := by
    rw [hu, sub_sub_cancel_left, smul_neg, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
    abel
  rw [e] at hr
  refine ⟨x, x, rfl, y - x - F x + F x, ⟨_, hr, rfl⟩, ?_⟩
  abel

theorem ss_zer_closed_convex (T : E → Set E) (hT : IsMaximalMonotone T) :
    IsClosed (zer T) ∧ Convex ℝ (zer T) := by
  have hchar : zer T = ⋂ (p : E × E) (_ : p.2 ∈ T p.1), {x | ⟪x, p.2⟫_ℝ ≤ ⟪p.1, p.2⟫_ℝ} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hx p hp
      have := hT.1 x p.1 0 p.2 hx hp
      rw [zero_sub, inner_neg_right, inner_sub_left] at this
      linarith
    · intro h
      classical
      let T' : E → Set E := fun u => T u ∪ {w | u = x ∧ w = 0}
      have hmon : IsMonotoneOp T' := by
        intro a b u v hu hv
        rcases hu with hu | ⟨rfl, rfl⟩ <;> rcases hv with hv | ⟨rfl, rfl⟩
        · exact hT.1 _ _ _ _ hu hv
        · have := h (a, u) hu
          simp only at this
          rw [sub_zero, inner_sub_left]
          linarith
        · have := h (b, v) hv
          simp only at this
          rw [zero_sub, inner_neg_right, inner_sub_left]
          linarith
        · simp
      have hsub : ∀ u, T u ⊆ T' u := fun u w hw => Or.inl hw
      have heq := hT.2 T' hmon hsub
      have : (0 : E) ∈ T' x := Or.inr ⟨rfl, rfl⟩
      rw [heq] at this
      exact this
  rw [hchar]
  refine ⟨isClosed_iInter fun p => isClosed_iInter fun _ => ?_,
    convex_iInter fun p => convex_iInter fun _ => ?_⟩
  · exact isClosed_le (continuous_id.inner continuous_const) continuous_const
  · exact convex_halfSpace_le (isBoundedBilinearMap_inner.isBoundedLinearMap_left p.2).toIsLinearMap _
end Gen


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section XS
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem xs_eta (X : XSpace H G) : mkX (pX X) (pY X) (pZ X) (pV X) = X := rfl

theorem xs_ext {X X' : XSpace H G} (h1 : pX X = pX X') (h2 : pY X = pY X')
    (h3 : pZ X = pZ X') (h4 : pV X = pV X') : X = X' := by
  rw [← xs_eta X, ← xs_eta X', h1, h2, h3, h4]

@[simp] theorem pX_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pX (mkX x y z v) = x := rfl
@[simp] theorem pY_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pY (mkX x y z v) = y := rfl
@[simp] theorem pZ_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pZ (mkX x y z v) = z := rfl
@[simp] theorem pV_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pV (mkX x y z v) = v := rfl
@[simp] theorem pX_add (X X' : XSpace H G) : pX (X + X') = pX X + pX X' := rfl
@[simp] theorem pY_add (X X' : XSpace H G) : pY (X + X') = pY X + pY X' := rfl
@[simp] theorem pZ_add (X X' : XSpace H G) : pZ (X + X') = pZ X + pZ X' := rfl
@[simp] theorem pV_add (X X' : XSpace H G) : pV (X + X') = pV X + pV X' := rfl
@[simp] theorem pX_sub (X X' : XSpace H G) : pX (X - X') = pX X - pX X' := rfl
@[simp] theorem pY_sub (X X' : XSpace H G) : pY (X - X') = pY X - pY X' := rfl
@[simp] theorem pZ_sub (X X' : XSpace H G) : pZ (X - X') = pZ X - pZ X' := rfl
@[simp] theorem pV_sub (X X' : XSpace H G) : pV (X - X') = pV X - pV X' := rfl
@[simp] theorem pX_smul (c : ℝ) (X : XSpace H G) : pX (c • X) = c • pX X := rfl
@[simp] theorem pY_smul (c : ℝ) (X : XSpace H G) : pY (c • X) = c • pY X := rfl
@[simp] theorem pZ_smul (c : ℝ) (X : XSpace H G) : pZ (c • X) = c • pZ X := rfl
@[simp] theorem pV_smul (c : ℝ) (X : XSpace H G) : pV (c • X) = c • pV X := rfl
@[simp] theorem pX_zero : pX (0 : XSpace H G) = 0 := rfl
@[simp] theorem pY_zero : pY (0 : XSpace H G) = 0 := rfl
@[simp] theorem pZ_zero : pZ (0 : XSpace H G) = 0 := rfl
@[simp] theorem pV_zero : pV (0 : XSpace H G) = 0 := rfl

theorem xs_inner4 (X X' : XSpace H G) : ⟪X, X'⟫_ℝ =
    ⟪pX X, pX X'⟫_ℝ + ⟪pY X, pY X'⟫_ℝ + ⟪pZ X, pZ X'⟫_ℝ + ⟪pV X, pV X'⟫_ℝ := by
  simp only [WithLp.prod_inner_apply, pX, pY, pZ, pV]; ring

theorem xs_inner (X X' : XSpace H G) : ⟪X, X'⟫_ℝ =
    ∑ i, ⟪pX X i, pX X' i⟫_ℝ + ∑ k, ⟪pY X k, pY X' k⟫_ℝ + ∑ k, ⟪pZ X k, pZ X' k⟫_ℝ
      + ∑ k, ⟪pV X k, pV X' k⟫_ℝ := by
  rw [xs_inner4]; simp only [PiLp.inner_apply]

theorem xs_normsq4 (X : XSpace H G) : ‖X‖ ^ 2 =
    ‖pX X‖ ^ 2 + ‖pY X‖ ^ 2 + ‖pZ X‖ ^ 2 + ‖pV X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, xs_inner4]
  simp only [real_inner_self_eq_norm_sq]

theorem xs_normsq (X : XSpace H G) : ‖X‖ ^ 2 =
    ∑ i, ‖pX X i‖ ^ 2 + ∑ k, ‖pY X k‖ ^ 2 + ∑ k, ‖pZ X k‖ ^ 2 + ∑ k, ‖pV X k‖ ^ 2 := by
  rw [xs_normsq4]; simp only [PiLp.norm_sq_eq_of_L2]

theorem norm_pX_le (X : XSpace H G) : ‖pX X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pX X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pY_le (X : XSpace H G) : ‖pY X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pY X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pX X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pZ_le (X : XSpace H G) : ‖pZ X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pZ X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pX X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pV_le (X : XSpace H G) : ‖pV X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pV X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pX X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pXi_le (X : XSpace H G) (i : I) : ‖pX X i‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ i).trans (norm_pX_le X)
theorem norm_pYk_le (X : XSpace H G) (k : K) : ‖pY X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pY_le X)
theorem norm_pZk_le (X : XSpace H G) (k : K) : ‖pZ X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pZ_le X)
theorem norm_pVk_le (X : XSpace H G) (k : K) : ‖pV X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pV_le X)

/-- if every block coordinate is bounded by `c`, the norm is bounded. -/
theorem xs_norm_le_of_blocks (W : XSpace H G) (c : ℝ) (hc : 0 ≤ c)
    (hx : ∀ i, ‖pX W i‖ ≤ c) (hy : ∀ k, ‖pY W k‖ ≤ c) (hz : ∀ k, ‖pZ W k‖ ≤ c)
    (hv : ∀ k, ‖pV W k‖ ≤ c) :
    ‖W‖ ≤ Real.sqrt (Fintype.card I + 3 * Fintype.card K) * c := by
  have hsq : ‖W‖ ^ 2 ≤ (Fintype.card I + 3 * Fintype.card K) * c ^ 2 := by
    rw [xs_normsq]
    have h1 : ∑ i, ‖pX W i‖ ^ 2 ≤ ∑ _i : I, c ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    have h2 : ∑ k, ‖pY W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hy k) 2
    have h3 : ∑ k, ‖pZ W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
    have h4 : ∑ k, ‖pV W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hv k) 2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1 h2 h3 h4
    nlinarith
  calc ‖W‖ = Real.sqrt (‖W‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card I + 3 * Fintype.card K) * c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

end XS


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section MM
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

/-- the block-diagonal set-valued part of `𝐌`. -/
def Pop (P : Problem H G) : XSpace H G → Set (XSpace H G) := fun X => {W |
  (∀ i, pX W i ∈ P.A i (pX X i)) ∧ (∀ k, pY W k ∈ P.Bm k (pY X k)) ∧
  (∀ k, pZ W k ∈ P.Dm k (pZ X k)) ∧ pV W = 0}

/-- the single-valued part of `𝐌`. -/
noncomputable def Fop (P : Problem H G) (X : XSpace H G) : XSpace H G :=
  mkX (WithLp.toLp 2 fun i => -P.s i + P.Q i (pX X i) + P.R (pX X) i + P.Ladj (pV X) i)
    (WithLp.toLp 2 fun k => P.Bl k (pY X k) - pV X k)
    (WithLp.toLp 2 fun k => P.Dl k (pZ X k) - pV X k)
    (WithLp.toLp 2 fun k => P.r k + pY X k + pZ X k - P.Lx (pX X) k)

@[simp] theorem pX_Fop (P : Problem H G) (X : XSpace H G) (i : I) :
    pX (Fop P X) i = -P.s i + P.Q i (pX X i) + P.R (pX X) i + P.Ladj (pV X) i := rfl
@[simp] theorem pY_Fop (P : Problem H G) (X : XSpace H G) (k : K) :
    pY (Fop P X) k = P.Bl k (pY X k) - pV X k := rfl
@[simp] theorem pZ_Fop (P : Problem H G) (X : XSpace H G) (k : K) :
    pZ (Fop P X) k = P.Dl k (pZ X k) - pV X k := rfl
@[simp] theorem pV_Fop (P : Problem H G) (X : XSpace H G) (k : K) :
    pV (Fop P X) k = P.r k + pY X k + pZ X k - P.Lx (pX X) k := rfl

theorem opM_eq (P : Problem H G) : opM P = addSV (Pop P) (Fop P) := by
  funext X
  ext W
  constructor
  · rintro ⟨hx, hy, hz, hv⟩
    refine ⟨W - Fop P X, ⟨fun i => ?_, fun k => ?_, fun k => ?_, ?_⟩, (sub_add_cancel W _).symm⟩
    · obtain ⟨a, ha, he⟩ := hx i
      simp only [pX_sub, PiLp.sub_apply, pX_Fop, he]
      convert ha using 1; abel
    · obtain ⟨b, hb, he⟩ := hy k
      simp only [pY_sub, PiLp.sub_apply, pY_Fop, he]
      convert hb using 1; abel
    · obtain ⟨d, hd, he⟩ := hz k
      simp only [pZ_sub, PiLp.sub_apply, pZ_Fop, he]
      convert hd using 1; abel
    · ext k
      simp only [pV_sub, PiLp.sub_apply, pV_Fop, hv k, PiLp.zero_apply, sub_self]
  · rintro ⟨U, ⟨hx, hy, hz, hv⟩, rfl⟩
    refine ⟨fun i => ⟨pX U i, hx i, ?_⟩, fun k => ⟨pY U k, hy k, ?_⟩,
      fun k => ⟨pZ U k, hz k, ?_⟩, fun k => ?_⟩
    · simp only [pX_add, PiLp.add_apply, pX_Fop]; abel
    · simp only [pY_add, PiLp.add_apply, pY_Fop]; abel
    · simp only [pZ_add, PiLp.add_apply, pZ_Fop]; abel
    · simp only [pV_add, PiLp.add_apply, pV_Fop, hv, PiLp.zero_apply, zero_add]

theorem Pop_monotone (P : Problem H G) (hP : P.Hyp) : IsMonotoneOp (Pop P) := by
  rintro X X' W W' ⟨hx, hy, hz, hv⟩ ⟨hx', hy', hz', hv'⟩
  rw [xs_inner]
  have h1 : 0 ≤ ∑ i, ⟪pX (X - X') i, pX (W - W') i⟫_ℝ := Finset.sum_nonneg fun i _ => by
    simp only [pX_sub, PiLp.sub_apply]; exact (hP.1 i).1.1 _ _ _ _ (hx i) (hx' i)
  have h2 : 0 ≤ ∑ k, ⟪pY (X - X') k, pY (W - W') k⟫_ℝ := Finset.sum_nonneg fun k _ => by
    simp only [pY_sub, PiLp.sub_apply]; exact (hP.2.1 k).1.1 _ _ _ _ (hy k) (hy' k)
  have h3 : 0 ≤ ∑ k, ⟪pZ (X - X') k, pZ (W - W') k⟫_ℝ := Finset.sum_nonneg fun k _ => by
    simp only [pZ_sub, PiLp.sub_apply]; exact (hP.2.2.1 k).1.1 _ _ _ _ (hz k) (hz' k)
  have h4 : ∑ k, ⟪pV (X - X') k, pV (W - W') k⟫_ℝ = 0 := by
    simp [hv, hv']
  linarith

theorem Pop_maximal (P : Problem H G) (hP : P.Hyp) : IsMaximalMonotone (Pop P) := by
  have hmon := Pop_monotone P hP
  rw [minty_theorem _ hmon, Set.eq_univ_iff_forall]
  intro Y
  have hA : ∀ i, ∃ x, ∃ a ∈ P.A i x, pX Y i = x + a := by
    intro i
    have h := (minty_theorem _ (hP.1 i).1.1).1 (hP.1 i).1
    have hm : pX Y i ∈ imOp (opAdd opId (P.A i)) := by rw [h]; trivial
    obtain ⟨x, y', hy', a, ha, he⟩ := hm
    rw [show y' = x from hy'] at he
    exact ⟨x, a, ha, he⟩
  have hB : ∀ k, ∃ y, ∃ b ∈ P.Bm k y, pY Y k = y + b := by
    intro k
    have h := (minty_theorem _ (hP.2.1 k).1.1).1 (hP.2.1 k).1
    have hm : pY Y k ∈ imOp (opAdd opId (P.Bm k)) := by rw [h]; trivial
    obtain ⟨x, y', hy', a, ha, he⟩ := hm
    rw [show y' = x from hy'] at he
    exact ⟨x, a, ha, he⟩
  have hD : ∀ k, ∃ z, ∃ d ∈ P.Dm k z, pZ Y k = z + d := by
    intro k
    have h := (minty_theorem _ (hP.2.2.1 k).1.1).1 (hP.2.2.1 k).1
    have hm : pZ Y k ∈ imOp (opAdd opId (P.Dm k)) := by rw [h]; trivial
    obtain ⟨x, y', hy', a, ha, he⟩ := hm
    rw [show y' = x from hy'] at he
    exact ⟨x, a, ha, he⟩
  choose xs a ha hae using hA
  choose ys b hb hbe using hB
  choose zs d hd hde using hD
  set X : XSpace H G := mkX (WithLp.toLp 2 xs) (WithLp.toLp 2 ys) (WithLp.toLp 2 zs) (pV Y)
  refine ⟨X, X, rfl, Y - X, ⟨fun i => ?_, fun k => ?_, fun k => ?_, ?_⟩, by abel⟩
  · simp only [X, pX_sub, PiLp.sub_apply, pX_mkX, hae]
    convert ha i using 1 <;> simp
  · simp only [X, pY_sub, PiLp.sub_apply, pY_mkX, hbe]
    convert hb k using 1 <;> simp
  · simp only [X, pZ_sub, PiLp.sub_apply, pZ_mkX, hde]
    convert hd k using 1 <;> simp
  · simp [X]

end MM


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section FF
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem Ladj_sub (P : Problem H G) (v v' : PiLp 2 G) (i : I) :
    P.Ladj v i - P.Ladj v' i = P.Ladj (v - v') i := by
  simp only [Problem.Ladj, ← Finset.sum_sub_distrib, PiLp.sub_apply, map_sub]

theorem Lx_sub (P : Problem H G) (x x' : PiLp 2 H) (k : K) :
    P.Lx x k - P.Lx x' k = P.Lx (x - x') k := by
  simp only [Problem.Lx, ← Finset.sum_sub_distrib, PiLp.sub_apply, map_sub]

/-- the skew identity `⟪x, L* v⟫ = ⟪L x, v⟫`. -/
theorem Ladj_skew (P : Problem H G) (x : PiLp 2 H) (v : PiLp 2 G) :
    ∑ i, ⟪x i, P.Ladj v i⟫_ℝ = ∑ k, ⟪v k, P.Lx x k⟫_ℝ := by
  simp only [Problem.Ladj, Problem.Lx, inner_sum, sum_inner,
    ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem Fop_monotone (P : Problem H G) (hP : P.Hyp) (X X' : XSpace H G) :
    0 ≤ ⟪X - X', Fop P X - Fop P X'⟫_ℝ := by
  rw [xs_inner]
  have ex : ∀ i, (pX (Fop P X) - pX (Fop P X')) i =
      (P.Q i ((pX X) i) - P.Q i ((pX X') i)) + (P.R (pX X) - P.R (pX X')) i + P.Ladj ((pV X) - (pV X')) i := by
    intro i
    simp only [PiLp.sub_apply, pX_Fop, ← Ladj_sub]
    abel
  have ey : ∀ k, (pY (Fop P X) - pY (Fop P X')) k = (P.Bl k ((pY X) k) - P.Bl k ((pY X') k)) - ((pV X) - (pV X')) k := by
    intro k; simp only [PiLp.sub_apply, pY_Fop]; abel
  have ez : ∀ k, (pZ (Fop P X) - pZ (Fop P X')) k = (P.Dl k ((pZ X) k) - P.Dl k ((pZ X') k)) - ((pV X) - (pV X')) k := by
    intro k; simp only [PiLp.sub_apply, pZ_Fop]; abel
  have ev : ∀ k, (pV (Fop P X) - pV (Fop P X')) k = ((pY X) - (pY X')) k + ((pZ X) - (pZ X')) k - P.Lx ((pX X) - (pX X')) k := by
    intro k; simp only [PiLp.sub_apply, pV_Fop, ← Lx_sub]; abel
  simp only [pX_sub, pY_sub, pZ_sub, pV_sub]
  have hX : ∑ i, ⟪(pX X - pX X') i, (pX (Fop P X) - pX (Fop P X')) i⟫_ℝ =
      ∑ i, ⟪(pX X - pX X') i, P.Q i (pX X i) - P.Q i (pX X' i)⟫_ℝ
      + ∑ i, ⟪(pX X - pX X') i, (P.R (pX X) - P.R (pX X')) i⟫_ℝ
      + ∑ i, ⟪(pX X - pX X') i, P.Ladj (pV X - pV X') i⟫_ℝ := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ex i, inner_add_right, inner_add_right]
  have hY : ∑ k, ⟪(pY X - pY X') k, (pY (Fop P X) - pY (Fop P X')) k⟫_ℝ =
      ∑ k, ⟪(pY X - pY X') k, P.Bl k (pY X k) - P.Bl k (pY X' k)⟫_ℝ
      - ∑ k, ⟪(pY X - pY X') k, (pV X - pV X') k⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ey k, inner_sub_right]
  have hZ : ∑ k, ⟪(pZ X - pZ X') k, (pZ (Fop P X) - pZ (Fop P X')) k⟫_ℝ =
      ∑ k, ⟪(pZ X - pZ X') k, P.Dl k (pZ X k) - P.Dl k (pZ X' k)⟫_ℝ
      - ∑ k, ⟪(pZ X - pZ X') k, (pV X - pV X') k⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ez k, inner_sub_right]
  have hV : ∑ k, ⟪(pV X - pV X') k, (pV (Fop P X) - pV (Fop P X')) k⟫_ℝ =
      ∑ k, ⟪(pV X - pV X') k, (pY X - pY X') k⟫_ℝ
      + ∑ k, ⟪(pV X - pV X') k, (pZ X - pZ X') k⟫_ℝ
      - ∑ k, ⟪(pV X - pV X') k, P.Lx (pX X - pX X') k⟫_ℝ := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev k, inner_sub_right, inner_add_right]
  rw [hX, hY, hZ, hV]
  have hQ : 0 ≤ ∑ i, ⟪((pX X) - (pX X')) i, P.Q i ((pX X) i) - P.Q i ((pX X') i)⟫_ℝ :=
    Finset.sum_nonneg fun i _ => by
      simp only [PiLp.sub_apply]; exact (hP.1 i).2.2.2.1 _ _
  have hR : 0 ≤ ∑ i, ⟪((pX X) - (pX X')) i, (P.R (pX X) - P.R (pX X')) i⟫_ℝ := by
    rw [← PiLp.inner_apply]; exact hP.2.2.2.1 _ _
  have hB : 0 ≤ ∑ k, ⟪((pY X) - (pY X')) k, P.Bl k ((pY X) k) - P.Bl k ((pY X') k)⟫_ℝ :=
    Finset.sum_nonneg fun k _ => by
      simp only [PiLp.sub_apply]; exact (hP.2.1 k).2.2.2.1 _ _
  have hD : 0 ≤ ∑ k, ⟪((pZ X) - (pZ X')) k, P.Dl k ((pZ X) k) - P.Dl k ((pZ X') k)⟫_ℝ :=
    Finset.sum_nonneg fun k _ => by
      simp only [PiLp.sub_apply]; exact (hP.2.2.1 k).2.2.2.1 _ _
  have hS := Ladj_skew P ((pX X) - (pX X')) ((pV X) - (pV X'))
  have hy : ∑ k, ⟪((pY X) - (pY X')) k, ((pV X) - (pV X')) k⟫_ℝ = ∑ k, ⟪((pV X) - (pV X')) k, ((pY X) - (pY X')) k⟫_ℝ :=
    Finset.sum_congr rfl fun k _ => real_inner_comm _ _
  have hz : ∑ k, ⟪((pZ X) - (pZ X')) k, ((pV X) - (pV X')) k⟫_ℝ = ∑ k, ⟪((pV X) - (pV X')) k, ((pZ X) - (pZ X')) k⟫_ℝ :=
    Finset.sum_congr rfl fun k _ => real_inner_comm _ _
  linarith

theorem Fop_lipschitz (P : Problem H G) (hP : P.Hyp) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ X X' : XSpace H G, ‖Fop P X - Fop P X'‖ ≤ L * ‖X - X'‖ := by
  set cx : I → ℝ := fun i => P.αl i + P.χ + ∑ k, ‖ContinuousLinearMap.adjoint (P.L k i)‖
  set cy : K → ℝ := fun k => P.βl k + 1
  set cz : K → ℝ := fun k => P.δl k + 1
  set cv : K → ℝ := fun k => 2 + ∑ j, ‖P.L k j‖
  have hcx : ∀ i, 0 ≤ cx i := fun i => by
    have := (hP.1 i).2.2.2.2.1; have := hP.2.2.2.2.1
    have : 0 ≤ ∑ k, ‖ContinuousLinearMap.adjoint (P.L k i)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    simp only [cx]; linarith
  have hcy : ∀ k, 0 ≤ cy k := fun k => by have := (hP.2.1 k).2.2.2.2.1; simp only [cy]; linarith
  have hcz : ∀ k, 0 ≤ cz k := fun k => by have := (hP.2.2.1 k).2.2.2.2.1; simp only [cz]; linarith
  have hcv : ∀ k, 0 ≤ cv k := fun k => by
    have : 0 ≤ ∑ j, ‖P.L k j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    simp only [cv]; linarith
  set c := ∑ i, cx i + ∑ k, (cy k + cz k + cv k) with hc
  have hSx : ∀ i, cx i ≤ c := fun i => by
    have h1 := Finset.single_le_sum (fun j _ => hcx j) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ k, (cy k + cz k + cv k) :=
      Finset.sum_nonneg fun k _ => by linarith [hcy k, hcz k, hcv k]
    linarith
  have hSk : ∀ k, cy k + cz k + cv k ≤ c := fun k => by
    have h1 := Finset.single_le_sum (f := fun k => cy k + cz k + cv k)
      (fun j _ => by linarith [hcy j, hcz j, hcv j]) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ i, cx i := Finset.sum_nonneg fun i _ => hcx i
    linarith
  have hc0 : 0 ≤ c := by
    have h2 : 0 ≤ ∑ k, (cy k + cz k + cv k) :=
      Finset.sum_nonneg fun k _ => by linarith [hcy k, hcz k, hcv k]
    have : 0 ≤ ∑ i, cx i := Finset.sum_nonneg fun i _ => hcx i
    linarith
  refine ⟨Real.sqrt (Fintype.card I + 3 * Fintype.card K) * c, by positivity, fun X X' => ?_⟩
  set D := ‖X - X'‖
  have hD0 : 0 ≤ D := norm_nonneg _
  rw [mul_assoc]
  apply xs_norm_le_of_blocks _ _ (by positivity)
  · intro i
    have e : pX (Fop P X - Fop P X') i =
        (P.Q i (pX X i) - P.Q i (pX X' i)) + (P.R (pX X) - P.R (pX X')) i
          + P.Ladj (pV X - pV X') i := by
      simp only [pX_sub, PiLp.sub_apply, pX_Fop, ← Ladj_sub]; abel
    rw [e]
    have h1 : ‖P.Q i (pX X i) - P.Q i (pX X' i)‖ ≤ P.αl i * D := by
      refine ((hP.1 i).2.2.2.2.2 _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hP.1 i).2.2.2.2.1
      have := norm_pXi_le (X - X') i; simpa using this
    have h2 : ‖(P.R (pX X) - P.R (pX X')) i‖ ≤ P.χ * D := by
      refine (PiLp.norm_apply_le _ i).trans ((hP.2.2.2.2.2 _ _).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hP.2.2.2.2.1
      have := norm_pX_le (X - X'); simpa using this
    have h3 : ‖P.Ladj (pV X - pV X') i‖ ≤ (∑ k, ‖ContinuousLinearMap.adjoint (P.L k i)‖) * D := by
      simp only [Problem.Ladj]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := norm_pVk_le (X - X') k; simpa using this
    have h4 := norm_add₃_le (a := P.Q i (pX X i) - P.Q i (pX X' i))
      (b := (P.R (pX X) - P.R (pX X')) i) (c := P.Ladj (pV X - pV X') i)
    have h5 : cx i * D ≤ c * D := mul_le_mul_of_nonneg_right (hSx i) hD0
    simp only [cx] at h5
    nlinarith
  · intro k
    have e : pY (Fop P X - Fop P X') k = (P.Bl k (pY X k) - P.Bl k (pY X' k)) - (pV X k - pV X' k) := by
      simp only [pY_sub, PiLp.sub_apply, pY_Fop]; abel
    rw [e]
    have h1 : ‖P.Bl k (pY X k) - P.Bl k (pY X' k)‖ ≤ P.βl k * D := by
      refine ((hP.2.1 k).2.2.2.2.2 _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hP.2.1 k).2.2.2.2.1
      have := norm_pYk_le (X - X') k; simpa using this
    have h2 : ‖pV X k - pV X' k‖ ≤ D := by have := norm_pVk_le (X - X') k; simpa using this
    have h4 := norm_sub_le (P.Bl k (pY X k) - P.Bl k (pY X' k)) (pV X k - pV X' k)
    have h5 : (cy k + cz k + cv k) * D ≤ c * D := mul_le_mul_of_nonneg_right (hSk k) hD0
    have h6 : 0 ≤ (cz k + cv k) * D := mul_nonneg (by linarith [hcz k, hcv k]) hD0
    simp only [cy] at h5
    nlinarith
  · intro k
    have e : pZ (Fop P X - Fop P X') k = (P.Dl k (pZ X k) - P.Dl k (pZ X' k)) - (pV X k - pV X' k) := by
      simp only [pZ_sub, PiLp.sub_apply, pZ_Fop]; abel
    rw [e]
    have h1 : ‖P.Dl k (pZ X k) - P.Dl k (pZ X' k)‖ ≤ P.δl k * D := by
      refine ((hP.2.2.1 k).2.2.2.2.2 _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hP.2.2.1 k).2.2.2.2.1
      have := norm_pZk_le (X - X') k; simpa using this
    have h2 : ‖pV X k - pV X' k‖ ≤ D := by have := norm_pVk_le (X - X') k; simpa using this
    have h4 := norm_sub_le (P.Dl k (pZ X k) - P.Dl k (pZ X' k)) (pV X k - pV X' k)
    have h5 : (cy k + cz k + cv k) * D ≤ c * D := mul_le_mul_of_nonneg_right (hSk k) hD0
    have h6 : 0 ≤ (cy k + cv k) * D := mul_nonneg (by linarith [hcy k, hcv k]) hD0
    simp only [cz] at h5
    nlinarith
  · intro k
    have e : pV (Fop P X - Fop P X') k =
        (pY X k - pY X' k) + (pZ X k - pZ X' k) - P.Lx (pX X - pX X') k := by
      simp only [pV_sub, PiLp.sub_apply, pV_Fop, ← Lx_sub]; abel
    rw [e]
    have h1 : ‖pY X k - pY X' k‖ ≤ D := by have := norm_pYk_le (X - X') k; simpa using this
    have h2 : ‖pZ X k - pZ X' k‖ ≤ D := by have := norm_pZk_le (X - X') k; simpa using this
    have h3 : ‖P.Lx (pX X - pX X') k‖ ≤ (∑ j, ‖P.L k j‖) * D := by
      simp only [Problem.Lx]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := norm_pXi_le (X - X') j; simpa using this
    have h4 := norm_sub_le ((pY X k - pY X' k) + (pZ X k - pZ X' k)) (P.Lx (pX X - pX X') k)
    have h4' := norm_add_le (pY X k - pY X' k) (pZ X k - pZ X' k)
    have h5 : (cy k + cz k + cv k) * D ≤ c * D := mul_le_mul_of_nonneg_right (hSk k) hD0
    have h6 : 0 ≤ (cy k + cz k) * D := mul_nonneg (by linarith [hcy k, hcz k]) hD0
    simp only [cv] at h5
    nlinarith

theorem opM_maximal (P : Problem H G) (hP : P.Hyp) : IsMaximalMonotone (opM P) := by
  obtain ⟨L, hL0, hL⟩ := Fop_lipschitz P hP
  rw [opM_eq]
  exact ss_max_add_lip _ (Pop_maximal P hP) _ (Fop_monotone P hP) L hL0 hL

end FF


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section P25
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

@[simp] theorem pX_opC (P : Problem H G) (X : XSpace H G) (i : I) :
    pX (opC P X) i = P.C i (pX X i) := rfl
@[simp] theorem pY_opC (P : Problem H G) (X : XSpace H G) (k : K) :
    pY (opC P X) k = P.Bc k (pY X k) := rfl
@[simp] theorem pZ_opC (P : Problem H G) (X : XSpace H G) (k : K) :
    pZ (opC P X) k = P.Dc k (pZ X k) := rfl
@[simp] theorem pV_opC (P : Problem H G) (X : XSpace H G) : pV (opC P X) = 0 := rfl

theorem saddle_eq (P : Problem H G) : saddleOp P = addSV (opM P) (opC P) := by
  funext X
  ext W
  constructor
  · rintro ⟨hx, hy, hz, hv⟩
    refine ⟨W - opC P X, ⟨fun i => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩,
      (sub_add_cancel W _).symm⟩
    · obtain ⟨a, ha, he⟩ := hx i
      refine ⟨a, ha, ?_⟩
      simp only [pX_sub, PiLp.sub_apply, pX_opC, he]; abel
    · obtain ⟨b, hb, he⟩ := hy k
      refine ⟨b, hb, ?_⟩
      simp only [pY_sub, PiLp.sub_apply, pY_opC, he]; abel
    · obtain ⟨d, hd, he⟩ := hz k
      refine ⟨d, hd, ?_⟩
      simp only [pZ_sub, PiLp.sub_apply, pZ_opC, he]; abel
    · simp only [pV_sub, PiLp.sub_apply, pV_opC, hv k, PiLp.zero_apply, sub_zero]
  · rintro ⟨U, ⟨hx, hy, hz, hv⟩, rfl⟩
    refine ⟨fun i => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
    · obtain ⟨a, ha, he⟩ := hx i
      refine ⟨a, ha, ?_⟩
      simp only [pX_add, PiLp.add_apply, pX_opC, he]; abel
    · obtain ⟨b, hb, he⟩ := hy k
      refine ⟨b, hb, ?_⟩
      simp only [pY_add, PiLp.add_apply, pY_opC, he]; abel
    · obtain ⟨d, hd, he⟩ := hz k
      refine ⟨d, hd, ?_⟩
      simp only [pZ_add, PiLp.add_apply, pZ_opC, he]; abel
    · simp only [pV_add, PiLp.add_apply, pV_opC, hv k, PiLp.zero_apply, add_zero]

theorem alpha_pos (P : Problem H G) (hP : P.Hyp) (α : ℝ)
    (hα : IsLeast (Set.range P.αc ∪ Set.range P.βc ∪ Set.range P.δc) α) : 0 < α := by
  rcases hα.1 with (⟨i, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · exact (hP.1 i).2.1
  · exact (hP.2.1 k).2.1
  · exact (hP.2.2.1 k).2.1

theorem opC_cocoercive (P : Problem H G) (hP : P.Hyp) (α : ℝ)
    (hα : IsLeast (Set.range P.αc ∪ Set.range P.βc ∪ Set.range P.δc) α) :
    IsCocoercive α (opC P) := by
  intro X Y
  have hαi : ∀ i, α ≤ P.αc i := fun i => hα.2 (Or.inl (Or.inl ⟨i, rfl⟩))
  have hαb : ∀ k, α ≤ P.βc k := fun k => hα.2 (Or.inl (Or.inr ⟨k, rfl⟩))
  have hαd : ∀ k, α ≤ P.δc k := fun k => hα.2 (Or.inr ⟨k, rfl⟩)
  rw [xs_normsq, xs_inner]
  simp only [pX_sub, pY_sub, pZ_sub, pV_sub, PiLp.sub_apply, pX_opC, pY_opC, pZ_opC, pV_opC,
    sub_self, PiLp.zero_apply, norm_zero, inner_zero_left]
  have h1 : α * ∑ i, ‖P.C i (pX X i) - P.C i (pX Y i)‖ ^ 2 ≤
      ∑ i, ⟪P.C i (pX X i) - P.C i (pX Y i), pX X i - pX Y i⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact (mul_le_mul_of_nonneg_right (hαi i) (sq_nonneg _)).trans ((hP.1 i).2.2.1 _ _)
  have h2 : α * ∑ k, ‖P.Bc k (pY X k) - P.Bc k (pY Y k)‖ ^ 2 ≤
      ∑ k, ⟪P.Bc k (pY X k) - P.Bc k (pY Y k), pY X k - pY Y k⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact (mul_le_mul_of_nonneg_right (hαb k) (sq_nonneg _)).trans ((hP.2.1 k).2.2.1 _ _)
  have h3 : α * ∑ k, ‖P.Dc k (pZ X k) - P.Dc k (pZ Y k)‖ ^ 2 ≤
      ∑ k, ⟪P.Dc k (pZ X k) - P.Dc k (pZ Y k), pZ X k - pZ Y k⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact (mul_le_mul_of_nonneg_right (hαd k) (sq_nonneg _)).trans ((hP.2.2.1 k).2.2.1 _ _)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    add_zero]
  nlinarith

theorem opC_lipschitz (P : Problem H G) (hP : P.Hyp) (α : ℝ)
    (hα : IsLeast (Set.range P.αc ∪ Set.range P.βc ∪ Set.range P.δc) α) (X Y : XSpace H G) :
    ‖opC P X - opC P Y‖ ≤ α⁻¹ * ‖X - Y‖ := by
  have hα0 := alpha_pos P hP α hα
  have hc := opC_cocoercive P hP α hα X Y
  have hcs := real_inner_le_norm (opC P X - opC P Y) (X - Y)
  by_cases h0 : ‖opC P X - opC P Y‖ = 0
  · rw [h0]; positivity
  · have hp : 0 < ‖opC P X - opC P Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [le_inv_mul_iff₀ hα0]
    nlinarith

theorem opM_monotone (P : Problem H G) (hP : P.Hyp) : IsMonotoneOp (opM P) :=
  (opM_maximal P hP).1

theorem halfspace (P : Problem H G) (hP : P.Hyp) (α : ℝ)
    (hα : IsLeast (Set.range P.αc ∪ Set.range P.βc ∪ Set.range P.δc) α)
    (p ps q : XSpace H G) (hps : ps ∈ opM P p) :
    zer (saddleOp P) ⊆ {X | ⟪X - p, ps + opC P q⟫_ℝ ≤ (4 * α)⁻¹ * ‖p - q‖ ^ 2} := by
  intro X hX
  have hα0 := alpha_pos P hP α hα
  have h0 : (0 : XSpace H G) ∈ addSV (opM P) (opC P) X := by
    rw [← saddle_eq]; exact hX
  obtain ⟨U, hU, he⟩ := h0
  have hUe : U = -opC P X := by rw [eq_neg_iff_add_eq_zero]; exact he.symm
  have hmon := opM_monotone P hP X p U ps hU hps
  rw [hUe] at hmon
  have hco := opC_cocoercive P hP α hα q X
  have e1 : ⟪X - p, ps + opC P q⟫_ℝ = ⟪X - p, ps - -opC P X⟫_ℝ
      + ⟪X - q, opC P q - opC P X⟫_ℝ + ⟪q - p, opC P q - opC P X⟫_ℝ := by
    rw [add_assoc, ← inner_add_left, sub_add_sub_cancel, ← inner_add_right]
    congr 1; abel
  have e2 : ⟪X - p, ps - -opC P X⟫_ℝ = -⟪X - p, -opC P X - ps⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  have e3 : ⟪X - q, opC P q - opC P X⟫_ℝ = -⟪opC P q - opC P X, q - X⟫_ℝ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  have hcs := real_inner_le_norm (q - p) (opC P q - opC P X)
  set t := ‖opC P q - opC P X‖
  set s := ‖q - p‖
  have hs : ‖p - q‖ = s := norm_sub_rev _ _
  simp only [Set.mem_ofPred_eq]
  rw [e1, e2, e3, hs]
  have key : s * t - α * t ^ 2 ≤ (4 * α)⁻¹ * s ^ 2 := by
    rw [← sub_nonneg]
    have : (4 * α)⁻¹ * s ^ 2 - (s * t - α * t ^ 2) = (4 * α)⁻¹ * (s - 2 * α * t) ^ 2 := by
      field_simp; ring
    rw [this]; positivity
  nlinarith

end P25


theorem solution {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) :
    saddleOp prob = addSV (opM prob) (opC prob) ∧
    IsMaximalMonotone (opM prob) ∧
    ∀ α : ℝ, IsLeast (Set.range prob.αc ∪ Set.range prob.βc ∪ Set.range prob.δc) α →
      IsCocoercive α (opC prob) ∧
      ∀ p ps q : XSpace H G, ps ∈ opM prob p →
        zer (saddleOp prob) ⊆
          {X | ⟪X - p, ps + opC prob q⟫_ℝ ≤ (4 * α)⁻¹ * ‖p - q‖ ^ 2} :=
  ⟨saddle_eq prob, opM_maximal prob hprob, fun α hα =>
    ⟨opC_cocoercive prob hprob α hα, fun p ps q hps => halfspace prob hprob α hα p ps q hps⟩⟩
