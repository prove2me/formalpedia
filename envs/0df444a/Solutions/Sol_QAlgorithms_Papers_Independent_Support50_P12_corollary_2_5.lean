-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.corollary_2_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:30:46.96481+00:00
-- url     : https://prove2.me/submissions/30514c1f-ce6d-467c-8cf7-3c53a13d61c6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


namespace A3S55C25

/-- indicator -/
def ind (l : ℝ) (x : ℝ) : ℝ := if x = l then 1 else 0

lemma cont (X : Mat I) (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ X) :=
  X.finite_real_spectrum.continuousOn g

lemma cmul (X : Mat I) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (cont X f) (cont X g)).symm

lemma toCLM_eq (X : Mat I) :
    ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) X : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
      EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) = Matrix.toEuclideanLin X :=
  Matrix.coe_toEuclideanCLM_eq_toEuclideanLin X

lemma algebraMap_eq (l : ℝ) : (algebraMap ℝ (Mat I) l) = (l : ℂ) • (1 : Mat I) := by
  rw [Algebra.algebraMap_eq_smul_one]; rfl

theorem proj_eq_cfc (H : Mat I) (hH : H.IsHermitian) (l : ℝ) :
    spectralProjector H l = cfc (ind l) H := by
  have hsa : IsSelfAdjoint H := hH
  set P := cfc (ind l) H with hPdef
  set φ := (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ))
  set T := φ H
  set p := φ P
  have hPP : P * P = P := by
    rw [hPdef, cmul]; congr 1; funext x; unfold ind; split_ifs <;> simp
  have hPsa : IsSelfAdjoint P := cfc_predicate _ _
  have hstar : IsStarProjection p := ⟨by
      show p * p = p
      rw [← map_mul, hPP], by
      show star p = p
      rw [← map_star, hPsa.star_eq]⟩
  -- (H - l) P = 0
  have h1 : (H - (l : ℂ) • 1) * P = 0 := by
    have : H - (l : ℂ) • 1 = cfc (fun x => x - l) H := by
      rw [cfc_sub (fun x => x) (fun _ => l) H, cfc_id' ℝ H, cfc_const l H, algebraMap_eq]
    rw [this, hPdef, cmul]
    rw [← cfc_zero ℝ H]; congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]
  -- 1 - P = Q (H - l)
  have h2 : 1 - P = cfc (fun x => if x = l then 0 else (x - l)⁻¹) H * (H - (l : ℂ) • 1) := by
    have : H - (l : ℂ) • 1 = cfc (fun x => x - l) H := by
      rw [cfc_sub (fun x => x) (fun _ => l) H, cfc_id' ℝ H, cfc_const l H, algebraMap_eq]
    rw [this, cmul, hPdef, ← cfc_one ℝ H, ← cfc_sub (1 : ℝ → ℝ) (ind l) H (cont _ _) (cont _ _)]
    congr 1; funext x; unfold ind; split_ifs with h
    · simp
    · have : x - l ≠ 0 := sub_ne_zero.mpr h
      simp [this]
  have hT : φ (H - (l : ℂ) • 1) = T - (l : ℂ) • 1 := by
    rw [map_sub, map_smul, map_one]
  have hrange : LinearMap.range (p : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) =
      Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) (l : ℂ) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      have := congrArg (fun M => φ M w) h1
      simp only [map_mul, map_zero, hT] at this
      have h' := this
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.zero_apply, sub_eq_zero] at h'
      exact h'
    · intro hv
      refine ⟨v, ?_⟩
      have := congrArg (fun M => φ M v) h2
      simp only [map_mul, map_sub, map_one, hT] at this
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
      change T v = (l:ℂ) • v at hv
      rw [hv, sub_self, map_zero, sub_eq_zero] at this
      exact this.symm
  obtain ⟨_, hp⟩ := _root_.isStarProjection_iff_eq_starProjection_range.mp hstar
  unfold spectralProjector eigenProjection
  have hK : (⨆ μ ∈ ({(l : ℂ)} : Set ℂ), Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) μ)
      = LinearMap.range (p : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) := by
    rw [hrange]; simp
  have : (⨆ μ ∈ ({(l : ℂ)} : Set ℂ), Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) μ).starProjection = p := by
    rw [hp]; congr 1
  rw [this, toCLM_eq]; exact LinearEquiv.symm_apply_apply _ _


theorem proj_shift (B : Mat I) (b e : ℝ) :
    spectralProjector (B + (e : ℂ) • 1) (b + e) = spectralProjector B b := by
  unfold spectralProjector eigenProjection
  congr 3
  have hT : (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (B + (e : ℂ) • 1) :
      EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) =
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) B : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I)
        + (e : ℂ) • 1 := by
    rw [map_add, map_smul, map_one]; rfl
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  rw [hT]
  ext v
  simp only [Module.End.mem_eigenspace_iff, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Complex.ofReal_add, add_smul]
  constructor
  · intro h; exact add_right_cancel h
  · intro h; rw [h]

lemma mem_spec (X : Mat I) (hX : X.IsHermitian) (x : ℝ) : x ∈ spec X ↔ x ∈ spectrum ℝ X := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  simp [spec, hX]

lemma spec_nonneg (X : Mat I) (hX : X.PosSemidef) (x : ℝ) (hx : x ∈ spec X) : 0 ≤ x := by
  simp only [spec, hX.isHermitian, dif_pos, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hX.eigenvalues_nonneg i

lemma herm_shift (B : Mat I) (hB : B.IsHermitian) (e : ℝ) : (B + (e : ℂ) • 1).IsHermitian := by
  refine hB.add ?_
  simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]

theorem spec_shift (B : Mat I) (hB : B.IsHermitian) (e : ℝ) :
    spec (B + (e : ℂ) • 1) = (spec B).image (· + e) := by
  ext x
  rw [mem_spec _ (herm_shift B hB e), Finset.mem_image]
  constructor
  · intro hx
    refine ⟨x - e, ?_, by ring⟩
    rw [mem_spec _ hB]
    rw [spectrum.mem_iff] at hx ⊢
    convert hx using 2
    rw [algebraMap_eq, algebraMap_eq, Complex.ofReal_sub, sub_smul]
    abel
  · rintro ⟨y, hy, rfl⟩
    rw [mem_spec _ hB] at hy
    rw [spectrum.mem_iff] at hy ⊢
    convert hy using 2
    rw [algebraMap_eq, algebraMap_eq, Complex.ofReal_add, add_smul]
    abel


lemma hs_eq (X Y : Mat I) : hs X Y = (Xᴴ * Y).trace := by
  unfold hs QAlgorithms.Papers.Independent.Frontier18.P17.res
  rw [PiLp.inner_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.inner_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]; rfl

def sfun (x : ℝ) : ℝ := if x = 0 then 0 else Real.rpow x (1 / 2)

lemma supportPower_half (B : Mat I) : supportPower B (1 / 2) = cfc sfun B := rfl

/-- overlap coefficient -/
def cc (A B : Mat I) (a b : ℝ) : ℝ := (spectralProjector A a * spectralProjector B b).trace.re

lemma sQs (B : Mat I) (hB : B.IsHermitian) (b : ℝ) (hb : 0 ≤ b) :
    supportPower B (1 / 2) * spectralProjector B b * supportPower B (1 / 2) =
      b • spectralProjector B b := by
  rw [proj_eq_cfc B hB, supportPower_half, cmul, cmul, ← cfc_const_mul b _ B (cont _ _)]
  congr 1; funext x
  unfold sfun ind
  by_cases hx : x = b
  · subst hx
    by_cases h0 : x = 0
    · simp [h0]
    · simp only [h0, if_true, if_false, mul_one]
      show x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x
      rw [← Real.rpow_add (lt_of_le_of_ne hb (Ne.symm h0))]
      norm_num
  · simp [hx]

theorem quasi_formula (f : ℝ → ℝ) (A B : Mat I) (hB : B.PosSemidef) :
    quasi f A B = ∑ a ∈ spec A, ∑ b ∈ spec B, f (a / b) * b * cc A B a b := by
  have hS : (supportPower B (1 / 2))ᴴ = supportPower B (1 / 2) := by
    have : IsSelfAdjoint (supportPower B (1 / 2)) := cfc_predicate _ _
    exact this.star_eq
  unfold quasi modular
  rw [hs_eq, hS, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb0 := spec_nonneg B hB b hb
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have : (supportPower B (1 / 2) * (spectralProjector A a * supportPower B (1 / 2) *
      spectralProjector B b)).trace = (spectralProjector A a *
      (supportPower B (1 / 2) * spectralProjector B b * supportPower B (1 / 2))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [this, sQs B hB.isHermitian b hb0, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  unfold cc; simp only [smul_eq_mul]; ring


lemma proj_idem (H : Mat I) (hH : H.IsHermitian) (l : ℝ) :
    spectralProjector H l * spectralProjector H l = spectralProjector H l := by
  rw [proj_eq_cfc H hH, cmul]; congr 1; funext x; unfold ind; split_ifs <;> simp

lemma proj_herm (H : Mat I) (hH : H.IsHermitian) (l : ℝ) :
    (spectralProjector H l)ᴴ = spectralProjector H l := by
  rw [proj_eq_cfc H hH]
  have : IsSelfAdjoint (cfc (ind l) H) := cfc_predicate _ _
  exact this.star_eq

theorem cc_nonneg (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) (a b : ℝ) :
    0 ≤ cc A B a b := by
  have key : ∀ P Q : Mat I, P * P = P → Q * Q = Q → Pᴴ = P → Qᴴ = Q →
      0 ≤ (P * Q).trace.re := by
    intro P Q hP hQ hP' hQ'
    have h : (P * Q).trace = ((P * Q)ᴴ * (P * Q)).trace := by
      rw [Matrix.conjTranspose_mul, hP', hQ']
      conv_lhs => rw [← hP, ← hQ]
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h]
    exact (Complex.nonneg_iff.1 (Matrix.posSemidef_conjTranspose_mul_self (P * Q)).trace_nonneg).1
  exact key _ _ (proj_idem A hA a) (proj_idem B hB b) (proj_herm A hA a) (proj_herm B hB b)

lemma one_sub_supp (B : Mat I) (hB : B.IsHermitian) : 1 - supp B = cfc (ind 0) B := by
  have hsa : IsSelfAdjoint B := hB
  unfold supp supportPower
  rw [← cfc_one ℝ B, ← cfc_sub (1 : ℝ → ℝ) _ B (cont _ _) (cont _ _)]
  congr 1; funext x; unfold ind; split_ifs with h <;> simp


lemma decomp (A : Mat I) (hA : A.IsHermitian) :
    A = ∑ a ∈ spec A, a • spectralProjector A a := by
  have hsa : IsSelfAdjoint A := hA
  have h1 : A = cfc (∑ a ∈ spec A, fun x => a * ind a x) A := by
    conv_lhs => rw [← cfc_id' ℝ A]
    apply cfc_congr
    intro x hx
    rw [← mem_spec A hA] at hx
    simp only [Finset.sum_apply, ind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp [hx]
  conv_lhs => rw [h1]
  rw [cfc_sum _ A _ (fun _ _ => cont _ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cfc_const_mul a _ A (cont _ _), proj_eq_cfc A hA]

theorem tr_eq_sum (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ a ∈ spec A, a * cc A B a 0 = tr (A * (1 - supp B)) := by
  rw [one_sub_supp B hB, ← proj_eq_cfc B hB]
  conv_rhs => rw [decomp A hA]
  unfold tr cc
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem tr_zero_of_supports (A B : Mat I) (hB : B.IsHermitian) (h : Supports A B) :
    tr (A * (1 - supp B)) = 0 := by
  have hsa : IsSelfAdjoint B := hB
  rw [one_sub_supp B hB]
  set Q := cfc (ind 0) B with hQ
  have hBQ : B * Q = 0 := by
    conv_lhs => rw [← cfc_id' ℝ B]
    rw [hQ, cmul, ← cfc_zero ℝ B]
    congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]
  have hAQ : A * Q = 0 := by
    have hcol : ∀ j, B *ᵥ (fun k => Q k j) = 0 := by
      intro j; funext i
      have := congrFun (congrFun hBQ i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    ext i j
    have := congrFun (h _ (hcol j)) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  rw [hAQ]; simp [tr]

theorem supports_shift (A B : Mat I) (hB : B.PosSemidef) (e : ℝ) (he : 0 < e) :
    Supports A (B + (e : ℂ) • 1) := by
  have hpd : (B + (e : ℂ) • 1).PosDef :=
    Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul (by exact_mod_cast he))
  intro v hv
  by_cases h0 : v = 0
  · simp [h0]
  · have := hpd.dotProduct_mulVec_pos h0
    rw [hv] at this; simp at this

theorem quasi_shift (f : ℝ → ℝ) (A B : Mat I) (hB : B.PosSemidef) (e : ℝ) (he : 0 ≤ e) :
    quasi f A (B + (e : ℂ) • 1) =
      ∑ a ∈ spec A, ∑ b ∈ spec B, f (a / (b + e)) * (b + e) * cc A B a b := by
  have hpsd : (B + (e : ℂ) • 1).PosSemidef :=
    hB.add (Matrix.PosSemidef.one.smul (by exact_mod_cast he))
  rw [quasi_formula f A _ hpsd, spec_shift B hB.isHermitian e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold cc; rw [proj_shift]


lemma ereal_top (ω : EReal) (r k : ℝ) (hk : 0 ≤ k) (h : (r : EReal) + ω * k = ⊤) : ω = ⊤ := by
  induction ω using EReal.rec with
  | bot =>
    rcases hk.eq_or_lt with h0 | h0
    · subst h0; simp at h
    · rw [EReal.bot_mul_coe_of_pos h0] at h; simp at h
  | coe x =>
    have h' : ((r + x * k : ℝ) : EReal) = ⊤ := by push_cast; exact h
    exact absurd h' (EReal.coe_ne_top _)
  | top => rfl

lemma ereal_bot (ω : EReal) (r k : ℝ) (hk : 0 ≤ k) (h : (r : EReal) + ω * k = ⊥) : ω = ⊥ := by
  induction ω using EReal.rec with
  | bot => rfl
  | coe x =>
    have h' : ((r + x * k : ℝ) : EReal) = ⊥ := by push_cast; exact h
    exact absurd h' (EReal.coe_ne_bot _)
  | top =>
    rcases hk.eq_or_lt with h0 | h0
    · subst h0; simp at h
    · rw [EReal.top_mul_coe_of_pos h0] at h; simp at h

lemma ereal_mul_add (ω : EReal) (k k' : ℝ) (hk : 0 ≤ k) (hk' : 0 ≤ k') :
    ω * k + ω * k' = ω * ((k + k' : ℝ) : EReal) := by
  rcases hk.eq_or_lt with h0 | h0
  · subst h0; simp
  rcases hk'.eq_or_lt with h1 | h1
  · subst h1; simp
  have h2 : 0 < k + k' := by linarith
  induction ω using EReal.rec with
  | bot => rw [EReal.bot_mul_coe_of_pos h0, EReal.bot_mul_coe_of_pos h1,
      EReal.bot_mul_coe_of_pos h2]; rfl
  | coe x => rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring
  | top => rw [EReal.top_mul_coe_of_pos h0, EReal.top_mul_coe_of_pos h1,
      EReal.top_mul_coe_of_pos h2]; rfl

theorem sum_tendsto {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (ρ κ : ι → ℝ)
    (hκ : ∀ i ∈ s, 0 ≤ κ i) (ω : EReal) (l : Filter ℝ)
    (h : ∀ i ∈ s, Tendsto (fun e => (F i e : EReal)) l (𝓝 ((ρ i : EReal) + ω * κ i))) :
    Tendsto (fun e => ((∑ i ∈ s, F i e : ℝ) : EReal)) l
      (𝓝 (((∑ i ∈ s, ρ i : ℝ) : EReal) + ω * ((∑ i ∈ s, κ i : ℝ) : EReal))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert j s hj ih =>
    have ih' := ih (fun i hi => hκ i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hj' := h j (Finset.mem_insert_self j s)
    have hκj := hκ j (Finset.mem_insert_self j s)
    have hKs : 0 ≤ ∑ i ∈ s, κ i := Finset.sum_nonneg fun i hi => hκ i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hj, EReal.coe_add]
    have hadd := (EReal.continuousAt_add (p := (((ρ j : EReal) + ω * κ j),
        (((∑ i ∈ s, ρ i : ℝ) : EReal) + ω * ((∑ i ∈ s, κ i : ℝ) : EReal)))) ?_ ?_).tendsto.comp
      (hj'.prodMk_nhds ih')
    · convert hadd using 2
      · simp only [Function.comp]
      · have hm := ereal_mul_add ω _ _ hκj hKs
        rw [EReal.coe_add] at hm
        rw [← hm]
        dsimp only
        abel
    · by_contra hc; push Not at hc
      have := ereal_top ω _ _ hκj hc.1
      have := ereal_bot ω _ _ hKs hc.2
      simp_all
    · by_contra hc; push Not at hc
      have := ereal_bot ω _ _ hκj hc.1
      have := ereal_top ω _ _ hKs hc.2
      simp_all


theorem term_tendsto (f : ℝ → ℝ) (hf : DivergenceGenerator f) (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    Tendsto (fun e : ℝ => ((f (a / (b + e)) * (b + e) * c : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (((f (a / b) * b * c : ℝ) : EReal) +
        recessionSlope f * ((if b = 0 then a * c else 0 : ℝ) : EReal))) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    simp only [if_true, mul_zero, zero_mul, EReal.coe_zero, zero_add, zero_add]
    rcases ha.eq_or_lt with ha0 | hapos
    · subst ha0
      simp only [zero_div, zero_mul, EReal.coe_zero, mul_zero]
      have : Tendsto (fun e : ℝ => f 0 * e * c) (𝓝[>] 0) (𝓝 0) := by
        have h0 := ((by fun_prop : Continuous fun e : ℝ => f 0 * e * c).tendsto 0)
        simp only [mul_zero, zero_mul] at h0
        exact tendsto_nhdsWithin_of_tendsto_nhds h0
      have h2 := (continuous_coe_real_ereal.tendsto _).comp this
      simp only [EReal.coe_zero] at h2
      refine h2.congr (fun e => ?_)
      simp [Function.comp]
    · have hg : Tendsto (fun e : ℝ => (((f (a / e) / (a / e)) : ℝ) : EReal)) (𝓝[>] 0)
          (𝓝 (recessionSlope f)) := by
        have h1 : Tendsto (fun e : ℝ => a / e) (𝓝[>] 0) atTop := by
          simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hapos
        exact hf.2.comp h1
      have hm := EReal.Tendsto.const_mul hg (a := ((a * c : ℝ) : EReal))
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      rw [mul_comm ((a * c : ℝ) : EReal)] at hm
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with e he
      have he' : (0 : ℝ) < e := he
      rw [← EReal.coe_mul]; congr 1
      field_simp
  · have hb0 : b ≠ 0 := hbpos.ne'
    simp only [hb0, if_false, EReal.coe_zero, mul_zero, add_zero]
    have hc : ContinuousAt (fun e : ℝ => f (a / (b + e)) * (b + e) * c) 0 := by
      have hf' : ContinuousAt (fun e : ℝ => f (a / (b + e))) 0 := by
        rcases ha.eq_or_lt with ha0 | hapos
        · subst ha0; simp only [zero_div]; exact continuousAt_const
        · have h1 : ContinuousAt f (a / b) := by
            exact hf.1.continuousAt (Ioi_mem_nhds (div_pos hapos hbpos))
          have h2 : ContinuousAt (fun e : ℝ => a / (b + e)) 0 :=
            continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simpa using hb0)
          exact ContinuousAt.comp_of_eq h1 h2 (by simp)
      exact (hf'.mul (continuousAt_const.add continuousAt_id)).mul continuousAt_const
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hc.tendsto
    simp only [add_zero] at this
    exact (continuous_coe_real_ereal.tendsto _).comp this

lemma proj_zero (H : Mat I) (hH : H.IsHermitian) (l : ℝ) (hl : l ∉ spec H) :
    spectralProjector H l = 0 := by
  have hsa : IsSelfAdjoint H := hH
  rw [proj_eq_cfc H hH, ← cfc_zero ℝ H]
  apply cfc_congr
  intro x hx
  rw [← mem_spec H hH] at hx
  have : x ≠ l := fun h => hl (h ▸ hx)
  simp [ind, this]


theorem main [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e : ℝ => div f A (B + (e : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 ((quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal))) ∧
    (Supports A B → Tendsto (fun e : ℝ => div f A (B + (e : ℂ) • 1))
      (𝓝[>] 0) (𝓝 (quasi f A B : EReal))) := by
  have hlim := sum_tendsto (spec A)
    (fun a e => ∑ b ∈ spec B, f (a / (b + e)) * (b + e) * cc A B a b)
    (fun a => ∑ b ∈ spec B, f (a / b) * b * cc A B a b)
    (fun a => ∑ b ∈ spec B, (if b = 0 then a * cc A B a b else 0))
    (fun a ha => Finset.sum_nonneg fun b _ => by
      split_ifs
      · exact mul_nonneg (spec_nonneg A hA a ha) (cc_nonneg A B hA.isHermitian hB.isHermitian a b)
      · exact le_rfl)
    (recessionSlope f) (𝓝[>] 0)
    (fun a ha => sum_tendsto (spec B) _ _ _
      (fun b _ => by
        split_ifs
        · exact mul_nonneg (spec_nonneg A hA a ha) (cc_nonneg A B hA.isHermitian hB.isHermitian a b)
        · exact le_rfl)
      _ _ (fun b hb => term_tendsto f hf a b (cc A B a b) (spec_nonneg A hA a ha)
        (spec_nonneg B hB b hb)))
  have hK : ∑ a ∈ spec A, ∑ b ∈ spec B, (if b = 0 then a * cc A B a b else 0) =
      tr (A * (1 - supp B)) := by
    rw [← tr_eq_sum A B hA.isHermitian hB.isHermitian]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · unfold cc; rw [proj_zero B hB.isHermitian 0 h]; simp
  rw [← quasi_formula f A B hB, hK] at hlim
  have hfirst : Tendsto (fun e : ℝ => div f A (B + (e : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 ((quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal))) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : (0 : ℝ) < e := he
    unfold div
    rw [if_pos (supports_shift A B hB e he'), quasi_shift f A B hB e he'.le]
  refine ⟨hfirst, fun hs => ?_⟩
  rw [tr_zero_of_supports A B hB.isHermitian hs] at hfirst
  simpa using hfirst


lemma div_eq [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f A B = (quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal) := by
  by_cases hs : Supports A B
  · unfold div; rw [if_pos hs, tr_zero_of_supports A B hB.isHermitian hs]; simp
  · have h1 := (main f hf A B hA hB).1
    have h2 : Tendsto (fun e : ℝ => (quasi f A (B + (e : ℂ) • 1) : EReal)) (𝓝[>] 0)
        (𝓝 ((quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal))) := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with e he
      unfold div; rw [if_pos (supports_shift A B hB e he)]
    unfold div; rw [if_neg hs]
    exact h2.limUnder_eq

lemma proj_sum (A : Mat I) (hA : A.IsHermitian) :
    ∑ a ∈ spec A, spectralProjector A a = 1 := by
  have hsa : IsSelfAdjoint A := hA
  have h1 : (1 : Mat I) = cfc (∑ a ∈ spec A, ind a) A := by
    rw [← cfc_one ℝ A]
    apply cfc_congr
    intro x hx
    rw [← mem_spec A hA] at hx
    simp only [Finset.sum_apply, ind, Pi.one_apply]
    rw [Finset.sum_ite_eq]; simp [hx]
  rw [h1, cfc_sum _ A _ (fun _ _ => cont _ _)]
  exact Finset.sum_congr rfl fun a _ => proj_eq_cfc A hA a

lemma tr_B_sum (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    tr B = ∑ a ∈ spec A, ∑ b ∈ spec B, b * cc A B a b := by
  have h : ∀ a, ∑ b ∈ spec B, b * cc A B a b = (spectralProjector A a * B).trace.re := by
    intro a
    conv_rhs => rw [decomp B hB]
    unfold cc
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  simp only [h]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, proj_sum A hA, one_mul]
  rfl

lemma quasi_split (f : ℝ → ℝ) (A B : Mat I) (hA : A.IsHermitian) (hB : B.PosSemidef) :
    quasi f A B = f 0 * tr B + quasi (fun x => f x - f 0) A B := by
  rw [quasi_formula f A B hB, quasi_formula _ A B hB, tr_B_sum A B hA hB.isHermitian,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ereal_sum {ι : Type*} (s : Finset ι) (ρ κ : ι → ℝ) (hκ : ∀ i ∈ s, 0 ≤ κ i) (ω : EReal) :
    ∑ i ∈ s, ((ρ i : EReal) + ω * κ i) =
      ((∑ i ∈ s, ρ i : ℝ) : EReal) + ω * ((∑ i ∈ s, κ i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ih' := ih (fun i hi => hκ i (Finset.mem_insert_of_mem hi))
    have hκj := hκ j (Finset.mem_insert_self j s)
    have hKs : 0 ≤ ∑ i ∈ s, κ i := Finset.sum_nonneg fun i hi => hκ i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, ih']
    have hm := ereal_mul_add ω _ _ hκj hKs
    rw [← hm, EReal.coe_add]
    abel

lemma expansion3 (f : ℝ → ℝ) (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal) =
    ∑ a ∈ spec A,
      (((∑ b ∈ (spec B).filter (fun b => b ≠ 0),
        b * f (a / b) * tr (spectralProjector A a * spectralProjector B b) : ℝ) : EReal) +
        (a : EReal) * recessionSlope f *
          (tr (spectralProjector A a * spectralProjector B 0) : EReal)) := by
  have hterm : ∀ a : ℝ, (a : EReal) * recessionSlope f *
      (tr (spectralProjector A a * spectralProjector B 0) : EReal) =
      recessionSlope f * ((a * cc A B a 0 : ℝ) : EReal) := by
    intro a
    rw [mul_comm (a : EReal), mul_assoc, EReal.coe_mul]; rfl
  simp_rw [hterm]
  rw [ereal_sum _ _ _ (fun a ha => mul_nonneg (spec_nonneg A hA a ha)
    (cc_nonneg A B hA.isHermitian hB.isHermitian a 0)),
    tr_eq_sum A B hA.isHermitian hB.isHermitian, quasi_formula f A B hB]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · unfold cc tr; ring
  · simp at h; subst h; simp

lemma supp_mulVec (B : Mat I) (hB : B.IsHermitian) (v : I → ℂ) (hv : B *ᵥ v = 0) :
    supp B *ᵥ v = 0 := by
  have hsa : IsSelfAdjoint B := hB
  have : supp B = cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) B * B := by
    conv_rhs => arg 2; rw [← cfc_id' ℝ B]
    rw [cmul]
    unfold supp supportPower
    congr 1; funext x
    split_ifs with h
    · simp
    · simp [h]
  rw [this, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

open scoped MatrixOrder in
lemma supports_of_tr_zero (A B : Mat I) (hA : A.PosSemidef) (hB : B.IsHermitian)
    (h : tr (A * (1 - supp B)) = 0) : Supports A B := by
  have hQ : 1 - supp B = spectralProjector B 0 := by
    rw [one_sub_supp B hB, ← proj_eq_cfc B hB]
  set Q := 1 - supp B with hQdef
  have hQQ : Q * Q = Q := by rw [hQ]; exact proj_idem B hB 0
  have hQh : Qᴴ = Q := by rw [hQ]; exact proj_herm B hB 0
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hRs : star R = Rᴴ := rfl
  rw [hRs] at hR
  have htr : (A * Q).trace = ((R * Q) * (R * Q)ᴴ).trace := by
    rw [Matrix.conjTranspose_mul, hQh, hR]
    rw [show R * Q * (Q * Rᴴ) = (R * (Q * Q)) * Rᴴ by simp only [Matrix.mul_assoc],
      hQQ, Matrix.mul_assoc Rᴴ, Matrix.trace_mul_comm Rᴴ]
  have hX : R * Q = 0 := by
    rw [← Matrix.trace_mul_conjTranspose_self_eq_zero_iff, ← htr]
    have hnn := (Complex.nonneg_iff.1
      (Matrix.posSemidef_self_mul_conjTranspose (R * Q)).trace_nonneg)
    rw [← htr] at hnn
    apply Complex.ext
    · exact h
    · exact hnn.2.symm
  intro v hv
  have hQv : Q *ᵥ v = v := by
    rw [hQdef, Matrix.sub_mulVec, supp_mulVec B hB v hv, Matrix.one_mulVec, sub_zero]
  rw [← hQv, hR, Matrix.mulVec_mulVec, Matrix.mul_assoc, hX, Matrix.mul_zero, Matrix.zero_mulVec]

lemma ereal_eq (q t : ℝ) (ht : 0 < t) (ω : EReal) (h : (q : EReal) + ω * t = q) : ω = 0 := by
  induction ω using EReal.rec with
  | bot => rw [EReal.bot_mul_coe_of_pos ht] at h; simp at h
  | coe x =>
    have h' : ((q + x * t : ℝ) : EReal) = q := by push_cast; exact h
    have := EReal.coe_injective h'
    have hx : x = 0 := by
      rcases mul_eq_zero.1 (by linarith : x * t = 0) with h0 | h0
      · exact h0
      · linarith
    simp [hx]
  | top => rw [EReal.top_mul_coe_of_pos ht] at h; simp at h

/-! ## C25 helpers -/

lemma mul_proj (X : Mat I) (hX : X.IsHermitian) (l : ℝ) :
    X * spectralProjector X l = l • spectralProjector X l := by
  have hsa : IsSelfAdjoint X := hX
  rw [proj_eq_cfc X hX]
  conv_lhs => arg 1; rw [← cfc_id' ℝ X]
  rw [cmul, ← cfc_const_mul l _ X (cont _ _)]
  congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]

lemma proj_mul (X : Mat I) (hX : X.IsHermitian) (l : ℝ) :
    spectralProjector X l * X = l • spectralProjector X l := by
  have hsa : IsSelfAdjoint X := hX
  rw [proj_eq_cfc X hX]
  conv_lhs => arg 2; rw [← cfc_id' ℝ X]
  rw [cmul, ← cfc_const_mul l _ X (cont _ _)]
  congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]

lemma sum_ext {M : Type*} [AddCommMonoid M] (s t : Finset ℝ) (F : ℝ → M)
    (hs : ∀ a ∈ s, a ∉ t → F a = 0) (ht : ∀ a ∈ t, a ∉ s → F a = 0) :
    ∑ a ∈ s, F a = ∑ a ∈ t, F a := by
  calc ∑ a ∈ s, F a = ∑ a ∈ s ∪ t, F a :=
        Finset.sum_subset Finset.subset_union_left (fun x hx hxs => by
          have : x ∈ t := by rcases Finset.mem_union.1 hx with h | h <;> tauto
          exact ht x this hxs)
    _ = ∑ a ∈ t, F a :=
        (Finset.sum_subset Finset.subset_union_right (fun x hx hxt => by
          have : x ∈ s := by rcases Finset.mem_union.1 hx with h | h <;> tauto
          exact hs x this hxt)).symm

lemma proj_char (Y : Mat I) (hY : Y.IsHermitian) (S : Finset ℝ) (Q : ℝ → Mat I)
    (hQ0 : ∀ a ∉ S, Q a = 0) (hQh : ∀ a, (Q a)ᴴ = Q a) (hsum : ∑ a ∈ S, Q a = 1)
    (hYQ : ∀ a, Y * Q a = a • Q a) (a : ℝ) : spectralProjector Y a = Q a := by
  have hQY : ∀ a, Q a * Y = a • Q a := by
    intro a
    have := congrArg Matrix.conjTranspose (hYQ a)
    rw [Matrix.conjTranspose_mul, hQh, hY.eq, Matrix.conjTranspose_smul, hQh] at this
    simpa using this
  have h1 : ∀ b c, b ≠ c → spectralProjector Y b * Q c = 0 := by
    intro b c hbc
    have e : (b - c) • (spectralProjector Y b * Q c) = 0 := by
      rw [sub_smul, ← smul_mul_assoc, ← proj_mul Y hY b, Matrix.mul_assoc, hYQ,
        mul_smul_comm, sub_self]
    rcases smul_eq_zero.1 e with h | h
    · exact absurd (sub_eq_zero.1 h) hbc
    · exact h
  have h2 : ∀ b c, b ≠ c → Q b * spectralProjector Y c = 0 := by
    intro b c hbc
    have e : (b - c) • (Q b * spectralProjector Y c) = 0 := by
      rw [sub_smul, ← smul_mul_assoc, ← hQY b, Matrix.mul_assoc, mul_proj Y hY c,
        mul_smul_comm, sub_self]
    rcases smul_eq_zero.1 e with h | h
    · exact absurd (sub_eq_zero.1 h) hbc
    · exact h
  have e1 : spectralProjector Y a = spectralProjector Y a * Q a := by
    conv_lhs => rw [← Matrix.mul_one (spectralProjector Y a), ← hsum, Matrix.mul_sum]
    rw [Finset.sum_eq_single a (fun b _ hb => h1 a b (Ne.symm hb))
      (fun ha => by rw [hQ0 a ha, Matrix.mul_zero])]
  have e2 : Q a = Q a * spectralProjector Y a := by
    conv_lhs => rw [← Matrix.mul_one (Q a), ← proj_sum Y hY, Matrix.mul_sum]
    rw [Finset.sum_eq_single a (fun b _ hb => h2 a b (Ne.symm hb))
      (fun ha => by rw [proj_zero Y hY a ha, Matrix.mul_zero])]
  calc spectralProjector Y a = spectralProjector Y a * Q a := e1
    _ = (Q a * spectralProjector Y a)ᴴ := by
        rw [Matrix.conjTranspose_mul, hQh, proj_herm Y hY]
    _ = Q a := by rw [← e2, hQh]

lemma quasi_ST (f : ℝ → ℝ) (A B : Mat I) (hA : A.IsHermitian) (hB : B.PosSemidef)
    (S T : Finset ℝ)
    (hS : ∀ a ∉ S, spectralProjector A a = 0) (hT : ∀ b ∉ T, spectralProjector B b = 0) :
    quasi f A B = ∑ a ∈ S, ∑ b ∈ T, f (a / b) * b * cc A B a b := by
  rw [quasi_formula f A B hB]
  have hc1 : ∀ a b, spectralProjector A a = 0 → cc A B a b = 0 := by
    intro a b h; simp [cc, h]
  have hc2 : ∀ a b, spectralProjector B b = 0 → cc A B a b = 0 := by
    intro a b h; simp [cc, h]
  rw [sum_ext (spec A) S _
    (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hc1 a b (hS a ha), mul_zero])
    (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hc1 a b (proj_zero A hA a ha), mul_zero])]
  refine Finset.sum_congr rfl fun a _ => sum_ext _ _ _
    (fun b _ hb => by rw [hc2 a b (hT b hb), mul_zero])
    (fun b _ hb => by rw [hc2 a b (proj_zero B hB.isHermitian b hb), mul_zero])

lemma tr_proj (A B : Mat I) (hB : B.IsHermitian) :
    tr (A * (1 - supp B)) = tr (A * spectralProjector B 0) := by
  rw [one_sub_supp B hB, proj_eq_cfc B hB]

lemma tr_nonneg' (A B : Mat I) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    0 ≤ tr (A * spectralProjector B 0) := by
  rw [← tr_proj A B hB, ← tr_eq_sum A B hA.isHermitian hB]
  exact Finset.sum_nonneg fun a ha => mul_nonneg (spec_nonneg A hA a ha)
    (cc_nonneg A B hA.isHermitian hB a 0)

/-! transpose -/

lemma proj_transpose (A : Mat I) (hA : A.IsHermitian) (a : ℝ) :
    spectralProjector Aᵀ a = (spectralProjector A a)ᵀ := by
  refine proj_char Aᵀ hA.transpose (spec A) (fun a => (spectralProjector A a)ᵀ)
    (fun a ha => by rw [proj_zero A hA a ha, Matrix.transpose_zero])
    (fun a => ?_) ?_ (fun a => ?_) a
  · have h := proj_herm A hA a
    ext i j
    have := congrFun (congrFun h j) i
    simpa [Matrix.conjTranspose_apply] using this
  · rw [← Matrix.transpose_sum, proj_sum A hA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, proj_mul A hA, Matrix.transpose_smul]

lemma cc_transpose (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) (a b : ℝ) :
    cc Aᵀ Bᵀ a b = cc A B a b := by
  unfold cc
  rw [proj_transpose A hA, proj_transpose B hB, ← Matrix.transpose_mul, Matrix.trace_transpose,
    Matrix.trace_mul_comm]

lemma div_transpose [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f Aᵀ Bᵀ = div f A B := by
  rw [div_eq f hf _ _ hA.transpose hB.transpose, div_eq f hf A B hA hB,
    tr_proj _ _ hB.isHermitian.transpose, tr_proj _ _ hB.isHermitian,
    quasi_ST f Aᵀ Bᵀ hA.isHermitian.transpose hB.transpose (spec A) (spec B)
      (fun a ha => by rw [proj_transpose A hA.isHermitian, proj_zero A hA.isHermitian a ha,
        Matrix.transpose_zero])
      (fun b hb => by rw [proj_transpose B hB.isHermitian, proj_zero B hB.isHermitian b hb,
        Matrix.transpose_zero]),
    quasi_formula f A B hB, proj_transpose B hB.isHermitian]
  simp only [cc_transpose A B hA.isHermitian hB.isHermitian]
  congr 3
  unfold tr
  rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

/-! isometries -/

section iso
variable (W : Matrix J I ℂ) (hW : Wᴴ * W = 1)
include hW

lemma iso_k1 (X M : Mat I) : (W * X * Wᴴ) * (W * M * Wᴴ) = W * (X * M) * Wᴴ := by
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]

lemma iso_k2 (X : Mat I) : W * X * Wᴴ * (1 - W * Wᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul, sub_self]

lemma iso_k3 (X : Mat I) : (1 - W * Wᴴ) * (W * X * Wᴴ) = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul, sub_self]

lemma iso_tr (M : Mat I) : (W * M * Wᴴ).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]

lemma iso_proj (A : Mat I) (hA : A.IsHermitian) (a : ℝ) :
    spectralProjector (W * A * Wᴴ) a =
      W * spectralProjector A a * Wᴴ + (if a = 0 then 1 - W * Wᴴ else 0) := by
  have hY : (W * A * Wᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.eq, Matrix.mul_assoc]
  have hsumP : ∑ a ∈ insert 0 (spec A), spectralProjector A a = 1 := by
    rw [← proj_sum A hA]
    exact sum_ext _ _ _ (fun a _ ha => proj_zero A hA a ha)
      (fun a ha h => absurd (Finset.mem_insert_of_mem ha) h)
  refine proj_char _ hY (insert 0 (spec A))
    (fun a => W * spectralProjector A a * Wᴴ + (if a = 0 then 1 - W * Wᴴ else 0))
    (fun a ha => ?_) (fun a => ?_) ?_ (fun a => ?_) a <;> beta_reduce
  · have h0 : a ≠ 0 := fun h => ha (h ▸ Finset.mem_insert_self _ _)
    have h1 : a ∉ spec A := fun h => ha (Finset.mem_insert_of_mem h)
    simp [h0, proj_zero A hA a h1]
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, proj_herm A hA, Matrix.mul_assoc]
    split_ifs
    · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    · simp
  · rw [Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum, hsumP, Finset.sum_ite_eq',
      if_pos (Finset.mem_insert_self _ _), Matrix.mul_one]
    abel
  · rw [Matrix.mul_add, iso_k1 W hW, mul_proj A hA, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    split_ifs with h
    · subst h; rw [iso_k2 W hW]; simp
    · simp

lemma cc_iso (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) (a b : ℝ) (hb : b ≠ 0) :
    cc (W * A * Wᴴ) (W * B * Wᴴ) a b = cc A B a b := by
  unfold cc
  rw [iso_proj W hW A hA, iso_proj W hW B hB, if_neg hb, add_zero, Matrix.add_mul, iso_k1 W hW]
  split_ifs
  · rw [iso_k3 W hW, add_zero, iso_tr W hW]
  · rw [Matrix.zero_mul, add_zero, iso_tr W hW]

lemma div_iso [Nonempty J] [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f (W * A * Wᴴ) (W * B * Wᴴ) = div f A B := by
  have hA' := hA.mul_mul_conjTranspose_same W
  have hB' := hB.mul_mul_conjTranspose_same W
  have hz : ∀ (X : Mat I) (hX : X.IsHermitian) (a : ℝ), a ∉ insert 0 (spec X) →
      spectralProjector (W * X * Wᴴ) a = 0 := by
    intro X hX a ha
    have h0 : a ≠ 0 := fun h => ha (h ▸ Finset.mem_insert_self _ _)
    have h1 : a ∉ spec X := fun h => ha (Finset.mem_insert_of_mem h)
    rw [iso_proj W hW X hX]; simp [h0, proj_zero X hX a h1]
  have hz' : ∀ (X : Mat I) (hX : X.IsHermitian) (a : ℝ), a ∉ insert 0 (spec X) →
      spectralProjector X a = 0 := by
    intro X hX a ha
    exact proj_zero X hX a (fun h => ha (Finset.mem_insert_of_mem h))
  rw [div_eq f hf _ _ hA' hB', div_eq f hf A B hA hB,
    tr_proj _ _ hB'.isHermitian, tr_proj _ _ hB.isHermitian,
    quasi_ST f _ _ hA'.isHermitian hB' (insert 0 (spec A)) (insert 0 (spec B))
      (hz A hA.isHermitian) (hz B hB.isHermitian),
    quasi_ST f A B hA.isHermitian hB (insert 0 (spec A)) (insert 0 (spec B))
      (hz' A hA.isHermitian) (hz' B hB.isHermitian)]
  have hq : ∀ a b, f (a / b) * b * cc (W * A * Wᴴ) (W * B * Wᴴ) a b =
      f (a / b) * b * cc A B a b := by
    intro a b
    by_cases hb : b = 0
    · simp [hb]
    · rw [cc_iso W hW A B hA.isHermitian hB.isHermitian a b hb]
  simp only [hq]
  congr 3
  unfold tr
  rw [iso_proj W hW B hB.isHermitian, if_pos rfl, Matrix.mul_add, iso_k1 W hW, iso_k2 W hW,
    add_zero, iso_tr W hW]

end iso

/-! scaling -/

lemma proj_scale (A : Mat I) (hA : A.IsHermitian) (l : ℝ) (hl : l ≠ 0) (c : ℝ) :
    spectralProjector ((l : ℂ) • A) c = spectralProjector A (c / l) := by
  have hY : ((l : ℂ) • A).IsHermitian := by
    rw [Complex.coe_smul]; unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, hA.eq]; simp
  refine proj_char _ hY ((spec A).image (fun a => l * a)) (fun c => spectralProjector A (c / l))
    (fun c hc => ?_) (fun c => proj_herm A hA _) ?_ (fun c => ?_) c <;> beta_reduce
  · apply proj_zero A hA
    intro h; apply hc; exact Finset.mem_image.2 ⟨c / l, h, by field_simp⟩
  · rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hl h)]
    simp only [mul_div_cancel_left₀ _ hl]; exact proj_sum A hA
  · rw [Complex.coe_smul, smul_mul_assoc, mul_proj A hA, smul_smul,
      show l * (c / l) = c by field_simp]

lemma quasi_scale (f : ℝ → ℝ) (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (l : ℝ) (hl : 0 < l) :
    quasi f ((l : ℂ) • A) ((l : ℂ) • B) = l * quasi f A B := by
  have hl0 : l ≠ 0 := hl.ne'
  have hl' : (0 : ℂ) ≤ (l : ℂ) := by exact_mod_cast hl.le
  have hA' : ((l : ℂ) • A).PosSemidef := hA.smul hl'
  have hB' : ((l : ℂ) • B).PosSemidef := hB.smul hl'
  have hz : ∀ (X : Mat I) (hX : X.IsHermitian) (c : ℝ), c ∉ (spec X).image (fun a => l * a) →
      spectralProjector ((l : ℂ) • X) c = 0 := by
    intro X hX c hc
    rw [proj_scale X hX l hl0]
    apply proj_zero X hX
    intro h; apply hc; exact Finset.mem_image.2 ⟨c / l, h, by field_simp⟩
  rw [quasi_ST f _ _ hA'.isHermitian hB' _ _ (hz A hA.isHermitian) (hz B hB.isHermitian),
    quasi_formula f A B hB, Finset.mul_sum,
    Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hl0 h)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hl0 h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : cc ((l : ℂ) • A) ((l : ℂ) • B) (l * a) (l * b) = cc A B a b := by
    unfold cc
    rw [proj_scale A hA.isHermitian l hl0, proj_scale B hB.isHermitian l hl0,
      mul_div_cancel_left₀ _ hl0, mul_div_cancel_left₀ _ hl0]
  rw [this, mul_div_mul_left _ _ hl0]; ring

lemma div_scale [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) (l : ℝ) (hl : 0 ≤ l) :
    div f ((l : ℂ) • A) ((l : ℂ) • B) = (l : EReal) * div f A B := by
  rcases hl.eq_or_lt with h0 | hl
  · subst h0
    simp only [Complex.ofReal_zero, zero_smul, EReal.coe_zero, zero_mul]
    have h00 : (0 : Mat I).PosSemidef := Matrix.PosSemidef.zero
    rw [div_eq f hf 0 0 h00 h00]
    have hz : ∀ b ∉ ({0} : Finset ℝ), spectralProjector (0 : Mat I) b = 0 := by
      intro b hb
      rw [proj_char (0 : Mat I) h00.isHermitian {0} (fun b => if b = 0 then 1 else 0) ?_ ?_ ?_ ?_ b]
      · simp at hb; simp [hb]
      · intro a ha; simp at ha; simp [ha]
      · intro a; split_ifs <;> simp
      · simp
      · intro a; split_ifs with h <;> simp [h]
    rw [quasi_ST f 0 0 h00.isHermitian h00 (spec 0) {0}
      (fun a ha => proj_zero _ h00.isHermitian a ha) hz]
    simp [tr]
  · have hl' : (0 : ℂ) ≤ (l : ℂ) := by exact_mod_cast hl.le
    have hA' : ((l : ℂ) • A).PosSemidef := hA.smul hl'
    have hB' : ((l : ℂ) • B).PosSemidef := hB.smul hl'
    rw [div_eq f hf _ _ hA' hB', div_eq f hf A B hA hB, quasi_scale f A B hA hB l hl,
      tr_proj _ _ hB'.isHermitian, tr_proj _ _ hB.isHermitian,
      proj_scale B hB.isHermitian l hl.ne', zero_div]
    have htr : tr ((l : ℂ) • A * spectralProjector B 0) = l * tr (A * spectralProjector B 0) := by
      unfold tr; rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [htr, EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hl.le) (EReal.coe_ne_top l),
      EReal.coe_mul, EReal.coe_mul]
    congr 1
    rw [← mul_assoc, mul_comm (recessionSlope f) (l : EReal), mul_assoc]

/-! orthogonal sums -/

lemma herm_swap (A C : Mat I) (hA : A.IsHermitian) (hC : C.IsHermitian) (h : A * C = 0) :
    C * A = 0 := by
  have := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_mul, hA.eq, hC.eq, Matrix.conjTranspose_zero] at this

lemma supports_add (A C : Mat I) (hA : A.PosSemidef) (hC : C.PosSemidef) :
    Supports A (A + C) := by
  intro v hv
  have h1 : star v ⬝ᵥ (A + C) *ᵥ v = 0 := by rw [hv]; simp
  rw [Matrix.add_mulVec, dotProduct_add] at h1
  have h2 := (add_eq_zero_iff_of_nonneg (hA.dotProduct_mulVec_nonneg v)
    (hC.dotProduct_mulVec_nonneg v)).1 h1
  exact (hA.dotProduct_mulVec_zero_iff v).1 h2.1

lemma col_zero (A X M : Mat I) (h : Supports A X) (hXM : X * M = 0) : A * M = 0 := by
  have hcol : ∀ j, X *ᵥ (fun k => M k j) = 0 := by
    intro j; funext i
    have := congrFun (congrFun hXM i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  ext i j
  have := congrFun (h _ (hcol j)) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma orth (X1 X2 A C : Mat I) (hX2 : X2.IsHermitian) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (h : X1 * X2 = 0) (h1 : Supports A X1) (h2 : Supports C X2) : A * C = 0 ∧ C * A = 0 := by
  have e1 : A * X2 = 0 := col_zero A X1 X2 h1 h
  have e2 : X2 * A = 0 := herm_swap _ _ hA hX2 e1
  have e3 : C * A = 0 := col_zero C X2 A h2 e2
  exact ⟨herm_swap _ _ hC hA e3, e3⟩

lemma mul_proj_zero (X M : Mat I) (hX : X.IsHermitian) (hMX : M * X = 0) (l : ℝ) (hl : l ≠ 0) :
    M * spectralProjector X l = 0 := by
  have : spectralProjector X l = l⁻¹ • (X * spectralProjector X l) := by
    rw [mul_proj X hX, smul_smul, inv_mul_cancel₀ hl, one_smul]
  rw [this, Matrix.mul_smul, ← Matrix.mul_assoc, hMX, Matrix.zero_mul, smul_zero]

lemma proj_mul_zero (X M : Mat I) (hX : X.IsHermitian) (hXM : X * M = 0) (l : ℝ) (hl : l ≠ 0) :
    spectralProjector X l * M = 0 := by
  have : spectralProjector X l = l⁻¹ • (spectralProjector X l * X) := by
    rw [proj_mul X hX, smul_smul, inv_mul_cancel₀ hl, one_smul]
  rw [this, Matrix.smul_mul, Matrix.mul_assoc, hXM, Matrix.mul_zero, smul_zero]

lemma supp_eq (X : Mat I) (hX : X.IsHermitian) :
    supp X = X * cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) X ∧
    supp X = cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) X * X := by
  have hsa : IsSelfAdjoint X := hX
  constructor
  · conv_rhs => arg 1; rw [← cfc_id' ℝ X]
    rw [cmul]
    unfold supp supportPower; congr 1; funext x
    split_ifs with hx
    · simp [hx]
    · simp [hx, Real.rpow_eq_pow]
  · conv_rhs => arg 2; rw [← cfc_id' ℝ X]
    rw [cmul]
    unfold supp supportPower; congr 1; funext x
    split_ifs with hx
    · simp [hx]
    · simp [hx, Real.rpow_eq_pow]

lemma mul_P0 (X M : Mat I) (hX : X.IsHermitian) (hMX : M * X = 0) :
    M * spectralProjector X 0 = M := by
  rw [proj_eq_cfc X hX, ← one_sub_supp X hX, Matrix.mul_sub, Matrix.mul_one, (supp_eq X hX).1,
    ← Matrix.mul_assoc, hMX, Matrix.zero_mul, sub_zero]

lemma P0_mul (X M : Mat I) (hX : X.IsHermitian) (hXM : X * M = 0) :
    spectralProjector X 0 * M = M := by
  rw [proj_eq_cfc X hX, ← one_sub_supp X hX, Matrix.sub_mul, Matrix.one_mul, (supp_eq X hX).2,
    Matrix.mul_assoc, hXM, Matrix.mul_zero, sub_zero]

lemma orth_proj (A1 A2 : Mat I) (h1 : A1.IsHermitian) (h2 : A2.IsHermitian) (h12 : A1 * A2 = 0)
    (h21 : A2 * A1 = 0) (a : ℝ) :
    spectralProjector (A1 + A2) a =
      spectralProjector A1 a + spectralProjector A2 a - (if a = 0 then 1 else 0) := by
  have hY : (A1 + A2).IsHermitian := h1.add h2
  set S := insert 0 (spec A1 ∪ spec A2) with hS
  have hsum : ∀ X : Mat I, X.IsHermitian → spec X ⊆ S → ∑ a ∈ S, spectralProjector X a = 1 := by
    intro X hX hsub
    rw [← proj_sum X hX]
    exact sum_ext _ _ _ (fun a _ ha => proj_zero X hX a ha) (fun a ha h => absurd (hsub ha) h)
  have hs1 : spec A1 ⊆ S := fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)
  have hs2 : spec A2 ⊆ S := fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_right _ ha)
  refine proj_char _ hY S
    (fun a => spectralProjector A1 a + spectralProjector A2 a - (if a = 0 then 1 else 0))
    (fun a ha => ?_) (fun a => ?_) ?_ (fun a => ?_) a <;> beta_reduce
  · have h0 : a ≠ 0 := fun h => ha (h ▸ Finset.mem_insert_self _ _)
    rw [proj_zero A1 h1 a (fun h => ha (hs1 h)), proj_zero A2 h2 a (fun h => ha (hs2 h))]
    simp [h0]
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, proj_herm A1 h1, proj_herm A2 h2]
    split_ifs <;> simp
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum A1 h1 hs1, hsum A2 h2 hs2,
      Finset.sum_ite_eq', if_pos (Finset.mem_insert_self _ _)]
    abel
  · by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl, zero_smul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
        mul_proj A1 h1, mul_proj A2 h2, mul_P0 A1 A2 h1 h21, mul_P0 A2 A1 h2 h12, zero_smul,
        zero_smul, Matrix.mul_one]
      abel
    · rw [if_neg ha, sub_zero, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
        mul_proj A1 h1, mul_proj A2 h2, mul_proj_zero A1 A2 h1 h21 a ha,
        mul_proj_zero A2 A1 h2 h12 a ha, smul_add]
      abel

lemma orth_prod (A1 A2 B1 B2 : Mat I) (hA1 : A1.IsHermitian) (hA2 : A2.IsHermitian)
    (hB1 : B1.IsHermitian) (hB2 : B2.IsHermitian) (hA12 : A1 * A2 = 0) (hA21 : A2 * A1 = 0)
    (hB12 : B1 * B2 = 0) (hB21 : B2 * B1 = 0) (h1 : A1 * B2 = 0) (h2 : A2 * B1 = 0)
    (a b : ℝ) (hb : b ≠ 0) :
    spectralProjector (A1 + A2) a * spectralProjector (B1 + B2) b =
      spectralProjector A1 a * spectralProjector B1 b +
        spectralProjector A2 a * spectralProjector B2 b := by
  have k1 : A1 * spectralProjector B2 b = 0 := mul_proj_zero B2 A1 hB2 h1 b hb
  have k2 : A2 * spectralProjector B1 b = 0 := mul_proj_zero B1 A2 hB1 h2 b hb
  rw [orth_proj A1 A2 hA1 hA2 hA12 hA21, orth_proj B1 B2 hB1 hB2 hB12 hB21, if_neg hb, sub_zero]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
      P0_mul A1 _ hA1 k1, P0_mul A2 _ hA2 k2]
    abel
  · rw [if_neg ha, sub_zero, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      proj_mul_zero A1 _ hA1 k1 a ha, proj_mul_zero A2 _ hA2 k2 a ha]
    abel

lemma div_orth [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A1 B1 A2 B2 : Mat I) (hA1 : A1.PosSemidef) (hB1 : B1.PosSemidef)
    (hA2 : A2.PosSemidef) (hB2 : B2.PosSemidef) (h : (A1 + B1) * (A2 + B2) = 0) :
    div f (A1 + A2) (B1 + B2) = div f A1 B1 + div f A2 B2 := by
  have hX2 : (A2 + B2).IsHermitian := hA2.isHermitian.add hB2.isHermitian
  have sA1 : Supports A1 (A1 + B1) := supports_add A1 B1 hA1 hB1
  have sB1 : Supports B1 (A1 + B1) := by rw [add_comm]; exact supports_add B1 A1 hB1 hA1
  have sA2 : Supports A2 (A2 + B2) := supports_add A2 B2 hA2 hB2
  have sB2 : Supports B2 (A2 + B2) := by rw [add_comm]; exact supports_add B2 A2 hB2 hA2
  obtain ⟨hA12, hA21⟩ := orth _ _ A1 A2 hX2 hA1.isHermitian hA2.isHermitian h sA1 sA2
  obtain ⟨hAB12, -⟩ := orth _ _ A1 B2 hX2 hA1.isHermitian hB2.isHermitian h sA1 sB2
  obtain ⟨-, hAB21⟩ := orth _ _ B1 A2 hX2 hB1.isHermitian hA2.isHermitian h sB1 sA2
  obtain ⟨hB12, hB21⟩ := orth _ _ B1 B2 hX2 hB1.isHermitian hB2.isHermitian h sB1 sB2
  have hY := hA1.add hA2
  have hZ := hB1.add hB2
  set S := insert 0 (spec A1 ∪ spec A2) with hS
  set T := insert 0 (spec B1 ∪ spec B2) with hT
  have z1 : ∀ (X1 X2 : Mat I), X1.IsHermitian → X2.IsHermitian → ∀ a,
      a ∉ insert 0 (spec X1 ∪ spec X2) → spectralProjector X1 a = 0 :=
    fun X1 X2 h1 _ a ha => proj_zero X1 h1 a
      (fun h => ha (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
  have z2 : ∀ (X1 X2 : Mat I), X1.IsHermitian → X2.IsHermitian → ∀ a,
      a ∉ insert 0 (spec X1 ∪ spec X2) → spectralProjector X2 a = 0 :=
    fun X1 X2 _ h2 a ha => proj_zero X2 h2 a
      (fun h => ha (Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))
  have z3 : ∀ (X1 X2 : Mat I) (h1 : X1.IsHermitian) (h2 : X2.IsHermitian), X1 * X2 = 0 →
      X2 * X1 = 0 → ∀ a, a ∉ insert 0 (spec X1 ∪ spec X2) →
      spectralProjector (X1 + X2) a = 0 := by
    intro X1 X2 h1 h2 h12 h21 a ha
    have h0 : a ≠ 0 := fun h => ha (h ▸ Finset.mem_insert_self _ _)
    rw [orth_proj X1 X2 h1 h2 h12 h21, z1 X1 X2 h1 h2 a ha, z2 X1 X2 h1 h2 a ha]
    simp [h0]
  rw [div_eq f hf _ _ hY hZ, div_eq f hf A1 B1 hA1 hB1, div_eq f hf A2 B2 hA2 hB2,
    quasi_ST f _ _ hY.isHermitian hZ S T
      (z3 A1 A2 hA1.isHermitian hA2.isHermitian hA12 hA21)
      (z3 B1 B2 hB1.isHermitian hB2.isHermitian hB12 hB21),
    quasi_ST f A1 B1 hA1.isHermitian hB1 S T
      (z1 A1 A2 hA1.isHermitian hA2.isHermitian) (z1 B1 B2 hB1.isHermitian hB2.isHermitian),
    quasi_ST f A2 B2 hA2.isHermitian hB2 S T
      (z2 A1 A2 hA1.isHermitian hA2.isHermitian) (z2 B1 B2 hB1.isHermitian hB2.isHermitian),
    tr_proj _ _ hZ.isHermitian, tr_proj _ _ hB1.isHermitian, tr_proj _ _ hB2.isHermitian]
  have hq : ∑ a ∈ S, ∑ b ∈ T, f (a / b) * b * cc (A1 + A2) (B1 + B2) a b =
      ∑ a ∈ S, ∑ b ∈ T, f (a / b) * b * cc A1 B1 a b +
        ∑ a ∈ S, ∑ b ∈ T, f (a / b) * b * cc A2 B2 a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b = 0
    · simp [hb]
    · unfold cc
      rw [orth_prod A1 A2 B1 B2 hA1.isHermitian hA2.isHermitian hB1.isHermitian
        hB2.isHermitian hA12 hA21 hB12 hB21 hAB12 hAB21 a b hb, Matrix.trace_add, Complex.add_re]
      ring
  have ht : tr ((A1 + A2) * spectralProjector (B1 + B2) 0) =
      tr (A1 * spectralProjector B1 0) + tr (A2 * spectralProjector B2 0) := by
    rw [orth_proj B1 B2 hB1.isHermitian hB2.isHermitian hB12 hB21, if_pos rfl]
    have e : (A1 + A2) * (spectralProjector B1 0 + spectralProjector B2 0 - 1) =
        A1 * spectralProjector B1 0 + A2 * spectralProjector B2 0 := by
      rw [Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
        mul_P0 B2 A1 hB2.isHermitian hAB12, mul_P0 B1 A2 hB1.isHermitian hAB21, Matrix.mul_one]
      abel
    unfold tr; rw [e, Matrix.trace_add, Complex.add_re]
  rw [hq, ht, ← ereal_mul_add _ _ _ (tr_nonneg' A1 B1 hA1 hB1.isHermitian)
    (tr_nonneg' A2 B2 hA2 hB2.isHermitian), EReal.coe_add]
  abel

/-! tensoring with a unit vector -/

def Vx (x : J → ℂ) : Matrix (I × J) I ℂ := fun p i => if p.1 = i then x p.2 else 0

lemma kron_eq (A : Mat I) (x : J → ℂ) :
    Matrix.kronecker A (fun i j => x i * conj (x j)) = Vx (I := I) x * A * (Vx (I := I) x)ᴴ := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Vx, Matrix.kroneckerMap, Matrix.mul_apply, Matrix.conjTranspose_apply,
    apply_ite (starRingEnd ℂ), Finset.sum_ite_eq]
  ring

lemma Vx_iso (x : J → ℂ) (hx : ∑ j, ‖x j‖ ^ 2 = 1) : (Vx (I := I) x)ᴴ * Vx (I := I) x = 1 := by
  have h1 : ∑ j, conj (x j) * x j = 1 := by
    simp only [Complex.conj_mul']
    exact_mod_cast hx
  ext k k'
  simp [Vx, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  by_cases hk : k = k'
  · subst hk; simpa using h1
  · simp [Ne.symm hk, hk]

theorem cor25 [Nonempty I] [Nonempty J] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B A1 B1 A2 B2 : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA1 : A1.PosSemidef) (hB1 : B1.PosSemidef)
    (hA2 : A2.PosSemidef) (hB2 : B2.PosSemidef) :
    (∀ l : ℝ, 0 ≤ l → div f ((l : ℂ) • A) ((l : ℂ) • B) = (l : EReal) * div f A B) ∧
    ((A1 + B1) * (A2 + B2) = 0 →
      div f (A1 + A2) (B1 + B2) = div f A1 B1 + div f A2 B2) ∧
    (∀ (anti : Bool) (W : Matrix J I ℂ), Wᴴ * W = 1 →
      div f (isometricConjugation anti W A) (isometricConjugation anti W B) = div f A B) ∧
    (∀ x : J → ℂ, ∑ j, ‖x j‖ ^ 2 = 1 →
      div f (Matrix.kronecker A (fun i j => x i * conj (x j)))
        (Matrix.kronecker B (fun i j => x i * conj (x j))) = div f A B) := by
  refine ⟨fun l hl => div_scale f hf A B hA hB l hl,
    fun h => div_orth f hf A1 B1 A2 B2 hA1 hB1 hA2 hB2 h, fun anti W hW => ?_, fun x hx => ?_⟩
  · cases anti
    · simpa [isometricConjugation] using div_iso W hW f hf A B hA hB
    · simp only [isometricConjugation, if_true]
      rw [div_iso W hW f hf _ _ hA.transpose hB.transpose, div_transpose f hf A B hA hB]
  · rw [kron_eq A x, kron_eq B x]
    exact div_iso (Vx x) (Vx_iso x hx) f hf A B hA hB

end A3S55C25

end QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Support50.P12 (div DivergenceGenerator isometricConjugation)
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B A1 B1 A2 B2 : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA1 : A1.PosSemidef) (hB1 : B1.PosSemidef)
    (hA2 : A2.PosSemidef) (hB2 : B2.PosSemidef) :
    (∀ l : ℝ, 0 ≤ l → div f ((l : ℂ) • A) ((l : ℂ) • B) = (l : EReal) * div f A B) ∧
    ((A1 + B1) * (A2 + B2) = 0 →
      div f (A1 + A2) (B1 + B2) = div f A1 B1 + div f A2 B2) ∧
    (∀ (anti : Bool) (W : Matrix J I ℂ), Wᴴ * W = 1 →
      div f (isometricConjugation anti W A) (isometricConjugation anti W B) = div f A B) ∧
    (∀ x : J → ℂ, ∑ j, ‖x j‖ ^ 2 = 1 →
      div f (Matrix.kronecker A (fun i j => x i * conj (x j)))
        (Matrix.kronecker B (fun i j => x i * conj (x j))) = div f A B) :=
  QAlgorithms.Papers.Independent.Support50.P12.A3S55C25.cor25 f hf A B A1 B1 A2 B2
    hA hB hA1 hB1 hA2 hB2


end
