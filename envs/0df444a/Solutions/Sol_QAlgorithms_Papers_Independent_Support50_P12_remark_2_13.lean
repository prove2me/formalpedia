-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.remark_2_13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:07:13.30898+00:00
-- url     : https://prove2.me/submissions/909f6982-ef9f-49da-bf7e-c4d307e4703c

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


namespace A3S55P22

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

end A3S55P22

end QAlgorithms.Papers.Independent.Support50.P12

attribute [local instance] Classical.propDecidable Classical.decEq

namespace A3S55R213X
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms (spectralProjector)
open scoped Matrix ComplexConjugate ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

theorem specProj_eq (A M : Mat I) (a : ℝ) (hM : Mᴴ = M) (hMM : M * M = M)
    (hAM : A * M = (a : ℂ) • M) (c : ℂ) (hc : 1 - M = c • (A - (a : ℂ) • 1)) :
    spectralProjector A a = M := by
  unfold spectralProjector QAlgorithms.eigenProjection
  rw [LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro u
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, ContinuousLinearMap.coe_coe]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Module.End.mem_eigenspace_iff]
    simp only [ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hAM, Matrix.smul_mulVec]
  · intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw
    simp only [ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hw
    simp only [Matrix.toEuclideanLin_apply] at hw ⊢
    have hw' : M *ᵥ w.ofLp = w.ofLp := by
      have h1 : (1 - M) *ᵥ w.ofLp = 0 := by
        rw [hc, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        have := congrArg WithLp.ofLp hw
        simp only [WithLp.ofLp_toLp] at this
        rw [this]; simp
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
      exact h1.symm
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [← hw']
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_toLp, star_sub, Matrix.star_mulVec, hM, Matrix.sub_vecMul,
      Matrix.vecMul_vecMul, hMM, sub_self, zero_dotProduct]

def two (b1 b2 : ℝ) (Q : Mat I) : Mat I := (b1 : ℂ) • Q + (b2 : ℂ) • (1 - Q)

section
variable {Q : Mat I} (hQQ : Q * Q = Q)
include hQQ

theorem two_mul_Q (b1 b2 : ℝ) : two b1 b2 Q * Q = (b1 : ℂ) • Q := by
  simp [two, add_mul, sub_mul, hQQ, smul_mul_assoc]
theorem Q_mul_two (b1 b2 : ℝ) : Q * two b1 b2 Q = (b1 : ℂ) • Q := by
  simp [two, mul_add, mul_sub, hQQ, mul_smul_comm]
theorem two_mul_Qc (b1 b2 : ℝ) : two b1 b2 Q * (1 - Q) = (b2 : ℂ) • (1 - Q) := by
  simp [two, add_mul, sub_mul, mul_sub, hQQ, smul_mul_assoc]
theorem Qc_mul_two (b1 b2 : ℝ) : (1 - Q) * two b1 b2 Q = (b2 : ℂ) • (1 - Q) := by
  simp [two, mul_add, mul_sub, sub_mul, hQQ, mul_smul_comm]

omit hQQ in
theorem two_herm (hQ : Qᴴ = Q) (b1 b2 : ℝ) : (two b1 b2 Q)ᴴ = two b1 b2 Q := by
  simp [two, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hQ]

theorem spectrum_two_sub (b1 b2 : ℝ) : spectrum ℝ (two b1 b2 Q) ⊆ {b1, b2} := by
  intro a ha
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  apply ha
  refine IsUnit.of_mul_eq_one (((a - b1)⁻¹ : ℝ) • Q + ((a - b2)⁻¹ : ℝ) • (1 - Q)) ?_
  have h1 : (a - b1 : ℝ) ≠ 0 := sub_ne_zero.mpr hne.1
  have h2 : (a - b2 : ℝ) ≠ 0 := sub_ne_zero.mpr hne.2
  rw [Algebra.algebraMap_eq_smul_one]
  have e : a • (1 : Mat I) - two b1 b2 Q = ((a - b1 : ℝ) : ℂ) • Q + ((a - b2 : ℝ) : ℂ) • (1 - Q) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e]
  have hc : ∀ (r : ℝ) (M : Mat I), r • M = (r : ℂ) • M := fun r M => by ext; simp
  rw [hc, hc]
  simp only [add_mul, mul_add, smul_mul_smul, mul_sub, sub_mul, hQQ, one_mul, mul_one, sub_self,
    smul_zero, add_zero, zero_add]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
  simp

theorem spectrum_two (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0) (b1 b2 : ℝ) :
    spectrum ℝ (two b1 b2 Q) = {b1, b2} := by
  apply (spectrum_two_sub hQQ b1 b2).antisymm
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hu
  rcases ha with rfl | rfl
  · apply hQ0
    have : (a • (1 : Mat I) - two a b2 Q) * Q = 0 := by
      rw [sub_mul, two_mul_Q hQQ]; ext; simp
    exact (hu.mul_right_eq_zero).mp this
  · apply hQ1
    have : (a • (1 : Mat I) - two b1 a Q) * (1 - Q) = 0 := by
      rw [sub_mul, two_mul_Qc hQQ]; ext; simp
    exact (hu.mul_right_eq_zero).mp this

theorem spec_two (hQ : Qᴴ = Q) (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0) (b1 b2 : ℝ) :
    QAlgorithms.Papers.Independent.Support50.P12.spec (two b1 b2 Q) = {b1, b2} := by
  have hH : (two b1 b2 Q).IsHermitian := two_herm hQ b1 b2
  unfold QAlgorithms.Papers.Independent.Support50.P12.spec
  rw [dif_pos hH]
  ext a
  have := spectrum_two hQQ hQ0 hQ1 b1 b2
  rw [hH.spectrum_real_eq_range_eigenvalues] at this
  have h2 := congrArg (a ∈ ·) this
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at h2
  simp [h2]

theorem cfc_two (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) (g : ℝ → ℝ) :
    cfc g (two b1 b2 Q) = two (g b1) (g b2) Q := by
  have hH : IsSelfAdjoint (two b1 b2 Q) := two_herm hQ b1 b2
  set β := (g b2 - g b1) / (b2 - b1)
  set α := g b1 - β * b1
  have hb' : b2 - b1 ≠ 0 := sub_ne_zero.mpr hb.symm
  have h1 : α + β * b1 = g b1 := by simp [α]
  have h2 : α + β * b2 = g b2 := by
    simp only [α, β]; field_simp; ring
  rw [cfc_congr (g := fun x => α + β * x)]
  · rw [cfc_add (a := two b1 b2 Q) (fun _ => α) (fun x => β * x), cfc_const α (two b1 b2 Q), cfc_const_mul β (fun x => x) (two b1 b2 Q), cfc_id' ℝ (two b1 b2 Q)]
    rw [← h1, ← h2, Algebra.algebraMap_eq_smul_one]
    simp only [two]; ext i j
    simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  · intro x hx
    rcases spectrum_two_sub hQQ b1 b2 hx with rfl | h
    · exact h1.symm
    · rw [Set.mem_singleton_iff] at h; subst h; exact h2.symm

theorem specProj_two1 (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    spectralProjector (two b1 b2 Q) b1 = Q := by
  have hb' : ((b2 : ℂ) - b1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb.symm
  apply specProj_eq _ _ _ hQ hQQ (two_mul_Q hQQ b1 b2) ((b2 - b1 : ℂ)⁻¹)
  have e : two b1 b2 Q - (b1 : ℂ) • 1 = ((b2 : ℂ) - b1) • (1 - Q) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e, smul_smul, inv_mul_cancel₀ hb', one_smul]

theorem specProj_two2 (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    spectralProjector (two b1 b2 Q) b2 = 1 - Q := by
  have hb' : ((b1 : ℂ) - b2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  have hQc : (1 - Q) * (1 - Q) = 1 - Q := by simp [mul_sub, sub_mul, hQQ]
  apply specProj_eq _ _ _ (by simp [Matrix.conjTranspose_sub, hQ]) hQc (two_mul_Qc hQQ b1 b2)
    ((b1 - b2 : ℂ)⁻¹)
  have e : two b1 b2 Q - (b2 : ℂ) • 1 = ((b1 : ℂ) - b2) • (1 - (1 - Q)) := by
    simp only [two]; ext i j; simp [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
  rw [e, smul_smul, inv_mul_cancel₀ hb', one_smul, sub_sub_cancel]
end

theorem hs_eq (A B : Mat I) : QAlgorithms.Papers.Independent.Frontier18.P17.hs A B = (Aᴴ * B).trace := by
  unfold QAlgorithms.Papers.Independent.Frontier18.P17.hs QAlgorithms.Papers.Independent.Frontier18.P17.res
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diag,
    Matrix.conjTranspose_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

def gh (x : ℝ) : ℝ := if x = 0 then 0 else Real.rpow x (1 / 2)

theorem sp_two {Q : Mat I} (hQQ : Q * Q = Q) (hQ : Qᴴ = Q) (b1 b2 : ℝ) (hb : b1 ≠ b2) :
    QAlgorithms.Papers.Independent.Information100.P71.supportPower (two b1 b2 Q) (1 / 2) =
      two (gh b1) (gh b2) Q := by
  unfold QAlgorithms.Papers.Independent.Information100.P71.supportPower
  exact cfc_two hQQ hQ b1 b2 hb _

theorem quasi_two (f : ℝ → ℝ) {P Q : Mat I} (hPP : P * P = P) (hP : Pᴴ = P) (hP0 : P ≠ 0)
    (hP1 : 1 - P ≠ 0) (hQQ : Q * Q = Q) (hQ : Qᴴ = Q) (hQ0 : Q ≠ 0) (hQ1 : 1 - Q ≠ 0)
    (a1 a2 b1 b2 : ℝ) (ha : a1 ≠ a2) (hb : b1 ≠ b2) :
    QAlgorithms.Papers.Independent.Support50.P12.quasi f (two a1 a2 P) (two b1 b2 Q) =
      f (a1 / b1) * (gh b1 * gh b1) * (Q * P).trace.re
      + f (a1 / b2) * (gh b2 * gh b2) * ((1 - Q) * P).trace.re
      + f (a2 / b1) * (gh b1 * gh b1) * (Q * (1 - P)).trace.re
      + f (a2 / b2) * (gh b2 * gh b2) * ((1 - Q) * (1 - P)).trace.re := by
  unfold QAlgorithms.Papers.Independent.Support50.P12.quasi
    QAlgorithms.Papers.Independent.Support50.P12.modular
  rw [sp_two hQQ hQ b1 b2 hb, spec_two hPP hP hP0 hP1, spec_two hQQ hQ hQ0 hQ1,
    Finset.sum_pair ha, Finset.sum_pair hb, Finset.sum_pair hb,
    specProj_two1 hPP hP _ _ ha, specProj_two2 hPP hP _ _ ha,
    specProj_two1 hQQ hQ _ _ hb, specProj_two2 hQQ hQ _ _ hb, hs_eq, two_herm hQ]
  set S := two (gh b1) (gh b2) Q
  have t1 : ∀ X : Mat I, (S * (X * S * Q)).trace = ((gh b1 * gh b1 : ℝ) : ℂ) * (Q * X).trace := by
    intro X
    rw [Matrix.mul_assoc X, two_mul_Q hQQ, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm, Matrix.mul_assoc, Q_mul_two hQQ, Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, mul_assoc, Matrix.trace_mul_comm X]
  have t2 : ∀ X : Mat I, (S * (X * S * (1 - Q))).trace =
      ((gh b2 * gh b2 : ℝ) : ℂ) * ((1 - Q) * X).trace := by
    intro X
    rw [Matrix.mul_assoc X, two_mul_Qc hQQ, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm, Matrix.mul_assoc, Qc_mul_two hQQ, Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, mul_assoc, Matrix.trace_mul_comm X]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, t1, t2,
    smul_eq_mul, Complex.add_re]
  simp only [Complex.re_ofReal_mul]
  ring

end A3S55R213X

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

namespace A3S55R213

open A3S55P22

def P (u : I → ℂ) : Mat I := fun i j => u i * conj (u j)

lemma P_eq (u : I → ℂ) : P u = Matrix.vecMulVec u (star u) := by
  ext i j; simp [P, Matrix.vecMulVec_apply]

lemma P_psd (u : I → ℂ) : (P u).PosSemidef := by
  rw [P_eq]; exact Matrix.posSemidef_vecMulVec_self_star u

lemma P_herm (u : I → ℂ) : (P u)ᴴ = P u := (P_psd u).isHermitian

lemma P_mul (u v : I → ℂ) :
    P u * P v = (∑ k, conj (u k) * v k) • Matrix.of (fun i j => u i * conj (v j)) := by
  ext i j
  simp only [P, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sum_one (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : ∑ k, conj (u k) * u k = 1 := by
  simp_rw [Complex.conj_mul']
  exact_mod_cast hu

lemma P_idem (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : P u * P u = P u := by
  rw [P_mul, sum_one u hu, one_smul]; rfl

lemma P_trace (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : (P u).trace = 1 := by
  have := sum_one u hu
  rw [← this]
  simp only [Matrix.trace, Matrix.diag, P]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma tr_PP (u v : I → ℂ) :
    (P u * P v).trace.re = ‖∑ k, conj (u k) * v k‖ ^ 2 := by
  rw [P_mul, Matrix.trace_smul, smul_eq_mul]
  have : (Matrix.trace (Matrix.of (fun i j => u i * conj (v j)))) = conj (∑ k, conj (u k) * v k) := by
    simp [Matrix.trace, map_sum]
  rw [this, Complex.mul_conj']
  norm_cast

lemma toLp_norm (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ I)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [hu]

lemma inner_lt (x v : I → ℂ) (hx : ∑ i, ‖x i‖ ^ 2 = 1) (hv : ∑ i, ‖v i‖ ^ 2 = 1)
    (hn : ¬ ∃ c : ℂ, v = c • x) : ‖∑ k, conj (x k) * v k‖ < 1 := by
  set X : EuclideanSpace ℂ I := WithLp.toLp 2 x
  set V : EuclideanSpace ℂ I := WithLp.toLp 2 v
  have hin : inner ℂ X V = ∑ k, conj (x k) * v k := by
    simp [X, V, PiLp.inner_apply, mul_comm]
  have hX : ‖X‖ = 1 := toLp_norm x hx
  have hV : ‖V‖ = 1 := toLp_norm v hv
  rw [← hin]
  have hle : ‖inner ℂ X V‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) X V
    rw [hX, hV] at this; simpa using this
  refine lt_of_le_of_ne hle fun heq => hn ?_
  have hX0 : X ≠ 0 := fun h => by rw [h, norm_zero] at hX; exact zero_ne_one hX
  have hV0 : V ≠ 0 := fun h => by rw [h, norm_zero] at hV; exact zero_ne_one hV
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hX0 hV0).1 (by rw [heq, hX, hV, mul_one])
  refine ⟨r, ?_⟩
  have := congrArg WithLp.ofLp hr
  simpa [X, V] using this

lemma two10 (Q : Mat I) : A3S55R213X.two 1 0 Q = Q := by simp [A3S55R213X.two]

lemma P_ne0 (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : P u ≠ 0 := by
  intro h; have := P_trace u hu; rw [h] at this; simp at this

lemma P_ne1 (hI : 2 ≤ Fintype.card I) (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : 1 - P u ≠ 0 := by
  intro h
  have := congrArg Matrix.trace h
  rw [Matrix.trace_sub, P_trace u hu, Matrix.trace_one, Matrix.trace_zero, sub_eq_zero] at this
  have h2 : ((Fintype.card I : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by simpa using this
  have := Nat.cast_injective h2
  omega

lemma supp_P (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) : supp (P u) = P u := by
  have h := A3S55R213X.cfc_two (P_idem u hu) (P_herm u) 1 0 one_ne_zero
    (fun x : ℝ => if x = 0 then 0 else Real.rpow x 0)
  rw [two10] at h
  unfold supp supportPower
  rw [h]
  simp [A3S55R213X.two]

lemma quasi_PP (hI : 2 ≤ Fintype.card I) (f : ℝ → ℝ) (u : I → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) :
    quasi f (P u) (P u) = f 1 := by
  have h := A3S55R213X.quasi_two f (P_idem u hu) (P_herm u) (P_ne0 u hu) (P_ne1 hI u hu)
    (P_idem u hu) (P_herm u) (P_ne0 u hu) (P_ne1 hI u hu) 1 0 1 0 one_ne_zero one_ne_zero
  rw [two10] at h
  rw [h]
  have h0 : P u * (1 - P u) = 0 := by rw [Matrix.mul_sub, P_idem u hu, mul_one, sub_self]
  rw [P_idem u hu, P_trace u hu, h0]
  simp [A3S55R213X.gh]

lemma ereal_val (ω : EReal) (hw : ω = ⊤ ∨ ω = ⊥) (q k : ℝ) (hk : 0 < k) :
    (q : EReal) + ω * (k : EReal) = ω := by
  rcases hw with rfl | rfl
  · rw [EReal.top_mul_coe_of_pos hk, EReal.coe_add_top]
  · rw [EReal.bot_mul_coe_of_pos hk, EReal.add_bot]

theorem key (hI : 2 ≤ Fintype.card I) (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (hw : recessionSlope f = ⊤ ∨ recessionSlope f = ⊥) (x : I → ℂ) (seq : ℕ → I → ℂ)
    (hx : ∑ i, ‖x i‖ ^ 2 = 1) (hseq : ∀ n, ∑ i, ‖seq n i‖ ^ 2 = 1)
    (hlim : Tendsto seq atTop (𝓝 x))
    (hn : ∀ n, ¬ ∃ c : ℂ, seq n = c • x) :
    Tendsto (fun n => P (seq n)) atTop (𝓝 (P x)) ∧ div f (P x) (P x) = (f 1 : EReal) ∧
      (∀ n, div f (P x) (P (seq n)) = recessionSlope f) ∧
      ¬ Tendsto (fun n => div f (P x) (P (seq n))) atTop (𝓝 (div f (P x) (P x))) := by
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hcont : Continuous (P : (I → ℂ) → Mat I) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply i).mul (Complex.continuous_conj.comp (continuous_apply j))
  have hAA : div f (P x) (P x) = (f 1 : EReal) := by
    have hs : Supports (P x) (P x) := fun v hv => hv
    unfold div; rw [if_pos hs, quasi_PP hI f x hx]
  have hAB : ∀ n, div f (P x) (P (seq n)) = recessionSlope f := by
    intro n
    set A := P x
    set B := P (seq n)
    have hA := P_psd x
    have hB := P_psd (seq n)
    have hk : tr (A * (1 - supp B)) = 1 - ‖∑ k, conj (x k) * seq n k‖ ^ 2 := by
      rw [supp_P _ (hseq n), Matrix.mul_sub, mul_one]
      unfold tr
      rw [Matrix.trace_sub, Complex.sub_re, tr_PP, P_trace x hx]
      simp
    have hlt := inner_lt x (seq n) hx (hseq n) (hn n)
    have hkpos : 0 < tr (A * (1 - supp B)) := by
      rw [hk]
      have : ‖∑ k, conj (x k) * seq n k‖ ^ 2 < 1 := by
        have h0 := norm_nonneg (∑ k, conj (x k) * seq n k)
        nlinarith
      linarith
    have hns : ¬ Supports A B := fun h => by
      have := tr_zero_of_supports A B hB.isHermitian h; linarith
    have hm := (main f hf A B hA hB).1
    have hq : Tendsto (fun e : ℝ => (quasi f A (B + (e : ℂ) • 1) : EReal)) (𝓝[>] 0)
        (𝓝 ((quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal))) := by
      refine hm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with e he
      unfold div; rw [if_pos (supports_shift A B hB e he)]
    unfold div; rw [if_neg hns, hq.limUnder_eq]
    exact ereal_val _ hw _ _ hkpos
  refine ⟨(hcont.tendsto x).comp hlim, hAA, hAB, fun h => ?_⟩
  simp only [hAB, hAA] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  rcases hw with hw | hw <;> rw [hw] at this
  · exact EReal.coe_ne_top _ this
  · exact EReal.coe_ne_bot _ this

end A3S55R213

end QAlgorithms.Papers.Independent.Support50.P12

open Filter Set
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Support50.P12 (div recessionSlope DivergenceGenerator)
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] [DecidableEq I] (hI : 2 ≤ Fintype.card I) (f : ℝ → ℝ)
    (hf : DivergenceGenerator f)
    (hw : recessionSlope f = ⊤ ∨ recessionSlope f = ⊥) (x : I → ℂ) (seq : ℕ → I → ℂ)
    (hx : ∑ i, ‖x i‖ ^ 2 = 1) (hseq : ∀ n, ∑ i, ‖seq n i‖ ^ 2 = 1)
    (hlim : Tendsto seq atTop (𝓝 x))
    (hn : ∀ n, ¬ ∃ c : ℂ, seq n = c • x) :
    let A : Mat I := fun i j => x i * conj (x j)
    let B : ℕ → Mat I := fun n i j => seq n i * conj (seq n j)
    Tendsto B atTop (𝓝 A) ∧ div f A A = (f 1 : EReal) ∧
      (∀ n, div f A (B n) = recessionSlope f) ∧
      ¬ Tendsto (fun n => div f A (B n)) atTop (𝓝 (div f A A)) :=
  QAlgorithms.Papers.Independent.Support50.P12.A3S55R213.key hI f hf hw x seq hx hseq hlim hn


end
