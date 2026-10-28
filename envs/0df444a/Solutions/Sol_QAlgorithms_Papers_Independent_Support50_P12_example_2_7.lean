-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.example_2_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:07:14.645925+00:00
-- url     : https://prove2.me/submissions/3a74f707-e315-469e-97f9-40923be016a2

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

namespace A3S55E27
open A3S55P22

lemma cfc_eq_sum (X : Mat I) (hX : X.IsHermitian) (g : ℝ → ℝ) :
    cfc g X = ∑ l ∈ spec X, g l • spectralProjector X l := by
  have hsa : IsSelfAdjoint X := hX
  have h1 : cfc g X = cfc (∑ l ∈ spec X, fun x => g l * ind l x) X := by
    apply cfc_congr
    intro x hx
    rw [← mem_spec X hX] at hx
    simp only [Finset.sum_apply, ind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp [hx]
  rw [h1, cfc_sum _ X _ (fun _ _ => cont _ _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cfc_const_mul (g l) _ X (cont _ _), proj_eq_cfc X hX]

lemma tr_cfc_mul (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) (g h : ℝ → ℝ) :
    tr (cfc g A * cfc h B) = ∑ a ∈ spec A, ∑ b ∈ spec B, g a * h b * cc A B a b := by
  rw [cfc_eq_sum A hA, cfc_eq_sum B hB, Finset.sum_mul]
  unfold tr
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_smul_comm, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  unfold cc; ring

lemma ssp_term (a x b : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b) :
    supportScalarPower a (x / b) * b =
      (if x = 0 then 0 else Real.rpow x a) * (if b = 0 then 0 else Real.rpow b (1 - a)) := by
  unfold supportScalarPower
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  rw [if_neg (div_pos hx' hb').ne', if_neg hx'.ne', if_neg hb'.ne']
  show (x / b) ^ a * b = x ^ a * b ^ (1 - a)
  have : 0 < b ^ a := Real.rpow_pos_of_pos hb' a
  rw [Real.div_rpow hx hb, Real.rpow_sub hb', Real.rpow_one]
  field_simp

theorem quasi_ssp (a : ℝ) (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quasi (supportScalarPower a) A B = tr (supportPower A a * supportPower B (1 - a)) := by
  rw [quasi_formula _ A B hB]
  show _ = tr (cfc _ A * cfc _ B)
  rw [tr_cfc_mul A B hA.isHermitian hB.isHermitian]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun b hb => ?_
  rw [ssp_term a x b (spec_nonneg A hA x hx) (spec_nonneg B hB b hb)]

theorem div_eq [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f A B = (quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal) := by
  by_cases hs : Supports A B
  · rw [div, if_pos hs, tr_zero_of_supports A B hB.isHermitian hs]; simp
  · rw [div, if_neg hs]
    apply Filter.Tendsto.limUnder_eq
    refine (main f hf A B hA hB).1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [div, if_pos (supports_shift A B hB e he)]

lemma gen_of (f : ℝ → ℝ) (hc : ContinuousOn f (Ioi 0)) (L : EReal)
    (h : Tendsto (fun x : ℝ => ((f x / x : ℝ) : EReal)) atTop (𝓝 L)) :
    DivergenceGenerator f ∧ recessionSlope f = L := by
  have hL : recessionSlope f = L := h.limUnder_eq
  exact ⟨⟨hc, by rw [hL]; exact h⟩, hL⟩

lemma ssp_cont (a : ℝ) : ContinuousOn (supportScalarPower a) (Ioi 0) := by
  have : ContinuousOn (fun x : ℝ => x ^ a) (Ioi 0) := fun x hx =>
    (Real.continuousAt_rpow_const x a (Or.inl (ne_of_gt hx))).continuousWithinAt
  refine this.congr fun x hx => ?_
  show (if x = 0 then 0 else Real.rpow x a) = x ^ a
  rw [if_neg (ne_of_gt hx)]; rfl

lemma ssp_ratio (a : ℝ) : (fun x : ℝ => (x ^ (a - 1) : ℝ)) =ᶠ[atTop]
    (fun x : ℝ => supportScalarPower a x / x) := by
  filter_upwards [eventually_gt_atTop 0] with x hx
  show _ = (if x = 0 then 0 else Real.rpow x a) / x
  rw [if_neg (ne_of_gt hx), Real.rpow_sub_one hx.ne']; rfl

lemma ssp_lt (a : ℝ) (ha : a < 1) :
    DivergenceGenerator (supportScalarPower a) ∧ recessionSlope (supportScalarPower a) = 0 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (a - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 - a) (by linarith)
    simpa using this
  have h2 := ((continuous_coe_real_ereal.tendsto 0).comp (h1.congr' (ssp_ratio a)))
  have := gen_of _ (ssp_cont a) _ h2
  simpa using this

lemma ssp_one :
    DivergenceGenerator (supportScalarPower 1) ∧ recessionSlope (supportScalarPower 1) = 1 := by
  have h1 : Tendsto (fun x : ℝ => x ^ ((1:ℝ) - 1)) atTop (𝓝 1) := by
    simp
  have h2 := ((continuous_coe_real_ereal.tendsto 1).comp (h1.congr' (ssp_ratio 1)))
  have := gen_of _ (ssp_cont 1) _ h2
  simpa using this

lemma ssp_gt (a : ℝ) (ha : 1 < a) :
    DivergenceGenerator (supportScalarPower a) ∧ recessionSlope (supportScalarPower a) = ⊤ := by
  have h1 : Tendsto (fun x : ℝ => x ^ (a - 1)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have h2 := EReal.tendsto_coe_nhds_top_iff.2 (h1.congr' (ssp_ratio a))
  exact gen_of _ (ssp_cont a) _ h2

lemma ssp_gen (a : ℝ) : DivergenceGenerator (supportScalarPower a) := by
  rcases lt_trichotomy a 1 with h | rfl | h
  · exact (ssp_lt a h).1
  · exact ssp_one.1
  · exact (ssp_gt a h).1

lemma xlog_gen : DivergenceGenerator (fun x : ℝ => x * Real.log x) ∧
    recessionSlope (fun x : ℝ => x * Real.log x) = ⊤ := by
  have h1 : (fun x : ℝ => Real.log x) =ᶠ[atTop] (fun x : ℝ => x * Real.log x / x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  have h2 := EReal.tendsto_coe_nhds_top_iff.2 (Real.tendsto_log_atTop.congr' h1)
  exact gen_of _ Real.continuous_mul_log.continuousOn _ h2

theorem supports_of_tr (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : tr (A * (1 - supp B)) ≤ 0) : Supports A B := by
  have hsa : IsSelfAdjoint B := hB.isHermitian
  set Q := 1 - supp B with hQdef
  have hQ : Q = spectralProjector B 0 := by
    rw [hQdef, one_sub_supp B hB.isHermitian, proj_eq_cfc B hB.isHermitian]
  have hQQ : Q * Q = Q := by rw [hQ]; exact proj_idem _ hB.isHermitian 0
  have hQh : Qᴴ = Q := by rw [hQ]; exact proj_herm _ hB.isHermitian 0
  have htr : (A * Q).trace = (Qᴴ * A * Q).trace := by
    rw [hQh]
    calc (A * Q).trace = (A * (Q * Q)).trace := by rw [hQQ]
      _ = (Q * A * Q).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have hpsd := hA.conjTranspose_mul_mul_same Q
  have hnn := hpsd.trace_nonneg
  rw [Complex.nonneg_iff] at hnn
  have h0 : (Qᴴ * A * Q).trace = 0 := by
    apply Complex.ext
    · unfold tr at h; rw [htr] at h; simp only [Complex.zero_re]; linarith [hnn.1]
    · simp only [Complex.zero_im]; exact hnn.2.symm
  have hQAQ : Qᴴ * A * Q = 0 := hpsd.trace_eq_zero_iff.1 h0
  have hs : supp B = cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) B * B := by
    calc supp B = cfc (fun x : ℝ => (if x = 0 then 0 else x⁻¹) * x) B := by
          unfold supp supportPower; congr 1; funext x
          split_ifs with hx
          · simp
          · simp [hx, Real.rpow_eq_pow]
      _ = cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) B * cfc (fun x : ℝ => x) B :=
          (cmul _ _ _).symm
      _ = _ := by rw [cfc_id' ℝ B]
  intro v hv
  have hQv : Q *ᵥ v = v := by
    rw [hQdef, Matrix.sub_mulVec, Matrix.one_mulVec, hs, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero, sub_zero]
  rw [← hA.dotProduct_mulVec_zero_iff]
  calc star v ⬝ᵥ A *ᵥ v = star (Q *ᵥ v) ⬝ᵥ A *ᵥ (Q *ᵥ v) := by rw [hQv]
    _ = star v ⬝ᵥ (Qᴴ * A * Q) *ᵥ v := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
    _ = 0 := by rw [hQAQ]; simp

theorem tr_pos (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) (h : ¬ Supports A B) :
    0 < tr (A * (1 - supp B)) := by
  by_contra h'
  exact h (supports_of_tr A B hA hB (not_lt.1 h'))

lemma add_top_mul (r t : ℝ) (ht : 0 < t) : (r : EReal) + ⊤ * (t : EReal) = ⊤ := by
  rw [EReal.top_mul_coe_of_pos ht]; simp

theorem part5 [Nonempty I] (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div (fun x => x * Real.log x) A B = relativeEntropy A B := by
  have hiff : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported A B ↔ Supports A B :=
    ⟨fun h v hv => h hv, fun h v hv => h v hv⟩
  have hsaA : IsSelfAdjoint A := hA.isHermitian
  have hsaB : IsSelfAdjoint B := hB.isHermitian
  rw [div_eq _ xlog_gen.1 A B hA hB, xlog_gen.2]
  unfold relativeEntropy
  by_cases hs : Supports A B
  · rw [if_pos (hiff.2 hs), tr_zero_of_supports A B hB.isHermitian hs]
    simp only [EReal.coe_zero, mul_zero, add_zero]
    congr 1
    have hz : ∀ a ∈ spec A, a * cc A B a 0 = 0 := by
      have h0 := tr_eq_sum A B hA.isHermitian hB.isHermitian
      rw [tr_zero_of_supports A B hB.isHermitian hs] at h0
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => mul_nonneg (spec_nonneg A hA a ha)
        (cc_nonneg A B hA.isHermitian hB.isHermitian a 0))).1 h0
    have e1 : (cfc (fun x : ℝ => x * Real.log x) A - A * cfc Real.log B).trace.re =
        tr (cfc (fun x : ℝ => x * Real.log x) A * cfc (fun _ : ℝ => (1:ℝ)) B) -
          tr (cfc (fun x : ℝ => x) A * cfc Real.log B) := by
      rw [cfc_const_one ℝ B, cfc_id' ℝ A, Matrix.mul_one]
      unfold tr; rw [Matrix.trace_sub, Complex.sub_re]
    rw [e1, tr_cfc_mul A B hA.isHermitian hB.isHermitian, tr_cfc_mul A B hA.isHermitian
      hB.isHermitian, quasi_formula _ A B hB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hx0 := spec_nonneg A hA x hx
    have hb0 := spec_nonneg B hB b hb
    rcases hb0.eq_or_lt with rfl | hbp
    · have := hz x hx
      simp only [div_zero, Real.log_zero, mul_zero, zero_mul, mul_one, sub_zero]
      calc (0:ℝ) = Real.log x * (x * cc A B x 0) := by rw [this, mul_zero]
        _ = _ := by ring
    rcases hx0.eq_or_lt with rfl | hxp
    · simp
    rw [Real.log_div hxp.ne' hbp.ne']
    field_simp
  · rw [if_neg (fun h => hs (hiff.1 h))]
    exact add_top_mul _ _ (tr_pos A B hA hB hs)

theorem e27_main [Nonempty I] (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∀ a : ℝ, 0 ≤ a →
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal) +
        recessionSlope (supportScalarPower a) * (tr (A * (1 - supp B)) : EReal)) ∧
    (∀ a ∈ Ico (0 : ℝ) 1,
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal)) ∧
    (∀ a : ℝ, 1 < a → div (supportScalarPower a) A B =
      if Supports A B then (tr (supportPower A a * supportPower B (1 - a)) : EReal) else ⊤) ∧
    (∀ a : ℝ, 0 ≤ a → a ≠ 1 →
      petzRenyi a A B = (((a - 1)⁻¹ : ℝ) : EReal) *
        (if div (supportScalarPower a) A B = ⊤ then ⊤ else logNonnegativeExtended (div (supportScalarPower a) A B).toReal)) ∧
    div (fun x => x * Real.log x) A B = relativeEntropy A B := by
  have p1 : ∀ a : ℝ, 0 ≤ a →
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal) +
        recessionSlope (supportScalarPower a) * (tr (A * (1 - supp B)) : EReal) := by
    intro a _
    rw [div_eq _ (ssp_gen a) A B hA hB, quasi_ssp a A B hA hB]
  have p2 : ∀ a ∈ Ico (0 : ℝ) 1,
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal) := by
    rintro a ⟨ha0, ha1⟩
    rw [p1 a ha0, (ssp_lt a ha1).2]; simp
  have p3 : ∀ a : ℝ, 1 < a → div (supportScalarPower a) A B =
      if Supports A B then (tr (supportPower A a * supportPower B (1 - a)) : EReal) else ⊤ := by
    intro a ha
    rw [p1 a (by linarith), (ssp_gt a ha).2]
    split_ifs with hs
    · rw [tr_zero_of_supports A B hB.isHermitian hs]; simp
    · exact add_top_mul _ _ (tr_pos A B hA hB hs)
  refine ⟨p1, p2, p3, ?_, part5 A B hA hB⟩
  intro a ha0 ha1
  unfold petzRenyi
  rcases lt_or_gt_of_ne ha1 with h | h
  · rw [if_pos (Or.inr h), p2 a ⟨ha0, h⟩]; simp [EReal.coe_ne_top]
  · by_cases hs : Supports A B
    · rw [if_pos (Or.inl hs), p3 a h, if_pos hs]; simp [EReal.coe_ne_top]
    · rw [if_neg (by push Not; exact ⟨hs, h.le⟩), p3 a h, if_neg hs, if_pos rfl]
      exact (EReal.coe_mul_top_of_pos (inv_pos.2 (by linarith))).symm

end A3S55E27

end QAlgorithms.Papers.Independent.Support50.P12

open Filter Set
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr logNonnegativeExtended)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Next46.P23 (Supports)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Support50.P12 (supp div recessionSlope supportScalarPower petzRenyi)
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∀ a : ℝ, 0 ≤ a →
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal) +
        recessionSlope (supportScalarPower a) * (tr (A * (1 - supp B)) : EReal)) ∧
    (∀ a ∈ Ico (0 : ℝ) 1,
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal)) ∧
    (∀ a : ℝ, 1 < a → div (supportScalarPower a) A B =
      if Supports A B then (tr (supportPower A a * supportPower B (1 - a)) : EReal) else ⊤) ∧
    (∀ a : ℝ, 0 ≤ a → a ≠ 1 →
      petzRenyi a A B = (((a - 1)⁻¹ : ℝ) : EReal) *
        (if div (supportScalarPower a) A B = ⊤ then ⊤ else logNonnegativeExtended (div (supportScalarPower a) A B).toReal)) ∧
    div (fun x => x * Real.log x) A B = relativeEntropy A B :=
  QAlgorithms.Papers.Independent.Support50.P12.A3S55E27.e27_main A B hA hB


end
