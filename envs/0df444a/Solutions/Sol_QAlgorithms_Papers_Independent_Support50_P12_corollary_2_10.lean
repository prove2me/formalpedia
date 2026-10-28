-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.corollary_2_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:21:36.782986+00:00
-- url     : https://prove2.me/submissions/00895015-c355-41f7-b799-8fac35065c40

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


namespace A3S55C210

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

theorem cor [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f A B = (quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal) ∧
    div f A B = ((f 0 * tr B + quasi (fun x => f x - f 0) A B : ℝ) : EReal) +
      recessionSlope f * (tr (A * (1 - supp B)) : EReal) ∧
    div f A B = ∑ a ∈ spec A,
      (((∑ b ∈ (spec B).filter (fun b => b ≠ 0),
        b * f (a / b) * tr (spectralProjector A a * spectralProjector B b) : ℝ) : EReal) +
        (a : EReal) * recessionSlope f * (tr (spectralProjector A a * spectralProjector B 0) : EReal)) ∧
    (div f A B = (quasi f A B : EReal) ↔ Supports A B ∨ recessionSlope f = 0) := by
  have h1 := div_eq f hf A B hA hB
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h1, ← quasi_split f A B hA.isHermitian hB]
  · rw [h1, expansion3 f A B hA hB]
  · rw [h1]
    constructor
    · intro h
      by_cases hs : Supports A B
      · exact Or.inl hs
      · right
        have ht0 : 0 ≤ tr (A * (1 - supp B)) := by
          rw [← tr_eq_sum A B hA.isHermitian hB.isHermitian]
          exact Finset.sum_nonneg fun a ha => mul_nonneg (spec_nonneg A hA a ha)
            (cc_nonneg A B hA.isHermitian hB.isHermitian a 0)
        have ht : 0 < tr (A * (1 - supp B)) := by
          rcases ht0.eq_or_lt with h0 | h0
          · exact absurd (supports_of_tr_zero A B hA hB.isHermitian h0.symm) hs
          · exact h0
        exact ereal_eq _ _ ht _ h
    · rintro (hs | hω)
      · rw [tr_zero_of_supports A B hB.isHermitian hs]; simp
      · rw [hω]; simp


section diag
variable {α : Type} [Fintype α] [DecidableEq α]

theorem specProj_gen (A M : Mat I) (a : ℝ) (hM : Mᴴ = M) (hMM : M * M = M)
    (hAM : A * M = (a : ℂ) • M) (hker : ∀ w : I → ℂ, A *ᵥ w = (a : ℂ) • w → M *ᵥ w = w) :
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
      apply hker
      have := congrArg WithLp.ofLp hw
      simpa using this
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [← hw']
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_toLp, star_sub, Matrix.star_mulVec, hM, Matrix.sub_vecMul,
      Matrix.vecMul_vecMul, hMM, sub_self, zero_dotProduct]

def dg (p : α → ℝ) : Mat α := Matrix.diagonal (fun i => (p i : ℂ))

def pr (p : α → ℝ) (l : ℝ) : Mat α := Matrix.diagonal (fun i => if p i = l then (1 : ℂ) else 0)

lemma dg_herm (p : α → ℝ) : (dg p).IsHermitian := by
  unfold dg Matrix.IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma dg_psd (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) : (dg p).PosSemidef := by
  unfold dg
  rw [Matrix.posSemidef_diagonal_iff]
  intro i; exact_mod_cast hp i

lemma proj_dg (p : α → ℝ) (l : ℝ) : spectralProjector (dg p) l = pr p l := by
  apply specProj_gen
  · unfold pr; rw [Matrix.diagonal_conjTranspose]; congr 1; funext i; split_ifs <;> simp_all
  · unfold pr; rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp_all
  · unfold pr dg; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1; funext i; split_ifs with h <;> simp [h]
  · intro w hw
    funext i
    have := congrFun hw i
    unfold pr
    unfold dg at this
    rw [Matrix.mulVec_diagonal] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at this
    split_ifs with h
    · simp
    · have h' : ((p i : ℂ) - l) * w i = 0 := by rw [sub_mul, this, sub_self]
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) h
      · simp [h0]

lemma mem_spec_dg (p : α → ℝ) (i : α) : p i ∈ spec (dg p) := by
  by_contra h
  have h0 := proj_zero _ (dg_herm p) _ h
  rw [proj_dg] at h0
  have := congrFun (congrFun h0 i) i
  simp [pr] at this

lemma cc_dg (p q : α → ℝ) (a b : ℝ) :
    cc (dg p) (dg q) a b = ∑ i, (if p i = a then (1 : ℝ) else 0) * (if q i = b then 1 else 0) := by
  unfold cc
  rw [proj_dg, proj_dg, pr, pr, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma pick (s : Finset ℝ) (x : ℝ) (hx : x ∈ s) (F : ℝ → ℝ) :
    ∑ a ∈ s, F a * (if x = a then 1 else 0) = F x := by
  have : ∀ a, F a * (if x = a then (1 : ℝ) else 0) = if x = a then F x else 0 := by
    intro a; split_ifs with h
    · subst h; ring
    · ring
  simp only [this]
  rw [Finset.sum_ite_eq, if_pos hx]

lemma sum1 (p q : α → ℝ) (h : ℝ → ℝ) (b : ℝ) :
    ∑ a ∈ spec (dg p), h a * cc (dg p) (dg q) a b =
      ∑ i, h (p i) * (if q i = b then 1 else 0) := by
  simp only [cc_dg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ a, h a * ((if p i = a then (1 : ℝ) else 0) * (if q i = b then 1 else 0)) =
      (h a * (if q i = b then 1 else 0)) * (if p i = a then 1 else 0) := fun a => by ring
  simp only [this]
  exact pick _ _ (mem_spec_dg p i) (fun a => h a * (if q i = b then 1 else 0))

lemma sum2 (p q : α → ℝ) (g : ℝ → ℝ → ℝ) :
    ∑ a ∈ spec (dg p), ∑ b ∈ spec (dg q), g a b * cc (dg p) (dg q) a b =
      ∑ i, g (p i) (q i) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b _ => sum1 p q (fun a => g a b) b]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pick _ _ (mem_spec_dg q i) (fun b => g (p i) b)

theorem div_dg [Nonempty α] (f : ℝ → ℝ) (hf : DivergenceGenerator f) (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    div f (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
      ((∑ i, (if q i = 0 then 0 else q i * f (p i / q i)) : ℝ) : EReal) +
        recessionSlope f * ((∑ i, (if q i = 0 then p i else 0) : ℝ) : EReal) := by
  change div f (dg p) (dg q) = _
  rw [div_eq f hf _ _ (dg_psd p hp) (dg_psd q hq), quasi_formula f _ _ (dg_psd q hq),
    ← tr_eq_sum _ _ (dg_herm p) (dg_herm q)]
  have h2 := sum2 p q (fun a b => f (a / b) * b)
  have h1 := sum1 p q (fun a => a) 0
  beta_reduce at h1 h2
  rw [h1, h2]
  have e1 : ∑ i, f (p i / q i) * q i = ∑ i, (if q i = 0 then 0 else q i * f (p i / q i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp [h]
    · ring
  have e2 : ∑ i, p i * (if q i = 0 then 1 else 0) = ∑ i, (if q i = 0 then p i else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [e1, e2]

end diag

lemma sum_alpha (X Y : Mat I) (F : ℝ → ℝ → ℝ) :
    ∑ x : SpectralAlphabet X Y, F x.1.1 x.2.1 = ∑ a ∈ spec X, ∑ b ∈ spec Y, F a b := by
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (spec X)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_coe_sort (spec Y)]

lemma spec_ne (X : Mat I) [Nonempty I] (hX : X.IsHermitian) : (spec X).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨hX.eigenvalues i, ?_⟩
  unfold spec; rw [dif_pos hX]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

lemma alpha_ne [Nonempty I] (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Nonempty (SpectralAlphabet X Y) := by
  obtain ⟨a, ha⟩ := spec_ne X hX
  obtain ⟨b, hb⟩ := spec_ne Y hY
  exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

theorem l29 [Nonempty I] (A : Alg I) (rho sigma : Mat I)
    (hr : AlgebraDensity A rho) (hs : AlgebraDensity A sigma) (f : ℝ → ℝ) (hf : DivergenceGenerator f) :
    IsDistribution (law1 rho sigma) ∧ IsDistribution (law2 rho sigma) ∧
    div f rho sigma = div f
      (Matrix.diagonal (fun p => (law1 rho sigma p : ℂ)))
      (Matrix.diagonal (fun p => (law2 rho sigma p : ℂ))) := by
  obtain ⟨_, hρ, hρ1⟩ := hr
  obtain ⟨_, hσ, hσ1⟩ := hs
  have hcc : ∀ a b, tr (spectralProjector rho a * spectralProjector sigma b) = cc rho sigma a b :=
    fun _ _ => rfl
  have h1nn : ∀ x, 0 ≤ law1 rho sigma x := fun x =>
    mul_nonneg (spec_nonneg _ hρ _ x.1.2) (cc_nonneg _ _ hρ.isHermitian hσ.isHermitian _ _)
  have h2nn : ∀ x, 0 ≤ law2 rho sigma x := fun x =>
    mul_nonneg (spec_nonneg _ hσ _ x.2.2) (cc_nonneg _ _ hρ.isHermitian hσ.isHermitian _ _)
  refine ⟨⟨h1nn, ?_⟩, ⟨h2nn, ?_⟩, ?_⟩
  · unfold law1; simp only [hcc]
    rw [sum_alpha rho sigma (fun a b => a * cc rho sigma a b), Finset.sum_comm, ← hρ1,
      tr_B_sum sigma rho hσ.isHermitian hρ.isHermitian]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    unfold cc; rw [Matrix.trace_mul_comm]
  · unfold law2; simp only [hcc]
    rw [sum_alpha rho sigma (fun a b => b * cc rho sigma a b), ← hσ1,
      tr_B_sum rho sigma hρ.isHermitian hσ.isHermitian]
  · haveI := alpha_ne rho sigma hρ.isHermitian hσ.isHermitian
    rw [div_dg f hf _ _ h1nn h2nn, div_eq f hf rho sigma hρ hσ, quasi_formula f _ _ hσ,
      ← tr_eq_sum _ _ hρ.isHermitian hσ.isHermitian]
    unfold law1 law2; simp only [hcc]
    rw [sum_alpha rho sigma (fun a b => if b * cc rho sigma a b = 0 then 0 else
        b * cc rho sigma a b * f (a * cc rho sigma a b / (b * cc rho sigma a b))),
      sum_alpha rho sigma (fun a b => if b * cc rho sigma a b = 0 then a * cc rho sigma a b else 0)]
    have e1 : ∑ a ∈ spec rho, ∑ b ∈ spec sigma, f (a / b) * b * cc rho sigma a b =
        ∑ a ∈ spec rho, ∑ b ∈ spec sigma, (if b * cc rho sigma a b = 0 then 0 else
        b * cc rho sigma a b * f (a * cc rho sigma a b / (b * cc rho sigma a b))) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rcases mul_eq_zero.1 h with h0 | h0 <;> simp [h0]
      · have hc : cc rho sigma a b ≠ 0 := fun h0 => h (by simp [h0])
        rw [mul_div_mul_right _ _ hc]; ring
    have e2 : ∑ a ∈ spec rho, a * cc rho sigma a 0 = ∑ a ∈ spec rho, ∑ b ∈ spec sigma,
        (if b * cc rho sigma a b = 0 then a * cc rho sigma a b else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∀ b ∈ spec sigma, (if b * cc rho sigma a b = 0 then a * cc rho sigma a b else 0) =
          if b = 0 then a * cc rho sigma a b else 0 := by
        intro b _
        by_cases hb : b = 0
        · simp [hb]
        · by_cases hc : cc rho sigma a b = 0
          · simp [hc]
          · simp [hb, hc]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · unfold cc; rw [proj_zero sigma hσ.isHermitian 0 h]; simp
    rw [e1, e2]

lemma reindex {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ} [Nonempty (Fin n)]
    (f : ℝ → ℝ) (hf : DivergenceGenerator f) (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (e : α ≃ Fin n) :
    div f (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
    div f (Matrix.diagonal (fun j => (p (e.symm j) : ℂ)))
      (Matrix.diagonal (fun j => (q (e.symm j) : ℂ))) := by
  rw [div_dg f hf p q hp hq, div_dg f hf (fun j => p (e.symm j)) (fun j => q (e.symm j))
    (fun j => hp _) (fun j => hq _)]
  have s1 := (e.symm.sum_comp (fun i => if q i = 0 then 0 else q i * f (p i / q i)))
  have s2 := (e.symm.sum_comp (fun i => if q i = 0 then p i else 0))
  beta_reduce at s1 s2
  rw [s1, s2]

theorem c210 [Nonempty I] (f g : ℝ → ℝ)
    (hf : DivergenceGenerator f) (hg : DivergenceGenerator g)
    (hc : ∀ (n : ℕ) (p q : Fin n → ℝ), IsDistribution p → IsDistribution q →
      div f (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
      div g (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))))
    (A : Alg I) (rho sigma : Mat I) (hr : AlgebraDensity A rho) (hs : AlgebraDensity A sigma) :
    div f rho sigma = div g rho sigma := by
  obtain ⟨hd1, hd2, hfeq⟩ := l29 A rho sigma hr hs f hf
  obtain ⟨-, -, hgeq⟩ := l29 A rho sigma hr hs g hg
  have := alpha_ne rho sigma hr.2.1.isHermitian hs.2.1.isHermitian
  let e := Fintype.equivFin (SpectralAlphabet rho sigma)
  have : Nonempty (Fin (Fintype.card (SpectralAlphabet rho sigma))) :=
    ⟨e (Classical.arbitrary _)⟩
  rw [hfeq, hgeq, reindex f hf _ _ hd1.1 hd2.1 e, reindex g hg _ _ hd1.1 hd2.1 e]
  exact hc _ (fun j => law1 rho sigma (e.symm j)) (fun j => law2 rho sigma (e.symm j))
    ⟨fun j => hd1.1 _, (e.symm.sum_comp _).trans hd1.2⟩
    ⟨fun j => hd2.1 _, (e.symm.sum_comp _).trans hd2.2⟩

end A3S55C210

end QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr)
open QAlgorithms.Papers.Independent.Next46.P23 (Supports)
open QAlgorithms (spectralProjector)
open QAlgorithms.Learning (IsDistribution)
open QAlgorithms.Papers.Independent.Support50.P12
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (f g : ℝ → ℝ)
    (hf : DivergenceGenerator f) (hg : DivergenceGenerator g)
    (hc : ∀ (n : ℕ) (p q : Fin n → ℝ), IsDistribution p → IsDistribution q →
      div f (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
      div g (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))))
    (A : Alg I) (rho sigma : Mat I) (hr : AlgebraDensity A rho) (hs : AlgebraDensity A sigma) :
    div f rho sigma = div g rho sigma :=
  A3S55C210.c210 f g hf hg hc A rho sigma hr hs

end
