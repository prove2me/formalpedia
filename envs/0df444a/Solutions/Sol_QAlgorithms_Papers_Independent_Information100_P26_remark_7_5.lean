-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.remark_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:44:59.09754+00:00
-- url     : https://prove2.me/submissions/a4cb9f17-6a65-4eb8-bfce-4eabae2553ca

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
noncomputable section
open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set
namespace QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

lemma x8_ap (M : Map d) (X : Mat d) (i j : Fin d) :
    applyMap M X i j = ∑ p : Fin d × Fin d, M (i, j) p * X p.1 p.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma x8_ap_add (M : Map d) (X Y : Mat d) : applyMap M (X + Y) = applyMap M X + applyMap M Y := by
  ext i j; simp [x8_ap, mul_add, Finset.sum_add_distrib]

lemma x8_ap_smul (M : Map d) (c : ℂ) (X : Mat d) : applyMap M (c • X) = c • applyMap M X := by
  ext i j; simp [x8_ap, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

lemma x8_ap_zero (M : Map d) : applyMap M 0 = 0 := by
  ext i j; simp [x8_ap]

lemma x8_ap_sub (M : Map d) (X Y : Mat d) : applyMap M (X - Y) = applyMap M X - applyMap M Y := by
  ext i j; simp [x8_ap, mul_sub, Finset.sum_sub_distrib]

lemma x8_ap_msub (M N : Map d) (X : Mat d) : applyMap (M - N) X = applyMap M X - applyMap N X := by
  ext i j; simp [x8_ap, sub_mul, Finset.sum_sub_distrib]

lemma x8_ap_rsmul (M : Map d) (c : ℝ) (X : Mat d) : applyMap (c • M) X = (c : ℂ) • applyMap M X := by
  ext i j; simp [x8_ap, Finset.mul_sum, Complex.real_smul]; exact Finset.sum_congr rfl fun _ _ => by ring

lemma x8_ap_one (X : Mat d) : applyMap 1 X = X := by
  ext i j; simp [x8_ap, Matrix.one_apply]

lemma x8_ap_mul (M N : Map d) (X : Mat d) : applyMap (M * N) X = applyMap M (applyMap N X) := by
  ext i j; simp only [x8_ap, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma x8_ap_pow (M : Map d) (Y : Mat d) (h : applyMap M Y = 0) (n : ℕ) :
    applyMap (M ^ (n + 1)) Y = 0 := by
  rw [pow_succ, x8_ap_mul, h, x8_ap_zero]

lemma x8_ap_cont (X : Mat d) : Continuous fun M : Map d => applyMap M X := by
  have : (fun M : Map d => applyMap M X) = fun M i j => ∑ p : Fin d × Fin d, M (i, j) p * X p.1 p.2 := by
    funext M i j; exact x8_ap M X i j
  rw [this]
  refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun p _ => ?_
  exact (continuous_id.matrix_elem (i, j) p).mul continuous_const

/-- additive hom `M ↦ applyMap M X` -/
def x8Φ (X : Mat d) : Map d →+ Mat d where
  toFun M := applyMap M X
  map_zero' := by ext i j; simp [x8_ap]
  map_add' M N := by ext i j; simp [x8_ap, add_mul, Finset.sum_add_distrib]

lemma x8_lim (F : ℝ → Map d) (G : Map d) (hF : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds G))
    (X : Mat d) (h : ∀ t : ℝ, 0 < t → applyMap (F t) X = 0) : applyMap G X = 0 := by
  have h1 := ((x8_ap_cont X).tendsto G).comp hF
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h t ht).symm

lemma x8_exp_summable (A : Map d) (t : ℝ) :
    Summable (fun n : ℕ => (t ^ n / (n.factorial : ℝ)) • A ^ n) := by
  have h : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) (t • A)
  refine h.congr fun n => ?_
  rw [smul_pow, smul_smul]; congr 1; field_simp

lemma x8_exp_fix (A : Map d) (t : ℝ) (Y : Mat d) (h : applyMap A Y = 0) :
    applyMap (∑' n : ℕ, (t ^ n / (n.factorial : ℝ)) • A ^ n) Y = Y := by
  have hs := (x8_exp_summable A t).hasSum
  have h2 := hs.map (x8Φ Y) (x8_ap_cont Y)
  refine h2.unique ?_
  have : (⇑(x8Φ Y) ∘ fun n : ℕ => (t ^ n / (n.factorial : ℝ)) • A ^ n) =
      fun n => if n = 0 then Y else 0 := by
    funext n
    simp only [Function.comp, x8Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rcases n with _ | n
    · simp [x8_ap_one]
    · rw [x8_ap_rsmul, x8_ap_pow A Y h]; simp
  rw [this]; exact hasSum_ite_eq 0 Y

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section
open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set
namespace QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

lemma x8_kraus_entry (M : Map d) {m : ℕ} (E : Fin m → Mat d)
    (h : ∀ ρ, applyMap M ρ = QAlgorithms.krausApply E ρ) (i j k l : Fin d) :
    M (i, j) (k, l) = ∑ r, E r i k * conj (E r j l) := by
  have := congrFun (congrFun (h (Matrix.single k l 1)) i) j
  rw [x8_ap] at this
  simp only [Matrix.single_apply] at this
  rw [Finset.sum_eq_single (k, l)] at this
  · simp only [and_self, if_true, mul_one] at this
    rw [this]
    simp [QAlgorithms.krausApply, Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, ite_and,
      ite_mul]
  · intro p _ hp
    rw [if_neg (fun h => hp (Prod.ext h.1.symm h.2.symm)), mul_zero]
  · simp

lemma x8_adj_kraus (M : Map d) {m : ℕ} (E : Fin m → Mat d)
    (h : ∀ ρ, applyMap M ρ = QAlgorithms.krausApply E ρ) (Y : Mat d) :
    applyMap Mᴴ Y = ∑ r, (E r)ᴴ * Y * E r := by
  ext k l
  rw [x8_ap, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply]
  simp only [Matrix.conjTranspose_apply, x8_kraus_entry M E h, Matrix.mul_apply, star_sum,
    star_mul', Finset.sum_mul, RCLike.star_def, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => by ring

lemma x8_adj_one (M : Map d) (hM : QAlgorithms.IsChannel (applyMap M)) : applyMap Mᴴ 1 = 1 := by
  obtain ⟨m, E, hE, h⟩ := hM
  rw [x8_adj_kraus M E h]; simpa [QAlgorithms.IsKrausFamily] using hE

lemma x8_adj_herm (M : Map d) (hM : QAlgorithms.IsChannel (applyMap M)) (Y : Mat d) :
    applyMap Mᴴ Yᴴ = (applyMap Mᴴ Y)ᴴ := by
  obtain ⟨m, E, hE, h⟩ := hM
  rw [x8_adj_kraus M E h, x8_adj_kraus M E h, Matrix.conjTranspose_sum]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable (s : ChannelSemigroup d)

lemma x8_gen_ker (X : Mat d) (h : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t) X = X) :
    applyMap s.generator X = 0 := by
  refine x8_lim _ _ s.derivative X fun t ht => ?_
  rw [x8_ap_rsmul, x8_ap_msub, x8_ap_one, h t ht.le, sub_self, smul_zero]

lemma x8_gen_ker_adj (X : Mat d) (h : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ X = X) :
    applyMap s.generatorᴴ X = 0 := by
  have hT := ((continuous_id.matrix_conjTranspose).tendsto s.generator).comp s.derivative
  refine x8_lim _ _ hT X fun t ht => ?_
  simp only [Function.comp, id, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, star_trivial]
  rw [x8_ap_rsmul, x8_ap_msub, x8_ap_one, h t ht.le, sub_self, smul_zero]

lemma x8_ker_fix (X : Mat d) (h : applyMap s.generator X = 0) (t : ℝ) (ht : 0 ≤ t) :
    applyMap (s.time t) X = X := by
  rw [s.exponential t ht]; exact x8_exp_fix _ t X h

lemma x8_ker_fix_adj (X : Mat d) (h : applyMap s.generatorᴴ X = 0) (t : ℝ) (ht : 0 ≤ t) :
    applyMap (s.time t)ᴴ X = X := by
  rw [s.exponential t ht, Matrix.conjTranspose_tsum]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_pow, star_trivial]
  exact x8_exp_fix _ t X h

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section
open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set
namespace QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

/-- `applyMap M` as a linear map -/
def x8Ψ (M : Map d) : Mat d →ₗ[ℂ] Mat d where
  toFun := applyMap M
  map_add' := x8_ap_add M
  map_smul' := x8_ap_smul M

/-- vectorisation -/
def x8E : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] Mat d :=
  (LinearEquiv.curry ℂ ℂ (Fin d) (Fin d)).trans (Matrix.ofLinearEquiv ℂ)

lemma x8Ψ_eq (M : Map d) : x8Ψ M = (x8E.toLinearMap ∘ₗ M.mulVecLin) ∘ₗ x8E.symm.toLinearMap := by
  apply LinearMap.ext; intro X; ext i j
  simp only [x8Ψ, LinearMap.coe_mk, AddHom.coe_mk, x8_ap, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Matrix.mulVecLin_apply, x8E, LinearEquiv.trans_apply, LinearEquiv.trans_symm]
  simp [Matrix.mulVec, dotProduct, Matrix.ofLinearEquiv]
  rfl

lemma x8_ker_finrank (M : Map d) :
    Module.finrank ℂ (LinearMap.ker (x8Ψ M)) + M.rank = d * d := by
  have h1 : LinearMap.ker (x8Ψ M) = (LinearMap.ker M.mulVecLin).map x8E.toLinearMap := by
    rw [x8Ψ_eq, LinearMap.ker_comp, LinearMap.ker_comp]
    ext X; simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker,
      LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _ x8E.injective]
    constructor
    · intro h; exact ⟨x8E.symm X, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [h1, LinearEquiv.finrank_map_eq, Matrix.rank, add_comm,
    LinearMap.finrank_range_add_finrank_ker]
  simp

lemma x8_ker_adj_finrank (M : Map d) :
    Module.finrank ℂ (LinearMap.ker (x8Ψ Mᴴ)) = Module.finrank ℂ (LinearMap.ker (x8Ψ M)) := by
  have h1 := x8_ker_finrank M
  have h2 := x8_ker_finrank Mᴴ
  rw [Matrix.rank_conjTranspose] at h2
  omega

lemma x8_herm_im (A : Mat d) (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (A j i) = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [this]; ring

lemma x8_pd (H : Mat d) (hH : H.IsHermitian) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ (((d : ℂ)⁻¹) • (1 : Mat d) + (ε : ℂ) • H).PosDef := by
  set B : ℝ := ∑ i, ∑ j, ‖H i j‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  have hBij : ∀ i j, ‖H i j‖ ≤ B := fun i j => by
    have h1 : ‖H i j‖ ≤ ∑ j, ‖H i j‖ :=
      Finset.single_le_sum (f := fun j => ‖H i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, ‖H i j‖ ≤ ∑ i, ∑ j, ‖H i j‖ := Finset.single_le_sum (f := fun i => ∑ j, ‖H i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨1 / (2 * d ^ 2 * B), by positivity, ?_⟩
  set ε : ℝ := 1 / (2 * d ^ 2 * B) with hε
  have hherm : (((d : ℂ)⁻¹) • (1 : Mat d) + (ε : ℂ) • H).IsHermitian := by
    refine Matrix.IsHermitian.add ?_ ?_
    · unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      congr 1; simp [Complex.conj_ofReal]
    · unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, hH.eq]
      congr 1; simp [Complex.conj_ofReal]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  rw [Complex.lt_def]
  refine ⟨?_, (x8_herm_im _ hherm x).symm⟩
  have hsplit : star x ⬝ᵥ ((((d : ℂ)⁻¹) • (1 : Mat d) + (ε : ℂ) • H) *ᵥ x) =
      (d : ℂ)⁻¹ * (star x ⬝ᵥ x) + (ε : ℂ) * (star x ⬝ᵥ (H *ᵥ x)) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hsplit]
  set T : ℝ := ∑ i, ‖x i‖ ^ 2
  have hT : (star x ⬝ᵥ x) = (T : ℂ) := by
    simp only [T, dotProduct, Pi.star_apply, RCLike.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hTpos : 0 < T := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have : 0 < ‖x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hq : ‖star x ⬝ᵥ (H *ᵥ x)‖ ≤ B * d * T := by
    calc ‖star x ⬝ᵥ (H *ᵥ x)‖ ≤ ∑ i, ‖x i‖ * ∑ j, B * ‖x j‖ := by
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_star]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)) (norm_nonneg _)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hBij i j) (norm_nonneg _)
      _ = B * (∑ i, ‖x i‖) ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ B * (d * T) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0.le
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖x i‖)
          simpa [T] using this
      _ = B * d * T := by ring
  have hre : -(B * d * T) ≤ (star x ⬝ᵥ (H *ᵥ x)).re :=
    (neg_le_neg hq).trans' le_rfl |>.trans (by
      have := Complex.abs_re_le_norm (star x ⬝ᵥ (H *ᵥ x)); rw [abs_le] at this; linarith)
  simp only [Complex.zero_re, Complex.add_re, Complex.mul_re, hT, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.inv_re, Complex.natCast_re, Complex.inv_im,
    Complex.natCast_im, Complex.normSq_natCast, zero_div, mul_zero]
  have e1 : ((d : ℝ) / ((d : ℝ) * d)) = 1 / d := by field_simp
  rw [e1]
  have e2 : ε * (B * d * T) = T / (2 * d) := by rw [hε]; field_simp
  have : ε * (star x ⬝ᵥ (H *ᵥ x)).re ≥ -(T / (2 * d)) := by
    rw [← e2]; nlinarith [show 0 < ε by positivity]
  have h3 : T / (2 * d) < 1 / (d : ℝ) * T := by
    rw [one_div_mul_eq_div]; exact div_lt_div_of_pos_left hTpos hdR (by linarith)
  linarith

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section
open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set
namespace QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

lemma x8_mem_ker (M : Map d) (X : Mat d) : X ∈ LinearMap.ker (x8Ψ M) ↔ applyMap M X = 0 := Iff.rfl

lemma x8_scal_finrank (hd : 0 < d) : Module.finrank ℂ (scalars d) = 1 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact finrank_span_singleton one_ne_zero

lemma x8_scal_le (M : Map d) (h : applyMap M 1 = 0) : scalars d ≤ LinearMap.ker (x8Ψ M) := by
  rw [scalars, Submodule.span_le]
  rintro _ rfl; exact h

lemma x8_rho0 (hd : 0 < d) : QAlgorithms.IsDensityMatrix (((d : ℂ)⁻¹) • (1 : Mat d)) ∧
    (((d : ℂ)⁻¹) • (1 : Mat d)).PosDef := by
  obtain ⟨ε, -, hε⟩ := x8_pd (0 : Mat d) Matrix.isHermitian_zero hd
  rw [smul_zero, add_zero] at hε
  refine ⟨⟨hε.posSemidef, ?_⟩, hε⟩
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ this]

theorem x8_main {d : ℕ} (hd : 0 < d) (s : ChannelSemigroup d) :
    SemigroupPrimitive s ↔ {X : Mat d | applyMap s.generator X = 0} = (scalars d : Set (Mat d)) := by
  set L := s.generator
  have hL1 : applyMap L 1 = 0 := x8_gen_ker s 1 fun t ht => (s.channel_time t ht).2
  have hL1' : applyMap Lᴴ 1 = 0 :=
    x8_gen_ker_adj s 1 fun t ht => x8_adj_one _ (s.channel_time t ht).1
  have hK := x8_scal_le L hL1
  have hK' := x8_scal_le Lᴴ hL1'
  have hfr := x8_ker_adj_finrank L
  have h1 := x8_scal_finrank hd
  have hset : {X : Mat d | applyMap L X = 0} = (LinearMap.ker (x8Ψ L) : Set (Mat d)) := rfl
  obtain ⟨hρd, hρp⟩ := x8_rho0 hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hρf : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ (((d : ℂ)⁻¹) • (1 : Mat d)) =
      ((d : ℂ)⁻¹) • (1 : Mat d) := fun t ht => by
    rw [x8_ap_smul, x8_adj_one _ (s.channel_time t ht).1]
  rw [hset]
  constructor
  · intro hprim
    have huniq : ∀ ρ : Mat d, QAlgorithms.IsDensityMatrix ρ → ρ.PosDef →
        (∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ ρ = ρ) → ρ = ((d : ℂ)⁻¹) • (1 : Mat d) :=
      fun ρ h1 h2 h3 => hprim.unique ⟨h1, h2, h3⟩ ⟨hρd, hρp, hρf⟩
    -- fixed Hermitian matrices are scalar
    have hherm : ∀ H : Mat d, H.IsHermitian → (∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ H = H) →
        H ∈ scalars d := by
      intro H hH hfix
      set c : ℂ := H.trace / d
      have hc : star c = c := by
        simp only [c, star_div₀, star_natCast]
        rw [← Matrix.trace_conjTranspose, hH.eq]
      set H0 := H - c • (1 : Mat d)
      have hH0 : H0.IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq, hc]
      have htr : H0.trace = 0 := by
        simp only [H0, c, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
          smul_eq_mul]
        field_simp; ring
      have hfix0 : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ H0 = H0 := fun t ht => by
        rw [x8_ap_sub, x8_ap_smul, hfix t ht, x8_adj_one _ (s.channel_time t ht).1]
      obtain ⟨ε, hε, hpd⟩ := x8_pd H0 hH0 hd
      have e := huniq _ ⟨hpd.posSemidef, by
          rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr, Matrix.trace_one,
            Fintype.card_fin, smul_eq_mul, smul_zero, add_zero, inv_mul_cancel₀ hd0]⟩ hpd
        (fun t ht => by rw [x8_ap_add, x8_ap_smul, x8_ap_smul,
          x8_adj_one _ (s.channel_time t ht).1, hfix0 t ht])
      have e2 : (ε : ℂ) • H0 = 0 := by
        have := congrArg (· - ((d : ℂ)⁻¹) • (1 : Mat d)) e
        simpa using this
      have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have : H0 = 0 := (smul_eq_zero.mp e2).resolve_left hε0
      have hHc : H = c • (1 : Mat d) := sub_eq_zero.mp this
      rw [hHc]; exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    have hK'le : LinearMap.ker (x8Ψ Lᴴ) ≤ scalars d := by
      intro Y hY
      have hfix : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ Y = Y := x8_ker_fix_adj s Y hY
      have hfixh : ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ Yᴴ = Yᴴ := fun t ht => by
        rw [x8_adj_herm _ (s.channel_time t ht).1, hfix t ht]
      have hA : (Y + Yᴴ) ∈ scalars d := hherm _ (by
          unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
            add_comm])
        (fun t ht => by rw [x8_ap_add, hfix t ht, hfixh t ht])
      have hB : (Complex.I • (Y - Yᴴ)) ∈ scalars d := hherm _ (by
          unfold Matrix.IsHermitian
          rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
          simp only [Complex.star_def, Complex.conj_I]
          rw [neg_smul, ← smul_neg, neg_sub])
        (fun t ht => by rw [x8_ap_smul, x8_ap_sub, hfix t ht, hfixh t ht])
      have : Y = (1 / 2 : ℂ) • (Y + Yᴴ) + (-Complex.I / 2) • (Complex.I • (Y - Yᴴ)) := by
        rw [smul_smul]
        have : -Complex.I / 2 * Complex.I = 1 / 2 := by
          rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]; ring
        rw [this, ← smul_add]; rw [show (Y + Yᴴ) + (Y - Yᴴ) = (2 : ℂ) • Y by rw [two_smul]; abel, smul_smul]; norm_num
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hA) (Submodule.smul_mem _ _ hB)
    have hle : Module.finrank ℂ (LinearMap.ker (x8Ψ L)) ≤ Module.finrank ℂ (scalars d) := by
      rw [← hfr]; exact Submodule.finrank_mono hK'le
    exact congrArg (fun S : Submodule ℂ (Mat d) => (S : Set (Mat d)))
      (Submodule.eq_of_le_of_finrank_le hK hle).symm
  · intro hker
    have hK0 : LinearMap.ker (x8Ψ L) = scalars d := SetLike.coe_injective hker
    have hK'0 : LinearMap.ker (x8Ψ Lᴴ) = scalars d :=
      (Submodule.eq_of_le_of_finrank_eq hK' (by rw [hfr, hK0])).symm
    refine ⟨((d : ℂ)⁻¹) • (1 : Mat d), ⟨hρd, hρp, hρf⟩, ?_⟩
    rintro ρ ⟨h1ρ, -, h3ρ⟩
    have hmem : ρ ∈ scalars d := by
      rw [← hK'0]; exact x8_gen_ker_adj s ρ h3ρ
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    have htr := h1ρ.2
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
    have : a = (d : ℂ)⁻¹ := by field_simp; linear_combination htr
    rw [this]

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (s : ChannelSemigroup d) :
    SemigroupPrimitive s ↔ {X : Mat d | applyMap s.generator X = 0} = (scalars d : Set (Mat d)) :=
  x8_main hd s
