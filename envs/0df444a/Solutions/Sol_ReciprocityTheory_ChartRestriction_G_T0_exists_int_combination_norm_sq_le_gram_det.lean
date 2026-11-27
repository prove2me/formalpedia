-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.exists_int_combination_norm_sq_le_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:43.422895+00:00
-- url     : https://prove2.me/submissions/53f66036-6e23-4d14-88a2-c7317996f043

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule Matrix
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (u : Fin N → E) (hu : LinearIndependent ℝ u) :
    ∃ y : Fin N → ℤ, y ≠ 0 ∧ ‖∑ i, y i • u i‖ ^ 2 ≤ N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by
  classical
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range u) with hV
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hu, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range u)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let uV : Fin N → V := fun i => ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
  have huV : LinearIndependent ℝ uV := LinearIndependent.of_comp V.subtype hu
  let vb : Fin N → (Fin N → ℝ) := fun i => (f.repr (uV i)).ofLp
  have hvb : LinearIndependent ℝ vb :=
    huV.map' (f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).toLinearMap
      (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = vb i := fun i => by simp [b]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ u).det = d ^ 2 := by
    have hG : gram ℝ u = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb]
      have e1 : inner ℝ (u i) (u j) = inner ℝ (f.repr (uV i)) (f.repr (uV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [vb, mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  set t : ℝ := |d| ^ ((N : ℝ)⁻¹) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (abs_nonneg _) _
  have htN : t ^ N = |d| := Real.rpow_inv_natCast_pow (abs_nonneg _) (by omega)
  haveI : Countable ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    have hc : ((Submodule.span ℤ (Set.range b)).toAddSubgroup : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    (ZSpan.isAddFundamentalDomain b MeasureTheory.volume)
    (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [ZSpan.volume_fundamentalDomain, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal |d| := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, ← hd, mul_comm])
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp x.2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    apply hx0
    have : ((x : Fin N → ℝ)) = 0 := by rw [← hy]; simp
    exact Subtype.ext this
  have hcoe : (∑ i, y i • u i) = ((∑ i, y i • uV i : V) : E) := by simp [uV]
  have hrepr : (f.repr (∑ i, y i • uV i)).ofLp = (x : Fin N → ℝ) := by
    rw [← hy]
    ext j
    simp [map_sum, hb, vb, Finset.sum_apply]
  have hnorm : ‖∑ i, y i • u i‖ ^ 2 = ∑ j, ((x : Fin N → ℝ) j) ^ 2 := by
    rw [hcoe]
    change ‖(∑ i, y i • uV i : V)‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hrepr]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  calc ∑ j, ((x : Fin N → ℝ) j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs] at this
    _ = N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg d), mul_comm,
          Real.rpow_mul (abs_nonneg d), Real.rpow_natCast, sq_abs]
end ReciprocityTheory.ChartRestriction.G.T0
