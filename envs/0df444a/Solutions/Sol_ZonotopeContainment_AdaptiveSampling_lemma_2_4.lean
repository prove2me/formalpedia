-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:08.164446+00:00
-- url     : https://prove2.me/submissions/e32b6929-5929-4bb7-bc09-7fa9eece188a

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_LocalGaussian
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_update_identities
import Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_5

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace Lemma24Aux

lemma support_eq_sum_abs {d n : ℕ} (v : Fin n → E d) (b : E d) :
    support v b = ∑ i, |inner ℝ b (v i)| := by
  unfold support
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ⟨0, ⟨0, fun _ => by simp, by simp⟩, by simp⟩⟩
    · rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by gcongr with i; exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
  · have hbdd : BddAbove ((fun y => inner ℝ b y) '' zonotope v) := by
      refine ⟨∑ i, |inner ℝ b (v i)|, ?_⟩
      rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      calc
        inner ℝ b (∑ i, t i • v i)
          = ∑ i, t i * inner ℝ b (v i) := by simp [inner_sum, real_inner_smul_right]
        _ ≤ ∑ i, |t i * inner ℝ b (v i)| := Finset.sum_le_sum (fun i _ => le_abs_self _)
        _ = ∑ i, |t i| * |inner ℝ b (v i)| := by simp [abs_mul]
        _ ≤ ∑ i, 1 * |inner ℝ b (v i)| := by gcongr with i; exact ht i
        _ = ∑ i, |inner ℝ b (v i)| := by simp
    let t : Fin n → ℝ := fun i => if 0 ≤ inner ℝ b (v i) then 1 else -1
    have ht : ∀ i, |t i| ≤ 1 := by intro i; dsimp [t]; split_ifs <;> simp
    have hx_mem : (∑ i, t i • v i) ∈ zonotope v := ⟨t, ht, rfl⟩
    have hx_val : inner ℝ b (∑ i, t i • v i) = ∑ i, |inner ℝ b (v i)| := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]
      dsimp [t]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · simp [abs_of_neg (not_le.mp h)]
    rw [← hx_val]
    exact le_csSup hbdd ⟨∑ i, t i • v i, hx_mem, rfl⟩

lemma act_rankOne {d : ℕ} (u x : E d) :
    act (rankOne u) x = (inner ℝ u x) • u := by
  ext k
  simp [act, rankOne, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, mul_assoc, Finset.mul_sum, mul_comm]

lemma inner_weightedMatrix {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) (x : E d) :
    inner ℝ x (act (weightedMatrix v r) x) =
      ∑ i, (r i / ‖v i‖) * (inner ℝ x (v i)) ^ 2 := by
  have hlin : act (weightedMatrix v r) x =
      ∑ i, (r i / ‖v i‖) • act (rankOne (v i)) x := by
    unfold weightedMatrix
    simp [act, map_sum, map_smul]
  rw [hlin, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [act_rankOne, real_inner_smul_right, real_inner_smul_right, real_inner_comm (v i) x]
  ring

lemma q_pos (t : ℝ) : 0 < q t := by
  unfold q
  exact div_pos one_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|))

lemma q_le_one (t : ℝ) : q t ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact (div_le_one hpos).mpr (le_max_left 1 |t|)

lemma q_even (t : ℝ) : q (-t) = q t := by
  unfold q; rw [abs_neg]

lemma abs_mul_q_le_one (t : ℝ) : |t * q t| ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  rw [abs_mul, abs_div, abs_one, abs_of_pos hpos, mul_one_div]
  exact (div_le_one hpos).mpr (le_max_right 1 |t|)

lemma q_continuous : Continuous q := by
  unfold q
  exact continuous_const.div (continuous_const.max continuous_abs)
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |x|)))

-- Pushforward of stdGaussian along an orthonormal basis coordinate map
lemma map_inner_orthonormalBasis {d : ℕ} (B : OrthonormalBasis (Fin d) ℝ (E d)) :
    Measure.map (fun z : E d => fun k : Fin d => inner ℝ z (B k)) (stdGaussian (E d)) =
      Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  set B₀ := stdOrthonormalBasis ℝ (E d)
  have hfin : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin
  let e : Fin (Module.finrank ℝ (E d)) ≃ Fin d := finCongr hfin
  let B' : OrthonormalBasis (Fin (Module.finrank ℝ (E d))) ℝ (E d) := B.reindex e.symm
  let Φ : E d ≃ₗᵢ[ℝ] E d := B₀.repr.trans B'.repr.symm
  have hΦ_std : Measure.map Φ (stdGaussian (E d)) = stdGaussian (E d) := stdGaussian_map Φ
  have hsum_cont : Continuous (fun x : Fin (Module.finrank ℝ (E d)) → ℝ => ∑ i, x i • B₀ i) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)
  have hΨ_cont : Continuous (fun z : E d => fun k : Fin d => inner ℝ z (B k)) :=
    continuous_pi (fun k => continuous_id.inner continuous_const)
  rw [← hΦ_std]
  unfold stdGaussian
  rw [Measure.map_map Φ.continuous.measurable hsum_cont.measurable,
    Measure.map_map hΨ_cont.measurable (Φ.continuous.comp hsum_cont).measurable]
  have hcomp : ((fun z : E d => fun k : Fin d => inner ℝ z (B k)) ∘
      (⇑Φ ∘ fun x : Fin (Module.finrank ℝ (E d)) → ℝ => ∑ i, x i • B₀ i)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) e) := by
    ext x k
    simp only [Function.comp_apply]
    have hΦ_sum : Φ (∑ i, x i • B₀ i) = ∑ i, x i • B (e i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
      congr 1
      simp [Φ, B']
    rw [hΦ_sum, sum_inner]
    have horth := orthonormal_iff_ite.mp B.orthonormal
    have hsum_eq : ∑ i, inner ℝ (x i • B (e i)) (B k) =
        ∑ i, if e i = k then x i else 0 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_left, horth (e i) k]
      split_ifs <;> ring
    rw [hsum_eq]
    have hiff : ∀ i, (e i = k) ↔ (i = e.symm k) := fun i => (Equiv.eq_symm_apply e).symm
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    change x (e.symm k) = Equiv.piCongrLeft (fun _ : Fin d => ℝ) e x k
    conv_rhs => rw [← e.apply_symm_apply k, Equiv.piCongrLeft_apply]
    simp
  rw [hcomp]
  exact (MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin d => gaussianReal 0 1) e).map_eq

lemma map_inner_unit {d : ℕ} (hd : 3 ≤ d) {u₀ : E d} (hu₀ : ‖u₀‖ = 1) :
    Measure.map (fun z : E d => inner ℝ z u₀) (stdGaussian (E d)) = gaussianReal 0 1 := by
  let k₀ : Fin d := ⟨0, by omega⟩
  let s : Set (Fin d) := {k₀}
  let v : Fin d → E d := fun _ => u₀
  have horth : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi0 : i = k₀ := Set.mem_singleton_iff.mp hi
    have hj0 : j = k₀ := Set.mem_singleton_iff.mp hj
    subst hi0; subst hj0
    simp [s, v, hu₀]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) horth
  have hBk₀ : B k₀ = u₀ := hB k₀ (Set.mem_singleton k₀)
  have hΨ_meas : Measurable (fun z : E d => fun k : Fin d => inner ℝ z (B k)) :=
    (continuous_pi (fun k => continuous_id.inner continuous_const)).measurable
  have hcomp : (fun z : E d => inner ℝ z u₀) =
      (fun x : Fin d → ℝ => x k₀) ∘ (fun z : E d => fun k : Fin d => inner ℝ z (B k)) := by
    ext z; simp [hBk₀]
  rw [hcomp, ← Measure.map_map (measurable_pi_apply k₀) hΨ_meas, map_inner_orthonormalBasis B]
  exact (MeasureTheory.measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) k₀).map_eq

lemma map_inner_pair {d : ℕ} (hd : 3 ≤ d) {u₀ e₁ : E d}
    (hu₀ : ‖u₀‖ = 1) (he₁ : ‖e₁‖ = 1) (hue : inner ℝ u₀ e₁ = 0) :
    Measure.map (fun z : E d => (inner ℝ z u₀, inner ℝ z e₁)) (stdGaussian (E d)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let k₀ : Fin d := ⟨0, by omega⟩
  let k₁ : Fin d := ⟨1, by omega⟩
  have hk01 : k₀ ≠ k₁ := by intro h; have := congrArg Fin.val h; norm_num [k₀, k₁] at this
  let s : Set (Fin d) := {k₀, k₁}
  let v : Fin d → E d := fun k => if k = k₀ then u₀ else e₁
  have horth : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Subtype.mk.injEq, Set.domRestrict_apply, v]
    rcases Set.mem_insert_iff.mp hi with rfl | hi1 <;>
      rcases Set.mem_insert_iff.mp hj with rfl | hj1
    · simp [hu₀]
    · have hj_eq : j = k₁ := Set.mem_singleton_iff.mp hj1
      subst hj_eq
      simp [hk01, hk01.symm, hue]
    · have hi_eq : i = k₁ := Set.mem_singleton_iff.mp hi1
      subst hi_eq
      simp [hk01.symm, real_inner_comm u₀ e₁, hue]
    · have hi_eq : i = k₁ := Set.mem_singleton_iff.mp hi1
      have hj_eq : j = k₁ := Set.mem_singleton_iff.mp hj1
      subst hi_eq; subst hj_eq
      simp [hk01.symm, he₁]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) horth
  have hBk₀ : B k₀ = u₀ := by
    have := hB k₀ (Set.mem_insert k₀ {k₁})
    simpa [v] using this
  have hBk₁ : B k₁ = e₁ := by
    have := hB k₁ (Set.mem_insert_of_mem k₀ (Set.mem_singleton k₁))
    simpa [v, hk01.symm] using this
  have hΨ_meas : Measurable (fun z : E d => fun k : Fin d => inner ℝ z (B k)) :=
    (continuous_pi (fun k => continuous_id.inner continuous_const)).measurable
  have hproj_meas : Measurable (fun x : Fin d → ℝ => (x k₀, x k₁)) :=
    (measurable_pi_apply k₀).prodMk (measurable_pi_apply k₁)
  have hcomp : (fun z : E d => (inner ℝ z u₀, inner ℝ z e₁)) =
      (fun x : Fin d → ℝ => (x k₀, x k₁)) ∘
        (fun z : E d => fun k : Fin d => inner ℝ z (B k)) := by
    ext z <;> simp [hBk₀, hBk₁]
  rw [hcomp, ← Measure.map_map hproj_meas hΨ_meas, map_inner_orthonormalBasis B]
  set μ_pi := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  have hind_all : iIndepFun (fun k (x : Fin d → ℝ) => x k) μ_pi :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hind01 : IndepFun (fun x : Fin d → ℝ => x k₀) (fun x : Fin d → ℝ => x k₁) μ_pi :=
    hind_all.indepFun hk01
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply k₀).aemeasurable (measurable_pi_apply k₁).aemeasurable).mp hind01
  have hm0 : Measure.map (fun x : Fin d → ℝ => x k₀) μ_pi = gaussianReal 0 1 :=
    (MeasureTheory.measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) k₀).map_eq
  have hm1 : Measure.map (fun x : Fin d → ℝ => x k₁) μ_pi = gaussianReal 0 1 :=
    (MeasureTheory.measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) k₁).map_eq
  rw [hprod, hm0, hm1]

-- Unified set-integral identity on alignmentEvent for a bounded continuous function g
lemma setIntegral_alignment_unit {d : ℕ} (hd : 3 ≤ d) {C lam : ℝ} {b w : E d}
    (hb : b ≠ 0) (_hw : ‖w‖ = 1)
    {g : ℝ → ℝ} (hg_cont : Continuous g) {Bg : ℝ} (hg_bnd : ∀ s, |g s| ≤ Bg) :
    let u₀ := ‖b‖⁻¹ • b
    let y := inner ℝ u₀ w
    let σ := ‖w - y • u₀‖
    let t := Real.sqrt (Real.log d) / (C * lam)
    (∫ z in alignmentEvent C lam b, g (inner ℝ z w) ∂stdGaussian (E d)) =
      ∫ u in Icc t (t + 1),
        (∫ x : ℝ, g (u * y + σ * x) ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
  intro u₀ y σ t
  have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hu₀ : ‖u₀‖ = 1 := by
    simp [u₀, norm_smul, inv_mul_cancel₀ (ne_of_gt hb_pos)]
  set wperp := w - y • u₀
  have horth_perp : inner ℝ u₀ wperp = 0 := by
    dsimp [wperp, y]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu₀]
    ring
  by_cases hσ0 : σ = 0
  · have hwperp0 : wperp = 0 := norm_eq_zero.mp hσ0
    have hw_eq : w = y • u₀ := sub_eq_zero.mp hwperp0
    have hpre : alignmentEvent C lam b = (fun z : E d => inner ℝ z u₀) ⁻¹' Icc t (t + 1) := by
      ext z; simp [alignmentEvent, u₀, t]
    have hu_meas : AEMeasurable (fun z : E d => inner ℝ z u₀) (stdGaussian (E d)) :=
      (continuous_id.inner continuous_const).measurable.aemeasurable
    have hmap1 := map_inner_unit hd hu₀
    have hlhs : (∫ z in alignmentEvent C lam b, g (inner ℝ z w) ∂stdGaussian (E d)) =
        ∫ z in (fun z : E d => inner ℝ z u₀) ⁻¹' Icc t (t + 1),
          (fun u : ℝ => g (u * y)) (inner ℝ z u₀) ∂stdGaussian (E d) := by
      rw [hpre]
      refine setIntegral_congr_fun (measurableSet_Icc.preimage (continuous_id.inner continuous_const).measurable)
        (fun z _ => ?_)
      dsimp only
      rw [hw_eq, real_inner_smul_right, mul_comm]
    rw [hlhs, ← setIntegral_map measurableSet_Icc
      (f := fun u : ℝ => g (u * y))
      (hg_cont.comp (continuous_id.mul continuous_const)).aestronglyMeasurable hu_meas, hmap1]
    refine setIntegral_congr_fun measurableSet_Icc (fun u _ => ?_)
    simp [hσ0, integral_const, probReal_univ]
  · have hσ_pos : 0 < σ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hσ0)
    let e₁ : E d := σ⁻¹ • wperp
    have he₁ : ‖e₁‖ = 1 := by
      dsimp [e₁]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ_pos)]
      exact inv_mul_cancel₀ (ne_of_gt hσ_pos)
    have hue : inner ℝ u₀ e₁ = 0 := by
      simp [e₁, real_inner_smul_right, horth_perp]
    have hw_decomp : w = y • u₀ + σ • e₁ := by
      dsimp [e₁]
      rw [smul_smul σ σ⁻¹ wperp, mul_inv_cancel₀ (ne_of_gt hσ_pos), one_smul]
      dsimp [wperp]
      abel
    let F2 : E d → ℝ × ℝ := fun z => (inner ℝ z u₀, inner ℝ z e₁)
    have hF2_cont : Continuous F2 :=
      (continuous_id.inner continuous_const).prodMk (continuous_id.inner continuous_const)
    have hmap2 := map_inner_pair hd hu₀ he₁ hue
    have hpre2 : alignmentEvent C lam b = F2 ⁻¹' (Icc t (t + 1) ×ˢ univ) := by
      ext z; simp [alignmentEvent, F2, u₀, t]
    let G2 : ℝ × ℝ → ℝ := fun p => g (p.1 * y + σ * p.2)
    have hG2_cont : Continuous G2 :=
      hg_cont.comp ((continuous_fst.mul continuous_const).add
        (continuous_const.mul continuous_snd))
    have hlhs : (∫ z in alignmentEvent C lam b, g (inner ℝ z w) ∂stdGaussian (E d)) =
        ∫ z in F2 ⁻¹' (Icc t (t + 1) ×ˢ univ), G2 (F2 z) ∂stdGaussian (E d) := by
      rw [hpre2]
      refine setIntegral_congr_fun
        ((measurableSet_Icc.prod MeasurableSet.univ).preimage hF2_cont.measurable)
        (fun z _ => ?_)
      dsimp only [G2, F2]
      congr 1
      rw [hw_decomp, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right]
      ring
    rw [hlhs, ← setIntegral_map (measurableSet_Icc.prod MeasurableSet.univ)
      (f := G2) hG2_cont.aestronglyMeasurable hF2_cont.measurable.aemeasurable, hmap2]
    rw [← Measure.prod_restrict (Icc t (t + 1)) univ, Measure.restrict_univ]
    have hG2_int : Integrable G2
        (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
      refine Integrable.of_bound hG2_cont.aestronglyMeasurable Bg (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs]
      exact hg_bnd _
    exact integral_prod G2 hG2_int

end Lemma24Aux

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ C lam : ℝ, 64 ≤ C → 1 ≤ lam →
    ∀ (v : Fin n → E d), Submodule.span ℝ (Set.range v) = ⊤ →
    ∀ b : E d, b ≠ 0 →
    ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))) ≤
      stdGaussian (E d) (alignmentEvent C lam b) ∧
    0 < conditionalMean C lam v b ∧
    stdGaussian (E d) {z | z ∈ alignmentEvent C lam b ∧ ¬ GoodUpdate C lam v b z} ≤
      stdGaussian (E d) (alignmentEvent C lam b) / 2 := by
  let c₀ : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)
  have hc₀_pos : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀, hc₀_pos, ?_⟩
  intro d n hd C lam hC hlam v hv b hb
  have hd_gt1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlogd_pos : 0 < Real.log d := Real.log_pos hd_gt1
  set L : ℝ := C * lam
  have hL_ge1 : 1 ≤ L := by dsimp [L]; nlinarith
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge1
  set t : ℝ := Real.sqrt (Real.log d) / L
  have ht_pos : 0 < t := div_pos (Real.sqrt_pos.mpr hlogd_pos) hL_pos
  have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set u₀ : E d := ‖b‖⁻¹ • b
  have hu₀ : ‖u₀‖ = 1 := by simp [u₀, norm_smul, inv_mul_cancel₀ (ne_of_gt hb_pos)]
  set Ev := alignmentEvent C lam b
  have hE_pre : Ev = (fun z : E d => inner ℝ z u₀) ⁻¹' Icc t (t + 1) := by
    ext z; simp [Ev, alignmentEvent, u₀, t, L]
  have hE_meas : MeasurableSet Ev := by
    rw [hE_pre]
    exact measurableSet_Icc.preimage (continuous_id.inner continuous_const).measurable
  -- Part 1: Lower bound on P(Ev)
  have hmap_u₀ := Lemma24Aux.map_inner_unit hd hu₀
  have hPE_eq : stdGaussian (E d) Ev = (gaussianReal 0 1) (Icc t (t + 1)) := by
    have hm : Measurable (fun z : E d => inner ℝ z u₀) :=
      (continuous_id.inner continuous_const).measurable
    have h1 := Measure.map_apply hm (measurableSet_Icc (a := t) (b := t + 1)) (μ := stdGaussian (E d))
    rw [hE_pre, ← h1, hmap_u₀]
  have hPE_lb : ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))) ≤
      stdGaussian (E d) Ev := by
    rw [hPE_eq, gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Icc]
    have ht_sq : t ^ 2 = Real.log d / (C ^ 2 * lam ^ 2) := by
      dsimp [t, L]
      rw [div_pow, Real.sq_sqrt (le_of_lt hlogd_pos), mul_pow]
    have hconst_le : ∀ u ∈ Icc t (t + 1),
        ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))) ≤
          gaussianPDF 0 1 u := by
      intro u hu
      unfold gaussianPDF
      apply ENNReal.ofReal_le_ofReal
      unfold gaussianPDFReal
      simp only [sub_zero, NNReal.coe_one, mul_one]
      have hu_ge : 0 ≤ u := le_trans (le_of_lt ht_pos) hu.1
      have hu_le : u ≤ t + 1 := hu.2
      have hsq_le : u ^ 2 ≤ (t + 1) ^ 2 := sq_le_sq' (by linarith) hu_le
      have ht_quad : (t + 1) ^ 2 / 2 ≤ t ^ 2 + 1 := by
        nlinarith [sq_nonneg (t - 1)]
      have hexp_ge : - (t ^ 2 + 1) ≤ - u ^ 2 / 2 := by linarith
      have hexp_eq : -1 + (-Real.log d / (C ^ 2 * lam ^ 2)) = - (t ^ 2 + 1) := by
        rw [ht_sq]; ring
      calc
        c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- (t ^ 2 + 1)) := by
              dsimp [c₀]
              rw [mul_assoc, ← Real.exp_add, hexp_eq]
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- u ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_ge) (by positivity)
    have hlint := setLIntegral_mono (μ := volume) (measurable_gaussianPDF 0 1) hconst_le
    rw [setLIntegral_const, Real.volume_Icc] at hlint
    have hlen : (t + 1) - t = 1 := by ring
    simpa [hlen] using hlint
  have hPE_pos_enn : 0 < stdGaussian (E d) Ev := by
    have hpos_rhs : 0 < ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact lt_of_lt_of_le hpos_rhs hPE_lb
  have hPE_lt_top : stdGaussian (E d) Ev < ⊤ := measure_lt_top (stdGaussian (E d)) Ev
  have hPE_pos : 0 < (stdGaussian (E d) Ev).toReal :=
    ENNReal.toReal_pos (ne_of_gt hPE_pos_enn) (ne_of_lt hPE_lt_top)
  -- Define oriented unit vectors w_i, correlations y_i, and σ_i
  let w_unit : Fin n → E d := fun i =>
    if v i = 0 then u₀
    else (if 0 ≤ inner ℝ b (v i) then (1 : ℝ) else -1) • (‖v i‖⁻¹ • v i)
  have hw_norm : ∀ i, ‖w_unit i‖ = 1 := by
    intro i
    dsimp [w_unit]
    split_ifs with hv0 hsign
    · exact hu₀
    · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let y : Fin n → ℝ := fun i => inner ℝ u₀ (w_unit i)
  have hy_val : ∀ i, v i ≠ 0 → y i = |inner ℝ b (v i)| / (‖b‖ * ‖v i‖) := by
    intro i hvi
    dsimp [y, u₀, w_unit]
    rw [if_neg hvi]
    split_ifs with hsign
    · rw [one_smul, real_inner_smul_left, real_inner_smul_right, abs_of_nonneg hsign]
      ring
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        abs_of_neg (not_le.mp hsign)]
      ring
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    by_cases hvi : v i = 0
    · dsimp [y, w_unit]; rw [if_pos hvi, real_inner_self_eq_norm_sq, hu₀]; norm_num
    · rw [hy_val i hvi]; positivity
  let σ : Fin n → ℝ := fun i => ‖w_unit i - y i • u₀‖
  have hσ_nonneg : ∀ i, 0 ≤ σ i := fun i => norm_nonneg _
  have hσ_le1 : ∀ i, σ i ≤ 1 := by
    intro i
    have hsq : (σ i) ^ 2 = 1 - (y i) ^ 2 := by
      dsimp [σ, y]
      rw [norm_sub_sq_real, hw_norm i, norm_smul, Real.norm_eq_abs, hu₀, mul_one,
        real_inner_smul_right, real_inner_comm (w_unit i) u₀, sq_abs]
      ring
    nlinarith [sq_nonneg (y i), norm_nonneg (w_unit i - y i • u₀)]
  -- Pointwise algebraic identities relating v i to w_unit i
  have hweights_eq : ∀ (z : E d) (i : Fin n), v i ≠ 0 →
      weights C lam v z i = q (inner ℝ z (w_unit i) / L) := by
    intro z i hvi
    unfold weights projections
    dsimp [w_unit, L]
    rw [if_neg hvi]
    split_ifs with hsign
    · rw [one_smul, real_inner_smul_right]
      congr 1; field_simp [norm_ne_zero_iff.mpr hvi]
    · rw [real_inner_smul_right, real_inner_smul_right]
      have hneg : (-1 * (‖v i‖⁻¹ * inner ℝ z (v i))) / (C * lam) =
          - (inner ℝ z (v i) / (C * lam * ‖v i‖)) := by
        field_simp [norm_ne_zero_iff.mpr hvi]
      rw [hneg, Lemma24Aux.q_even]
  have hloc_term : ∀ (z : E d) (i : Fin n),
      projections C lam v z i * weights C lam v z i * inner ℝ b (v i) =
      |inner ℝ b (v i)| * ((inner ℝ z (w_unit i) / L) * q (inner ℝ z (w_unit i) / L)) := by
    intro z i
    by_cases hvi : v i = 0
    · simp [hvi, projections]
    · rw [hweights_eq z i hvi]
      unfold projections
      dsimp [w_unit, L]
      rw [if_neg hvi]
      have hnv : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hvi
      have hL_ne : C * lam ≠ 0 := ne_of_gt hL_pos
      split_ifs with hsign
      · rw [one_smul, real_inner_smul_right, abs_of_nonneg hsign]
        field_simp [hnv, hL_ne]
      · rw [real_inner_smul_right, real_inner_smul_right, abs_of_neg (not_le.mp hsign)]
        field_simp [hnv, hL_ne]
  -- Three bounded continuous functions g₁, g₂, g₃
  let g₁ : ℝ → ℝ := fun s => (s / L) * q (s / L)
  let g₂ : ℝ → ℝ := fun s => q (s / L)
  let g₃ : ℝ → ℝ := fun s => 1 - q (s / L)
  have hg₁_cont : Continuous g₁ :=
    (continuous_id.div_const L).mul (Lemma24Aux.q_continuous.comp (continuous_id.div_const L))
  have hg₂_cont : Continuous g₂ := Lemma24Aux.q_continuous.comp (continuous_id.div_const L)
  have hg₃_cont : Continuous g₃ := continuous_const.sub hg₂_cont
  have hg₁_bnd : ∀ s, |g₁ s| ≤ 1 := fun s => Lemma24Aux.abs_mul_q_le_one (s / L)
  have hg₂_bnd : ∀ s, |g₂ s| ≤ 1 := fun s => by
    rw [abs_of_pos (Lemma24Aux.q_pos _)]; exact Lemma24Aux.q_le_one _
  have hg₃_bnd : ∀ s, |g₃ s| ≤ 1 := fun s => by
    have hpos := Lemma24Aux.q_pos (s / L)
    have hle := Lemma24Aux.q_le_one (s / L)
    rw [abs_of_nonneg (by linarith)]; linarith
  -- Set-integral evaluation for each i
  let I₁ : Fin n → ℝ := fun i =>
    ∫ u in Icc t (t + 1),
      (∫ x : ℝ, (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1
  let I₂ : Fin n → ℝ := fun i =>
    ∫ u in Icc t (t + 1),
      (∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) ∂gaussianReal 0 1
  let I₃ : Fin n → ℝ := fun i =>
    ∫ u in Icc t (t + 1),
      (∫ x : ℝ, 1 - q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) ∂gaussianReal 0 1
  have h_int_loc : (∫ z in Ev, inner ℝ b (localPoint C lam v z) ∂stdGaussian (E d)) =
      ∑ i, (|inner ℝ b (v i)| / L) * I₁ i := by
    have hpwise : ∀ z : E d, inner ℝ b (localPoint C lam v z) =
        ∑ i, |inner ℝ b (v i)| * g₁ (inner ℝ z (w_unit i)) := by
      intro z
      unfold localPoint
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right, hloc_term z i]
    have hint_each : ∀ i : Fin n, IntegrableOn
        (fun z : E d => |inner ℝ b (v i)| * g₁ (inner ℝ z (w_unit i))) Ev (stdGaussian (E d)) := by
      intro i
      refine (Integrable.of_bound
        ((continuous_const.mul (hg₁_cont.comp (continuous_id.inner continuous_const))) |>.aestronglyMeasurable)
        (|inner ℝ b (v i)|) (ae_of_all _ fun z => ?_)).integrableOn
      simp only [Pi.mul_apply, Function.comp_apply, id_eq, Real.norm_eq_abs]
      rw [abs_mul, abs_abs]
      calc
        |inner ℝ b (v i)| * |g₁ (inner ℝ z (w_unit i))| ≤ |inner ℝ b (v i)| * 1 :=
          mul_le_mul_of_nonneg_left (hg₁_bnd _) (abs_nonneg _)
        _ = |inner ℝ b (v i)| := mul_one _
    rw [setIntegral_congr_fun hE_meas (fun z _ => hpwise z),
      integral_finsetSum Finset.univ (fun i _ => hint_each i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul,
      Lemma24Aux.setIntegral_alignment_unit hd hb (hw_norm i) hg₁_cont hg₁_bnd]
    have hpull : (∫ u in Icc t (t + 1),
        (∫ x : ℝ, g₁ (u * y i + σ i * x) ∂gaussianReal 0 1) ∂gaussianReal 0 1) =
        (1 / L) * I₁ i := by
      dsimp [I₁, g₁]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc (fun u _ => ?_)
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
    rw [hpull]
    ring
  -- Part 2: Prove 0 < μ
  have hex_i : ∃ i₀, inner ℝ b (v i₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have horth : ∀ x ∈ Submodule.span ℝ (Set.range v), inner ℝ b x = 0 := by
      intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩; exact hall i
      · simp
      · intro x₁ x₂ _ _ h₁ h₂; rw [inner_add_right, h₁, h₂, add_zero]
      · intro c x₁ _ h₁; rw [real_inner_smul_right, h₁, mul_zero]
    exact hb (inner_self_eq_zero.mp (horth b (hv ▸ Submodule.mem_top)))
  obtain ⟨i₀, hi₀⟩ := hex_i
  have hvi₀ : v i₀ ≠ 0 := fun h0 => hi₀ (by simp [h0])
  have hyi₀_pos : 0 < y i₀ := by
    rw [hy_val i₀ hvi₀]
    exact div_pos (abs_pos.mpr hi₀) (mul_pos hb_pos (norm_pos_iff.mpr hvi₀))
  -- Inner expectation bounds from Lemma 2.5 for every u ∈ [t, t + 1]
  have hinner_Yq_nn : ∀ (i : Fin n) (u : ℝ), u ∈ Icc t (t + 1) →
      0 ≤ ∫ x : ℝ, (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1 := by
    intro i u hu
    have hu_nn : 0 ≤ u := le_trans (le_of_lt ht_pos) hu.1
    have hm_nn : 0 ≤ u * y i := mul_nonneg hu_nn (hy_nonneg i)
    have h25 := (lemma_2_5 (u * y i) (σ i) L hm_nn (hσ_nonneg i) (hσ_le1 i) hL_ge1).1
    have hq_nn : 0 ≤ ∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1 :=
      integral_nonneg (fun _ => le_of_lt (Lemma24Aux.q_pos _))
    have hlhs_nn : 0 ≤ (u * y i) * ∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1 :=
      mul_nonneg hm_nn hq_nn
    linarith
  have hI₁_nn : ∀ i, 0 ≤ I₁ i := fun i =>
    setIntegral_nonneg measurableSet_Icc (fun u hu => hinner_Yq_nn i u hu)
  have hI₁_i₀_pos : 0 < I₁ i₀ := by
    set δ₀ : ℝ := min 1 (t * y i₀ / 4)
    have hδ₀_pos : 0 < δ₀ := lt_min zero_lt_one (by positivity)
    have hlb : ∀ u ∈ Icc t (t + 1),
        δ₀ ≤ ∫ x : ℝ, (u * y i₀ + σ i₀ * x) * q ((u * y i₀ + σ i₀ * x) / L) ∂gaussianReal 0 1 := by
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le ht_pos hu.1
      have hm_nn : 0 ≤ u * y i₀ := le_of_lt (mul_pos hu_pos hyi₀_pos)
      obtain ⟨h25_1, h25_2⟩ := lemma_2_5 (u * y i₀) (σ i₀) L hm_nn
        (hσ_nonneg i₀) (hσ_le1 i₀) hL_ge1
      set EY := ∫ x : ℝ, (u * y i₀ + σ i₀ * x) * q ((u * y i₀ + σ i₀ * x) / L) ∂gaussianReal 0 1
      set Eq := ∫ x : ℝ, q ((u * y i₀ + σ i₀ * x) / L) ∂gaussianReal 0 1
      have hq_int : Integrable (fun x : ℝ => q ((u * y i₀ + σ i₀ * x) / L)) (gaussianReal 0 1) := by
        refine Integrable.of_bound
          ((Lemma24Aux.q_continuous.comp
            ((continuous_const.add (continuous_const.mul continuous_id)).div_const L)) |>.aestronglyMeasurable)
          1 (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Lemma24Aux.q_pos _)]
        exact Lemma24Aux.q_le_one _
      have h1mq : (∫ x : ℝ, 1 - q ((u * y i₀ + σ i₀ * x) / L) ∂gaussianReal 0 1) = 1 - Eq := by
        rw [integral_sub (integrable_const 1) hq_int, integral_const]
        simp [probReal_univ, Eq]
      rw [h1mq] at h25_2
      by_cases hEY1 : 1 ≤ EY
      · exact le_trans (min_le_left 1 _) hEY1
      · have hEY_lt1 : EY < 1 := not_le.mp hEY1
        have hEY_nn : 0 ≤ EY := hinner_Yq_nn i₀ u hu
        have hL64 : 64 ≤ L := by dsimp [L]; nlinarith
        have hdiv : (1 + EY) / L ≤ 2 / 64 := by
          calc
            (1 + EY) / L ≤ 2 / L := div_le_div_of_nonneg_right (by linarith) (le_of_lt hL_pos)
            _ ≤ 2 / 64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL64
        have hEq_ge : (1 : ℝ) / 2 ≤ Eq := by linarith
        have huy_ge : t * y i₀ ≤ u * y i₀ :=
          mul_le_mul_of_nonneg_right hu.1 (le_of_lt hyi₀_pos)
        have hEY_ge : t * y i₀ / 4 ≤ EY := by
          have : (t * y i₀) * (1 / 2) ≤ (u * y i₀) * Eq :=
            mul_le_mul huy_ge hEq_ge (by norm_num) hm_nn
          linarith
        exact le_trans (min_le_right 1 _) hEY_ge
    have hint_EY : IntegrableOn
        (fun u : ℝ =>
          ∫ x : ℝ, (u * y i₀ + σ i₀ * x) * q ((u * y i₀ + σ i₀ * x) / L) ∂gaussianReal 0 1)
        (Icc t (t + 1)) (gaussianReal 0 1) := by
      -- Notice I₁ i₀ = (L / |inner ℝ b (v i₀)|) * ∫ z in Ev, ... or directly Integrable.of_bound!
      have hG2_cont : Continuous (fun p : ℝ × ℝ =>
          (p.1 * y i₀ + σ i₀ * p.2) * q ((p.1 * y i₀ + σ i₀ * p.2) / L)) := by
        have hlin : Continuous (fun p : ℝ × ℝ => p.1 * y i₀ + σ i₀ * p.2) :=
          (continuous_fst.mul continuous_const).add (continuous_const.mul continuous_snd)
        exact hlin.mul (Lemma24Aux.q_continuous.comp (hlin.div_const L))
      have hG2_int : Integrable (fun p : ℝ × ℝ =>
          (p.1 * y i₀ + σ i₀ * p.2) * q ((p.1 * y i₀ + σ i₀ * p.2) / L))
          (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
        refine Integrable.of_bound hG2_cont.aestronglyMeasurable L (ae_of_all _ fun p => ?_)
        rw [Real.norm_eq_abs]
        have h1 := Lemma24Aux.abs_mul_q_le_one ((p.1 * y i₀ + σ i₀ * p.2) / L)
        have h2 : (p.1 * y i₀ + σ i₀ * p.2) * q ((p.1 * y i₀ + σ i₀ * p.2) / L) =
            L * (((p.1 * y i₀ + σ i₀ * p.2) / L) * q ((p.1 * y i₀ + σ i₀ * p.2) / L)) := by
          field_simp [ne_of_gt hL_pos]
        rw [h2, abs_mul, abs_of_pos hL_pos]
        calc
          L * |((p.1 * y i₀ + σ i₀ * p.2) / L) * q ((p.1 * y i₀ + σ i₀ * p.2) / L)| ≤ L * 1 :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
          _ = L := mul_one L
      exact hG2_int.integral_prod_left
    have hconst_int : IntegrableOn (fun _ : ℝ => δ₀) (Icc t (t + 1)) (gaussianReal 0 1) :=
      integrableOn_const (measure_ne_top _ _)
    have hmono := setIntegral_mono_on hconst_int hint_EY measurableSet_Icc hlb
    rw [setIntegral_const, smul_eq_mul] at hmono
    have hmeas_Icc : (gaussianReal 0 1).real (Icc t (t + 1)) = (stdGaussian (E d) Ev).toReal := by
      simp [Measure.real, hPE_eq]
    rw [hmeas_Icc] at hmono
    exact lt_of_lt_of_le (mul_pos hPE_pos hδ₀_pos) hmono
  set μ := conditionalMean C lam v b
  have hμ_eq : μ = (stdGaussian (E d) Ev).toReal⁻¹ *
      ∑ i, (|inner ℝ b (v i)| / L) * I₁ i := by
    unfold μ conditionalMean
    rw [h_int_loc]
  have hμ_pos : 0 < μ := by
    rw [hμ_eq]
    apply mul_pos (inv_pos.mpr hPE_pos)
    refine Finset.sum_pos'
      (fun i _ => mul_nonneg (div_nonneg (abs_nonneg _) (le_of_lt hL_pos)) (hI₁_nn i))
      ⟨i₀, Finset.mem_univ i₀,
        mul_pos (div_pos (abs_pos.mpr hi₀) hL_pos) hI₁_i₀_pos⟩
  -- Part 3: Conditional expectation bounds for X₁(z) = ‖bplus(z)‖^2 and X₂(z) = H - H^+(z)
  let X₁ : E d → ℝ := fun z =>
    ‖act (CFC.sqrt (weightedMatrix v (weights C lam v z))) b‖ ^ 2
  let X₂ : E d → ℝ := fun z =>
    support v b - support (updatedGenerators v (weights C lam v z))
      (act (CFC.sqrt (weightedMatrix v (weights C lam v z))) b)
  have hhr : ∀ (z : E d) (i : Fin n), 0 < weights C lam v z i ∧ weights C lam v z i ≤ 1 :=
    fun z i => ⟨Lemma24Aux.q_pos _, Lemma24Aux.q_le_one _⟩
  have hX₁_eq : ∀ z : E d, X₁ z =
      ∑ i, (‖b‖ * |inner ℝ b (v i)| * y i) * g₂ (inner ℝ z (w_unit i)) := by
    intro z
    have hid := (update_identities d n v hv (weights C lam v z) (hhr z) b).1
    dsimp [X₁]
    rw [hid, Lemma24Aux.inner_weightedMatrix]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hvi : v i = 0
    · simp [hvi]
    · rw [hweights_eq z i hvi, hy_val i hvi]
      dsimp [g₂]
      have hnv : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hvi
      have hnb : ‖b‖ ≠ 0 := ne_of_gt hb_pos
      have hsq : |inner ℝ b (v i)| * |inner ℝ b (v i)| = (inner ℝ b (v i)) ^ 2 := by
        rw [← sq, sq_abs]
      calc
        q (inner ℝ z (w_unit i) / L) / ‖v i‖ * (inner ℝ b (v i)) ^ 2
          = ((|inner ℝ b (v i)| * |inner ℝ b (v i)|) / ‖v i‖) *
              q (inner ℝ z (w_unit i) / L) := by rw [hsq]; ring
        _ = (‖b‖ * |inner ℝ b (v i)| * (|inner ℝ b (v i)| / (‖b‖ * ‖v i‖))) *
              q (inner ℝ z (w_unit i) / L) := by field_simp [hnv, hnb]
  have hX₂_eq : ∀ z : E d, X₂ z =
      ∑ i, |inner ℝ b (v i)| * g₃ (inner ℝ z (w_unit i)) := by
    intro z
    have hid := (update_identities d n v hv (weights C lam v z) (hhr z) b).2
    dsimp [X₂]
    rw [hid]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hvi : v i = 0
    · simp [hvi]
    · rw [hweights_eq z i hvi]
      dsimp [g₃]
      ring
  have hX₁_cont : Continuous X₁ := by
    have : X₁ = fun z => ∑ i, (‖b‖ * |inner ℝ b (v i)| * y i) * g₂ (inner ℝ z (w_unit i)) :=
      funext hX₁_eq
    rw [this]
    exact continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (hg₂_cont.comp (continuous_id.inner continuous_const)))
  have hX₂_cont : Continuous X₂ := by
    have : X₂ = fun z => ∑ i, |inner ℝ b (v i)| * g₃ (inner ℝ z (w_unit i)) := funext hX₂_eq
    rw [this]
    exact continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (hg₃_cont.comp (continuous_id.inner continuous_const)))
  have hX₁_nn : ∀ z : E d, 0 ≤ X₁ z := fun z => sq_nonneg _
  have hX₂_nn : ∀ z : E d, 0 ≤ X₂ z := by
    intro z
    rw [hX₂_eq z]
    refine Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) ?_)
    dsimp [g₃]
    linarith [Lemma24Aux.q_le_one (inner ℝ z (w_unit i) / L)]
  have hX₁_int_each : ∀ i : Fin n, IntegrableOn
      (fun z : E d => (‖b‖ * |inner ℝ b (v i)| * y i) * g₂ (inner ℝ z (w_unit i)))
      Ev (stdGaussian (E d)) := by
    intro i
    set Ci := ‖b‖ * |inner ℝ b (v i)| * y i
    have hCi_nn : 0 ≤ Ci := mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (hy_nonneg i)
    refine (Integrable.of_bound
      ((continuous_const.mul (hg₂_cont.comp (continuous_id.inner continuous_const))) |>.aestronglyMeasurable)
      Ci (ae_of_all _ fun z => ?_)).integrableOn
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg hCi_nn]
    calc
      Ci * |g₂ (inner ℝ z (w_unit i))| ≤ Ci * 1 :=
        mul_le_mul_of_nonneg_left (hg₂_bnd _) hCi_nn
      _ = Ci := mul_one _
  have hX₂_int_each : ∀ i : Fin n, IntegrableOn
      (fun z : E d => |inner ℝ b (v i)| * g₃ (inner ℝ z (w_unit i))) Ev (stdGaussian (E d)) := by
    intro i
    refine (Integrable.of_bound
      ((continuous_const.mul (hg₃_cont.comp (continuous_id.inner continuous_const))) |>.aestronglyMeasurable)
      (|inner ℝ b (v i)|) (ae_of_all _ fun z => ?_)).integrableOn
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, Real.norm_eq_abs]
    rw [abs_mul, abs_abs]
    calc
      |inner ℝ b (v i)| * |g₃ (inner ℝ z (w_unit i))| ≤ |inner ℝ b (v i)| * 1 :=
        mul_le_mul_of_nonneg_left (hg₃_bnd _) (abs_nonneg _)
      _ = |inner ℝ b (v i)| := mul_one _
  have hX₁_int : IntegrableOn X₁ Ev (stdGaussian (E d)) := by
    have : X₁ = fun z => ∑ i, (‖b‖ * |inner ℝ b (v i)| * y i) * g₂ (inner ℝ z (w_unit i)) :=
      funext hX₁_eq
    rw [this]
    exact integrable_finsetSum Finset.univ (fun i _ => hX₁_int_each i)
  have hX₂_int : IntegrableOn X₂ Ev (stdGaussian (E d)) := by
    have : X₂ = fun z => ∑ i, |inner ℝ b (v i)| * g₃ (inner ℝ z (w_unit i)) := funext hX₂_eq
    rw [this]
    exact integrable_finsetSum Finset.univ (fun i _ => hX₂_int_each i)
  -- Bound I₂ i and I₃ i via Lemma 2.5
  have hI₂_bound : ∀ i : Fin n, y i * I₂ i ≤ (2 / t) * I₁ i := by
    intro i
    dsimp [I₂, I₁]
    rw [← integral_const_mul, ← integral_const_mul]
    have hpwise_u : ∀ u ∈ Icc t (t + 1),
        y i * (∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) ≤
        (2 / t) * (∫ x : ℝ, (u * y i + σ i * x) * q ((u * y i + σ i * x) / L)
          ∂gaussianReal 0 1) := by
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le ht_pos hu.1
      have hm_nn : 0 ≤ u * y i := mul_nonneg (le_of_lt hu_pos) (hy_nonneg i)
      have h25 := (lemma_2_5 (u * y i) (σ i) L hm_nn (hσ_nonneg i) (hσ_le1 i) hL_ge1).1
      set EY := ∫ x : ℝ, (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1
      set Eq := ∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1
      have hEY_nn : 0 ≤ EY := hinner_Yq_nn i u hu
      have hdiv_u : y i * Eq ≤ (2 / u) * EY := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hu_pos]
        linarith
      have h2u_le : (2 / u) * EY ≤ (2 / t) * EY := by
        apply mul_le_mul_of_nonneg_right _ hEY_nn
        exact div_le_div_of_nonneg_left (by norm_num) ht_pos hu.1
      exact le_trans hdiv_u h2u_le
    -- Integrability of both functions of u on Icc t (t + 1)
    have hint_u2 : IntegrableOn
        (fun u : ℝ => y i * ∫ x : ℝ, q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1)
        (Icc t (t + 1)) (gaussianReal 0 1) := by
      have hG_cont : Continuous (fun p : ℝ × ℝ => q ((p.1 * y i + σ i * p.2) / L)) :=
        Lemma24Aux.q_continuous.comp
          (((continuous_fst.mul continuous_const).add
            (continuous_const.mul continuous_snd)).div_const L)
      have hG_int : Integrable (fun p : ℝ × ℝ => q ((p.1 * y i + σ i * p.2) / L))
          (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
        refine Integrable.of_bound hG_cont.aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Lemma24Aux.q_pos _)]
        exact Lemma24Aux.q_le_one _
      exact hG_int.integral_prod_left.const_mul (y i)
    have hint_u1 : IntegrableOn
        (fun u : ℝ => (2 / t) * ∫ x : ℝ,
          (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1)
        (Icc t (t + 1)) (gaussianReal 0 1) := by
      have hG_cont : Continuous (fun p : ℝ × ℝ =>
          (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L)) := by
        have hlin : Continuous (fun p : ℝ × ℝ => p.1 * y i + σ i * p.2) :=
          (continuous_fst.mul continuous_const).add (continuous_const.mul continuous_snd)
        exact hlin.mul (Lemma24Aux.q_continuous.comp (hlin.div_const L))
      have hG_int : Integrable (fun p : ℝ × ℝ =>
          (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L))
          (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
        refine Integrable.of_bound hG_cont.aestronglyMeasurable L (ae_of_all _ fun p => ?_)
        rw [Real.norm_eq_abs]
        have h1 := Lemma24Aux.abs_mul_q_le_one ((p.1 * y i + σ i * p.2) / L)
        have h2 : (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L) =
            L * (((p.1 * y i + σ i * p.2) / L) * q ((p.1 * y i + σ i * p.2) / L)) := by
          field_simp [ne_of_gt hL_pos]
        rw [h2, abs_mul, abs_of_pos hL_pos]
        calc
          L * |((p.1 * y i + σ i * p.2) / L) * q ((p.1 * y i + σ i * p.2) / L)| ≤ L * 1 :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
          _ = L := mul_one L
      exact hG_int.integral_prod_left.const_mul (2 / t)
    exact setIntegral_mono_on hint_u2 hint_u1 measurableSet_Icc hpwise_u
  have hI₃_bound : ∀ i : Fin n, I₃ i ≤ ((stdGaussian (E d) Ev).toReal + I₁ i) / L := by
    intro i
    dsimp [I₃, I₁]
    have hpwise_u : ∀ u ∈ Icc t (t + 1),
        (∫ x : ℝ, 1 - q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) ≤
        (1 + ∫ x : ℝ, (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) / L := by
      intro u hu
      have hm_nn : 0 ≤ u * y i := mul_nonneg (le_trans (le_of_lt ht_pos) hu.1) (hy_nonneg i)
      exact (lemma_2_5 (u * y i) (σ i) L hm_nn (hσ_nonneg i) (hσ_le1 i) hL_ge1).2
    have hint_u3 : IntegrableOn
        (fun u : ℝ => ∫ x : ℝ, 1 - q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1)
        (Icc t (t + 1)) (gaussianReal 0 1) := by
      have hG_cont : Continuous (fun p : ℝ × ℝ => 1 - q ((p.1 * y i + σ i * p.2) / L)) :=
        continuous_const.sub (Lemma24Aux.q_continuous.comp
          (((continuous_fst.mul continuous_const).add
            (continuous_const.mul continuous_snd)).div_const L))
      have hG_int : Integrable (fun p : ℝ × ℝ => 1 - q ((p.1 * y i + σ i * p.2) / L))
          (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
        refine Integrable.of_bound hG_cont.aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
        rw [Real.norm_eq_abs]
        exact hg₃_bnd _
      exact hG_int.integral_prod_left
    have hint_EY_i : IntegrableOn
        (fun u : ℝ => ∫ x : ℝ,
          (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1)
        (Icc t (t + 1)) (gaussianReal 0 1) := by
      have hG_cont : Continuous (fun p : ℝ × ℝ =>
          (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L)) := by
        have hlin : Continuous (fun p : ℝ × ℝ => p.1 * y i + σ i * p.2) :=
          (continuous_fst.mul continuous_const).add (continuous_const.mul continuous_snd)
        exact hlin.mul (Lemma24Aux.q_continuous.comp (hlin.div_const L))
      have hG_int : Integrable (fun p : ℝ × ℝ =>
          (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L))
          (((gaussianReal 0 1).restrict (Icc t (t + 1))).prod (gaussianReal 0 1)) := by
        refine Integrable.of_bound hG_cont.aestronglyMeasurable L (ae_of_all _ fun p => ?_)
        rw [Real.norm_eq_abs]
        have h1 := Lemma24Aux.abs_mul_q_le_one ((p.1 * y i + σ i * p.2) / L)
        have h2 : (p.1 * y i + σ i * p.2) * q ((p.1 * y i + σ i * p.2) / L) =
            L * (((p.1 * y i + σ i * p.2) / L) * q ((p.1 * y i + σ i * p.2) / L)) := by
          field_simp [ne_of_gt hL_pos]
        rw [h2, abs_mul, abs_of_pos hL_pos]
        calc
          L * |((p.1 * y i + σ i * p.2) / L) * q ((p.1 * y i + σ i * p.2) / L)| ≤ L * 1 :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
          _ = L := mul_one L
      exact hG_int.integral_prod_left
    have hconst1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc t (t + 1)) (gaussianReal 0 1) :=
      integrable_const (1 : ℝ)
    have hint_rhs_i : IntegrableOn
        (fun u : ℝ => (1 + ∫ x : ℝ,
          (u * y i + σ i * x) * q ((u * y i + σ i * x) / L) ∂gaussianReal 0 1) / L)
        (Icc t (t + 1)) (gaussianReal 0 1) :=
      (hconst1.add hint_EY_i).div_const L
    have hmono := setIntegral_mono_on hint_u3 hint_rhs_i measurableSet_Icc hpwise_u
    rw [integral_div, integral_add hconst1 hint_EY_i,
      setIntegral_const, smul_eq_mul, mul_one] at hmono
    have hmeas_Icc : (gaussianReal 0 1).real (Icc t (t + 1)) = (stdGaussian (E d) Ev).toReal := by
      simp [Measure.real, hPE_eq]
    rwa [hmeas_Icc] at hmono
  -- Sum over i to bound ∫ z in Ev, X₁ z and ∫ z in Ev, X₂ z
  set B₁ : ℝ := (2 * C ^ 2 * lam ^ 2 / Real.sqrt (Real.log d)) * ‖b‖ * μ
  set B₂ : ℝ := support v b / (C * lam) + μ
  have hB₁_pos : 0 < B₁ := by dsimp [B₁]; positivity
  have hB₂_pos : 0 < B₂ := by
    dsimp [B₂]
    have hH_nn : 0 ≤ support v b := by
      rw [Lemma24Aux.support_eq_sum_abs]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    positivity
  have h_int_X₁_le : (∫ z in Ev, X₁ z ∂stdGaussian (E d)) ≤
      (stdGaussian (E d) Ev).toReal * B₁ := by
    have heval : (∫ z in Ev, X₁ z ∂stdGaussian (E d)) =
        ∑ i, (‖b‖ * |inner ℝ b (v i)|) * (y i * I₂ i) := by
      rw [setIntegral_congr_fun hE_meas (fun z _ => hX₁_eq z),
        integral_finsetSum Finset.univ (fun i _ => hX₁_int_each i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul,
        Lemma24Aux.setIntegral_alignment_unit hd hb (hw_norm i) hg₂_cont hg₂_bnd]
      dsimp [I₂, g₂]
      ring
    rw [heval]
    calc
      ∑ i, (‖b‖ * |inner ℝ b (v i)|) * (y i * I₂ i)
        ≤ ∑ i, (‖b‖ * |inner ℝ b (v i)|) * ((2 / t) * I₁ i) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (hI₂_bound i) (by positivity)
      _ = (2 * L / t) * ‖b‖ * ∑ i, (|inner ℝ b (v i)| / L) * I₁ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hL_ne : L ≠ 0 := ne_of_gt hL_pos
          field_simp [hL_ne]
      _ = (stdGaussian (E d) Ev).toReal * B₁ := by
          have hsum_μ : ∑ i, (|inner ℝ b (v i)| / L) * I₁ i =
              (stdGaussian (E d) Ev).toReal * μ := by
            rw [hμ_eq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hPE_pos), one_mul]
          rw [hsum_μ]
          dsimp [B₁, t, L]
          have hsqrt_ne : Real.sqrt (Real.log d) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.mpr hlogd_pos)
          have hC_ne : C ≠ 0 := by linarith
          have hlam_ne : lam ≠ 0 := by linarith
          field_simp [hsqrt_ne, hC_ne, hlam_ne]
  have h_int_X₂_le : (∫ z in Ev, X₂ z ∂stdGaussian (E d)) ≤
      (stdGaussian (E d) Ev).toReal * B₂ := by
    have heval : (∫ z in Ev, X₂ z ∂stdGaussian (E d)) =
        ∑ i, |inner ℝ b (v i)| * I₃ i := by
      rw [setIntegral_congr_fun hE_meas (fun z _ => hX₂_eq z),
        integral_finsetSum Finset.univ (fun i _ => hX₂_int_each i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul,
        Lemma24Aux.setIntegral_alignment_unit hd hb (hw_norm i) hg₃_cont hg₃_bnd]
    rw [heval]
    calc
      ∑ i, |inner ℝ b (v i)| * I₃ i
        ≤ ∑ i, |inner ℝ b (v i)| * (((stdGaussian (E d) Ev).toReal + I₁ i) / L) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (hI₃_bound i) (abs_nonneg _)
      _ = (stdGaussian (E d) Ev).toReal * ((∑ i, |inner ℝ b (v i)|) / L) +
          ∑ i, (|inner ℝ b (v i)| / L) * I₁ i := by
          rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ = (stdGaussian (E d) Ev).toReal * B₂ := by
          have hsum_μ : ∑ i, (|inner ℝ b (v i)| / L) * I₁ i =
              (stdGaussian (E d) Ev).toReal * μ := by
            rw [hμ_eq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hPE_pos), one_mul]
          rw [hsum_μ, ← Lemma24Aux.support_eq_sum_abs]
          dsimp [B₂, L]
          ring
  -- Part 4: Markov's inequality on S₁ and S₂ + union bound
  let S₁ : Set (E d) := {z | z ∈ Ev ∧ 4 * B₁ < X₁ z}
  let S₂ : Set (E d) := {z | z ∈ Ev ∧ 4 * B₂ < X₂ z}
  have hS₁_meas : MeasurableSet S₁ :=
    hE_meas.inter (measurableSet_lt measurable_const hX₁_cont.measurable)
  have hS₂_meas : MeasurableSet S₂ :=
    hE_meas.inter (measurableSet_lt measurable_const hX₂_cont.measurable)
  have hS₁_bound : stdGaussian (E d) S₁ ≤ stdGaussian (E d) Ev / 4 := by
    have hsub : S₁ ⊆ Ev := fun _ hz => hz.1
    have hm1 := setIntegral_mono_on
      (integrableOn_const (measure_ne_top _ _) (C := 4 * B₁))
      (hX₁_int.mono_set hsub) hS₁_meas (fun z hz => le_of_lt hz.2)
    have hm2 := setIntegral_mono_set hX₁_int (ae_of_all _ hX₁_nn)
      (Filter.Eventually.of_forall hsub)
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hm1
    have hchain : (stdGaussian (E d) S₁).toReal * (4 * B₁) ≤
        (stdGaussian (E d) Ev).toReal * B₁ := le_trans hm1 (le_trans hm2 h_int_X₁_le)
    have hdiv : (stdGaussian (E d) S₁).toReal ≤ (stdGaussian (E d) Ev).toReal / 4 := by
      have : (stdGaussian (E d) S₁).toReal * 4 ≤ (stdGaussian (E d) Ev).toReal :=
        le_of_mul_le_mul_right (by linarith) hB₁_pos
      linarith
    have hS₁_lt_top : stdGaussian (E d) S₁ < ⊤ := measure_lt_top _ _
    rw [← ENNReal.ofReal_toReal (ne_of_lt hS₁_lt_top),
      ← ENNReal.ofReal_toReal (ne_of_lt hPE_lt_top),
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hdiv
  have hS₂_bound : stdGaussian (E d) S₂ ≤ stdGaussian (E d) Ev / 4 := by
    have hsub : S₂ ⊆ Ev := fun _ hz => hz.1
    have hm1 := setIntegral_mono_on
      (integrableOn_const (measure_ne_top _ _) (C := 4 * B₂))
      (hX₂_int.mono_set hsub) hS₂_meas (fun z hz => le_of_lt hz.2)
    have hm2 := setIntegral_mono_set hX₂_int (ae_of_all _ hX₂_nn)
      (Filter.Eventually.of_forall hsub)
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hm1
    have hchain : (stdGaussian (E d) S₂).toReal * (4 * B₂) ≤
        (stdGaussian (E d) Ev).toReal * B₂ := le_trans hm1 (le_trans hm2 h_int_X₂_le)
    have hdiv : (stdGaussian (E d) S₂).toReal ≤ (stdGaussian (E d) Ev).toReal / 4 := by
      have : (stdGaussian (E d) S₂).toReal * 4 ≤ (stdGaussian (E d) Ev).toReal :=
        le_of_mul_le_mul_right (by linarith) hB₂_pos
      linarith
    have hS₂_lt_top : stdGaussian (E d) S₂ < ⊤ := measure_lt_top _ _
    rw [← ENNReal.ofReal_toReal (ne_of_lt hS₂_lt_top),
      ← ENNReal.ofReal_toReal (ne_of_lt hPE_lt_top),
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hdiv
  refine ⟨hPE_lb, hμ_pos, ?_⟩
  have hbad_sub : {z | z ∈ Ev ∧ ¬ GoodUpdate C lam v b z} ⊆ S₁ ∪ S₂ := by
    rintro z ⟨hzE, hnot⟩
    unfold GoodUpdate at hnot
    by_cases h1 : X₁ z ≤ 4 * B₁
    · right
      refine ⟨hzE, ?_⟩
      by_contra h2
      have h2' : X₂ z ≤ 4 * B₂ := not_lt.mp h2
      apply hnot
      refine ⟨?_, ?_⟩
      · have hrew1 : 4 * B₁ = (8 * C ^ 2 * lam ^ 2 / Real.sqrt (Real.log d)) * ‖b‖ * μ := by
          dsimp [B₁]; ring
        exact hrew1 ▸ h1
      · have hrew2 : 4 * B₂ = 4 * support v b / (C * lam) + 4 * μ := by
          dsimp [B₂]; ring
        exact hrew2 ▸ h2'
    · left
      exact ⟨hzE, not_le.mp h1⟩
  calc
    stdGaussian (E d) {z | z ∈ Ev ∧ ¬ GoodUpdate C lam v b z}
      ≤ stdGaussian (E d) (S₁ ∪ S₂) := measure_mono hbad_sub
    _ ≤ stdGaussian (E d) S₁ + stdGaussian (E d) S₂ := measure_union_le S₁ S₂
    _ ≤ stdGaussian (E d) Ev / 4 + stdGaussian (E d) Ev / 4 := add_le_add hS₁_bound hS₂_bound
    _ = stdGaussian (E d) Ev / 2 := by
        set r := (stdGaussian (E d) Ev).toReal
        have hr_nn : 0 ≤ r := ENNReal.toReal_nonneg
        have h4 : (stdGaussian (E d) Ev) / 4 = ENNReal.ofReal (r / 4) := by
          conv_lhs => rw [← ENNReal.ofReal_toReal (ne_of_lt hPE_lt_top)]
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
        have h2 : (stdGaussian (E d) Ev) / 2 = ENNReal.ofReal (r / 2) := by
          have hr_eq : stdGaussian (E d) Ev = ENNReal.ofReal r :=
            (ENNReal.ofReal_toReal (ne_of_lt hPE_lt_top)).symm
          rw [hr_eq]
          have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
          rw [htwo, ← ENNReal.ofReal_div_of_pos (by norm_num)]
        rw [h4, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

