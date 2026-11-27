-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_proof_e4400d312741
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:28.270529+00:00
-- url     : https://prove2.me/submissions/d0736353-f984-40e3-ad96-a64591d9a886

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open YPlusSmall
namespace GroundTheory.Heights₂.Heights
namespace YPlusSmall
theorem _root_.solution (hForms : ChartFormsAlt.Statement) (hConv : ConePointsConverse.Statement) :
    YPlusSmall.Statement := by
  intro ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hM hs hsup
  obtain ⟨d, hd⟩ := hForms ι n P D
  obtain ⟨g, hg⟩ := hd d le_rfl
  set e : ι → ℕ := fun k ↦ ((d k : ℤ) + D.deg k).toNat with he_def
  have he : ∀ k, (e k : ℤ) = d k + D.deg k := fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)
  have hgh : ∀ c j, Geo.IsMultiHomog (ι := blockIdx n) (g c j) e := by
    intro c j
    obtain ⟨δ, hδ, hδe⟩ := hg.homog c j
    have hδ' : δ = e := funext fun k ↦ by have := hδe k; have := he k; omega
    exact (geoMultiHomog_iff _ _).mpr (hδ' ▸ hδ)
  have hmh : ∀ c, Geo.IsMultiHomog (ι := blockIdx n) (chartMonomial c d) d := fun c ↦
    (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial c d)
  have hval : ∀ c, P.IsLive c → ∀ j,
      aeval y (g c j) = aeval y (chartMonomial c d) * x' j := by
    intro c hc j
    have := (hR.reads j (g c j) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mp (hgh c j))
      (isWeightedHomogeneous_chartMonomial c d) he).mpr (by rw [hg.value c hc j, mul_comm])
    rw [this, mul_comm]
  obtain ⟨f, hf, hfs⟩ := exists_of_mem_secM _ _ hs
  refine ⟨?_, ?_⟩
  ·
    show ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → _
    intro c hc
    have hlive : P.IsLive c := by
      intro k hk
      rw [hR.ideal_eq, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X] at hk
      exact hc k (C_eq_zero.mp ((mul_eq_zero.mp hk).resolve_right (X_ne_zero _)))
    rw [hNa]
    set u : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(D.deg k)) with hu_def
    have hu : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * D.deg k)) = u ^ τ := by
      rw [hu_def, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    have hx : ∀ j, u * x' j ∈ Geo.chartRingZ (ι := blockIdx n) y c := by
      intro j
      have hmem : aeval (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) (g c j) ∈
          Geo.chartRingZ (ι := blockIdx n) y c := by
        rw [Geo.chartRingZ, Algebra.adjoin_range_eq_range_aeval]
        exact ⟨g c j, rfl⟩
      have hsc := aeval_blockScale (hgh c j) (fun k ↦ (y ⟨k, c k⟩)⁻¹) y
      rw [show (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) = fun p ↦ (y ⟨p.1, c p.1⟩)⁻¹ * y p from
        funext fun _ ↦ div_eq_inv_mul _ _, hsc, hval c hlive j] at hmem
      have hm : aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
        simp [chartMonomial, map_prod]
      have hue : u = (∏ k, (y ⟨k, c k⟩)⁻¹ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ d k := by
        rw [hu_def, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        rw [inv_pow, ← zpow_natCast, ← zpow_natCast (y _) (d k), ← zpow_neg, ← zpow_add₀ (hc k)]
        congr 1
        have := he k
        omega
      rw [hue, ← hm, mul_assoc]
      exact hmem
    set c'' : Option ι → Ω := fun o ↦ o.elim u fun _ ↦ 0 with hc''
    have hsc := aeval_blockScale hf c'' (D.plusCoord y x')
    have hprod : ∏ o, c'' o ^ (Pi.single (none : Option ι) τ : Option ι → ℕ) o = u ^ τ := by
      simp [Fintype.prod_option, hc'']
    rw [hprod, hfs] at hsc
    rw [hu, mul_comm, ← hsc]
    refine aeval_mem_of_forall _ _ (fun p ↦ ?_) f
    rcases p with ⟨_ | k, i⟩
    · exact hx i
    · show 0 * y ⟨k, i⟩ ∈ _
      rw [zero_mul]
      exact zero_mem _
  ·
    intro dg dh G H z hG hH hdeg hGH hz
    have hzP' : z ∈ Geo.mcPts (ι := blockIdx n) P.ideal := by rw [hR.ideal_eq]; exact hz
    have hzP : unflatCone z ∈ P.points ℂ := (P.mem_mcPts_iff z).mp hzP'
    choose c hc using hz.1
    have hlc : P.IsLive c := fun k hk ↦ hc k (by simpa using hzP'.2 _ hk)
    set zc : Cone n ℂ := unflatCone z with hzc
    have hE : ∀ F, evalCone zc F = eval z (map (Int.castRingHom ℂ) F) :=
      fun F ↦ (eval_map_flatCone zc F).symm
    have hmz : evalCone zc (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hw := hConv ι n P D d g hg zc hzP c hmz
    set w := D.joinPt zc (fun j ↦ evalCone zc (g c j)) with hw_def
    have hwm : flatCone w ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')) := by
      rw [← hR.ext_eq]
      exact ⟨(blockNonzero_unflatCone_iff _).mp hw.1, fun F hF ↦ by
        rw [eval_map_flatCone]; exact hw.2 F hF⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw.1 none)
    have hj' : eval z (map (Int.castRingHom ℂ) (g c j)) ≠ 0 := by rw [← hE]; exact hj
    have hind := hM j (g c j) (chartMonomial c d) e d (hgh c j) (hmh c)
      (fun k ↦ by rw [hNa]; exact he k) (hval c hlc j) (flatCone w) hwm
    have hold : D.oldFlat (flatCone w) = z := rfl
    rw [hold] at hind
    change ‖evalCone zc (g c j)‖ * _ * _ = _ at hind
    rw [hE, mul_assoc] at hind
    have hAp : Ap.h (flatCone w) = ‖eval z (map (Int.castRingHom ℂ) (chartMonomial c d))‖ * N.h z :=
      (mul_left_cancel₀ (norm_ne_zero_iff.mpr hj') hind).symm

    set q : Coord D.extSizes → MvPolynomial (Coord n) ℤ := fun p ↦ match p with
      | ⟨none, j⟩ => g c j
      | ⟨some k, i⟩ => X ⟨k, i⟩ with hq
    have hFz : eval z (map (Int.castRingHom ℂ) (aeval q f)) =
        eval (flatCone w) (map (Int.castRingHom ℂ) f) := by
      rw [eval_map_int, eval_map_int, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
      have hfun : (fun p ↦ aeval z (q p)) = flatCone w := by
        funext p
        rcases p with ⟨_ | k, i⟩
        · show aeval z (g c i) = evalCone zc (g c i)
          rw [hE, eval_map_int]
        · show aeval z (X ⟨k, i⟩) = z ⟨k, i⟩
          rw [aeval_X]
      rw [hfun]

    set m := chartMonomial c d with hm_def
    have hΦ : m ^ τ * G - aeval q f * H ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker]
      set c' : Option ι → MvPolynomial ι Ω := fun o ↦ o.elim (∏ k, X k ^ e k) X with hc'
      have hq' : (fun p ↦ Geo.mConeMap (ι := blockIdx n) y (q p)) =
          fun p ↦ c' p.1 * C (D.plusCoord y (fun j ↦ aeval y m * x' j) p) := by
        funext p
        rcases p with ⟨_ | k, i⟩
        · show Geo.mConeMap (ι := blockIdx n) y (g c i) = (∏ k, X k ^ e k) * C (aeval y m * x' i)
          rw [mConeMap_of_homog (hgh c i), hval c hlc i, mul_comm]
        · show Geo.mConeMap (ι := blockIdx n) y (X ⟨k, i⟩) = X k * C (y ⟨k, i⟩)
          rw [Geo.mConeMap, aeval_X, mul_comm]
      have hF1 : Geo.mConeMap (ι := blockIdx n) y (aeval q f) =
          (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * C (aeval y m ^ τ * s) := by
        rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, hq']
        refine (aeval_blockScale hf c' (fun p ↦ C (D.plusCoord y (fun j ↦ aeval y m * x' j) p))).trans ?_
        erw [aeval_C_comp]
        have hsc := aeval_blockScale hf (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω))
          (D.plusCoord y x')
        rw [show (fun p : Coord D.extSizes ↦ (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω)) p.1 *
            D.plusCoord y x' p) = D.plusCoord y (fun j ↦ aeval y m * x' j) from by
          funext p; rcases p with ⟨_ | k, i⟩
          · rfl
          · show 1 * y ⟨k, i⟩ = y ⟨k, i⟩
            rw [one_mul]] at hsc
        rw [hsc, hfs]
        congr 1
        · simp [Fintype.prod_option, hc']
        · congr 1
          simp [Fintype.prod_option]
      have hT : (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ^ τ * ∏ k, X k ^ dg k =
          (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * ∏ k, X k ^ dh k := by
        simp only [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
        refine Finset.prod_congr rfl fun k _ ↦ congrArg _ ?_
        have h1 := hdeg k
        have h2 := he k
        rw [hNa] at h1
        zify
        linear_combination h1 - (τ : ℤ) * h2
      rw [map_sub, map_mul, map_mul, map_pow, hF1, mConeMap_of_homog (hmh c),
        mConeMap_of_homog hG, mConeMap_of_homog hH, hGH]
      simp only [map_mul, map_pow]
      linear_combination (C (aeval y m) : MvPolynomial ι Ω) ^ τ * C s * C (aeval y H) * hT
    have hzero := hz.2 _ hΦ
    simp only [map_sub, map_mul, map_pow] at hzero
    have hrel := sub_eq_zero.mp hzero
    have hmz' : eval z (map (Int.castRingHom ℂ) m) ≠ 0 := by rw [← hE]; exact hmz
    have hF : ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ ≤
        (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ := by
      rw [hFz, ← hAp]
      exact hsup f hf hfs (flatCone w) hwm
    have hpos : 0 < ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ := pow_pos (norm_pos_iff.mpr hmz') τ
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖eval z (map (Int.castRingHom ℂ) G)‖ * ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ
        = ‖eval z (map (Int.castRingHom ℂ) m) ^ τ * eval z (map (Int.castRingHom ℂ) G)‖ := by
          rw [norm_mul, norm_pow, mul_comm]
      _ = ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ * ‖eval z (map (Int.castRingHom ℂ) H)‖ := by
          rw [hrel, norm_mul]
      _ ≤ (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ * ‖eval z (map (Int.castRingHom ℂ) H)‖ :=
          mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ = ‖eval z (map (Int.castRingHom ℂ) H)‖ * N.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ := by
          ring
end YPlusSmall
end GroundTheory.Heights₂.Heights
