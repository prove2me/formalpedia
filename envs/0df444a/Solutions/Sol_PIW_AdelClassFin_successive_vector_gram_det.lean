-- Prove2me | solution 1 for PIW.AdelClassFin.successive_vector_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:18.648411+00:00
-- url     : https://prove2.me/submissions/3160c7e0-d749-496e-a041-42891966ca82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet
import Theorems.Thm_PIW_AdelClassFin_gd_int_smul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_left__345360160129
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_right__f0caf7c17a43
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : SvGramDet := by
  classical
  intro F E _ _ _ _ _ _ cm m d δ hd hδ hcod p hp e hli he hspan
  simp only [Lat, Set.mem_setOf_eq] at hp
  obtain ⟨hJh, hJdet, -, -, hMint, hMdual⟩ := hp
  set J := p.1 with hJdef
  set M := p.2 with hMdef
  have hO : ∀ b : E, b ∈ (algebraMap (𝓞 E) E).range → star b ∈ (algebraMap (𝓞 E) E).range := by
    intro b hb
    obtain ⟨β, rfl⟩ := RingHom.mem_range.mp hb
    have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E β)) :=
      IsIntegral.map (starRingEnd E).toIntAlgHom β.isIntegral_coe
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint)
  have F1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hsingle : ∀ (i : Fin m) (v : Fin m → E), hform (starRingEnd E) J (Pi.single i 1) v = (J *ᵥ v) i := by
    intro i v
    rw [F1]
    have hs : (fun a => starRingEnd E ((Pi.single i (1 : E) : Fin m → E) a)) = Pi.single i 1 := by
      funext a
      by_cases h : a = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    rw [hs]
    first
      | rw [single_dotProduct, one_mul]
      | simp [dotProduct, Pi.single_apply]
  have hnd : ∀ y : Fin m → E, (∀ x, hform (starRingEnd E) J x y = 0) → y = 0 := by
    intro y hy
    have hJy : J *ᵥ y = 0 := by
      funext i
      rw [← hsingle, Pi.zero_apply]
      exact hy _
    have h6 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec y J⁻¹ J, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJdet),
        Matrix.one_mulVec]
    rw [h6, hJy, Matrix.mulVec_zero]
  have htr : ∀ z : E, (∀ b : E, Algebra.trace ℚ E (b * z) = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz z⁻¹
    rw [inv_mul_cancel₀ hne, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one, Nat.cast_eq_zero] at h1
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne' h1
  have hRt : ∀ x y, gdRight J x y = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have hLt : ∀ x y, gdLeft J y x = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have Br : ∀ (x : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J x (∑ k, q k • e k)) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J x (e k)) := by
    intro x q
    rw [← hRt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hRt]
  have Bl : ∀ (y : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J (∑ k, q k • e k) y) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J (e k) y) := by
    intro y q
    rw [← hLt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hLt]
  have hGe : ∀ i j, gramTr J e i j = Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j)) :=
    fun i j => rfl
  have hdetG : (gramTr J e).det ≠ 0 := by
    rcases isEmpty_or_nonempty (Fin (m * Module.finrank ℚ E)) with hE | hE
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Module.finrank ℚ (Fin m → E) := by
      rw [Fintype.card_fin]
      first
        | simp [Module.finrank_pi_fintype]
        | rw [Module.finrank_pi_fintype]; simp
    let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbs : ∀ i, bs i = e i := fun i => by simp [bs]
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv0, hv⟩
    have hy : ∑ j, v j • e j = 0 := by
      apply hnd
      intro x
      apply htr
      intro b
      have e1 : b * hform (starRingEnd E) J x (∑ j, v j • e j) =
          hform (starRingEnd E) J (star b • x) (∑ j, v j • e j) := by
        rw [hform_smul_left', star_star]
      rw [e1]
      have hf : gdLeft J (∑ j, v j • e j) = 0 := by
        refine bs.ext fun i => ?_
        rw [hbs, LinearMap.zero_apply, hLt, Br]
        have h2 := congrFun hv i
        rw [Pi.zero_apply] at h2
        refine Eq.trans ?_ h2
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
      have h3 := LinearMap.congr_fun hf (star b • x)
      rw [LinearMap.zero_apply, hLt] at h3
      exact h3
    apply hv0
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) v hy i
  refine ⟨hdetG, ?_⟩
  set Gi := (gramTr J e)⁻¹ with hGi
  have hGGi : gramTr J e * Gi = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)
  obtain ⟨w, hw⟩ : ∃ w : Fin (m * Module.finrank ℚ E) → Fin m → E,
      ∀ j, w j = ∑ k, Gi k j • e k := ⟨_, fun j => rfl⟩
  have hBw : ∀ i j, Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (w j)) =
      (1 : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℚ) i j := by
    intro i j
    rw [hw, Br, ← hGGi, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
  have hint : ∀ x ∈ M, ∀ j, Algebra.trace ℚ E (hform (starRingEnd E) J x (w j)) ∈
      (algebraMap ℤ ℚ).range := by
    intro x hx j
    obtain ⟨c, rfl⟩ := hspan x hx
    have e2 : ∑ i, ((c i : ℤ) : E) • e i = ∑ i, ((c i : ℚ)) • e i :=
      Finset.sum_congr rfl fun i _ => gd_int_smul _ _
    rw [e2, Bl]
    simp only [hBw, Matrix.one_apply]
    refine RingHom.mem_range.mpr ⟨c j, ?_⟩
    simp
  have hdual : ∀ j, (d : E) • ((δ : E) • w j) ∈ M := by
    intro j
    apply hMdual
    intro x hx
    rw [hform_smul_right']
    apply hcod
    intro a
    have hsa : star (algebraMap (𝓞 E) E a) • x ∈ M := by
      obtain ⟨a', ha'⟩ := RingHom.mem_range.mp (hO _ (RingHom.mem_range.mpr ⟨a, rfl⟩))
      rw [← ha', algebraMap_smul]
      exact M.smul_mem a' hx
    have e3 : algebraMap (𝓞 E) E a * hform (starRingEnd E) J x (w j) =
        hform (starRingEnd E) J (star (algebraMap (𝓞 E) E a) • x) (w j) := by
      rw [hform_smul_left', star_star]
    rw [e3]
    exact hint _ hsa j
  have hn : ∀ (n : ℕ) (v : Fin m → E), (n : E) • v = (n : ℚ) • v := fun n v => by
    rw [gd_qsmul, Rat.cast_natCast]
  have hC : ∀ j, ∃ C : Fin (m * Module.finrank ℚ E) → ℤ,
      ∀ k, (C k : ℚ) = (d : ℚ) * (δ : ℚ) * Gi k j := by
    intro j
    obtain ⟨C, hCe⟩ := hspan _ (hdual j)
    refine ⟨C, ?_⟩
    have e4 : (d : E) • ((δ : E) • w j) = ∑ k, ((d : ℚ) * (δ : ℚ) * Gi k j) • e k := by
      rw [hn, hn, hw, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    have e5 : ∑ k, ((C k : ℚ) - (d : ℚ) * (δ : ℚ) * Gi k j) • e k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← e4, hCe]
      exact Finset.sum_congr rfl fun k _ => (gd_int_smul _ _).symm
    intro k
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ e5 k)
  choose C hCj using hC
  set C' : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℤ :=
    Matrix.of fun k j => C j k with hC'
  have hdq : (0 : ℚ) < (d : ℚ) * (δ : ℚ) := by
    have h1 : (0 : ℚ) < d := Nat.cast_pos.mpr hd
    have h2 : (0 : ℚ) < δ := Nat.cast_pos.mpr hδ
    positivity
  have hCm : C'.map (Int.cast : ℤ → ℚ) = ((d : ℚ) * (δ : ℚ)) • Gi := by
    ext k j
    simp [hC', hCj]
  have hdetC : ((C'.det : ℤ) : ℚ) =
      ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) * ((gramTr J e).det)⁻¹ := by
    have h1 : ((C'.det : ℤ) : ℚ) = (C'.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det C'
    rw [h1, hCm, Matrix.det_smul, Fintype.card_fin, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hCne : C'.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdetC
    exact mul_ne_zero (pow_ne_zero _ hdq.ne') (inv_ne_zero hdetG) hdetC.symm
  have h1 : (1 : ℚ) ≤ |((C'.det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hCne
  have hpos : 0 < |(gramTr J e).det| := abs_pos.mpr hdetG
  set X := ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) with hX
  have hXpos : 0 < X := pow_pos hdq _
  rw [hdetC, abs_mul, abs_inv, abs_of_pos hXpos] at h1
  have key : |(gramTr J e).det| ≤ X := by
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_comm X, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
  rw [hX] at key
  push_cast
  exact key
end PIW.AdelClassFin
