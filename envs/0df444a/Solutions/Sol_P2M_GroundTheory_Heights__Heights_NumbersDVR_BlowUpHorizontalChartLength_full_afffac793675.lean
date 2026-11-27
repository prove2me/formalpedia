-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalChartLength_full_afffac793675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:41.947082+00:00
-- url     : https://prove2.me/submissions/2ad296cc-07f3-492a-a6e6-d8fcf4eeafa0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_localizedModule_quotient_d887d68c64f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_quotient_self_e2208786fc77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_pow_mul_mem_of_aeval_chartSubst_mem_9a4afa4e37e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpHorizontalChartLength
theorem _root_.solution : BlowUpHorizontalChartLength.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨-, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  set 𝔮 := W₀.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with h𝔮
  set Jx := (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with hJx
  set I := blowUpOf P u ⊔ Ideal.span {liftForm x} with hI
  let φ : MRing (extIdx ι J) O →+* Polynomial (MRing ι O) := (aeval (R := O) (chartSubst a)).toRingHom
  have hφ : ∀ F, φ F = aeval (chartSubst a) F := fun _ => rfl
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hW𝔮 : W = 𝔮.comap φ := by
    refine le_antisymm ?_ ?_
    · refine hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩
        (fun G hG => ?_)
      · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
      · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
        exact Ideal.mem_map_of_mem _ hxW
      · exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
    · intro G hG
      exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hlfa : ∀ m : ℕ, liftForm (a j₀ ^ m) ∉ W := fun m h =>
    ha₀ (hW₀p.mem_of_pow_mem m (show a j₀ ^ m ∈ W₀ from h))
  have hCa : ∀ e : ℕ, Polynomial.C (a j₀ ^ e) ∉ 𝔮 := by
    intro e h
    have h1 := Ideal.mem_map_C_iff.mp h 0
    rw [Polynomial.coeff_C_zero] at h1
    exact ha₀ (hW₀p.mem_of_pow_mem _ h1)
  have hq : 𝔮.IsPrime := inferInstance

  have hlift : ∀ t, t ∉ 𝔮 → ∃ (e : ℕ) (T : MRing (extIdx ι J) O),
      φ T = Polynomial.C (a j₀ ^ e) * t ∧ T ∉ W := by
    intro t ht
    obtain ⟨e, T, hT⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ t
    refine ⟨e, T, hT, fun hTW => ?_⟩
    have h1 : φ T ∈ 𝔮 := by rw [hW𝔮] at hTW; exact hTW
    rw [hφ, hT] at h1
    exact (hq.mem_or_mem h1).elim (hCa e) ht

  have hIJ : I ≤ Jx.comap φ := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono le_sup_left (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  have memI : ∀ G, φ G ∈ Jx → ∃ m : ℕ, liftForm (a j₀ ^ m) * G ∈ I := by
    intro G hG
    rw [hJx, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at hG
    obtain ⟨y, hy, z, hz, hyz⟩ := hG
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    have h1 : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) ∈
        Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P := by
      have e : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) =
          Polynomial.C (a j₀ ^ d) * y := by
        rw [map_sub, map_mul, map_mul, aeval_chartSubst_liftForm, aeval_chartSubst_liftForm, hH, ← hφ G,
          ← hyz]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hy
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem (P := P) (u := u) j₀ hrelB h1
    have hPB : Ideal.map (liftForm (J := J) : MRing ι O →ₐ[O] MRing (extIdx ι J) O) P ≤ blowUpOf P u :=
      Ideal.map_le_iff_le_comap.mpr fun p hp => liftForm_mem_blowUpOf hp
    have hm' := sup_le le_rfl hPB hm
    refine ⟨m + d, ?_⟩
    have e : liftForm (a j₀ ^ (m + d)) * G =
        liftForm (a j₀ ^ m) * (liftForm (a j₀ ^ d) * G - H * liftForm x) +
          (liftForm (a j₀ ^ m) * H) * liftForm x := by
      rw [pow_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hm')
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

  let Φ := Localization.localRingHom W 𝔮 φ hW𝔮
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨h, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    obtain ⟨e, T, hT, hTW⟩ := hlift t t.2
    have hs : T * liftForm (a j₀ ^ d) ∈ W.primeCompl := W.primeCompl.mul_mem hTW (hlfa d)
    refine ⟨IsLocalization.mk' _ (H * liftForm (a j₀ ^ e)) ⟨_, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    change (t : Polynomial (MRing ι O)) * φ (H * liftForm (a j₀ ^ e)) = φ (T * liftForm (a j₀ ^ d)) * h
    rw [map_mul, map_mul, hT]
    simp only [hφ, aeval_chartSubst_liftForm, hH]
    ring
  have hker : I.map (algebraMap _ (Localization.AtPrime W)) =
      (Jx.map (algebraMap _ (Localization.AtPrime 𝔮))).comap Φ := by
    ext z
    obtain ⟨⟨F, T⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [Ideal.mem_comap, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨s, hs, hsF⟩
      refine ⟨φ s, fun h => hs (by rw [hW𝔮]; exact h), ?_⟩
      rw [← map_mul]
      exact hIJ hsF
    · rintro ⟨t, ht, htF⟩
      obtain ⟨e, T', hT', hT'W⟩ := hlift t ht
      obtain ⟨m, hm⟩ := memI (T' * F) (by
        rw [map_mul, hT', mul_assoc]
        exact Ideal.mul_mem_left _ _ htF)
      exact ⟨liftForm (a j₀ ^ m) * T', W.primeCompl.mul_mem (hlfa m) hT'W, by rw [mul_assoc]; exact hm⟩
  have hsurj' : Function.Surjective
      ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) :=
    Ideal.Quotient.mk_surjective.comp hsurj
  have hker' : I.map (algebraMap _ (Localization.AtPrime W)) =
      RingHom.ker ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hker
  let τ := (Ideal.quotEquivOfEq hker').trans (RingHom.quotientKerEquivOfSurjective hsurj')
  unfold multAt
  rw [chartLength_localizedModule_quotient, chartLength_localizedModule_quotient,
    chartLength_quotient_self, chartLength_quotient_self]
  exact chartLength_self_eq_of_ringEquiv τ
end BlowUpHorizontalChartLength
end GroundTheory.Heights₂.Heights.NumbersDVR
