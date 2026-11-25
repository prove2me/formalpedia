-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:36.59314+00:00
-- url     : https://prove2.me/submissions/f70c46c9-be6b-4203-8e91-1ce91e4a1e80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_secChart_of_mem_b8e5b6bc3283
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open AmpleAffineGen
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace AmpleAffineGen
theorem _root_.solution : AmpleAffineGen.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j h0
  classical
  have hh : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  obtain ⟨n, a, c, J, ha, hc, hsum, hrat⟩ := A.affine j h0
  have haB : ∀ k I, a k ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) := fun k I =>
    Set.mem_iInter.mp (ha k) I
  have hcB : ∀ k I, c k ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) := fun k I =>
    Set.mem_iInter.mp (hc k) I

  have hfg : ∀ k, ∃ G : Finset Ω,
      Submodule.span (chartRing S x (J k)) (G : Set Ω) = (Q.twist (H.pow b)).sub (J k) := by
    intro k
    obtain ⟨G, hG⟩ := (Q.tensorProd (H.powBundle b)).fg (J k)
    refine ⟨G, ?_⟩
    rw [hG, tensorProd_powBundle]
  choose G hG using hfg

  have stepA : ∀ k, ∀ γ ∈ G k, ∀ I : Chart x, ∀ᶠ M in Filter.atTop,
      c k ^ M * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    intro k γ hγ I
    have h1 : γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) (unionChart I (J k)) :=
      secChart_mono (subset_unionChart_right I (J k))
        (mem_secChart_of_mem (by rw [← hG k]; exact Submodule.subset_span hγ))
    obtain ⟨D, hD⟩ := secChart_loc Q H I (J k) h1
    obtain ⟨e, he⟩ := hrat k I
    have h2 : c k ^ (e * D) * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
      have := secChart_smul
        (pow_mem (show _ ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) from he) D) hD
      rwa [show c k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) = c k ^ e * chartRatio (J k) I
        from rfl, pow_mul_cancel (chartRatio_mul_chartRatio I (J k))] at this
    refine Filter.eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    have : c k ^ M * γ = c k ^ (M - e * D) * (c k ^ (e * D) * γ) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
    rw [this]
    exact secChart_smul (pow_mem (hcB k I) _) h2
  have stepA' : ∀ᶠ M in Filter.atTop, ∀ k, ∀ γ ∈ G k, ∀ I : Chart x,
      c k ^ M * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all_finset]
    intro γ hγ
    rw [Filter.eventually_all]
    exact stepA k γ hγ
  obtain ⟨M₀, hM₀⟩ := stepA'.exists

  set T : Finset Ω := Finset.univ.biUnion fun k => (G k).image fun γ => c k ^ M₀ * γ with hTdef
  have hTmem : ∀ k, ∀ γ ∈ G k, c k ^ M₀ * γ ∈ T := fun k γ hγ =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩⟩
  have hT : ∀ t ∈ T, ∀ I : Chart x, t ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    intro t ht I
    obtain ⟨k, -, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ht
    exact hM₀ k γ hγ I

  have stepC : ∀ (I : Chart x) (z : Ω),
      z ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I →
      z ∈ Submodule.span (ampleSubalg H.toSubSystem A.m (A.h j) I (hh I)) (T : Set Ω) := by
    intro I z hz
    set B := ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) with hBdef
    set V := Submodule.span B (T : Set Ω) with hVdef
    have hk : ∀ k, ∃ E, c k ^ E * z ∈ V := by
      intro k
      obtain ⟨D, hD⟩ := secChart_loc Q H (J k) I
        (secChart_mono (subset_unionChart_right (J k) I) hz)
      have hspan := secChart_le_span Q H A.m b h0 (J k) (hh (J k)) (hG k) hD
      have hP : ∀ y ∈ Submodule.span (ampleSubalg H.toSubSystem A.m (A.h j) (J k) (hh (J k)))
          (G k : Set Ω), ∃ E, c k ^ E * y ∈ V := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem γ hγ => exact ⟨M₀, Submodule.subset_span (by exact_mod_cast hTmem k γ hγ)⟩
        | zero => exact ⟨0, by rw [mul_zero]; exact V.zero_mem⟩
        | add y y' _ _ h1 h2 =>
          obtain ⟨E, hE⟩ := h1
          obtain ⟨E', hE'⟩ := h2
          refine ⟨E + E', ?_⟩
          have : c k ^ (E + E') * (y + y') =
              (⟨c k ^ E', pow_mem (hcB k I) _⟩ : B) • (c k ^ E * y) +
              (⟨c k ^ E, pow_mem (hcB k I) _⟩ : B) • (c k ^ E' * y') := by
            simp only [Subalgebra.smul_def, smul_eq_mul]
            ring
          rw [this]
          exact V.add_mem (V.smul_mem _ hE) (V.smul_mem _ hE')
        | smul β y _ h1 =>
          obtain ⟨E, hE⟩ := h1
          obtain ⟨D', hD'⟩ := ampleChart_loc H I (J k)
            (ampleChart_mono (subset_unionChart_right I (J k)) β.2)
          obtain ⟨e, he⟩ := hrat k I
          have hβ : c k ^ (e * D') * β ∈ B := by
            have := mul_mem (pow_mem (show _ ∈ B from he) D') (show _ ∈ B from hD')
            rwa [show c k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) =
              c k ^ e * chartRatio (J k) I from rfl,
              pow_mul_cancel (chartRatio_mul_chartRatio I (J k))] at this
          refine ⟨e * D' + E, ?_⟩
          have : c k ^ (e * D' + E) * (β • y) = (⟨_, hβ⟩ : B) • (c k ^ E * y) := by
            simp only [Subalgebra.smul_def, smul_eq_mul]
            ring
          rw [this]
          exact V.smul_mem _ hE
      obtain ⟨E, hE⟩ := hP _ hspan
      refine ⟨E, ?_⟩
      have hr : chartRatio I (J k) ^ D ∈ B :=
        mem_ampleSubalg_of_mem_chartRing (hh I) (pow_mem (chartRatio_mem I (J k)) D)
      have : c k ^ E * z = (⟨_, hr⟩ : B) • (c k ^ E * (chartRatio (J k) I ^ D * z)) := by
        rw [Subalgebra.smul_def, smul_eq_mul]
        calc c k ^ E * z = c k ^ E * (chartRatio (J k) I * chartRatio I (J k)) ^ D * z := by
              rw [chartRatio_mul_chartRatio, one_pow, mul_one]
          _ = _ := by ring
      rw [this]
      exact V.smul_mem _ hE
    choose E hE using hk
    set E₀ := Finset.univ.sup E with hE₀
    have hbig : ∀ k, c k ^ E₀ * z ∈ V := by
      intro k
      have hle : E k ≤ E₀ := Finset.le_sup (Finset.mem_univ k)
      have : c k ^ E₀ * z = (⟨c k ^ (E₀ - E k), pow_mem (hcB k I) _⟩ : B) • (c k ^ E k * z) := by
        rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [this]
      exact V.smul_mem _ (hE k)

    let cB : Fin n → B := fun k => ⟨c k, hcB k I⟩
    let aB : Fin n → B := fun k => ⟨a k, haB k I⟩
    have hspan : Ideal.span (Set.range cB) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have : (1 : B) = ∑ k, aB k * cB k := Subtype.ext (by simp [aB, cB, hsum])
      rw [this]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
    have hpow := Ideal.span_pow_eq_top _ hspan E₀
    have hle : Ideal.span ((fun y : B => y ^ E₀) '' Set.range cB) ≤
        V.comap (LinearMap.toSpanSingleton B Ω z) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.toSpanSingleton_apply,
        Subalgebra.smul_def, smul_eq_mul, SubmonoidClass.coe_pow, cB]
      exact hbig k
    rw [hpow, top_le_iff] at hle
    have h1 : (1 : B) ∈ V.comap (LinearMap.toSpanSingleton B Ω z) := hle ▸ Submodule.mem_top
    simpa using h1
  refine ⟨T.card, fun t => (T.equivFin.symm t : Ω), fun t I => hT _ (T.equivFin.symm t).2 I,
    fun I z k hz => ?_⟩
  obtain ⟨f, hf⟩ := Submodule.mem_span_finset'.mp (stepC I z ⟨k, hz⟩)
  have hev : ∀ᶠ e in Filter.atTop, ∀ t : Fin T.card,
      (f (T.equivFin.symm t) : Ω) * A.h j ^ e ∈ (H.pow (A.m * e)).sub I := by
    rw [Filter.eventually_all]
    intro t
    exact ampleChart_eventually (hh I) (f (T.equivFin.symm t)).2
  obtain ⟨e, he⟩ := hev.exists
  refine ⟨e, fun t => (f (T.equivFin.symm t) : Ω), he, ?_⟩
  rw [← hf, ← Equiv.sum_comp T.equivFin.symm]
  simp only [Subalgebra.smul_def, smul_eq_mul]
end AmpleAffineGen
end GroundTheory.Heights₂.Heights.Kleiman
