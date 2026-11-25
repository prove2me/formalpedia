-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdAbs.exists_selfDual_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:05.460872+00:00
-- url     : https://prove2.me/submissions/8a5c7ee5-f5b0-4ab1-be6b-5c2b4366b2f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Theorems.Thm_PI_OmFibreUniq_W_SdAbs_haar_smul_preimage
import Theorems.Thm_PI_OmFibreUniq_W_SdChar_Aset_mem_nhds
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_isClosed_ann
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_selfDual_of_pairs
import Theorems.Thm_PI_VolStabSW_SdUniqW_mem_of_psi
import Theorems.Thm_PI_VolStabSW_exists_unif_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdAbs
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)
namespace PI.OmFibreUniq.W.SdAbs
theorem _root_.solution (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
    (hψn : ∀ r, ‖ψ0 r‖ = 1) (hnt : ∃ y, ψ0 y ≠ 1)
    (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBjc : Continuous (fun p : V × V => B p.1 p.2)) (hD : DualAt v B) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y)) := by
  obtain ⟨π, hπ0, hπt, -⟩ := PI.VolStabSW.exists_unif_Fv v
  set χ : V → V → ℂ := fun x y => ψ0 (B x y) with hχdef
  have hχc : Continuous (fun p : V × V => χ p.1 p.2) :=
    hψc.comp hBjc
  have hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y := fun x t y => by
    simp only [hχdef]; rw [hBa, hψa]
  have hsym : ∀ x y, χ x y = χ y x := fun x y => by simp only [hχdef]; rw [hBsym]
  have hn : ∀ x y, ‖χ x y‖ = 1 := fun x y => hψn _
  obtain ⟨L, hLc, hLo, hsL, hK⟩ := hD
  have hBzr : ∀ x, B x 0 = 0 := fun x => by rw [hBsym]; exact B_zero_left v B hBs x
  have hQ : ∀ᶠ q in 𝓝 (0 : V), ∀ x ∈ (L : Set V), B x q ∈ Aset v ψ0 := by
    have hP : ∀ x ∈ (L : Set V), ∀ᶠ z : V × V in 𝓝 ((0 : V), x), B z.2 z.1 ∈ Aset v ψ0 :=
      fun x _ => by
        have hc : Continuous fun z : V × V => B z.2 z.1 :=
          hBjc.comp (continuous_snd.prodMk continuous_fst)
        exact (hc.tendsto ((0 : V), x)).eventually_mem
          (by rw [show B ((0 : V), x).2 ((0 : V), x).1 = 0 from hBzr x]
              exact Aset_mem_nhds v ψ0 hψc hψa hψn)
    exact hLc.eventually_forall_of_forall_eventually (P := fun q x => B x q ∈ Aset v ψ0) hP
  have hNo0 : IsOpen (ann χ (L : Set V)) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
      have := (continuous_sub_right y).tendsto y
      rwa [sub_self] at this
    filter_upwards [ht hQ] with y' hy'
    intro x hx
    have hq : ψ0 (B x (y' - y)) = 1 := by
      have := hy' x hx 1 (one_mem _)
      rwa [one_mul] at this
    have hyx := hy x hx
    show ψ0 (B x y') = 1
    have e1 : y' = y + (y' - y) := by abel
    rw [e1, hBsym, hBa, hψa, hBsym y, hBsym (y' - y)]
    rw [show ψ0 (B x y) = 1 from hyx, hq, one_mul]
  have hNcl : IsClosed (ann χ (L : Set V)) := isClosed_ann χ hχc L
  have hNc0 : IsCompact (ann χ (L : Set V)) := by
    obtain ⟨y0, hy0⟩ := hnt
    obtain ⟨K, hKc, hKs⟩ := hK y0
    refine hKc.of_isClosed_subset hNcl fun y hy => hKs fun x hx => ?_
    apply mem_of_psi v ψ0 y0 _ hy0
    intro s hs'
    obtain ⟨x', hx', hB'⟩ := hsL s hs' x hx
    rw [← hB' y]
    exact hy x' hx'

  set M : ℕ → AddSubgroup V := fun k => L.comap (DistribMulAction.toAddMonoidHom V (π ^ k))
    with hMdef
  have hMset : ∀ k, (M k : Set V) = (fun x => π ^ k • x) ⁻¹' (L : Set V) := fun k => rfl
  have hπk : ∀ k, π ^ k ≠ 0 := fun k => pow_ne_zero k hπ0
  have hann : ∀ k, ann χ (M k : Set V) = (fun y => (π ^ k)⁻¹ • y) ⁻¹' ann χ (L : Set V) := by
    intro k
    ext y
    constructor
    · intro hy x hx
      have hx' : (π ^ k)⁻¹ • x ∈ (M k : Set V) := by
        show π ^ k • ((π ^ k)⁻¹ • x) ∈ L
        rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul]
      have := hy _ hx'
      simp only [hχdef] at this ⊢
      rwa [hBs, hBsym, ← hBs, hBsym] at this
    · intro hy x hx
      have := hy _ hx
      change ψ0 (B (π ^ k • x) ((π ^ k)⁻¹ • y)) = 1 at this
      simp only [hχdef]
      rwa [hBs, hBsym, hBs, hBsym, ← mul_assoc, mul_inv_cancel₀ (hπk k), one_mul] at this
  have hMo : ∀ k, IsOpen (M k : Set V) := fun k => by
    rw [hMset]; exact hLo.preimage (continuous_const_smul _)
  have hMc : ∀ k, IsCompact (M k : Set V) := fun k => by
    rw [hMset]
    exact (Homeomorph.smulOfNeZero (π ^ k) (hπk k)).isCompact_preimage.2 hLc
  have hNo : ∀ k, IsOpen (ann χ (M k : Set V)) := fun k => by
    rw [hann]; exact hNo0.preimage (continuous_const_smul _)
  have hNc : ∀ k, IsCompact (ann χ (M k : Set V)) := fun k => by
    rw [hann]
    exact (Homeomorph.smulOfNeZero ((π ^ k)⁻¹) (inv_ne_zero (hπk k))).isCompact_preimage.2 hNc0
  have hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k := by
    intro y
    have ht : Tendsto (fun k => π ^ k • y) atTop (𝓝 0) := by simpa using hπt.smul_const y
    exact (ht.eventually_mem (hLo.mem_nhds L.zero_mem)).mono fun k hk => hk
  have hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k : Set V) ⊆ U := by
    intro U hU
    have hP : ∀ w ∈ ann χ (L : Set V), ∀ᶠ z : Fv F v × V in 𝓝 ((0 : Fv F v), w), z.1 • z.2 ∈ U :=
      fun w _ => (continuous_smul.tendsto ((0 : Fv F v), w)).eventually_mem
        (by rw [show ((0 : Fv F v), w).1 • ((0 : Fv F v), w).2 = (0 : V) by simp]; exact hU)
    have hev := hNc0.eventually_forall_of_forall_eventually (P := fun c w => c • w ∈ U) hP
    filter_upwards [hπt.eventually hev] with k hk y hy
    rw [hann] at hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul] at this

  let μ0 : Measure V := Measure.addHaar
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hNm : MeasurableSet (ann χ (L : Set V)) := hNcl.measurableSet
  have hL0 : μ0 (L : Set V) ≠ 0 := (hLo.measure_pos μ0 ⟨0, L.zero_mem⟩).ne'
  have hLt : μ0 (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hgen : ∀ k, μ0 (M k : Set V) * μ0 (ann χ (M k : Set V)) =
      μ0 (L : Set V) * μ0 (ann χ (L : Set V)) := by
    intro k
    obtain ⟨c1, hc1⟩ := haar_smul_preimage v μ0 (π ^ k) (hπk k)
    obtain ⟨c2, hc2⟩ := haar_smul_preimage v μ0 ((π ^ k)⁻¹) (inv_ne_zero (hπk k))
    have hid : (fun y : V => (π ^ k)⁻¹ • y) ⁻¹' ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) =
        (L : Set V) := by
      ext y; simp [smul_smul, mul_inv_cancel₀ (hπk k)]
    have hm1 : MeasurableSet ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) :=
      hLm.preimage (continuous_const_smul _).measurable
    have h12 : c2 * c1 = 1 := by
      have := hc2 _ hm1
      rw [hid, hc1 _ hLm, ← mul_assoc] at this
      have h3 : μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ = 1 := ENNReal.mul_inv_cancel hL0 hLt
      calc c2 * c1 = c2 * c1 * μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ := by
            rw [mul_assoc (c2 * c1), h3, mul_one]
        _ = 1 := by rw [← this, h3]
    rw [hann, hMset, hc1 _ hLm, hc2 _ hNm]
    calc c1 * μ0 (L : Set V) * (c2 * μ0 (ann χ (L : Set V)))
        = (c2 * c1) * (μ0 (L : Set V) * μ0 (ann χ (L : Set V))) := by ring
      _ = _ := by rw [h12, one_mul]
  exact selfDual_of_pairs χ hχc hχ hsym hn M hMc hMo hNc hNo hex hsh μ0
    (fun k => (hgen k).trans (hgen 0).symm)
end PI.OmFibreUniq.W.SdAbs
