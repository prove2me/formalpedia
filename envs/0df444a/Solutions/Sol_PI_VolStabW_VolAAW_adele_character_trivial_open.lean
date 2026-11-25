-- Prove2me | solution 1 for PI.VolStabW.VolAAW.adele_character_trivial_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:59.840872+00:00
-- url     : https://prove2.me/submissions/8d34c516-8255-478b-8eb4-3b1b4ea1d62f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolS
import Theorems.Thm_PI_VolStabW_VolAAW_pairA_nsmul0
import Theorems.Thm_PI_VolStabW_VolAAW_ev_pow_mul_sub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_VolStabW_VolAAW_eq_one_of_pow
import Theorems.Thm_PI_VolStabW_unifV_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabW.VolAAW
theorem _root_.solution (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ),
      ∀ y ∈ U0 I n, ψ (pairA F 0 y) = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ m : ℕ, w ∈ I → ∀ s ∈ w.adicCompletionIntegers F,
      ∃ h : unifV w ^ m * s ∈ ((w.adicCompletionIntegers F : Set (w.adicCompletion F))),
        (⟨unifV w ^ m * s, h⟩ : ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈ u w := by
    intro w
    by_cases hw : w ∈ I
    · obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 (hu w hw).1
      have h0 : (0 : Fv F w) ∈ t := by
        have := (hu w hw).2
        rw [← hte] at this
        exact this
      obtain ⟨m, hm⟩ := ev_pow_mul_sub w (ht.mem_nhds h0)
      refine ⟨m, fun _ s hs => ⟨mul_mem (pow_mem (unifV_spec w).2.2 m) hs, ?_⟩⟩
      rw [← hte]
      exact hm s hs
    · exact ⟨0, fun h => absurd h hw⟩
  choose n hn using hn
  refine ⟨I, n, ?_⟩
  have hbig : ∀ y ∈ U0 I n, 1 / 2 < (ψ (pairA F 0 y)).re := by
    intro y hy
    let x : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      fun w => ⟨y w, hy.1 w⟩
    have hx : x ∈ (I : Set _).pi u := by
      intro w hw
      have hne : unifV w ^ n w ≠ 0 := pow_ne_zero _ (unifV_spec w).1
      obtain ⟨h, hmem⟩ := hn w hw _ (hy.2 w hw)
      have e : (⟨unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w), h⟩ :
          ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) = x w := by
        apply Subtype.ext
        show unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w) = y w
        rw [mul_inv_cancel_left₀ hne]
      rw [← e]
      exact hmem
    have e : Φ x = pairA F 0 y := by
      show pairA F 0 _ = _
      congr 1
    have := hsub hx
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  apply eq_one_of_pow _ (hψ.2.1 _)
  intro k
  rw [← AddChar.map_nsmul_eq_pow, ← pairA_nsmul0]
  exact hbig _ (AddSubgroup.nsmul_mem _ hy _)
end PI.VolStabW.VolAAW
