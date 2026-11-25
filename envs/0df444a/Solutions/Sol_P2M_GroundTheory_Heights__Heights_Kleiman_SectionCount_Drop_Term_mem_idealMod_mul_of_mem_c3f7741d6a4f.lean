-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:06.928598+00:00
-- url     : https://prove2.me/submissions/be16b6c5-ed0b-4f2c-899e-7f4743a37ad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce

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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution (L : LineBundle k x) (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {I K : Chart x} (h : I.1 ⊆ K.1) (hK : ∀ i ∈ K.1, (X i : Poly k N) ∉ pp) {s : Ω}
    (hs : s ∈ L.sub I) (hsK : s ∈ idealMod pp K * L.sub K) : s ∈ idealMod pp I * L.sub I := by
  obtain ⟨u, hu, hus⟩ : ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧
      (u : Ω) * s ∈ idealMod pp I * L.sub I := by
    refine Submodule.mul_induction_on (C := fun r => ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧
      (u : Ω) * r ∈ idealMod pp I * L.sub I) hsK ?_ ?_
    · intro a ha l hl
      obtain ⟨u₁, hu₁, h₁⟩ := exists_isUnit_mul_mem_idealMod h ha
      obtain ⟨u₂, hu₂, h₂⟩ := (L.mem_iff I K h l).mp hl
      refine ⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
      have : ((u₁ * u₂ : chartRing k x I) : Ω) * (a * l) = ((u₁ : Ω) * a) * ((u₂ : Ω) • l) := by
        simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
      rw [this]
      exact Submodule.mul_mem_mul h₁ h₂
    · rintro y₁ y₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
      refine ⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
      have : ((u₁ * u₂ : chartRing k x I) : Ω) * (y₁ + y₂) =
          u₂ • ((u₁ : Ω) * y₁) + u₁ • ((u₂ : Ω) * y₂) := by
        simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  have hu' : (u : Ω) ∉ idealMod pp I := by
    intro hmem
    have hK1 : (u : Ω) ∈ idealMod pp K := (idealSys x pp).mono I K h _ hmem
    obtain ⟨v, hv⟩ := hu
    apply one_not_mem_idealMod hW hle hK
    have hvu : ((↑v⁻¹ : chartRing k x K) : Ω) * (u : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul v)
      rw [hv] at this
      exact this
    rw [← hvu, ← chartRing_smul_def]
    exact Submodule.smul_mem _ _ hK1
  obtain ⟨L', hL'⟩ := L.invertible I
  refine mem_of_mul_mem (L := 1) (L' := 1) (mul_one 1) hL' (idealMod_prime hW hle fun i hi => hK i (h hi))
    (s := (u : Ω)) (Submodule.mem_one.mpr ⟨u, rfl⟩) (by rwa [mul_one]) hs (by rwa [one_mul])
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
