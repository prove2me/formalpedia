-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpExcessDecreases_proof_f7630c0bf469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:52.685394+00:00
-- url     : https://prove2.me/submissions/72b7827e-b480-43c8-b5f9-75b79b77af54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ZeroLeDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_zero_le_divCycle_3ccb42c86900
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleFiniteSupport_proof_010201f3d63e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53


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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpExcessDecreases
theorem _root_.solution (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon
  set N := commonExcess ϖ P f g s with hN
  have hε : 0 < N := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  have hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} =>
      (divCycle P s G.1 * ratDiv P f g G.1).toNat) := by
    refine (((DivCycleFiniteSupport.proof O K ι P s).image
      fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_
    rintro _ ⟨G, rfl⟩
    by_cases h : divCycle P s G.1 = 0
    · left; simp [h]
    · right; exact ⟨G.1, h, rfl⟩
  have hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G →
      y ≤ ratDiv P f g G → x * y ≤ N := by
    intro G hG x y hx hy hxG hyG
    have h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N := le_ciSup hbdd ⟨G, hG⟩
    have h2 : x * y ≤ divCycle P s G * ratDiv P f g G := mul_le_mul hxG hyG hy (hx.trans hxG)
    exact h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))

  have hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1 := by
    intro x y hx h
    rcases lt_or_ge 0 x with hx' | hx'
    · rcases lt_or_ge 0 y with hy | hy
      · have h1 := h hx' hy
        generalize x * y = p at h1 ⊢
        omega
      · have h1 : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
        generalize x * y = p at h1 ⊢
        omega
    · obtain rfl : x = 0 := le_antisymm hx' hx
      simp
  have hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) //
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'} := ⟨⟨⊤, Submodule.mem_top⟩⟩
  constructor
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ hx.le (by linarith) h1 h2
      nlinarith
    omega
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ (by linarith) hy.le h1 h2
      nlinarith
    omega
end BlowUpExcessDecreases
end GroundTheory.Heights₂.Heights.NumbersDVR
