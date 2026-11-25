-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:03.049975+00:00
-- url     : https://prove2.me/submissions/30a20c56-463c-41af-a9e4-08f87a30fe2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_not_mem_idealMod_1352903a0e1d

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
theorem _root_.solution (G : SubSystem k x Ω) (hG : G.Generated)
    (hinv : ∀ I, ∃ G' : Submodule (chartRing k x I) Ω, G.sub I * G' = 1) (hW : pp.IsPrime)
    (hle : primeOf (S := k) x ≤ pp) {I : Chart x} (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∃ t ∈ G.secs, t ∉ idealMod pp I * G.sub I := by
  by_contra hcon
  push Not at hcon
  apply one_not_mem_idealMod hW hle hI
  have hle' : G.sub I ≤ idealMod pp I * G.sub I := by
    calc G.sub I = Submodule.span _ (G.secs : Set Ω) := (hG I).symm
      _ ≤ _ := by
        rw [Submodule.span_le]
        intro t ht
        exact hcon t ht
  obtain ⟨G', hG'⟩ := hinv I
  have h1 : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I := by
    calc (1 : Submodule (chartRing k x I) Ω) = G.sub I * G' := hG'.symm
      _ ≤ idealMod pp I * G.sub I * G' := mul_le_mul' hle' le_rfl
      _ = idealMod pp I := by rw [mul_assoc, hG', mul_one]
  exact Submodule.one_le.mp h1
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
