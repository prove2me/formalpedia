-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:24.671949+00:00
-- url     : https://prove2.me/submissions/19062c78-2847-4329-bde4-f58d61d5c427

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_zero_550d911f4552
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_C_a37c90fadbec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_add_c9d56145775a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_smul_8e170cd1372f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_mul_3ef960ca9ac7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V : Ideal (MRingOver S ι)}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {T : Submonoid (MRingOver S ι)} {γ : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ locPart ι (quotPart S V) T γ) :
    ∃ (g : MRingOver S ι) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ ((∀ k, 0 ≤ γ k + a k) ∨ g = 0) ∧
      x = LocalizedModule.mk (Ideal.Quotient.mk V g) t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨g, hg, hd, rfl⟩ := exists_homog_of_mem_quotPart hm
    exact ⟨g, t, a, ht, hg, hd, rfl⟩
  | zero =>
    refine ⟨0, 1, 0, ?_, isMultiHomog_zero _, Or.inr rfl, ?_⟩
    · simpa using isMultiHomog_C (S := S) (ι := ι) 1
    · rw [map_zero, LocalizedModule.zero_mk]
  | add x x' _ _ h h' =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    obtain ⟨g', t', a', ht', hg', hd', rfl⟩ := h'
    rcases hd with hd | rfl
    swap
    · exact ⟨g', t', a', ht', hg', hd', by rw [map_zero, LocalizedModule.zero_mk, zero_add]⟩
    rcases hd' with hd' | rfl
    swap
    · exact ⟨g, t, a, ht, hg, Or.inl hd, by rw [map_zero, LocalizedModule.zero_mk, add_zero]⟩
    refine ⟨(t' : MRingOver S ι) * g + (t : MRingOver S ι) * g', t * t', a + a', ?_, ?_, Or.inl ?_, ?_⟩
    · simpa using isMultiHomog_mul ht ht'
    · have e1 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a' + (fun k => (γ k + a k).toNat) := by
        funext k
        have := hd k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      have e2 : (fun k => (γ k + ((a + a') k : ℕ)).toNat) = a + (fun k => (γ k + a' k).toNat) := by
        funext k
        have := hd' k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      refine isMultiHomog_add ?_ ?_
      · rw [e1]; exact isMultiHomog_mul ht' hg
      · rw [e2]; exact isMultiHomog_mul ht hg'
    · intro k
      have := hd k
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [LocalizedModule.mk_add_mk]
      congr 1
  | smul s x _ h =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    refine ⟨s • g, t, a, ht, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [LocalizedModule.smul'_mk, ← Ideal.Quotient.mkₐ_eq_mk S, map_smul]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
