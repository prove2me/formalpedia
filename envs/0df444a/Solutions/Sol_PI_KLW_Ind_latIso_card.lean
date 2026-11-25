-- Prove2me | solution 1 for PI.KLW.Ind.latIso_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:01.114202+00:00
-- url     : https://prove2.me/submissions/c59952b5-c45a-46e0-ae4d-030f461f8511

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_exists_refl
import Theorems.Thm_PI_KLW_Ind_unimod_preimage
import Theorems.Thm_PI_KLW_Ind_spans_preimage
import Theorems.Thm_PI_KLW_Ind_split_step
import Theorems.Thm_PI_KLW_Ind_card_ne_sub
import Theorems.Thm_PI_KLW_Ind_hf_neg_left
import Theorems.Thm_PI_KLW_Ind_hf_neg_right
import Theorems.Thm_PI_KLW_Ind_hf_single_single
import Theorems.Thm_PI_KLW_Ind_neg_mem_of
import Theorems.Thm_PI_KLW_Ind_unitary_symm
import Theorems.Thm_PI_KLW_Ind_unitary_trans
import Theorems.Thm_PI_KLW_Ind_zero_mem_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution (hN : NormOne) {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ)
    (hK : Module.finrank ℚ K = 2) (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = k → ∀ L : Set (ι → K),
      Unimod K c p L → Spans K L →
        ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by
  intro k
  induction k with
  | zero =>
    intro ι _ hk L hL _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hk
    refine ⟨LinearEquiv.refl K _, fun v w => rfl, fun v => ?_⟩
    have h0 := zero_mem_of hL
    constructor
    · intro _ i
      exact isEmptyElim i
    · intro _
      rwa [Subsingleton.elim v 0]
  | succ k ih =>
    intro ι _ hk L hL hS
    classical
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i0⟩ := ‹Nonempty ι›
    obtain ⟨e, heL, hee⟩ := hN K c p ι L hK hc hp hs hL hS
    obtain ⟨e1, he1L, he1, hne⟩ :
        ∃ e1 ∈ L, hf c e1 e1 = 1 ∧ hf c (Pi.single i0 1) e1 ≠ 1 := by
      by_cases h1 : hf c (Pi.single i0 1) e = 1
      · refine ⟨-e, neg_mem_of hL heL, by rw [hf_neg_left, hf_neg_right, neg_neg, hee], ?_⟩
        rw [hf_neg_right, h1]
        norm_num
      · exact ⟨e, heL, hee, h1⟩
    obtain ⟨σ, hσ, hσe⟩ :=
      exists_refl c hc (Pi.single i0 1) e1 (hf_single_single c i0) he1 hne
    obtain ⟨u'', hu'', hmem''⟩ := split_step c p i0 (σ ⁻¹' L) (unimod_preimage c p hσ hL)
      (spans_preimage hS) (by show σ _ ∈ L; rw [hσe]; exact he1L)
      (fun L' hL' hS' => ih _ (card_ne_sub i0 k hk) L' hL' hS')
    refine ⟨σ.symm.trans u'', unitary_trans (unitary_symm hσ) hu'', fun v => ?_⟩
    have h := hmem'' (σ.symm v)
    have hm : σ.symm v ∈ σ ⁻¹' L ↔ v ∈ L := by
      show σ (σ.symm v) ∈ L ↔ v ∈ L
      rw [LinearEquiv.apply_symm_apply]
    rw [hm] at h
    simpa only [LinearEquiv.trans_apply] using h
end PI.KLW.Ind
